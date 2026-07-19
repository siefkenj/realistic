use crate::computable::scale;

use super::prescaled_value::*;
use super::*;

#[derive(Clone, Debug, PartialEq)]
pub struct StackComputable {
    /// Stack of computations to get the number, stored in RPN.
    stack: Vec<OpStack>,
    literals: Vec<Literal>,
    // required_precisions: Vec<RequiredPrecision>,
}

impl StackComputable {
    /// Don't bother with computations that require more precision than this.
    const STOP_PRECISION: Precision = -10000;

    pub fn one() -> Self {
        StackComputable {
            stack: vec![OpStack::One],
            literals: vec![],
        }
    }
    pub fn rational(r: Rational) -> Self {
        StackComputable {
            stack: vec![OpStack::Literal],
            literals: vec![Literal::Ratio(r)],
        }
    }
    pub fn integer(i: BigInt) -> Self {
        StackComputable {
            stack: vec![OpStack::Literal],
            literals: vec![Literal::Int(i)],
        }
    }
    pub fn add(self, other: &Self) -> Self {
        const OP: BinaryOp = BinaryOp::Add;
        let Self {
            mut stack,
            mut literals,
        } = self;
        stack.extend_from_slice(&other.stack);
        stack.push(OpStack::BinaryOp(OP));
        literals.extend_from_slice(&other.literals);
        StackComputable { stack, literals }
    }
    pub fn mul(self, other: &Self) -> Self {
        const OP: BinaryOp = BinaryOp::Mul;
        let Self {
            mut stack,
            mut literals,
        } = self;
        stack.extend_from_slice(&other.stack);
        stack.push(OpStack::BinaryOp(OP));
        literals.extend_from_slice(&other.literals);
        StackComputable { stack, literals }
    }
    pub fn sqrt(self) -> Self {
        const OP: UnaryOp = UnaryOp::Sqrt;
        let Self {
            mut stack,
            mut literals,
        } = self;
        stack.push(OpStack::UnaryOp(OP));
        StackComputable { stack, literals }
    }
    pub fn inverse(self) -> Self {
        const OP: UnaryOp = UnaryOp::Inverse;
        let Self {
            mut stack,
            mut literals,
        } = self;
        stack.push(OpStack::UnaryOp(OP));
        StackComputable { stack, literals }
    }
    /// Compute exp of the value, but only for values between 0 and 0.5.
    pub fn exp(self) -> Self {
        const OP: UnaryOp = UnaryOp::PrescaledExp;
        let Self {
            mut stack,
            mut literals,
        } = self;
        stack.push(OpStack::UnaryOp(OP));
        StackComputable { stack, literals }
    }
    /// Compute ln(1+x). Assumes |x| < 1/2.
    pub fn ln_one_plus_x(self) -> Self {
        const OP: UnaryOp = UnaryOp::PrescaledLn;
        let Self {
            mut stack,
            mut literals,
        } = self;
        stack.push(OpStack::UnaryOp(OP));
        StackComputable { stack, literals }
    }
    /// Compute cos(x) where |x| < 1
    pub fn cos(self) -> Self {
        const OP: UnaryOp = UnaryOp::PrescaledCos;
        let Self {
            mut stack,
            mut literals,
        } = self;
        stack.push(OpStack::UnaryOp(OP));
        StackComputable { stack, literals }
    }

    /// Approximate this `StackComputable` to a `BigInt` with the given precision.
    /// The approximation is scale. Put the radix point at `p` places to the _right_ of the least significant bit,
    /// to get the "correct" approximation. For example `1/4` with `p = -2` would be `1b`, which should be interpreted as `.01b`,
    /// similarly, `1/4` with `p = -3` would be `10b`, which should be interpreted as `.010b`.
    pub fn approximate(&self, p: Precision) -> BigInt {
        let mut cache = vec![Cache::Empty; self.stack.len()];
        let mut required_precisions = vec![p; self.stack.len()];
        update_required_precisions(self, self.stack.len() - 1, p, &mut required_precisions);

        // Our required precisions are now calculated, though they may not be sufficient, since some operations don't know what precision they
        // require until they see the actual numbers involved.
        //
        // We start computing left-to-right. If we encounter a situation where we need more precision, we bump the precision and start over.

        let mut literal_index = 0_usize;
        let mut next_i = 0_usize;
        let mut op: &OpStack;
        while (next_i < self.stack.len()) {
            // Sometimes we will need to jump backwards in the stack and recompute things with higher precision.
            // When we do, we do so by setting `next_i` and continuing.
            let i = next_i;
            next_i += 1;

            op = &self.stack[i];
            let needed_precision = required_precisions[i];
            if needed_precision < Self::STOP_PRECISION {
                panic!(
                    "Required precision {needed_precision} is too low, stopping computation to avoid infinite loop"
                )
            }

            // If we have already computed this value with sufficient precision, do nothing.
            if let Cache::Computed(cached) = &cache[i]
                && cached.meets_precision(needed_precision)
            {
                match op {
                    OpStack::Literal => {
                        literal_index += 1;
                    }
                    _ => {}
                }
                continue;
            }
            // If we made it hear, this value has not been computed, or has not been computed with sufficient precision.
            match op {
                OpStack::Literal => {
                    let literal = &self.literals[literal_index];

                    let approx = literal.into_prescaled_value(needed_precision);
                    cache[i] = Cache::Computed(approx);
                    literal_index += 1;
                }
                OpStack::One => {
                    cache[i] = Cache::Computed(PrescaledValue(
                        scale(signed::ONE.clone(), needed_precision),
                        needed_precision,
                    ));
                }
                OpStack::Pi => {
                    unimplemented!()
                }
                OpStack::UnaryOp(op) => {
                    let args = self.operator_argument_indices(i);
                    if let (Some(arg_index), None) = args {
                        if let Cache::Computed(arg) = &cache[arg_index] {
                            // We have a pre-computed argument.
                            let approx = op.approximate_unary_op(arg, needed_precision);
                            match approx {
                                AttemptedComputation::Success(approx, approx_precision) => {
                                    cache[i] =
                                        Cache::Computed(PrescaledValue(approx, approx_precision));
                                }
                                AttemptedComputation::NeedMorePrecision(new_precision) => {
                                    // We need more precision from our argument.
                                    required_precisions[arg_index] = new_precision;
                                    // Jump back to the beginning to recompute
                                    // Since we have to keep track of the `literal_index`, it is easiest to jump back to the beginning
                                    // rather than to just the previous argument. Since the values are cached, this shouldn't waste too much time.
                                    next_i = 0;
                                    literal_index = 0;
                                    continue;
                                }
                                AttemptedComputation::Failed => {
                                    panic!("Computation failed, even with the required precision")
                                }
                            }
                        } else {
                            panic!("Expected argument to already be pre-computed and cached")
                        }
                    } else {
                        panic!("Unary operator should have one argument")
                    }
                }
                OpStack::BinaryOp(op) => {
                    let args = self.operator_argument_indices(i);
                    if let (Some(arg1_index), Some(arg2_index)) = args {
                        if let (Cache::Computed(arg1), Cache::Computed(arg2)) =
                            (&cache[arg1_index], &cache[arg2_index])
                        {
                            // We have pre-computed arguments.
                            let approx = op.approximate_binary_op(arg1, arg2, needed_precision);
                            match approx {
                                AttemptedComputation::Success(approx, approx_precision) => {
                                    cache[i] =
                                        Cache::Computed(PrescaledValue(approx, approx_precision));
                                }
                                AttemptedComputation::NeedMorePrecision(new_precision) => {
                                    // We need more precision from both arguments.
                                    required_precisions[arg1_index] = new_precision;
                                    required_precisions[arg2_index] = new_precision;
                                    // Jump back to the beginning
                                    next_i = 0;
                                    literal_index = 0;
                                    continue;
                                }
                                AttemptedComputation::Failed => {
                                    panic!("Computation failed, even with the required precision")
                                }
                            }
                        } else {
                            panic!("Expected arguments to already be pre-computed and cached")
                        }
                    } else {
                        panic!("Binary operator should have two arguments")
                    }
                }
            }
        }

        // The last value in the Cache should be the result of the computation.
        match cache.last() {
            Some(Cache::Computed(result)) => {
                // In theory the result should have the correct precision.
                if result.1 != p {
                    panic!(
                        "The result has precision {}, but we expected precision {}",
                        result.1, p
                    );
                }
                result.0.clone()
            }
            _ => {
                unreachable!("The last value in the cache should be the result of the computation")
            }
        }
    }

    /// Returns the indices of the arguments for the operator at `operator_index`, if they exist.
    pub fn operator_argument_indices(
        &self,
        operator_index: usize,
    ) -> (Option<usize>, Option<usize>) {
        match &self.stack[operator_index] {
            OpStack::Literal | OpStack::Pi | OpStack::One => (None, None),
            OpStack::UnaryOp(_) => {
                if operator_index == 0 {
                    (None, None)
                } else {
                    (Some(operator_index - 1), None)
                }
            }
            OpStack::BinaryOp(_) => {
                if operator_index == 0 {
                    (None, None)
                } else if operator_index == 1 {
                    (Some(operator_index - 1), None)
                } else {
                    let first_arg_index = operator_index - 1;

                    // Arguments are stored using RPN. We need to walk backwards until we find the next argument.
                    // For example, `1 2 + 3 4 + +`, we should report index (5,2) (zero-indexed).
                    fn num_args(op: &OpStack) -> i32 {
                        match op {
                            OpStack::Literal | OpStack::Pi | OpStack::One => 0,
                            OpStack::UnaryOp(_) => 1,
                            OpStack::BinaryOp(_) => 2,
                        }
                    }
                    let mut args_to_consume = num_args(&self.stack[first_arg_index]);
                    for i in (0..first_arg_index).rev() {
                        if args_to_consume == 0 {
                            return (Some(i), Some(first_arg_index));
                        }
                        args_to_consume += num_args(&self.stack[i]) - 1;
                    }

                    (Some(first_arg_index), None)
                }
            }
        }
    }
}

/// Walk backwards starting at `start_index` and update the `required_precisions` vector according to the precision each operator needs.
fn update_required_precisions(
    stack_computable: &StackComputable,
    start_index: usize,
    start_required_precision: Precision,
    required_precisions: &mut Vec<Precision>,
) {
    let mut index_stack = vec![(start_index, start_required_precision)];
    while let Some((i, current_required_precision)) = index_stack.pop() {
        required_precisions[i] = current_required_precision;
        let next_required_precision =
            stack_computable.stack[i].precision_needed(current_required_precision);
        match stack_computable.operator_argument_indices(i) {
            (None, Some(..)) => unreachable!(),
            (None, None) => {
                // No arguments
            }
            (Some(arg1_index), None) => {
                index_stack.push((arg1_index, next_required_precision));
            }
            (Some(arg1_index), Some(arg2_index)) => {
                index_stack.push((arg1_index, next_required_precision));
                index_stack.push((arg2_index, next_required_precision));
            }
        }
    }
}

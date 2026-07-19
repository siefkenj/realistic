use num::bigint::{Sign, ToBigInt};
use num::{Signed, Zero};

use super::prescaled_value::PrescaledValue;
use super::*;

impl UnaryOp {
    pub fn approximate_unary_op(&self, arg: &PrescaledValue, p: Precision) -> AttemptedComputation {
        match self {
            UnaryOp::Neg => AttemptedComputation::Success(-arg.0.clone(), p),
            UnaryOp::Inverse => {
                if let Some(msb) = arg.msb() {
                    let inv_msd = 1 - msb;
                    let digits_needed = inv_msd - p + 3;
                    let prec_needed = msb - digits_needed;
                    let log_scale_factor = -p - prec_needed;

                    if log_scale_factor < 0 {
                        return AttemptedComputation::Success(Zero::zero(), p);
                    }

                    let dividend = signed::ONE.deref() << log_scale_factor;
                    if !arg.meets_precision(prec_needed) {
                        return AttemptedComputation::NeedMorePrecision(prec_needed);
                    }
                    // This unwrap is safe because we already returned if we don't have the needed precision.
                    let scaled_divisor = arg.clone().rescale(prec_needed).unwrap().0;

                    let abs_scaled_divisor = scaled_divisor.abs();
                    let adj_dividend = dividend + (&abs_scaled_divisor >> 1);
                    let result: BigInt = adj_dividend / abs_scaled_divisor;

                    let result = if scaled_divisor.sign() == Sign::Minus {
                        -result
                    } else {
                        result
                    };
                    AttemptedComputation::Success(result, p)
                } else {
                    // We cannot find the Most Significant Bit. Request a higher precision.
                    // I don't know where this heuristic comes from, but it is taken from the previous source code.
                    AttemptedComputation::NeedMorePrecision((p.min(0) * 3) / 2 - 16)
                }
            }
            UnaryOp::PrescaledCos => {
                /// Compute cosine of |c| < 1
                /// uses a Taylor series expansion.
                if p >= 1 {
                    // XXX: this doesn't seem right...shouldn't the result be scaled by 2^p?
                    AttemptedComputation::Success(signed::ONE.deref().clone(), p)
                } else {
                    let iterations_needed = -p / 2 + 2;
                    //  Claim: each intermediate term is accurate
                    //  to 2*2^calc_precision.
                    //  Total rounding error in series computation is
                    //  2*iterations_needed*2^calc_precision,
                    //  exclusive of error in op.
                    let calc_precision = p - bound_log2(2 * iterations_needed) - 4; // for error in op, truncation.
                    let op_prec = p - 3;

                    if let Some(PrescaledValue(op_appr, _)) = arg.clone().rescale(op_prec) {
                        // Error in argument results in error of < 1/4 ulp.
                        // Cumulative arithmetic rounding error is < 1/16 ulp.
                        // Series truncation error < 1/16 ulp.
                        // Final rounding error is <= 1/2 ulp.
                        // Thus final error is < 1 ulp.

                        let max_trunc_error = signed::ONE.deref() << (p - 4 - calc_precision);
                        let mut n = 0;
                        let mut current_term = signed::ONE.deref() << (-calc_precision);
                        let mut current_sum = current_term.clone();

                        while current_term.abs() > max_trunc_error {
                            n += 2;

                            /* current_term = - current_term * op * op / n * (n - 1)   */
                            current_term = scale(current_term * &op_appr, op_prec);
                            current_term = scale(current_term * &op_appr, op_prec);
                            let divisor = ToBigInt::to_bigint(&-n).unwrap()
                                * ToBigInt::to_bigint(&(n - 1)).unwrap();
                            current_term /= divisor;

                            current_sum += &current_term;
                        }

                        let result = scale(current_sum, calc_precision - p);
                        AttemptedComputation::Success(result, p)
                    } else {
                        // We need more precision from our argument.
                        AttemptedComputation::NeedMorePrecision(op_prec)
                    }
                }
            }
            UnaryOp::PrescaledExp => {
                // Value is assumed < 0.5. This should be ensured by Computable::exp
                if p >= 1 {
                    AttemptedComputation::Success(Zero::zero(), p)
                } else {
                    let iterations_needed = -p / 2 + 2;
                    //  Claim: each intermediate term is accurate
                    //  to 2*2^calc_precision.
                    //  Total rounding error in series computation is
                    //  2*iterations_needed*2^calc_precision,
                    //  exclusive of error in op.
                    let calc_precision = p - bound_log2(2 * iterations_needed) - 4; // for error in op, truncation.
                    let op_prec = p - 3;

                    if let Some(PrescaledValue(op_appr, _)) = arg.clone().rescale(op_prec) {
                        // Error in argument results in error of < 3/8 ulp.
                        // Sum of term eval. rounding error is < 1/16 ulp.
                        // Series truncation error < 1/16 ulp.
                        // Final rounding error is <= 1/2 ulp.
                        // Thus final error is < 1 ulp.
                        let scaled_1 = signed::ONE.deref() << -calc_precision;

                        let max_trunc_error = signed::ONE.deref() << (p - 4 - calc_precision);
                        let mut current_term = scaled_1.clone();
                        let mut sum = scaled_1;
                        let mut n = BigInt::zero();

                        while current_term.abs() > max_trunc_error {
                            n += signed::ONE.deref();
                            current_term = scale(current_term * &op_appr, op_prec) / &n;
                            sum += &current_term;
                        }

                        let result = scale(sum, calc_precision - p);
                        AttemptedComputation::Success(result, p)
                    } else {
                        // We need more precision from our argument.
                        AttemptedComputation::NeedMorePrecision(op_prec)
                    }
                }
            }
            UnaryOp::PrescaledLn => {
                /// Compute an approximation of ln(1+x) to precision p.
                /// This assumes |x| < 1/2.
                /// It uses a Taylor series expansion.
                /// Unfortunately there appears to be no way to take
                /// advantage of old information.
                /// Note: this is known to be a bad algorithm for
                /// floating point.  Unfortunately, other alternatives
                /// appear to require precomputed tabular information.
                if p >= 0 {
                    AttemptedComputation::Success(Zero::zero(), p)
                } else {
                    let iterations_needed = -p;
                    let calc_precision = p - bound_log2(2 * iterations_needed) - 4;
                    let op_prec = p - 3;
                    if let Some(PrescaledValue(op_appr, _)) = arg.clone().rescale(op_prec) {
                        // Error in argument results in error of < 3/8 ulp.

                        let mut x_nth = scale(op_appr.clone(), op_prec - calc_precision);
                        let mut current_term = x_nth.clone();
                        let mut sum = current_term.clone();

                        let mut n = 1;
                        let mut sign = 1;

                        let max_trunc_error = signed::ONE.deref() << (p - 4 - calc_precision);

                        while current_term.abs() > max_trunc_error {
                            n += 1;
                            sign = -sign;
                            x_nth = scale(&x_nth * &op_appr, op_prec);

                            let divisor: BigInt = (n * sign).into();
                            current_term = &x_nth / divisor;
                            sum += &current_term;
                        }

                        let result = scale(sum, calc_precision - p);

                        AttemptedComputation::Success(result, p)
                    } else {
                        // We need more precision from our argument.
                        AttemptedComputation::NeedMorePrecision(op_prec)
                    }
                }
            }
            UnaryOp::Sqrt => {
                // We want to compute the sqrt of arg, which is approximately sqrt(arg.0) * 2^(-arg.1/2).
                // To get a result with precision p, we need to compute sqrt(arg.0) with precision p + arg.1/2.
                let required_arg_precision = self.precision_needed(p);
                if let Some(rescaled_arg) = arg.clone().rescale(required_arg_precision) {
                    let approx_sqrt = rescaled_arg.0.sqrt();

                    AttemptedComputation::Success(
                        scale(approx_sqrt, -1),
                        required_arg_precision / 2 + 1,
                    )
                } else {
                    AttemptedComputation::NeedMorePrecision(required_arg_precision)
                }
            }
        }
    }
    pub fn precision_needed(&self, out_precision: Precision) -> Precision {
        match self {
            UnaryOp::Neg => out_precision,
            // This is a lie. We need the MSB of the argument, so we will probably require a recompute.
            UnaryOp::Inverse => out_precision,
            UnaryOp::PrescaledCos => out_precision - 3,
            // The argument is assumed to be < 0.5, which helps to bound our truncation error.
            UnaryOp::PrescaledExp => out_precision - 3,
            // For the bigint sqrt function, we want an even precision so that the result can be immediately returned as having precision p/2
            UnaryOp::Sqrt => out_precision * 2 - 2,
            UnaryOp::PrescaledLn => out_precision - 3,
        }
    }
}

impl BinaryOp {
    pub fn approximate_binary_op(
        &self,
        arg1: &PrescaledValue,
        arg2: &PrescaledValue,
        p: Precision,
    ) -> AttemptedComputation {
        match self {
            BinaryOp::Add => {
                // We need p - 2 precision from both arguments.
                let required_precision = self.precision_needed(p);
                if let (Some(arg1), Some(arg2)) = (
                    arg1.clone().rescale(required_precision),
                    arg2.clone().rescale(required_precision),
                ) {
                    AttemptedComputation::Success(scale(arg1.0 + arg2.0, required_precision - p), p)
                } else {
                    AttemptedComputation::NeedMorePrecision(required_precision)
                }
            }
            BinaryOp::Mul => {
                let required_precision = self.precision_needed(p);
                if let (Some(arg1), Some(arg2)) = (
                    arg1.clone().rescale(required_precision),
                    arg2.clone().rescale(required_precision),
                ) {
                    AttemptedComputation::Success(
                        scale(arg1.0 * arg2.0, 2 * required_precision - p),
                        p,
                    )
                } else {
                    AttemptedComputation::NeedMorePrecision(required_precision)
                }
            }
        }
    }
    pub fn precision_needed(&self, out_precision: Precision) -> Precision {
        match self {
            BinaryOp::Add => out_precision - 2,
            BinaryOp::Mul => out_precision * 2,
        }
    }
}

pub fn ratio(r: &Rational, p: Precision) -> BigInt {
    if p >= 0 {
        scale(r.shifted_big_integer(0), -p)
    } else {
        r.shifted_big_integer(-p)
    }
}
pub fn shift(n: BigInt, p: Precision) -> BigInt {
    match 0.cmp(&p) {
        Ordering::Greater => n >> -p,
        Ordering::Equal => n,
        Ordering::Less => n << p,
    }
}

/// Scale (left shift) n by p bits, rounding if this makes n smaller.
/// e.g. scale(10, 2) == 40
///      scale(10, -2) == 3
///
/// This is a similar operation to multiplying by 2^(-p)
pub fn scale(n: BigInt, p: Precision) -> BigInt {
    if p >= 0 {
        n << p
    } else {
        let adj = shift(n, p + 1) + signed::ONE.deref();
        adj >> 1
    }
}

/// Compute an integer approximation to `log2(1+|n|)`.
fn bound_log2(n: i32) -> i32 {
    let abs_n = n.abs();
    let ln2 = 2.0_f64.ln();
    let n_plus_1: f64 = (abs_n + 1).into();
    let ans: f64 = (n_plus_1.ln() / ln2).ceil();
    ans as i32
}

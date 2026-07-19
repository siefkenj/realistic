//! A version of `Computable` that uses a stack for its computations instead of making recursive calls.

#![allow(unused)]

use std::cmp::Ordering;
use std::ops::{Add, Deref, Mul, Sub};

use num::BigInt;

use crate::Rational;
use crate::computable::{Precision, signed};
use crate::stack_computable::prescaled_value::PrescaledValue;

mod approximate;
mod prescaled_value;
mod stack_computable;
mod precision_req;

/// A computation that was attempted at a required level of precision.
#[derive(Clone, Debug, PartialEq)]
enum AttemptedComputation {
    /// The computation succeeded and we return a prescaled integer approximation.
    Success(BigInt, Precision),
    /// The computation failed because more precision was required from the arguments.
    NeedMorePrecision(Precision),
    /// The computation failed because it is impossible.
    Failed,
}

#[derive(Clone, Debug, PartialEq, Default)]
enum Cache {
    #[default]
    Empty,
    Computed(PrescaledValue),
}

#[derive(Clone, Debug, PartialEq)]
enum OpStack {
    /// Placeholder for a number (integer or rational)
    Literal,
    Pi,
    One,
    UnaryOp(UnaryOp),
    BinaryOp(BinaryOp),
}

#[derive(Clone, Debug, PartialEq)]
enum Literal {
    Int(BigInt),
    Ratio(Rational),
}

#[derive(Clone, Debug, PartialEq)]
enum UnaryOp {
    Neg,
    Inverse,
    PrescaledCos,
    PrescaledExp,
    PrescaledLn,
    Sqrt,
}

#[derive(Clone, Debug, PartialEq)]
enum BinaryOp {
    Add,
    Mul,
}

impl OpStack {
    /// Given the required out_precision, what precision is needed for the inputs?
    fn precision_needed(&self, out_precision: Precision) -> Precision {
        match self {
            OpStack::Literal | OpStack::Pi | OpStack::One => out_precision,
            OpStack::UnaryOp(unary_op) => unary_op.precision_needed(out_precision),
            OpStack::BinaryOp(binary_op) => binary_op.precision_needed(out_precision),
        }
    }
}

#[cfg(test)]
mod test {
    use super::stack_computable::*;
    use super::*;

    #[test]
    fn operator_indices() {
        let a = StackComputable::rational(Rational::fraction(1, 2).unwrap());
        let b = StackComputable::rational(Rational::fraction(1, 3).unwrap());
        let c = a.add(&b);
        assert_eq!(c.operator_argument_indices(2), (Some(0), Some(1)));
        let d = c.clone().add(&c);
        assert_eq!(d.operator_argument_indices(5), (Some(3), Some(4)));
        assert_eq!(d.operator_argument_indices(6), (Some(2), Some(5)));
    }

    #[test]
    fn can_approximate_rationals() {
        let a = StackComputable::rational(Rational::fraction(1, 2).unwrap());
        let x = a.approximate(-1);
        assert_eq!(x, BigInt::from(1u64));

        let x = a.approximate(-2);
        assert_eq!(x, BigInt::from(2u64));

        let x = a.approximate(-3);
        assert_eq!(x, BigInt::from(4u64));

        let a = StackComputable::rational(Rational::fraction(4, 3).unwrap());
        let x = a.approximate(-10);
        assert_eq!(x, BigInt::from(0b10101010101_u64));
        let x = a.approximate(0);
        assert_eq!(x, BigInt::from(1_u64));
    }

    #[test]
    fn can_approximate_ints() {
        // 0b101011 == 43
        let a = StackComputable::integer(BigInt::from(0b101011_u64));
        let x = a.approximate(0);
        assert_eq!(x, BigInt::from(0b101011_u64));

        let x = a.approximate(2);
        assert_eq!(x, BigInt::from(0b1011_u64));

        let x = a.approximate(-2);
        assert_eq!(x, BigInt::from(0b101011_00_u64));
    }

    #[test]
    fn addition() {
        let a = StackComputable::rational(Rational::fraction(1, 2).unwrap());
        let b = StackComputable::rational(Rational::fraction(1, 3).unwrap());
        let c = a.add(&b);
        // println!("c.approximate in binary: {:b}", c.approximate(-10));
        assert_eq!(c.approximate(-5), BigInt::from(0b11011_u64));
        assert_eq!(c.approximate(-10), BigInt::from(0b1101010101_u64));

        let d = c.clone().add(&c);
        assert_eq!(d.approximate(-5), BigInt::from(0b110110_u64));
        assert_eq!(d.approximate(-10), BigInt::from(0b11010101011_u64));
    }

    #[test]
    fn multiplication() {
        let a = StackComputable::rational(Rational::fraction(1, 2).unwrap());
        let b = StackComputable::rational(Rational::fraction(1, 3).unwrap());
        let c = a.mul(&b);
        //  println!("c.approximate in binary: {:b}", c.approximate(-10));
        assert_eq!(c.approximate(-5), BigInt::from(0b00101_u64));
        assert_eq!(c.approximate(-10), BigInt::from(0b0010101011_u64));

        let d = c.clone().mul(&c);
        assert_eq!(d.approximate(-5), BigInt::from(0b00001_u64));
        assert_eq!(d.approximate(-10), BigInt::from(0b0000011100_u64));
        
        let a = StackComputable::rational(Rational::fraction(5, 1).unwrap());
        let b = StackComputable::rational(Rational::fraction(1, 3).unwrap());
        let c = a.mul(&b);
        //  println!("c.approximate in binary: {:b}", c.approximate(-10));
        assert_eq!(c.approximate(-5), BigInt::from(0b1_10101_u64));
    }

    #[test]
    fn square_root() {
        let a = StackComputable::rational(Rational::fraction(1, 4).unwrap());
        let b = a.sqrt();
        assert_eq!(b.approximate(-4), BigInt::from(8u64));

        let a = StackComputable::rational(Rational::fraction(2, 1).unwrap());
        let b = a.sqrt();
        assert_eq!(b.approximate(-13), BigInt::from(0b1_0110101000001_u64));
    }

    #[test]
    fn invert() {
        let a = StackComputable::rational(Rational::fraction(1, 4).unwrap());
        let b = a.inverse();
        assert_eq!(b.approximate(0), BigInt::from(0b100_u64));

        let a = StackComputable::rational(Rational::fraction(5, 3).unwrap());
        let b = a.inverse();
        assert_eq!(b.approximate(0), BigInt::from(0b1_u64));
        assert_eq!(b.approximate(-6), BigInt::from(0b0_100110_u64));
    }
    
    #[test]
    fn invert_big_number() {
        let a = StackComputable::rational(Rational::fraction(0b1_000_000_000_000, 1).unwrap());
        let b = a.inverse();
        assert_eq!(b.approximate(0), BigInt::from(0b0_u64));
        assert_eq!(b.approximate(-20), BigInt::from(0b100000000_u64));
    }

    #[test]
    fn exponential() {
        // exp only works on numbers between 0 and 0.5.
        let a = StackComputable::rational(Rational::fraction(1, 4).unwrap());
        let b = a.exp();
        // From wolframalpha.com
        // 1.010010001011010111100011110000111110100000011000011001100111..._2
        assert_eq!(b.approximate(-5), BigInt::from(0b1_01001_u64));
        assert_eq!(b.approximate(-10), BigInt::from(0b1_0100100011_u64));
        assert_eq!(b.approximate(-60), BigInt::from(0b1_010010001011010111100011110000111110100000011000011001100111_u64));
    }

    #[test]
    fn ln_one_plus_x() {
        let a = StackComputable::rational(Rational::fraction(1, 4).unwrap());
        let b = a.ln_one_plus_x();
        // From wolframalpha.com
        // 0.0011100100011111111011111000111100110101001101000100001101011..._2
        assert_eq!(b.approximate(-5), BigInt::from(0b0_00111_u64));
        assert_eq!(b.approximate(-10), BigInt::from(0b0_0011100100_u64));
        assert_eq!(b.approximate(-60), BigInt::from(0b0_001110010001111111101111100011110011010100110100010000110110_u64));
    }

    #[test]
    fn cos() {
        // cos only works on numbers with |x| < 1.
        let a = StackComputable::rational(Rational::fraction(1, 4).unwrap());
        let b = a.cos();
        // From wolframalpha.com
        //  0.11111000000010101010010011111011111011110111010100001011101001..._2
        assert_eq!(b.approximate(-5), BigInt::from(0b0_11111_u64));
        assert_eq!(b.approximate(-10), BigInt::from(0b0_1111100000_u64));
        assert_eq!(b.approximate(-60), BigInt::from(0b0_111110000000101010100100111110111110111101110101000010111010_u64));
    }

    // Print out the size of the `StackComputable` struct.
    #[test]
    fn size_of_stack_computable() {
        println!(
            "Size of StackComputable: {} bytes",
            std::mem::size_of::<StackComputable>()
        );
        panic!(
            "Size of StackComputable: {} bytes",
            std::mem::size_of::<OpStack>()
        );
    }
}

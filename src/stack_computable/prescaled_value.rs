use num::{BigInt, Zero};

use crate::{
    Rational,
    computable::{Precision, scale},
    stack_computable::{Literal, approximate::ratio},
};

#[derive(Clone, Debug, PartialEq)]
pub struct PrescaledValue(pub BigInt, pub Precision);

impl PrescaledValue {
    /// Rescale this `PrescaledValue` to the new precision, but only if this results in a _decrease_ in precision.
    pub fn rescale(self, new_precision: Precision) -> Option<PrescaledValue> {
        if new_precision < self.1 {
            None
        } else if new_precision == self.1 {
            Some(self)
        } else {
            Some(PrescaledValue(
                scale(self.0, -new_precision + self.1),
                new_precision,
            ))
        }
    }

    /// Does this `PrescaledValue` have at enough digits stored to meet the required precision?
    pub fn meets_precision(&self, required_precision: Precision) -> bool {
        self.1 <= required_precision
    }

    /// Get the Most Significant Bit of the stored value, or `None` if there is no such bit.
    pub fn msb(&self) -> Option<Precision> {
        if self.0 == BigInt::zero() {
            None
        } else {
            let length = self.0.bits() as Precision;
            Some(length + self.1 - 1)
        }
    }
}

pub trait IntoPrescaledValue {
    fn into_prescaled_value(self, p: Precision) -> PrescaledValue;
}

impl IntoPrescaledValue for &Rational {
    fn into_prescaled_value(self, p: Precision) -> PrescaledValue {
        PrescaledValue(ratio(&self, p), p)
    }
}
impl IntoPrescaledValue for &BigInt {
    fn into_prescaled_value(self, p: Precision) -> PrescaledValue {
        PrescaledValue(scale(self.clone(), -p), p)
    }
}
impl IntoPrescaledValue for &Literal {
    fn into_prescaled_value(self, p: Precision) -> PrescaledValue {
        match self {
            Literal::Int(i) => i.into_prescaled_value(p),
            Literal::Ratio(r) => r.into_prescaled_value(p),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rescale_value() {
        // The value 1
        let a = PrescaledValue(BigInt::from(0b1_00_u64), -2);
        let b = a.clone().rescale(-1).unwrap();
        assert_eq!(b, PrescaledValue(BigInt::from(0b1_0_u64), -1));
    }
}

use std::cmp::Ordering;
use std::ops::{Add, AddAssign, Sub, SubAssign};

macro_rules! implement_field_array_type {
    ($type_name:ident) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub struct $type_name<F>([F; 8]);

        impl<F: Copy + Default + Ord + From<u32>> $type_name<F> {
            /// Create a new instance of the type
            /// # Panics
            /// Panics if any of the values in the array are greater than 255
            pub fn new(value: [F; 8]) -> Self {
                assert!(value.iter().all(|&x| x < F::from(256)));
                Self(value)
            }

            pub fn zero() -> Self {
                Self([F::default(); 8])
            }

            // Convert from u64 to field elements in little-endian order
            pub fn from_u64(value: u64) -> Self
            where
                F: From<u32>,
            {
                let bytes = value.to_le_bytes();
                let mut limbs = [F::default(); 8];
                for (i, &byte) in bytes.iter().enumerate() {
                    limbs[i] = F::from(byte as u32).into();
                }
                Self(limbs)
            }

            pub fn to_u64(&self) -> u64 {
                let mut bytes = [0u8; 8];
                for i in 0..8 {
                    let t: F = self.0[i];
                    bytes[i] = unsafe { *(&t as *const F as *const M31) }.0 as u8;
                }
                u64::from_le_bytes(bytes)
            }
        }

        impl<F: Copy + Default> Default for $type_name<F> {
            fn default() -> Self {
                Self([F::default(); 8])
            }
        }

        impl<F: Copy + Default + Add<Output = F>> Add for $type_name<F> {
            type Output = Self;
            fn add(self, rhs: Self) -> Self {
                let mut result = [F::default(); 8];
                for i in 0..8 {
                    result[i] = self.0[i] + rhs.0[i];
                }
                Self(result)
            }
        }

        impl<F: Copy + AddAssign> AddAssign for $type_name<F> {
            fn add_assign(&mut self, rhs: Self) {
                for i in 0..8 {
                    self.0[i] += rhs.0[i];
                }
            }
        }

        impl<F: Copy + Default + Sub<Output = F>> Sub for $type_name<F> {
            type Output = Self;
            fn sub(self, rhs: Self) -> Self {
                let mut result = [F::default(); 8];
                for i in 0..8 {
                    result[i] = self.0[i] - rhs.0[i];
                }
                Self(result)
            }
        }

        impl<F: Copy + SubAssign> SubAssign for $type_name<F> {
            fn sub_assign(&mut self, rhs: Self) {
                for i in 0..8 {
                    self.0[i] -= rhs.0[i];
                }
            }
        }

        impl<F: Copy + PartialOrd> PartialOrd for $type_name<F> {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                for (a, b) in self.0.iter().rev().zip(other.0.iter().rev()) {
                    match a.partial_cmp(b) {
                        Some(Ordering::Equal) => continue,
                        Some(ord) => return Some(ord),
                        None => return None,
                    }
                }
                Some(Ordering::Equal)
            }
        }

        impl<F: Copy + Ord> Ord for $type_name<F> {
            fn cmp(&self, other: &Self) -> Ordering {
                for (a, b) in self.0.iter().rev().zip(other.0.iter().rev()) {
                    match a.cmp(b) {
                        Ordering::Equal => continue,
                        ord => return ord,
                    }
                }
                Ordering::Equal
            }
        }
    };
}

pub use stwo_prover::core::fields::m31::M31;

implement_field_array_type!(Price);
implement_field_array_type!(Time);
implement_field_array_type!(Volume);

#[cfg(test)]
mod tests {
    use std::u64::MAX;

    use super::*;
    use stwo_prover::core::fields::m31::M31;

    #[test]
    fn test_price_with_m31() {
        // Test conversion from u64 to M31 field elements
        let price: Price<M31> = Price::from_u64(1234567);

        // Each limb should be within [0, 256) range
        for limb in price.0.iter() {
            assert!(limb.0 < 256);
        }

        // Test ordering with M31 values
        let p1: Price<M31> = Price::from_u64(1 << 40);
        let p2: Price<M31> = Price::from_u64((1 << 40) - 1);
        assert!(p1 > p2);
    }

    #[test]
    fn test_ordering_m31_edge_cases() {
        // Test with values near u64::MAX
        let p1: Price<M31> = Price::from_u64(MAX);
        let p2: Price<M31> = Price::from_u64(MAX - 1);
        assert!(p1 > p2);

        // Test with zero
        let p3 = Price::from_u64(123412424);
        assert!(p3 < p1);
        assert!(p3 < p2);
        assert!(p2 < p1);
    }

    #[test]
    fn test_field_array_arithmetics() {
        // Test addition
        let a = MAX - 5;
        let b = 2;
        let p1: Price<M31> = Price::from_u64(MAX - 5);
        let p2: Price<M31> = Price::from_u64(2);
        let sum = p1 + p2;

        // Each limb should be within [0, 256) range
        for limb in sum.0.iter() {
            assert!(limb.0 < 256);
        }

        // Test Sum
        assert_eq!(
            sum,
            Price::new([
                M31(252),
                M31(255),
                M31(255),
                M31(255),
                M31(255),
                M31(255),
                M31(255),
                M31(255)
            ])
        );

        // Test conversion to u64
        assert_eq!(sum.to_u64(), a + b);

        // Test subtraction
        let sub = p1 - p2;

        // Each limb should be within [0, 256) range
        for limb in sub.0.iter() {
            assert!(limb.0 < 256);
        }

        // Test Sum
        assert_eq!(
            sub,
            Price::new([
                M31(248),
                M31(255),
                M31(255),
                M31(255),
                M31(255),
                M31(255),
                M31(255),
                M31(255)
            ])
        );

        // Test conversion to u64
        assert_eq!(sub.to_u64(), a - b);
    }
}

use super::{biguint_from_tinyvec, BigUint};

use crate::big_digit;

use alloc::borrow::Cow;
use alloc::vec::Vec;
use tinyvec::TinyVec;
use core::mem;
use core::ops::{Shl, ShlAssign, Shr, ShrAssign};
use num_traits::{PrimInt, Zero};

#[inline]
fn biguint_shl<T: PrimInt>(n: Cow<'_, BigUint>, shift: T) -> BigUint {
    if shift < T::zero() {
        panic!("attempt to shift left with negative");
    }
    if n.is_zero() {
        return n.into_owned();
    }
    let bits = T::from(big_digit::BITS).unwrap();
    let digits = (shift / bits).to_usize().expect("capacity overflow");
    let shift = (shift % bits).to_u8().unwrap();
    biguint_shl2(n, digits, shift)
}

fn biguint_shl2(n: Cow<'_, BigUint>, digits: usize, shift: u8) -> BigUint {
    let mut data = match digits {
        0 => n.into_owned().data,
        _ => {
            let len = digits.saturating_add(n.data.len() + 1);
            let mut data = TinyVec::with_capacity(len);
            data.resize(digits, 0);
            data.extend(n.data.iter().copied());
            data
        }
    };

    if shift > 0 {
        let mut carry = 0;
        let carry_shift = big_digit::BITS - shift;
        for elem in data[digits..].iter_mut() {
            let new_carry = *elem >> carry_shift;
            *elem = (*elem << shift) | carry;
            carry = new_carry;
        }
        if carry != 0 {
            data.push(carry);
        }
    }

    biguint_from_tinyvec(data)
}

#[inline]
fn biguint_shr<T: PrimInt>(n: Cow<'_, BigUint>, shift: T) -> BigUint {
    if shift < T::zero() {
        panic!("attempt to shift right with negative");
    }
    if n.is_zero() {
        return n.into_owned();
    }
    let bits = T::from(big_digit::BITS).unwrap();
    let digits = (shift / bits).to_usize().unwrap_or(usize::MAX);
    let shift = (shift % bits).to_u8().unwrap();
    biguint_shr2(n, digits, shift)
}

fn biguint_shr2(n: Cow<'_, BigUint>, digits: usize, shift: u8) -> BigUint {
    if digits >= n.data.len() {
        let mut n = n.into_owned();
        n.set_zero();
        return n;
    }
    let n_data_len = n.data.len();
    // if n.data.len() > 6 {
    //     eprintln!("{:?}", n.data.len());
    // }
    // dbg!(n.data.len());
    let mut data = match n {
        Cow::Borrowed(n) => n.data[digits..].into_iter().copied().collect(),
        Cow::Owned(mut n) => {
            if digits != 0 {
                // eprintln!("draining digits={:?}", digits);
                n.data.drain(..digits);
            }
            n.data
        }
    };

    if shift > 0 {
        let mut borrow = 0;
        let borrow_shift = big_digit::BITS - shift;
        for elem in data.iter_mut().rev() {
            let new_borrow = *elem << borrow_shift;
            *elem = (*elem >> shift) | borrow;
            borrow = new_borrow;
        }
    }

    // if n_data_len > 6 || data.len() > 6 {
    //     eprintln!("n.data={:?} data={:?}", n_data_len, data.len());
    // }
    biguint_from_tinyvec(data)
}

macro_rules! impl_shift {
    (@ref $Shx:ident :: $shx:ident, $ShxAssign:ident :: $shx_assign:ident, $rhs:ty) => {
        impl $Shx<&$rhs> for BigUint {
            type Output = BigUint;

            #[inline]
            fn $shx(self, rhs: &$rhs) -> BigUint {
                $Shx::$shx(self, *rhs)
            }
        }
        impl $Shx<&$rhs> for &BigUint {
            type Output = BigUint;

            #[inline]
            fn $shx(self, rhs: &$rhs) -> BigUint {
                $Shx::$shx(self, *rhs)
            }
        }
        impl $ShxAssign<&$rhs> for BigUint {
            #[inline]
            fn $shx_assign(&mut self, rhs: &$rhs) {
                $ShxAssign::$shx_assign(self, *rhs);
            }
        }
    };
    ($($rhs:ty),+) => {$(
        impl Shl<$rhs> for BigUint {
            type Output = BigUint;

            #[inline]
            fn shl(self, rhs: $rhs) -> BigUint {
                biguint_shl(Cow::Owned(self), rhs)
            }
        }
        impl Shl<$rhs> for &BigUint {
            type Output = BigUint;

            #[inline]
            fn shl(self, rhs: $rhs) -> BigUint {
                biguint_shl(Cow::Borrowed(self), rhs)
            }
        }
        impl ShlAssign<$rhs> for BigUint {
            #[inline]
            fn shl_assign(&mut self, rhs: $rhs) {
                let n = mem::replace(self, Self::zero());
                *self = n << rhs;
            }
        }
        impl_shift! { @ref Shl::shl, ShlAssign::shl_assign, $rhs }

        impl Shr<$rhs> for BigUint {
            type Output = BigUint;

            #[inline]
            fn shr(self, rhs: $rhs) -> BigUint {
                biguint_shr(Cow::Owned(self), rhs)
            }
        }
        impl Shr<$rhs> for &BigUint {
            type Output = BigUint;

            #[inline]
            fn shr(self, rhs: $rhs) -> BigUint {
                biguint_shr(Cow::Borrowed(self), rhs)
            }
        }
        impl ShrAssign<$rhs> for BigUint {
            #[inline]
            fn shr_assign(&mut self, rhs: $rhs) {
                let n = mem::replace(self, Self::zero());
                *self = n >> rhs;
            }
        }
        impl_shift! { @ref Shr::shr, ShrAssign::shr_assign, $rhs }
    )*};
}

impl_shift! { u8, u16, u32, u64, u128, usize }
impl_shift! { i8, i16, i32, i64, i128, isize }

// Copyright 2016 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::convert::From;
use std::cmp;
use std::fmt;
use std::mem;
use std::hash::{Hash, Hasher};
use std::ops::Deref;

/// Miscelaneous things used to integrate other code with Supercow, but which
/// is not of interest to end users.
pub mod aux {
    use std::rc::Rc;
    use std::sync::Arc;

    /// Marker trait indicating a `Deref`-like which always returns the same
    /// reference.
    ///
    /// This is not indended for general use outside Supercow. Notably, `Box`
    /// and mundane references satisfy this trait's requirements, but
    /// deliberately do not implement it. It is also not a subtrait of `Deref`
    /// due to some additional special logic around boxes.
    ///
    /// ## Unsafety
    ///
    /// Behaviour is undefined if the implementation does not always return the
    /// same reference from `deref()` for any particular implementing value
    /// (including if that value is moved).
    pub unsafe trait ConstDeref {
        type Target : ?Sized;
        fn const_deref(&self) -> &Self::Target;
    }

    unsafe impl<T : ?Sized> ConstDeref for Rc<T> {
        type Target = T;
        fn const_deref(&self) -> &T { self }
    }

    unsafe impl<T : ?Sized> ConstDeref for Arc<T> {
        type Target = T;
        fn const_deref(&self) -> &T { self }
    }

    unsafe impl<T : ConstDeref + ?Sized> ConstDeref for Box<T> {
        type Target = T::Target;
        fn const_deref(&self) -> &T::Target {
            (**self).const_deref()
        }
    }
}

use self::aux::*;

/// Defines a "feature set" for a custom `Supercow` type.
///
/// ## Syntax
///
/// ```
/// supercow_features!(
///   /// Some documentation, etc, if desired.
///   pub trait FeatureName: SomeTrait, SomeTrait);
/// supercow_features!(
///   pub trait FeatureName: Clone, SomeTrait, SomeTrait);
/// ```
///
/// ## Semantics
///
/// A public trait named `FeatureName` is defined which extends all the listed
/// traits, other than `Clone`, and in addition to `ConstDeref`. If listed,
/// `Clone` *must* come first. If `Clone` is listed, the trait gains a
/// `clone_boxed()` method and `Box<FeatureName>` is `Clone`. All types which
/// implement all the listed traits (including `Clone`) and `ConstDeref`
/// implement `FeatureName`.
#[macro_export]
macro_rules! supercow_features {
    // It's unclear why $req:path doesn't work, but apparently constraints
    // allow neither `path` nor `ty`.
    ($(#[$meta:meta])* pub trait $feature_name:ident: Clone $(, $req:ident)*) => {
        $(#[$meta])*
        pub trait $feature_name<'a>: $($req +)* $crate::aux::ConstDeref + 'a {
            fn clone_boxed
                (&self)
                 -> Box<$feature_name<'a, Target = Self::Target> + 'a>;
        }
        impl<'a, T : 'a + $($req +)* Clone + $crate::aux::ConstDeref>
        $feature_name<'a> for T {
            fn clone_boxed
                (&self)
                 -> Box<$feature_name<'a, Target = Self::Target> + 'a>
            {
                let cloned: T = self.clone();
                Box::new(cloned)
            }
        }
        impl<'a, S : 'a> Clone for Box<$feature_name<'a, Target = S> + 'a> {
            fn clone(&self) -> Self {
                $feature_name::clone_boxed(self)
            }
        }
    };

    ($(#[$meta:meta])* pub trait $feature_name:ident: $($req:ident),*) => {
        $(#[$meta])*
        pub trait $feature_name<'a>: $($req +)* $crate::aux::ConstDeref + 'a {
        }
        impl<'a, T : 'a + $($req +)* Clone + $crate::aux::ConstDeref>
        $feature_name<'a> for T {
        }
    };
}

supercow_features!(
    /// The default feature set for special `Supercow` references.
    pub trait DefaultFeatures: Clone);
supercow_features!(
    /// The feature set used for `ASupercow` references.
    pub trait SyncFeatures: Clone, Send, Sync);

pub struct Supercow<'a, OWNED,
                    SPECIAL = Box<DefaultFeatures<'a, Target = OWNED>>>
where OWNED : 'a,
      SPECIAL : ConstDeref<Target = OWNED> {
    // In order to implement `Deref` in a branch-free fashion that isn't
    // sensitive to the Supercow being moved, we set `ptr_mask` and
    // `ptr_displacement` such that
    // `target = &*((&self & ptr_mask) + ptr_displacement)`
    // (arithmetic in terms of bytes, obviously).
    //
    // So for the three cases:
    //
    // Owned => ptr_mask = ~0u, ptr_displacement = offsetof(self, Owned.0)
    // Borrowed, Special => ptr_mask = 0u, ptr_displacement = address
    ptr_mask: usize,
    ptr_displacement: usize,
    state: SupercowData<'a, OWNED, SPECIAL>,
}

enum SupercowData<'a, OWNED : 'a, SPECIAL> {
    Owned(OWNED),
    Borrowed(&'a OWNED),
    Special(SPECIAL),
}
use self::SupercowData::*;

impl<'a, OWNED, SPECIAL> Deref
for Supercow<'a, OWNED, SPECIAL>
where OWNED : 'a,
      SPECIAL : ConstDeref<Target = OWNED> {
    type Target = OWNED;
    #[inline]
    fn deref(&self) -> &OWNED {
        unsafe {
            let self_address: usize = mem::transmute(self);
            mem::transmute((self_address & self.ptr_mask) +
                           self.ptr_displacement)
        }
    }
}

impl<'a, OWNED, SPECIAL>
Supercow<'a, OWNED, SPECIAL>
where OWNED : 'a,
      SPECIAL : ConstDeref<Target = OWNED> {
    pub fn owned(inner: OWNED) -> Self {
        Self::from_data(Owned(inner))
    }

    pub fn borrowed(inner: &'a OWNED) -> Self {
        Self::from_data(Borrowed(inner))
    }

    pub fn special<T : Into<SPECIAL>>(inner: T) -> Self {
        Self::from_data(Special(inner.into()))
    }

    fn from_data(data: SupercowData<'a, OWNED, SPECIAL>) -> Self {
        let mut this = Supercow {
            ptr_mask: 0,
            ptr_displacement: 0,
            state: data,
        };

        let ptr = match this.state {
            Owned(ref r) => r as *const OWNED,
            Borrowed(r) => r as *const OWNED,
            Special(ref s) => s.const_deref() as *const OWNED,
        };
        this.set_ptr(ptr);

        this
    }

    fn set_ptr(&mut self, ptr: *const OWNED) {
        // Use relative addressing if `ptr` is inside `self` and absolute
        // addressing otherwise.
        //
        // Ordinarily, `ptr` will always be inside `self` if the state is
        // `Owned`, and outside otherwise. However, it is possible to create
        // `Borrow` implementations that return arbitrary pointers, so we
        // handle the two cases like this instead.
        let self_start = self as *const Self as usize;
        let self_end = self_start + mem::size_of::<Self>();
        let addr = ptr as usize;

        if addr >= self_start && addr < self_end {
            self.ptr_mask = !0;
            self.ptr_displacement = addr - self_start;
        } else {
            self.ptr_mask = 0;
            self.ptr_displacement = addr;
        }
    }
}

impl<'a, OWNED, SPECIAL> From<OWNED>
for Supercow<'a, OWNED, SPECIAL>
where OWNED : 'a,
      SPECIAL : ConstDeref<Target = OWNED> {
    fn from(inner: OWNED) -> Self {
        Self::from_data(SupercowData::Owned(inner))
    }
}

impl<'a, OWNED, SPECIAL> From<&'a OWNED>
for Supercow<'a, OWNED, SPECIAL>
where OWNED : 'a,
      SPECIAL : ConstDeref<Target = OWNED> {
    fn from(inner: &'a OWNED) -> Self {
        Self::from_data(SupercowData::Borrowed(inner))
    }
}

impl<'a, OWNED, SPECIAL>
Supercow<'a, OWNED, SPECIAL>
where OWNED : 'a + Clone,
      SPECIAL : ConstDeref<Target = OWNED> {
    pub fn to_mut(&mut self) -> &mut OWNED {
        let new = match self.state {
            Owned(ref mut r) => return r,
            Borrowed(r) => Self::from(r.clone()),
            Special(ref s) => Self::from(s.const_deref().clone()),
        };
        *self = new;
        match self.state {
            Owned(ref mut r) => r,
            _ => unreachable!(),
        }
    }
}

impl<'a, OWNED, SPECIAL> Clone
for Supercow<'a, OWNED, SPECIAL>
where OWNED : Clone + 'a,
      SPECIAL : Clone + ConstDeref<Target = OWNED> {
    fn clone(&self) -> Self {
        Supercow {
            ptr_mask: self.ptr_mask,
            ptr_displacement: self.ptr_displacement,
            state: match self.state {
                Owned(ref o) => Owned(o.clone()),
                Borrowed(r) => Borrowed(r),
                Special(ref s) => Special(s.clone()),
            }
        }
    }
}

macro_rules! deleg_fmt {
    ($tr:ident) => {
        impl<'a, OWNED, SPECIAL> fmt::$tr
        for Supercow<'a, OWNED, SPECIAL>
        where OWNED : fmt::$tr + 'a,
              SPECIAL : ConstDeref<Target = OWNED> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                (**self).fmt(f)
            }
        }
    }
}
deleg_fmt!(Binary);
deleg_fmt!(Debug);
deleg_fmt!(Display);
deleg_fmt!(LowerExp);
deleg_fmt!(LowerHex);
deleg_fmt!(Octal);
deleg_fmt!(Pointer);
deleg_fmt!(UpperExp);
deleg_fmt!(UpperHex);

impl<'a, OWNED, SPECIAL, T> cmp::PartialEq<T>
for Supercow<'a, OWNED, SPECIAL>
where T : Deref<Target = OWNED>,
      OWNED : PartialEq<OWNED> + 'a,
      SPECIAL : ConstDeref<Target = OWNED> {
    fn eq(&self, other: &T) -> bool {
        **self == **other
    }

    fn ne(&self, other: &T) -> bool {
        **self != **other
    }
}

impl<'a, OWNED, SPECIAL> cmp::Eq
for Supercow<'a, OWNED, SPECIAL>
where OWNED : Eq + 'a,
      SPECIAL : ConstDeref<Target = OWNED> { }

impl<'a, OWNED, SPECIAL, T> cmp::PartialOrd<T>
for Supercow<'a, OWNED, SPECIAL>
where T : Deref<Target = OWNED>,
      OWNED : PartialOrd<OWNED> + 'a,
      SPECIAL : ConstDeref<Target = OWNED> {
    fn partial_cmp(&self, other: &T) -> Option<cmp::Ordering> {
        (**self).partial_cmp(other)
    }

    fn lt(&self, other: &T) -> bool {
        **self < **other
    }

    fn le(&self, other: &T) -> bool {
        **self <= **other
    }

    fn gt(&self, other: &T) -> bool {
        **self > **other
    }

    fn ge(&self, other: &T) -> bool {
        **self >= **other
    }
}

impl<'a, OWNED, SPECIAL> cmp::Ord
for Supercow<'a, OWNED, SPECIAL>
where OWNED : cmp::Ord + 'a,
      SPECIAL : ConstDeref<Target = OWNED> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        (**self).cmp(other)
    }
}

impl<'a, OWNED, SPECIAL> Hash
for Supercow<'a, OWNED, SPECIAL>
where OWNED : Hash + 'a,
      SPECIAL : ConstDeref<Target = OWNED> {
    fn hash<H : Hasher>(&self, h: &mut H) {
        (**self).hash(h)
    }
}

fn doit() {
    let _x: Supercow<'static, u32> = Supercow::owned(42u32);
}

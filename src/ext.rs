// Copyright 2016 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Miscelaneous things used to integrate other code with Supercow, but which
//! are not of interest to end users.

use std::borrow::Borrow;
use std::ffi::{CStr, OsStr};
use std::mem;
use std::path::Path;
use std::ptr;
use std::rc::Rc;
use std::slice;
use std::sync::Arc;

/// Marker trait indicating a `Deref`-like which always returns the same
/// reference.
///
/// This is not indended for general use outside Supercow. Notably, `Box` and
/// mundane references satisfy this trait's requirements, but deliberately do
/// not implement it. It is also not a subtrait of `Deref` due to some
/// additional special logic around boxes.
///
/// ## Unsafety
///
/// Behaviour is undefined if the implementation does not always return the
/// same reference from `deref()` for any particular implementing value
/// (including if that value is moved).
pub unsafe trait ConstDeref {
    /// The type this value dereferences to.
    type Target : ?Sized;
    /// Returns the (constant) value that this value dereferences to.
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

/// The maximum displacement (relative to the start of the object) that a
/// reference pointing into `self` from an instance of `SafeBorrow` may have.
///
/// This value is deliberately conservative to account for other memory layout
/// factors.
pub const MAX_INTERNAL_BORROW_DISPLACEMENT: usize = 2048;

/// Extension of `Borrow` used to allow `Supercow::to_mut()` to work safely.
///
/// ## Unsafety
///
/// Behaviour is undefined if the `borrow()` implementation may return a
/// reference into `self` which is more than `MAX_INTERNAL_BORROW_DISPLACEMENT`
/// bytes beyond the base of `self`.
pub unsafe trait SafeBorrow<T : ?Sized>: Borrow<T> {
    /// Given `ptr`, which was obtained from a prior call to `Self::borrow()`,
    /// return a value with the same nominal lifetime which is guaranteed to
    /// survive mutations to `Self`.
    ///
    /// Types which implement `Borrow` by pure, constant pointer arithmetic on
    /// `self` can simply return `ptr` unmodified. Other types typically need
    /// to provide some static reference, such as the empty string for `&str`.
    ///
    /// ## Unsafety
    ///
    /// Behaviour is undefined if this call returns `ptr`, but a mutation to
    /// `Self` could invalidate the reference.
    fn borrow_replacement<'a>(ptr: &'a T) -> &'a T;
}
unsafe impl<T : ?Sized> SafeBorrow<T> for T {
    fn borrow_replacement(ptr: &T) -> &T { ptr }
}
unsafe impl<B, T> SafeBorrow<[B]> for T where T : Borrow<[B]> {
    fn borrow_replacement(_: &[B]) -> &[B] {
        unsafe {
            slice::from_raw_parts(1 as usize as *const B, 0)
        }
    }
}
unsafe impl<T> SafeBorrow<str> for T where T : Borrow<str> {
    fn borrow_replacement(_: &str) -> &str { "" }
}
unsafe impl<T> SafeBorrow<CStr> for T
    where T : Borrow<CStr> {
        fn borrow_replacement(_: &CStr) -> &CStr {
        static EMPTY_CSTR: &'static [u8] = &[0];
        unsafe {
            CStr::from_bytes_with_nul_unchecked(EMPTY_CSTR)
        }
    }
    }
unsafe impl<T> SafeBorrow<OsStr> for T
    where T : Borrow<OsStr> {
            fn borrow_replacement(_: &OsStr) -> &OsStr {
                OsStr::new("")
            }
        }
unsafe impl<T> SafeBorrow<Path> for T
    where T : Borrow<Path> {
                fn borrow_replacement(_: &Path) -> &Path {
                Path::new("")
            }
            }

/// Marker trait identifying a reference type which begins with an absolute
/// address and contains no other address-dependent information.
///
/// `Supercow` expects to be able to read the first pointer-sized value of such
/// a reference and perform address arithmetic upon it.
///
/// There is no utility of applying this trait to anything other than a const
/// reference.
///
/// ## Unsafety
///
/// Behaviour is undefined if a marked type does not begin with a real pointer
/// to a value (with the usual exception of ZSTs, where the pointer does not
/// need to point to anything in particular) or if other parts of the type
/// contain address-dependent information.
///
/// Behaviour is undefined if the reference has any `Drop` implementation,
/// should a future Rust version make such things possible.
pub unsafe trait PointerFirstRef { }
unsafe impl<'a, T : Sized> PointerFirstRef for &'a T { }
unsafe impl<'a, T> PointerFirstRef for &'a [T] { }
unsafe impl<'a> PointerFirstRef for &'a str { }
unsafe impl<'a> PointerFirstRef for &'a ::std::ffi::CStr { }
unsafe impl<'a> PointerFirstRef for &'a ::std::ffi::OsStr { }
unsafe impl<'a> PointerFirstRef for &'a ::std::path::Path { }

/// Like `std::convert::From`, but without the blanket implementations that
/// cause problems for `supercow_features!`.
pub trait SharedFrom<T> {
    /// Converts the given `T` to `Self`.
    fn shared_from(t: T) -> Self;
}
impl <T> SharedFrom<Rc<T>> for Rc<T> {
    fn shared_from(t: Rc<T>) -> Rc<T> { t }
}
impl <T> SharedFrom<Arc<T>> for Arc<T> {
    fn shared_from(t: Arc<T>) -> Arc<T> { t }
}

/// Describes how an `OWNED` value is stored in a `Supercow`.
///
/// ## Unsafety
///
/// `Supercow` relies strongly on the contracts of the functions in this trait
/// being implemented correctly.
pub unsafe trait OwnedStorage<T> : Default {
    /// Allocates the given owned value.
    ///
    /// `self` is a `Default`-initialised instance.
    ///
    /// Returns a pointer with 2-byte alignment.
    ///
    /// ## Unsafety
    ///
    /// Behaviour is undefined if this call returns a pointer with incorrect
    /// alignment.
    ///
    /// Behaviour is undefined if the returned value is an address inside
    /// `self` offset by more than `MAX_INTERNAL_BORROW_DISPLACEMENT/2` (note
    /// division by two).
    ///
    /// Behaviour is undefined if this returns a null pointer. (But the
    /// returned pointer does not need to actually point at anything.)
    fn allocate(&mut self, value: T) -> *mut ();
    /// Extracts the immutable reference from the saved pointer and storage.
    ///
    /// ## Unsafety
    ///
    /// This call may assume that `ptr` is exactly a (2-byte-aligned) value it
    /// returned from `allocate`, and that `self` was initialised by a call to
    /// `allocate`.
    unsafe fn get_ptr<'a>(&'a self, ptr: *mut ()) -> &'a T;
    /// Extracts the mutable reference from the saved pointer and storage.
    ///
    /// ## Unsafety
    ///
    /// This call may assume that `ptr` is exactly a (2-byte-aligned) value it
    /// returned from `allocate` and that `self` was initialised by a call to
    /// `allocate`.
    unsafe fn get_mut<'a>(&'a mut self, ptr: *mut ()) -> &'a mut T;
    /// Releases any allocations that would not be released by `Stored`
    /// being dropped.
    ///
    /// ## Unsafety
    ///
    /// This call may assume that `ptr` is exactly a (2-byte-aligned) value it
    /// returned from `allocate`.
    ///
    /// Once this function is called, the given `ptr` is considered invalid and
    /// any further use is undefined.
    unsafe fn deallocate(&mut self, ptr: *mut ());
    /// Like `deallocate()`, but also return the owned value.
    unsafe fn deallocate_into(&mut self, ptr: *mut ()) -> T;

    /// Returns whether this storage implementation ever causes the owned
    /// object to be stored internally to the `Supercow`.
    ///
    /// ## Unsafety
    ///
    /// Behaviour is undefined if this returns `false` but the owned value is
    /// stored within the `Supercow`.
    fn is_internal_storage() -> bool;
}

/// Causes the `OWNED` value of a `Supercow` to be stored inline.
///
/// This makes allocation of owned `Supercow`s much faster, at the expense of
/// making the `Supercow` itself much bigger (since it now must contain the
/// whole object).
#[derive(Clone, Copy, Debug)]
pub struct InlineStorage<T>(Option<T>);
impl<T> Default for InlineStorage<T> {
    fn default() -> Self {
        InlineStorage(None)
    }
}

unsafe impl<T> OwnedStorage<T> for InlineStorage<T> {
    #[inline]
    fn allocate(&mut self, value: T) -> *mut () {
        self.0 = Some(value);
        2usize as *mut ()
    }

    #[inline]
    unsafe fn get_ptr<'a>(&'a self, _: *mut ()) -> &'a T {
        match self.0 {
            Some(ref r) => r,
            None => unreachable!(),
        }
    }

    #[inline]
    unsafe fn get_mut<'a>(&'a mut self, _: *mut ()) -> &'a mut T {
        match self.0 {
            Some(ref mut r) => r,
            None => unreachable!(),
        }
    }

    #[inline]
    unsafe fn deallocate(&mut self, _: *mut ()) { }

    #[inline]
    unsafe fn deallocate_into(&mut self, _: *mut ()) -> T {
        match mem::replace(self, InlineStorage(None)).0 {
            Some(v) => v,
            None => unreachable!(),
        }
    }

    #[inline]
    fn is_internal_storage() -> bool { true }
}

/// Causes the `OWNED` value of a `Supercow` to be stored in a `Box`.
///
/// This makes allocation of owned `Supercow`s more expensive, but incurs zero
/// space overhead within the `Supercow`. It also results in a faster `Deref`
/// implementation.
#[derive(Debug, Clone, Copy, Default)]
pub struct BoxedStorage;
unsafe impl<T> OwnedStorage<T> for BoxedStorage {
    #[inline]
    fn allocate(&mut self, value: T) -> *mut () {
        if mem::size_of::<T>() > 0 {
            let boxed = Box::new(value);
            let address = Box::into_raw(boxed);
            address as *mut ()
        } else {
            // Handle ZSTs specially, since `Box` "allocates" them at address
            // 1.
            2 as *mut ()
        }
    }

    #[inline]
    unsafe fn get_ptr<'a>(&'a self, ptr: *mut ()) -> &'a T {
        &*(ptr as *const T)
    }

    #[inline]
    unsafe fn get_mut<'a>(&'a mut self, ptr: *mut ()) -> &'a mut T {
        &mut*(ptr as *mut T)
    }

    #[inline]
    unsafe fn deallocate(&mut self, ptr: *mut ()) {
        if mem::size_of::<T>() > 0 {
            drop(Box::from_raw(ptr as *mut T))
        }
    }

    #[inline]
    unsafe fn deallocate_into(&mut self, ptr: *mut ()) -> T {
        if mem::size_of::<T>() > 0 {
            *Box::from_raw(ptr as *mut T)
        } else {
            ptr::read(ptr as *mut T)
        }
    }

    #[inline]
    fn is_internal_storage() -> bool { false }
}

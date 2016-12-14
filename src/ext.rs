// Copyright 2016 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Miscellaneous things used to integrate other code with Supercow, but which
//! are not of interest to most client developers.

use std::borrow::Borrow;
use std::ffi::{CStr, OsStr};
use std::marker::PhantomData;
use std::mem;
use std::path::Path;
use std::ptr;
use std::rc::Rc;
use std::sync::Arc;

/// Marker trait indicating a `Deref`-like which always returns the same
/// reference.
///
/// This is not intended for general use outside Supercow. Notably, mundane
/// references satisfy this trait's requirements, but deliberately do not
/// implement it. It is also not a subtrait of `Deref` due to some additional
/// special logic around boxes.
///
/// ## Unsafety
///
/// Behaviour is undefined if the implementation does not always return the
/// same reference from `const_deref()` for any particular implementing value
/// (including if that value is moved or cloned).
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


/// Trait for `ConstDeref` implementations which can be constructed in a
/// two-step process.
///
/// This is used by `Supercow` to safely promote owned values to shared values.
/// A two-step process is necessary because the implementation must atomically
/// transfer ownership of the value and so must set everything up first in case
/// setup panics.
///
/// Essentially, such shared references actually hold an `Option<Target>` which
/// defaults to `None`, and panic if dereferenced before the value is set.
pub trait TwoStepShared<OWNED, BORROWED : ?Sized> {
    /// Returns a new, empty instance of `Self`.
    fn new_two_step() -> Self;
    /// Returns the internal `Option<T>` backing this value.
    ///
    /// ## Unsafety
    ///
    /// This call may assume that `self` was produced by a call to
    /// `new_two_step` on the same implementation. (This is to allow
    /// downcasting without requiring `Any` which in turn requires `'static`.)
    ///
    /// The address of the value inside `Some` may not be altered by the
    /// implementation.
    unsafe fn deref_holder(&mut self) -> &mut Option<OWNED>;
}

macro_rules! twostepwrapper { ($outer:ident, $inner:ident) => {
    /// Wrapper providing a `TwoStepShared` implementation.
    pub struct $outer<T, B : ?Sized>($inner<Option<T>>, PhantomData<B>);
    impl<T, B : ?Sized> Clone for $outer<T, B> {
        fn clone(&self) -> Self {
            $outer(self.0.clone(), PhantomData)
        }
    }

    impl<T, B : ?Sized> TwoStepShared<T, B> for $outer<T, B>
    where T : SafeBorrow<B> {
        fn new_two_step() -> Self {
            $outer($inner::new(None), PhantomData)
        }
        unsafe fn deref_holder(&mut self) -> &mut Option<T> {
            // Safety: No operation here is actually unsafe.
            $inner::get_mut(&mut self.0)
                .expect("Two-step wrapper already cloned")
        }
    }
} }
twostepwrapper!(TwoStepRc, Rc);
twostepwrapper!(TwoStepArc, Arc);

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
        &[]
    }
}
unsafe impl<T> SafeBorrow<str> for T where T : Borrow<str> {
    fn borrow_replacement(_: &str) -> &str { "" }
}
unsafe impl<T> SafeBorrow<CStr> for T
where T : Borrow<CStr> {
    fn borrow_replacement(_: &CStr) -> &CStr {
        Default::default()
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

/// Marker trait identifying a pointer type which begins with an absolute
/// address and contains no other address-dependent information.
///
/// `Supercow` expects to be able to read the first machine-pointer-sized value
/// of such a pointer and perform address arithmetic upon it.
///
/// There is no utility of applying this trait to anything other than a const
/// pointer.
///
/// ## Unsafety
///
/// Behaviour is undefined if a marked type does not begin with a real pointer
/// to a value (with the usual exception of ZSTs, where the pointer does not
/// need to point to anything in particular) or if other parts of the type
/// contain address-dependent information.
///
/// Behaviour is undefined if the pointer has any `Drop` implementation,
/// should a future Rust version make such things possible.
pub unsafe trait PointerFirstRef : Copy { }

unsafe impl<T : Sized> PointerFirstRef for *const T { }
unsafe impl<T> PointerFirstRef for *const [T] { }
unsafe impl PointerFirstRef for *const str { }
unsafe impl PointerFirstRef for *const ::std::ffi::CStr { }
unsafe impl PointerFirstRef for *const ::std::ffi::OsStr { }
unsafe impl PointerFirstRef for *const ::std::path::Path { }

/// Like `std::convert::From`, but without the blanket implementations that
/// cause problems for `supercow_features!`.
///
/// ## Unsafety
///
/// The conversion may not invalidate the address returned by
/// `T::const_deref()` if `T` is `ConstDeref`.
pub unsafe trait SharedFrom<T> {
    /// Converts the given `T` to `Self`.
    fn shared_from(t: T) -> Self;
}
unsafe impl <T> SharedFrom<Rc<T>> for Rc<T> {
    fn shared_from(t: Rc<T>) -> Rc<T> { t }
}
unsafe impl <T> SharedFrom<Arc<T>> for Arc<T> {
    fn shared_from(t: Arc<T>) -> Arc<T> { t }
}

/// Describes how an `OWNED` or `SHARED` value is stored in a `Supercow`.
///
/// All notes for `*_b` functions are the same as the corresponding `*_a`
/// functions.
///
/// ## Unsafety
///
/// `Supercow` relies strongly on the contracts of the functions in this trait
/// being implemented correctly.
///
/// No function may mutate the `A` or `B` values.
pub unsafe trait OwnedStorage<A, B> : Default {
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
    fn allocate_a(&mut self, value: A) -> *mut ();
    /// See `allocate_a`.
    fn allocate_b(&mut self, value: B) -> *mut ();
    /// Extracts the immutable reference from the saved pointer and storage.
    ///
    /// ## Unsafety
    ///
    /// This call may assume that `ptr` is exactly a (2-byte-aligned) value it
    /// returned from `allocate_a`, and that `self` was initialised by a call
    /// to `allocate_a`.
    unsafe fn get_ptr_a<'a>(&'a self, ptr: *mut ()) -> &'a A;
    /// See `get_ptr_a`.
    unsafe fn get_ptr_b<'a>(&'a self, ptr: *mut ()) -> &'a B;
    /// Extracts the mutable reference from the saved pointer and storage.
    ///
    /// ## Unsafety
    ///
    /// This call may assume that `ptr` is exactly a (2-byte-aligned) value it
    /// returned from `allocate_a` and that `self` was initialised by a call to
    /// `allocate_a`.
    unsafe fn get_mut_a<'a>(&'a mut self, ptr: *mut ()) -> &'a mut A;
    /// See `get_mut_a`.
    unsafe fn get_mut_b<'a>(&'a mut self, ptr: *mut ()) -> &'a mut B;
    /// Releases any allocations that would not be released by `Stored`
    /// being dropped.
    ///
    /// ## Unsafety
    ///
    /// This call may assume that `ptr` is exactly a (2-byte-aligned) value it
    /// returned from `allocate_a`.
    ///
    /// Once this function is called, the given `ptr` is considered invalid and
    /// any further use is undefined.
    ///
    /// This call must not panic (assuming the input contract is satisfied).
    unsafe fn deallocate_a(&mut self, ptr: *mut ());
    /// See `deallocate_b`.
    unsafe fn deallocate_b(&mut self, ptr: *mut ());
    /// Like `deallocate_a()`, but also return the owned value.
    unsafe fn deallocate_into_a(&mut self, ptr: *mut ()) -> A;
    /// See `deallocate_into_a`.
    unsafe fn deallocate_into_b(&mut self, ptr: *mut ()) -> B;

    /// Returns whether this storage implementation ever causes the owned
    /// object to be stored internally to the `Supercow`.
    ///
    /// ## Unsafety
    ///
    /// Behaviour is undefined if this returns `false` but the owned value is
    /// stored within the `Supercow`.
    fn is_internal_storage() -> bool;
}

/// Causes the `OWNED` or `SHARED` value of a `Supercow` to be stored inline.
///
/// This makes allocation of owned `Supercow`s much faster, at the expense of
/// making the `Supercow` itself much bigger (since it now must contain the
/// whole object).
#[derive(Clone, Copy, Debug)]
pub struct InlineStorage<A, B>(InlineStorageImpl<A, B>);

#[derive(Clone, Copy, Debug)]
enum InlineStorageImpl<A, B> {
    None,
    A(A),
    B(B),
}

impl<A, B> Default for InlineStorage<A, B> {
    fn default() -> Self {
        InlineStorage(InlineStorageImpl::None)
    }
}

unsafe impl<A, B> OwnedStorage<A, B> for InlineStorage<A, B> {
    #[inline]
    fn allocate_a(&mut self, value: A) -> *mut () {
        self.0 = InlineStorageImpl::A(value);
        2usize as *mut ()
    }

    #[inline]
    fn allocate_b(&mut self, value: B) -> *mut () {
        self.0 = InlineStorageImpl::B(value);
        2usize as *mut ()
    }

    #[inline]
    unsafe fn get_ptr_a<'a>(&'a self, _: *mut ()) -> &'a A {
        match self.0 {
            InlineStorageImpl::A(ref r) => r,
            _ => unreachable!(),
        }
    }

    #[inline]
    unsafe fn get_ptr_b<'a>(&'a self, _: *mut ()) -> &'a B {
        match self.0 {
            InlineStorageImpl::B(ref r) => r,
            _ => unreachable!(),
        }
    }

    #[inline]
    unsafe fn get_mut_a<'a>(&'a mut self, _: *mut ()) -> &'a mut A {
        match self.0 {
            InlineStorageImpl::A(ref mut r) => r,
            _ => unreachable!(),
        }
    }

    #[inline]
    unsafe fn get_mut_b<'a>(&'a mut self, _: *mut ()) -> &'a mut B {
        match self.0 {
            InlineStorageImpl::B(ref mut r) => r,
            _ => unreachable!(),
        }
    }

    #[inline]
    unsafe fn deallocate_a(&mut self, _: *mut ()) { }

    #[inline]
    unsafe fn deallocate_b(&mut self, _: *mut ()) { }

    #[inline]
    unsafe fn deallocate_into_a(&mut self, _: *mut ()) -> A {
        match mem::replace(&mut self.0, InlineStorageImpl::None) {
            InlineStorageImpl::A(v) => v,
            _ => unreachable!(),
        }
    }

    #[inline]
    unsafe fn deallocate_into_b(&mut self, _: *mut ()) -> B {
        match mem::replace(&mut self.0, InlineStorageImpl::None) {
            InlineStorageImpl::B(v) => v,
            _ => unreachable!(),
        }
    }

    #[inline]
    fn is_internal_storage() -> bool { true }
}

/// Used to give arbitrary values at least pointer alignment without making
/// them otherwise bigger.
///
/// This likely isn't strictly necessary, since any allocator has an inherent
/// alignment anyway, but it doesn't hurt to be explicit.
type Aligned<T> = ([*const();0], T);

/// Causes the `OWNED` or `SHARED` value of a `Supercow` to be stored in a
/// `Box`.
///
/// This makes allocation of owned `Supercow`s more expensive, but incurs zero
/// space overhead within the `Supercow`. It also results in a faster `Deref`
/// implementation.
#[derive(Debug, Clone, Copy, Default)]
pub struct BoxedStorage;
unsafe impl<A, B> OwnedStorage<A, B> for BoxedStorage {
    #[inline]
    fn allocate_a(&mut self, value: A) -> *mut () {
        if mem::size_of::<A>() > 0 {
            let boxed: Box<Aligned<A>> = Box::new(([], value));
            let address = Box::into_raw(boxed);
            unsafe { &mut (*address).1 as *mut A as *mut () }
        } else {
            // Handle ZSTs specially, since `Box` "allocates" them at address
            // 1.
            2 as *mut ()
        }
    }

    #[inline]
    fn allocate_b(&mut self, value: B) -> *mut () {
        if mem::size_of::<B>() > 0 {
            let boxed: Box<Aligned<B>> = Box::new(([], value));
            let address = Box::into_raw(boxed);
            unsafe { &mut (*address).1 as *mut B as *mut () }
        } else {
            // Handle ZSTs specially, since `Box` "allocates" them at address
            // 1.
            2 as *mut ()
        }
    }

    #[inline]
    unsafe fn get_ptr_a<'a>(&'a self, ptr: *mut ()) -> &'a A {
        &(*(ptr as *const Aligned<A>)).1
    }

    #[inline]
    unsafe fn get_ptr_b<'a>(&'a self, ptr: *mut ()) -> &'a B {
        &(*(ptr as *const Aligned<B>)).1
    }

    #[inline]
    unsafe fn get_mut_a<'a>(&'a mut self, ptr: *mut ()) -> &'a mut A {
        &mut(*(ptr as *mut Aligned<A>)).1
    }

    #[inline]
    unsafe fn get_mut_b<'a>(&'a mut self, ptr: *mut ()) -> &'a mut B {
        &mut(*(ptr as *mut Aligned<B>)).1
    }

    #[inline]
    unsafe fn deallocate_a(&mut self, ptr: *mut ()) {
        if mem::size_of::<A>() > 0 {
            drop(Box::from_raw(ptr as *mut Aligned<A>))
        }
    }

    #[inline]
    unsafe fn deallocate_b(&mut self, ptr: *mut ()) {
        if mem::size_of::<B>() > 0 {
            drop(Box::from_raw(ptr as *mut B))
        }
    }

    #[inline]
    unsafe fn deallocate_into_a(&mut self, ptr: *mut ()) -> A {
        if mem::size_of::<A>() > 0 {
            let t = *Box::from_raw(ptr as *mut Aligned<A>);
            t.1
        } else {
            ptr::read(ptr as *mut A)
        }
    }

    #[inline]
    unsafe fn deallocate_into_b(&mut self, ptr: *mut ()) -> B {
        if mem::size_of::<B>() > 0 {
            let t = *Box::from_raw(ptr as *mut Aligned<B>);
            t.1
        } else {
            ptr::read(ptr as *mut B)
        }
    }

    #[inline]
    fn is_internal_storage() -> bool { false }
}

/// Optionally stores a pointer to a value.
///
/// It is doubtful that there are any types besides `()` and `*mut T` which
/// could implement this usefully.
pub unsafe trait PtrWrite<T : ?Sized> : Copy {
    /// Returns an instance of `Self` with no particular value.
    fn new() -> Self;

    /// Writes the given pointer into `self`.
    ///
    /// ## Unsafety
    ///
    /// The implementation must not inspect the given pointer. This call must
    /// not panic.
    fn store_ptr(&mut self, t: *const T);
}

unsafe impl<T : ?Sized> PtrWrite<T> for () {
    #[inline(always)]
    fn new() -> Self { () }

    #[inline(always)]
    fn store_ptr(&mut self, _: *const T) { }
}

unsafe impl<T : ?Sized> PtrWrite<T> for *const T {
    #[inline(always)]
    fn new() -> Self {
        unsafe { mem::uninitialized() }
    }

    #[inline(always)]
    fn store_ptr(&mut self, t: *const T) {
        *self = t;
    }
}

/// Read trait corresponding to `PtrWrite`.
pub unsafe trait PtrRead<T : ?Sized> : PtrWrite<T> {
    /// Returns the pointer most recently stored via `store_ptr()`.
    ///
    /// ## Unsafety
    ///
    /// Behaviour is undefined if the returned value is not *exactly* equal to
    /// the value passed in to the last call to `store_ptr()`. This call must
    /// not panic.
    fn get_ptr(&self) -> *const T;
}

unsafe impl<T : ?Sized> PtrRead<T> for *const T {
    #[inline(always)]
    fn get_ptr(&self) -> *const T {
        *self
    }
}

// This is completely unsafe for anything outside of `Ref` to use. It exists so
// that `Ref` doesn't need to have all the generics needed to refer to its
// parent directly, instead allowing anyone to just say `Ref<Supercow<...>>`.
//
// It does need to be public though since it's mentioned in type constraints
// and so forth.
#[allow(missing_docs)]
#[doc(hidden)]
pub trait RefParent {
    type Owned : ?Sized;

    /// Notifies `self` that a `Ref` has been dropped.
    ///
    /// ## Unsafety
    ///
    /// Behaviour is undefined if `self` is not in owned mode.
    ///
    /// Behaviour is undefined if a mutable reference to the owned value in
    /// `self` is still live.
    unsafe fn supercow_ref_drop(&mut self);
}

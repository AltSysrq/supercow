// Copyright 2016 Jason Lingle
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![deny(missing_docs)]

//! `Supercow` is `Cow` on steroids.
//!
//! `Supercow` provides a mechanism for making APIs that accept very general
//! references while maintaining very low overhead for usages not involving
//! heavy-weight references (eg, `Arc`). Though nominally similar to `Cow` in
//! structure (and being named after it), `Supercow` does not require the
//! containee to be `Clone` or `ToOwned` unless operations inherently depending
//! on either are invoked.
//!
//! # Quick Start
//!
//! ## Simple Types
//!
//! In many cases, you can think of a `Supercow` as having only one lifetime
//! parameter and one type parameter, corresponding to the lifetime and type of
//! an immutable reference.
//!
//! ```
//! extern crate supercow;
//!
//! use std::sync::Arc;
//! use supercow::Supercow;
//!
//! # fn main() {
//! // Declare some data we want to reference.
//! let fourty_two = 42u32;
//! // Make a Supercow referencing the above.
//! // N.B. Type inference doesn't work reliably if there is nothing explicitly
//! // typed to which the Supercow is passed, so we declare the type of this
//! // variable explicitly.
//! let mut a: Supercow<u32> = Supercow::borrowed(&fourty_two);
//! // We can deref `a` to a `u32`, and also see that it does
//! // indeed reference `fourty_two`.
//! assert_eq!(42, *a);
//! assert_eq!(&fourty_two as *const u32, &*a as *const u32);
//!
//! // Clone `a` so that it also points to `fourty_two`.
//! let mut b = a.clone();
//! assert_eq!(42, *b);
//! assert_eq!(&fourty_two as *const u32, &*b as *const u32);
//!
//! // `to_mut()` can be used to mutate `a` and `b` independently, taking
//! // ownership as needed.
//! *a.to_mut() += 2;
//! assert_eq!(42, fourty_two);
//! assert_eq!(44, *a);
//! assert_eq!(42, *b);
//! assert_eq!(&fourty_two as *const u32, &*b as *const u32);
//!
//! *b.to_mut() = 56;
//! assert_eq!(44, *a);
//! assert_eq!(56, *b);
//! assert_eq!(42, fourty_two);
//!
//! // We can also use `Arc` transparently.
//! let mut c: Supercow<u32> = Supercow::shared(Arc::new(99));
//! assert_eq!(99, *c);
//! *c.to_mut() += 1;
//! assert_eq!(100, *c);
//! # }
//! ```
//!
//! ## Owned/Borrowed Types
//!
//! `Supercow` can have different owned and borrowed types, for example
//! `String` and `str`. In this case, the two are separate type parameters,
//! with the owned one written first. (Both need to be listed explicitly since
//! `Supercow` does not require the contained value to be `ToOwned`.)
//!
//! ```
//! extern crate supercow;
//!
//! use std::sync::Arc;
//! use supercow::Supercow;
//!
//! # fn main() {
//! let hello: Supercow<String, str> = Supercow::borrowed("hello");
//! let mut hello_world = hello.clone();
//! hello_world.to_mut().push_str(" world");
//!
//! assert_eq!(hello, "hello");
//! assert_eq!(hello_world, "hello world");
//! # }
//! ```
//!
//! ## Accepting `Supercow` in an API
//!
//! If you want to make an API taking `Supercow` values, the recommended
//! approach is to accept anything that is `Into<Supercow<YourType>>`, which
//! allows bare owned types and references to owned values to be accepted as
//! well.
//!
//! ```
//! use std::sync::Arc;
//! use supercow::Supercow;
//!
//! fn some_api_function<'a, T : Into<Supercow<'a,u32>>>
//!   (t: T) -> Supercow<'a,u32>
//! {
//!   let mut x = t.into();
//!   *x.to_mut() *= 2;
//!   x
//! }
//!
//! fn main() {
//!   assert_eq!(42, *some_api_function(21));
//!   let twenty_one = 21;
//!   assert_eq!(42, *some_api_function(&twenty_one));
//!   assert_eq!(42, *some_api_function(Supercow::shared(Arc::new(21))));
//! }
//! ```
//!
//! # Use Cases
//!
//! ## More flexible Copy-on-Write
//!
//! `std::borrow::Cow` only supports two modes of ownership: You either fully
//! own the value, or only borrow it. `Rc` and `Arc` have the `make_mut()`
//! method, which allows either total ownership or shared ownership. `Supercow`
//! supports all three: owned, shared, and borrowed.
//!
//! ## More flexible Copy-if-Needed
//!
//! A major use of `Cow` in `std` is found on functions like
//! `OsStr::to_string_lossy()`, which returns a borrowed view into itself if
//! possible, or an owned string if it needed to change something. If the
//! caller does not intend to do its own writing, this is more a "copy if
//! needed" structure, and the fact that it requires the contained value to be
//! `ToOwned` limits it to things that can be cloned.
//!
//! `Supercow` only requires `ToOwned` if the caller actually intends to invoke
//! functionality which requires cloning a borrowed value, so it can fit this
//! use-case even for non-cloneable types.
//!
//! ## Working around awkward lifetimes
//!
//! This is the original case for which `Supercow` was designed.
//!
//! Say you have an API with a sort of hierarchical structure of heavyweight
//! resources, for example handles to a local database and tables within it. A
//! natural representation may be to make the table handle hold a reference to
//! the database handle.
//!
//! ```norun
//! struct Database;
//! impl Database {
//!   fn new() -> Self {
//!     // Computation...
//!     Database
//!   }
//!   fn close(self) -> bool {
//!     // Eg, it returns an error on failure or something
//!     true
//!   }
//! }
//! impl Drop for Database {
//!   fn drop(&mut self) {
//!     println!("Dropping database");
//!   }
//! }
//! struct Table<'a>(&'a Database);
//! impl<'a> Table<'a> {
//!   fn new(db: &'a Database) -> Self {
//!     // Computation...
//!     Table(db)
//!   }
//! }
//! impl<'a> Drop for Table<'a> {
//!   fn drop(&mut self) {
//!     println!("Dropping table");
//!     // Notify `self.db` about this
//!   }
//! }
//! ```
//!
//! We can use this quite easily:
//!
//! ```
//! # struct Database;
//! # impl Database {
//! #   fn new() -> Self {
//! #     // Computation...
//! #     Database
//! #   }
//! #   fn close(self) -> bool {
//! #     // Eg, it returns an error on failure or something
//! #     true
//! #   }
//! # }
//! # impl Drop for Database {
//! #   fn drop(&mut self) {
//! #     println!("Dropping database");
//! #   }
//! # }
//! # struct Table<'a>(&'a Database);
//! # impl<'a> Table<'a> {
//! #   fn new(db: &'a Database) -> Self {
//! #     // Computation...
//! #     Table(db)
//! #   }
//! # }
//! # impl<'a> Drop for Table<'a> {
//! #   fn drop(&mut self) {
//! #     println!("Dropping table");
//! #     // Notify `self.db` about this
//! #   }
//! # }
//!
//! # #[allow(unused_variables)]
//! fn main() {
//!   let db = Database::new();
//!   {
//!     let table1 = Table::new(&db);
//!     let table2 = Table::new(&db);
//!     do_stuff(&table1);
//!     // Etc
//!   }
//!   assert!(db.close());
//! }
//!
//! # #[allow(unused_variables)]
//! fn do_stuff(table: &Table) {
//!   // Stuff
//! }
//! ```
//!
//! That is, until we want to hold the database and the tables in a struct.
//!
//! ```ignore
//! struct Resources {
//!   db: Database,
//!   table: Table<'uhhh>, // Uh, what is the lifetime here?
//! }
//! ```
//!
//! There are several options here:
//!
//! - Change the API to use `Arc`s or similar. This works, but adds overhead
//! for clients that don't need it, and additionally removes from everybody the
//! ability to statically know whether `db.close()` can be called.
//!
//! - Force clients to resort to unsafety, such as
//! [`OwningHandle`](http://kimundi.github.io/owning-ref-rs/owning_ref/struct.OwningHandle.html).
//! This sacrifices no performance and allows the stack-based client usage to
//! be able to call `db.close()` easily, but makes things much more difficult
//! for other clients.
//!
//! - Take a `Borrow` type parameter. This works and is zero-overhead, but
//! results in a proliferation of generics throughout the API and client code,
//! and becomes especially problematic when the hierarchy is multiple such
//! levels deep.
//!
//! - Use `Supercow` to get the best of both worlds.
//!
//! We can adapt and use the API like so:
//!
//! ```
//! use std::sync::Arc;
//!
//! use supercow::Supercow;
//!
//! struct Database;
//! impl Database {
//!   fn new() -> Self {
//!     // Computation...
//!     Database
//!   }
//!   fn close(self) -> bool {
//!     // Eg, it returns an error on failure or something
//!     true
//!   }
//! }
//! impl Drop for Database {
//!   fn drop(&mut self) {
//!     println!("Dropping database");
//!   }
//! }
//! struct Table<'a>(Supercow<'a, Database>);
//! impl<'a> Table<'a> {
//!   fn new<T : Into<Supercow<'a, Database>>>(db: T) -> Self {
//!     // Computation...
//!     Table(db.into())
//!   }
//! }
//! impl<'a> Drop for Table<'a> {
//!   fn drop(&mut self) {
//!     println!("Dropping table");
//!     // Notify `self.db` about this
//!   }
//! }
//!
//! // The original stack-based code, unmodified
//!
//! # #[allow(unused_variables)]
//! fn on_stack() {
//!   let db = Database::new();
//!   {
//!     let table1 = Table::new(&db);
//!     let table2 = Table::new(&db);
//!     do_stuff(&table1);
//!     // Etc
//!   }
//!   assert!(db.close());
//! }
//!
//! // If we only wanted one Table and didn't care about ever getting the
//! // Database back, we don't even need a reference.
//! fn by_value() {
//!   let db = Database::new();
//!   let table = Table::new(db);
//!   do_stuff(&table);
//! }
//!
//! // And we can declare our holds-everything struct by using `Arc`s to deal
//! // with ownership.
//! struct Resources {
//!   db: Arc<Database>,
//!   table: Table<'static>,
//! }
//! impl Resources {
//!   fn new() -> Self {
//!     let db = Arc::new(Database::new());
//!     let table = Table::new(Supercow::shared(db.clone()));
//!     Resources { db: db, table: table }
//!   }
//!
//!   fn close(self) -> bool {
//!     drop(self.table);
//!     Arc::try_unwrap(self.db).ok().unwrap().close()
//!   }
//! }
//!
//! fn with_struct() {
//!   let res = Resources::new();
//!   do_stuff(&res.table);
//!   assert!(res.close());
//! }
//!
//! # #[allow(unused_variables)]
//! fn do_stuff(table: &Table) {
//!   // Stuff
//! }
//!
//! ```
//!
//! # Shared Reference Type
//!
//! The third type parameter type to `Supercow` specifies the shared reference
//! type.
//!
//! The default is `DefaultFeatures`, which is a boxed trait object describing
//! the features a shared reference type must have while allowing any such
//! reference to be used without needing a generic type argument.
//!
//! An alternate feature set can be found in `NonSyncFeatures`, which is also
//! usable through the `NonSyncSupercow` typedef. You can create custom feature
//! traits in this style with `supercow_features!`.
//!
//! Boxing the shared reference and putting it behind a trait object both add
//! overhead, of course. If you wish, you can use a real reference type in the
//! third parameter as long as you are OK with losing the flexibility the
//! boxing would provide. For example,
//!
//! ```
//! use std::rc::Rc;
//!
//! use supercow::Supercow;
//!
//! # fn main() {
//! let x: Supercow<u32, u32, Rc<u32>> = Supercow::shared(Rc::new(42u32));
//! println!("{}", *x);
//! # }
//! ```
//!
//! Note that you may need to provide an identity `supercow::aux::SharedFrom`
//! implementation if you have a custom reference type.
//!
//! # Advanced
//!
//! ## Variance
//!
//! `Supercow` is covariant on its lifetime and all its type parameters, except
//! for `SHARED` which is invariant. Note that because the default type of
//! `SHARED` uses `Supercow`'s only lifetime parameter, a simple `Supercow` is
//! effectively invariant.
//!
//! ```
//! use std::rc::Rc;
//!
//! use supercow::Supercow;
//!
//! fn assert_covariance<'a, 'b: 'a>(
//!   one: Supercow<'b, &'b u32, &'b u32, Rc<&'b u32>>,
//!   two: Supercow<'b, u32>)
//! {
//!   let _one_a: Supercow<'a, &'a u32, &'a u32, Rc<&'a u32>> = one;
//!   // We can't just write `Supercow<'a, u32>` because that would change
//!   // the boxed type of `SHARED`. There's also not much utility in
//!   // doing this since the original type parameter would need to be carried
//!   // around anyway.
//!   let _two_a: Supercow<'a, u32, u32,
//!     Box<supercow::DefaultFeatures<'b, Target = u32>>> = two;
//! }
//!
//! # fn main() { }
//! ```
//!
//! ## `Sync` and `Send`
//!
//! A `Supercow` is `Sync` and `Send` iff the types it contains, including the
//! shared reference type, are.
//!
//! ```
//! use supercow::Supercow;
//!
//! fn assert_sync_and_send<T : Sync + Send>(_: T) { }
//! fn main() {
//!   let s: Supercow<u32> = Supercow::owned(42);
//!   assert_sync_and_send(s);
//! }
//! ```
//!
//! # Performance Considerations
//!
//! ## Construction Cost
//!
//! Since it inherently moves certain decisions about ownership from
//! compile-time to run-time, `Supercow` is obviously not as fast as using an
//! owned value directly or a reference directly.
//!
//! Constructing a `Supercow` with an owned object or a simple reference is
//! reasonably fast, but does incur a small amount of overhead for the pointer
//! displacement to be set up.
//!
//! The default `Supercow` shared reference type boxes the reference, incurring
//! an allocation as well as virtual dispatch on certain operations. This is
//! obviously much more expensive than the other options, though note that the
//! allocation is only incurred when constructing the `Supercow`, so this is
//! inconsequential in a create-once-use-many case. Use of a concrete shared
//! reference type alleviates this issue.
//!
//! ## Destruction Cost
//!
//! Destroying a `Supercow` is roughly the same proportional cost of creating
//! it.
//!
//! ## `Deref` Cost
//!
//! `Supercow`'s `deref` implementation is branch-free and therefore generally
//! runs reasonably quickly. It is not dependent on the ownership mode of the
//! `Supercow`, and so is not affected by the shared reference type, most
//! importantly, making no virtual function calls even under the default boxed
//! shared reference type. However, the way it works may prevent LLVM
//! optimisations from applying in particular circumstances.
//!
//! For those wanting specifics, the function
//!
//! ```ignore
//! // Substitute Cow with Supercow for the other case.
//! // This takes references so that the destructor code is not intermingled.
//! fn add_two(a: &Cow<u32>, b: &Cow<u32>) -> u32 {
//!   **a + **b
//! }
//! ```
//!
//! results in the following on AMD64 with Rust 1.13.0:
//!
//! ```text
//!  Cow                                Supercow
//!  cmp    DWORD PTR [rdi],0x1         mov    rcx,QWORD PTR [rdi]
//!  lea    rcx,[rdi+0x4]               and    rdi,QWORD PTR [rdi+0x8]
//!  cmovne rcx,QWORD PTR [rdi+0x8]     mov    rax,QWORD PTR [rsi]
//!  cmp    DWORD PTR [rsi],0x1         and    rsi,QWORD PTR [rsi+0x8]
//!  lea    rax,[rsi+0x4]               mov    eax,DWORD PTR [rsi+rax]
//!  cmovne rax,QWORD PTR [rsi+0x8]     add    eax,DWORD PTR [rdi+rcx]
//!  mov    eax,DWORD PTR [rax]         ret
//!  add    eax,DWORD PTR [rcx]
//!  ret
//! ```
//!
//! The same code on ARM v7l and Rust 1.12.1:
//!
//! ```text
//!  Cow                                Supercow
//!  push       {fp, lr}                push    {fp, lr}
//!  mov        r2, r0                  ldr     r3, [r0, #4]
//!  ldr        r3, [r2, #4]!           ldr     r2, [r1, #4]
//!  ldr        ip, [r0]                ldr     lr, [r0]
//!  mov        r0, r1                  and     r0, r3, r0
//!  ldr        lr, [r0, #4]!           ldr     ip, [r1]
//!  ldr        r1, [r1]                and     r1, r2, r1
//!  cmp        ip, #1                  ldr     r0, [r0, lr]
//!  moveq      r3, r2                  ldr     r1, [r1, ip]
//!  cmp        r1, #1                  add     r0, r1, r0
//!  ldr        r2, [r3]                pop     {fp, pc}
//!  moveq      lr, r0
//!  ldr        r0, [lr]
//!  add        r0, r0, r2
//!  pop        {fp, pc}
//! ```
//!
//! ## `to_mut` Cost
//!
//! Obtaining a `Ref` is substantially more expensive than `Deref`, as it must
//! inspect the ownership mode of the `Supercow` and possibly move it into the
//! owned mode. This will include a virtual call to the boxed shared reference
//! if in shared mode when using the default `Supercow` shared reference type.
//!
//! There is also cost in releasing the mutable reference, though
//! insubstantial in comparison.
//!
//! ## Memory Usage
//!
//! `Supercow` can be quite large in comparison to a bare reference. This
//! stems from two sources:
//!
//! - There are two pointers of overhead (or three for DSTs) used for the
//! branch-free `Deref` implementation.
//!
//! - The `Supercow` must be able to contain a full instance of `OWNED`.
//!
//! The second can be addressed in a couple ways. Firstly, you can make the
//! `OWNED` type a `Box`. If you need something that depends on `ToOwned`, it
//! may be necessary to wrap the owned value in a non-`Clone` struct that
//! implements `ToOwned` by boxing itself.
//!
//! ```
//! use supercow::Supercow;
//!
//! const N: usize = 65536;
//! fn nth(array: &Supercow<Box<[u64;N]>, [u64;N]>, n: usize) -> u64 {
//!   array[n]
//! }
//! fn main() {
//!   let array: [u64;N] = [0;N];
//!   let boxed_array: Box<[u64;N]> = Box::new([0;N]);
//!   assert_eq!(0, nth(&Supercow::borrowed(&array), 42));
//!   assert_eq!(0, nth(&Supercow::owned(boxed_array), 56));
//! }
//! ```
//!
//! If the owned (or shared) states are certainly never used, another option is
//! to use an uninhabited type (possibly `!` depending on its state when it
//! becomes stable). Because there is currently no way to provide a blanket
//! implementation of `Borrow<T>` for all `T`, and there will never be a way to
//! blanket `ConstDeref` in this way, `supercow` does not provide such a type
//! at this time, but you can easily define your own.
//!
//! ```
//! use std::borrow::Borrow;
//! use std::sync::Arc;
//!
//! use supercow::Supercow;
//!
//! enum Void { }
//! impl Borrow<u32> for Void {
//!   fn borrow(&self) -> &u32 {
//!     match *self { }
//!   }
//! }
//! unsafe impl supercow::aux::SafeBorrow<u32> for Void {
//!   fn borrow_replacement(ptr: &u32) -> &u32 { ptr }
//! }
//! unsafe impl supercow::aux::ConstDeref for Void {
//!   type Target = u32;
//!   fn const_deref(&self) -> &u32 {
//!     match *self { }
//!   }
//! }
//!
//! fn never_owned(s: &Supercow<Void, u32>) -> u32 { **s }
//! fn never_shared(s: &Supercow<u32, u32, Void>) -> u32 { **s }
//!
//! fn main() {
//!   never_owned(&Supercow::shared(Arc::new(42)));
//!   never_shared(&Supercow::owned(56));
//! }
//!
//! ```
//!
//! # Other Notes
//!
//! Using `Supercow` will not give your application `apt-get`-style Super Cow
//! Powers.

use std::borrow::{Borrow, ToOwned};
use std::convert::{AsRef, From};
use std::cmp;
use std::fmt;
use std::mem;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::slice;

/// Miscelaneous things used to integrate other code with Supercow, but which
/// are not of interest to end users.
pub mod aux {
    use std::borrow::Borrow;
    use std::ffi::{CStr, OsStr};
    use std::path::Path;
    use std::rc::Rc;
    use std::slice;
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

    /// Extension of `Borrow` used to allow `Supercow::to_mut()` to work
    /// safely.
    pub unsafe trait SafeBorrow<T : ?Sized>: Borrow<T> {
        /// Given `ptr`, which was obtained from a prior call to
        /// `Self::borrow()`, return a value with the same nominal lifetime
        /// which is guaranteed to survive mutations to `Self`.
        ///
        /// Types which implement `Borrow` by pure, constant pointer arithmetic
        /// on `self` can simply return `ptr` unmodified. Other types typically
        /// need to provide some static reference, such as the empty string for
        /// `&str`.
        ///
        /// ## Unsafety
        ///
        /// Behaviour is undefined if this call returns `ptr`, but a mutation
        /// to `Self` could invalidate the reference.
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
    /// `Supercow` expects to be able to read the first pointer-sized value of
    /// such a reference and perform address arithmetic upon it.
    ///
    /// There is no utility of applying this trait to anything other than a
    /// const reference.
    ///
    /// ## Unsafety
    ///
    /// Behaviour is undefined if a marked type does not begin with a real
    /// pointer to a value (with the usual exception of ZSTs, where the pointer
    /// does not need to point to anything in particular) or if other parts of
    /// the type contain address-dependent information.
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
}

use self::aux::*;

/// Defines a "feature set" for a custom `Supercow` type.
///
/// ## Syntax
///
/// ```
/// #[macro_use] extern crate supercow;
///
/// # pub trait SomeTrait { }
/// # pub trait AnotherTrait { }
///
/// supercow_features!(
///   /// Some documentation, etc, if desired.
///   pub trait FeatureName: SomeTrait, AnotherTrait);
/// supercow_features!(
///   pub trait FeatureName2: Clone, SomeTrait, AnotherTrait);
///
/// # fn main() { }
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
            /// Clone this value, and then immediately put it into a `Box`
            /// behind a trait object of this trait.
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
        impl<'a, T : $feature_name<'a>> $crate::aux::SharedFrom<T>
        for Box<$feature_name<'a, Target = T::Target> + 'a> {
            fn shared_from(t: T) -> Self {
                Box::new(t)
            }
        }
        impl<'a, S : 'a + ?Sized> Clone for Box<$feature_name<'a, Target = S> + 'a> {
            fn clone(&self) -> Self {
                $feature_name::clone_boxed(&**self)
            }
        }
    };

    ($(#[$meta:meta])* pub trait $feature_name:ident: $($req:ident),*) => {
        $(#[$meta])*
        pub trait $feature_name<'a>: $($req +)* $crate::aux::ConstDeref + 'a {
        }
        impl<'a, T : 'a + $($req +)* $crate::aux::ConstDeref>
        $feature_name<'a> for T {
        }
        impl<'a, T : $feature_name<'a>> $crate::aux::SharedFrom<T>
        for Box<$feature_name<'a, Target = T::Target> + 'a> {
            fn shared_from(t: T) -> Self {
                Box::new(t)
            }
        }
    };
}

supercow_features!(
    /// The default shared reference type for `Supercow`.
    ///
    /// This requires the shared reference type to be `Clone`, `Send`, and
    /// `Sync`, which thus disqualifies using `Rc`. This was chosen as the
    /// default since the inability to use `Rc` is generally a less subtle
    /// issue than the `Supercow` not being `Send` or `Sync`.
    ///
    /// See also `NonSyncFeatures`.
    pub trait DefaultFeatures: Clone, Send, Sync);
supercow_features!(
    /// The shared reference type for `NonSyncSupercow`.
    ///
    /// Unlike `DefaultFeatures`, this only requires the shared reference type
    /// to be `Clone`, thus permitting `Rc`.
    pub trait NonSyncFeatures: Clone);

/// `Supercow` with the default `SHARED` changed to `NonSyncFeatures`, enabling
/// the use of `Rc` as a shared reference type.
///
/// ## Example
///
/// ```
/// use supercow::{NonSyncSupercow, Supercow};
///
/// # fn main() {
/// let x: NonSyncSupercow<u32> = Supercow::owned(42u32);
/// println!("{}", *x);
/// # }
/// ```
pub type NonSyncSupercow<'a, OWNED, BORROWED = OWNED> =
    Supercow<'a, OWNED, BORROWED,
             Box<NonSyncFeatures<'a, Target = BORROWED> + 'a>>;

/// The actual generic reference type.
///
/// See the module documentation for most of the details.
///
/// The generics here may look somewhat frightening at first; try not to be too
/// alarmed, and remember that in most use-cases all you need to worry about is
/// the stuff concerning `OWNED`.
pub struct Supercow<'a, OWNED, BORROWED : ?Sized = OWNED,
                    SHARED = Box<DefaultFeatures<'a, Target = BORROWED> + 'a>>
where BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> {
    // In order to implement `Deref` in a branch-free fashion that isn't
    // sensitive to the Supercow being moved, we set `ptr_mask` and
    // `ptr_displacement` such that
    // `target = &*((&self & sext(ptr_mask)) + ptr_displacement)`
    // (arithmetic in terms of bytes, obviously).
    //
    // So for the three cases:
    //
    // Owned => ptr_mask = ~0u, ptr_displacement = offsetof(self, Owned.0)
    // Borrowed, Shared => ptr_mask = 0u, ptr_displacement = address
    //
    // In order to support DSTs, `ptr_displacement` is actually a reference to
    // `BORROWED`. We assume the first pointer-sized value is the actual
    // pointer (see `PointerFirstRef`). `ptr_displacement` may not actually be
    // dereferenced.
    ptr_displacement: &'a BORROWED,
    ptr_mask: usize,
    state: SupercowData<'a, OWNED, BORROWED, SHARED>,
}

enum SupercowData<'a, OWNED, BORROWED : 'a + ?Sized, SHARED> {
    Owned(OWNED),
    Borrowed(&'a BORROWED),
    Shared(SHARED),
}
use self::SupercowData::*;

impl<'a, OWNED, BORROWED : ?Sized, SHARED> Deref
for Supercow<'a, OWNED, BORROWED, SHARED>
where BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> {
    type Target = BORROWED;
    #[inline]
    fn deref(&self) -> &BORROWED {
        let self_address = self as *const Self as usize;

        let mut target_ref = self.ptr_displacement;
        unsafe {
            let target_address: &mut usize = mem::transmute(&mut target_ref);
            let nominal_address = *target_address;
            *target_address = (self_address & self.ptr_mask) + nominal_address;
        }
        target_ref
    }
}

impl<'a, OWNED, BORROWED : ?Sized, SHARED>
Supercow<'a, OWNED, BORROWED, SHARED>
where OWNED : Borrow<BORROWED>,
      BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> {
    /// Creates a new `Supercow` which owns the given value.
    ///
    /// This can create a `Supercow` with a `'static` lifetime.
    pub fn owned(inner: OWNED) -> Self {
        Self::from_data(Owned(inner))
    }

    /// Creates a new `Supercow` which borrows the given value.
    pub fn borrowed<T : Borrow<BORROWED> + ?Sized>(inner: &'a T) -> Self {
        Self::from_data(Borrowed(inner.borrow()))
    }

    /// Creates a new `Supercow` using the given shared reference.
    ///
    /// The reference must be convertable to `SHARED` via `SharedFrom`.
    pub fn shared<T>(inner: T) -> Self
    where SHARED : SharedFrom<T> {
        Self::from_data(Shared(SHARED::shared_from(inner)))
    }

    fn from_data(data: SupercowData<'a, OWNED, BORROWED, SHARED>) -> Self {
        let mut this = Supercow {
            ptr_mask: 0,
            ptr_displacement: unsafe { mem::uninitialized() },
            state: data,
        };
        this.set_ptr();
        this
    }

    fn set_ptr(&mut self) {
        {
            let borrowed_ptr = match self.state {
                Owned(ref r) => r.borrow(),
                Borrowed(r) => r,
                Shared(ref s) => s.const_deref(),
            };
            // There's no safe way to propagate `borrowed_ptr` into
            // `ptr_displacement` since the former has a borrow scoped to this
            // function.
            unsafe {
                let dst: &mut [u8] = slice::from_raw_parts_mut(
                    &mut self.ptr_displacement as *mut&'a BORROWED
                        as *mut u8,
                    mem::size_of::<&'a BORROWED>());
                let src: &[u8] = slice::from_raw_parts(
                    &borrowed_ptr as *const&BORROWED as *const u8,
                    mem::size_of::<&'a BORROWED>());
                dst.copy_from_slice(src);
            }
        }
        self.adjust_ptr();
    }

    fn adjust_ptr(&mut self) {
        // Use relative addressing if `ptr` is inside `self` and absolute
        // addressing otherwise.
        //
        // Ordinarily, `ptr` will always be inside `self` if the state is
        // `Owned`, and outside otherwise. However, it is possible to create
        // `Borrow` implementations that return arbitrary pointers, so we
        // handle the two cases like self instead.
        let self_start = self as *const Self as usize;
        let self_end = self_start + mem::size_of::<Self>();
        let addr: &mut usize = unsafe {
            mem::transmute(&mut self.ptr_displacement)
        };

        if *addr >= self_start && *addr < self_end {
            self.ptr_mask = !0;
            *addr -= self_start;
        } else {
            self.ptr_mask = 0;
        }
    }
}

impl<'a, OWNED, BORROWED : ?Sized, SHARED> From<OWNED>
for Supercow<'a, OWNED, BORROWED, SHARED>
where OWNED : Borrow<BORROWED>,
      BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> {
    fn from(inner: OWNED) -> Self {
        Self::from_data(SupercowData::Owned(inner))
    }
}

impl<'a, OWNED, BORROWED : ?Sized, SHARED> From<&'a OWNED>
for Supercow<'a, OWNED, BORROWED, SHARED>
where OWNED : Borrow<BORROWED>,
      BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> {
    fn from(inner: &'a OWNED) -> Self {
        Self::from_data(SupercowData::Borrowed(inner.borrow()))
    }
}

impl<'a, OWNED, BORROWED : ?Sized, SHARED>
Supercow<'a, OWNED, BORROWED, SHARED>
where OWNED : Borrow<BORROWED>,
      BORROWED : 'a + ToOwned<Owned = OWNED>,
      for<'l> &'l BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> {
    /// Takes ownership of the underlying value, so that this `Supercow` has a
    /// `'static` lifetime.
    ///
    /// This may also change the `SHARED` type parameter arbitrarily (which
    /// happens, eg, when converting from `Supercow<'a,u32>` to
    /// `Supercow<'static,u32>`).
    ///
    /// ## Example
    ///
    /// ```
    /// use supercow::Supercow;
    ///
    /// let s = {
    ///   let fourty_two = 42u32;
    ///   let by_ref: Supercow<u32> = Supercow::borrowed(&fourty_two);
    ///   // We can't return `by_ref` because it holds a reference to
    ///   // `fourty_two`. However, we can change that lifetime parameter
    ///   // to `'static` and then move that out of the block.
    ///   let by_val: Supercow<'static, u32> =
    ///     Supercow::take_ownership(by_ref);
    ///   by_val
    /// };
    /// assert_eq!(42, *s);
    /// ```
    pub fn take_ownership<NS : ConstDeref<Target = BORROWED>>
        (this: Self)
         -> Supercow<'static, OWNED, BORROWED, NS>
    {
        match this.state {
            Owned(o) => Supercow {
                ptr_mask: this.ptr_mask,
                ptr_displacement: unsafe {
                    &*(this.ptr_displacement as *const BORROWED)
                },
                state: Owned(o),
            },
            Borrowed(r) => Supercow::owned(r.to_owned()),
            Shared(ref s) => Supercow::owned(s.const_deref().to_owned()),
        }
    }
}

impl<'a, OWNED, BORROWED : ?Sized, SHARED>
Supercow<'a, OWNED, BORROWED, SHARED>
where OWNED : Borrow<BORROWED>,
      BORROWED : 'a + ToOwned<Owned = OWNED>,
      &'a BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> {
    /// Takes ownership of the underling value if needed, then returns it,
    /// consuming `self`.
    pub fn into_inner(this: Self) -> OWNED {
        match this.state {
            Owned(o) => o,
            Borrowed(r) => r.to_owned(),
            Shared(ref s) => s.const_deref().to_owned(),
        }
    }
}

impl<'a, OWNED, BORROWED : ?Sized, SHARED>
Supercow<'a, OWNED, BORROWED, SHARED>
where OWNED : SafeBorrow<BORROWED>,
      BORROWED : 'a + ToOwned<Owned = OWNED>,
      &'a BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> {
    /// Returns a (indirect) mutable reference to an underlying owned value.
    ///
    /// If this `Supercow` does not currently own the value, it takes
    /// ownership. A `Ref` is then returned which allows accessing the mutable
    /// owned value directly.
    ///
    /// ## Leak Safety
    ///
    /// If the returned `Ref` is released without its destructor being run, the
    /// behaviour of the `Supercow` is unspecified (but does not result in
    /// memory unsafety).
    pub fn to_mut<'b>(&'b mut self) -> Ref<'a, 'b, OWNED, BORROWED, SHARED> {
        // Take ownership if we do not already have it
        let new = match self.state {
            Owned(_) => None,
            Borrowed(r) => Some(Self::owned(r.to_owned())),
            Shared(ref s) => Some(Self::owned(s.const_deref().to_owned())),
        };
        if let Some(new) = new {
            *self = new;
        }

        let r = match self.state {
            Owned(ref mut r) => r as *mut OWNED,
            _ => unreachable!(),
        };
        // Because mutating the owned value could invalidate the calculated
        // pointer we have, reset it to something that won't change, and then
        // recalculate it when the `Ref` is dropped.
        self.ptr_displacement =
            OWNED::borrow_replacement(self.ptr_displacement);
        self.adjust_ptr();

        Ref { r: r, parent: self }
    }
}

/// Provides mutable access to an owned value within a `Supercow`.
///
/// This is similar to the `Ref` used with `RefCell`.
pub struct Ref<'a, 'b, OWNED, BORROWED : ?Sized, SHARED>
where 'a: 'b,
      OWNED : 'b + SafeBorrow<BORROWED>,
      BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : 'b + ConstDeref<Target = BORROWED> {
    r: *mut OWNED,
    parent: &'b mut Supercow<'a, OWNED, BORROWED, SHARED>,
}

impl<'a, 'b, OWNED, BORROWED : ?Sized, SHARED> Deref
for Ref<'a, 'b, OWNED, BORROWED, SHARED>
where 'a: 'b,
      OWNED : 'b + SafeBorrow<BORROWED>,
      BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : 'b + ConstDeref<Target = BORROWED> {
    type Target = OWNED;

    #[inline]
    fn deref(&self) -> &OWNED {
        unsafe { &*self.r }
    }
}

impl<'a, 'b, OWNED, BORROWED : ?Sized, SHARED> DerefMut
for Ref<'a, 'b, OWNED, BORROWED, SHARED>
where 'a: 'b,
      OWNED : 'b + SafeBorrow<BORROWED>,
      BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : 'b + ConstDeref<Target = BORROWED> {
    #[inline]
    fn deref_mut(&mut self) -> &mut OWNED {
        unsafe { &mut*self.r }
    }
}

impl<'a, 'b, OWNED, BORROWED : ?Sized, SHARED> Drop
for Ref<'a, 'b, OWNED, BORROWED, SHARED>
where 'a: 'b,
      OWNED : 'b + SafeBorrow<BORROWED>,
      BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : 'b + ConstDeref<Target = BORROWED> {
    #[inline]
    fn drop(&mut self) {
        // The value of `OWNED::borrow()` may have changed, so recompute
        // everything instead of backing the old values up.
        self.parent.set_ptr()
    }
}

impl<'a, OWNED, BORROWED : ?Sized, SHARED> Clone
for Supercow<'a, OWNED, BORROWED, SHARED>
where OWNED : Clone,
      BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : Clone + ConstDeref<Target = BORROWED> {
    fn clone(&self) -> Self {
        Supercow {
            ptr_mask: self.ptr_mask,
            ptr_displacement: self.ptr_displacement,
            state: match self.state {
                Owned(ref o) => Owned(o.clone()),
                Borrowed(r) => Borrowed(r),
                Shared(ref s) => Shared(s.clone()),
            }
        }
    }
}

macro_rules! deleg_fmt {
    ($tr:ident) => {
        impl<'a, OWNED, BORROWED : ?Sized, SHARED> fmt::$tr
        for Supercow<'a, OWNED, BORROWED, SHARED>
        where BORROWED : 'a + fmt::$tr,
              &'a BORROWED : PointerFirstRef,
              SHARED : ConstDeref<Target = BORROWED> {
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

impl<'a, OWNED, BORROWED : ?Sized, SHARED, T> cmp::PartialEq<T>
for Supercow<'a, OWNED, BORROWED, SHARED>
where T : Borrow<BORROWED>,
      BORROWED : 'a + PartialEq<BORROWED>,
      &'a BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> {
    fn eq(&self, other: &T) -> bool {
        **self == *other.borrow()
    }

    fn ne(&self, other: &T) -> bool {
        **self != *other.borrow()
    }
}

impl<'a, OWNED, BORROWED : ?Sized, SHARED> cmp::Eq
for Supercow<'a, OWNED, BORROWED, SHARED>
where BORROWED : 'a + Eq,
      &'a BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> { }

impl<'a, OWNED, BORROWED : ?Sized, SHARED, T> cmp::PartialOrd<T>
for Supercow<'a, OWNED, BORROWED, SHARED>
where T : Borrow<BORROWED>,
      BORROWED : 'a + PartialOrd<BORROWED>,
      &'a BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> {
    fn partial_cmp(&self, other: &T) -> Option<cmp::Ordering> {
        (**self).partial_cmp(other.borrow())
    }

    fn lt(&self, other: &T) -> bool {
        **self < *other.borrow()
    }

    fn le(&self, other: &T) -> bool {
        **self <= *other.borrow()
    }

    fn gt(&self, other: &T) -> bool {
        **self > *other.borrow()
    }

    fn ge(&self, other: &T) -> bool {
        **self >= *other.borrow()
    }
}

impl<'a, OWNED, BORROWED : ?Sized, SHARED> cmp::Ord
for Supercow<'a, OWNED, BORROWED, SHARED>
where BORROWED : 'a + cmp::Ord,
      &'a BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        (**self).cmp(other)
    }
}

impl<'a, OWNED, BORROWED : ?Sized, SHARED> Hash
for Supercow<'a, OWNED, BORROWED, SHARED>
where BORROWED : 'a + Hash,
      &'a BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> {
    fn hash<H : Hasher>(&self, h: &mut H) {
        (**self).hash(h)
    }
}

impl<'a, OWNED, BORROWED : ?Sized, SHARED> Borrow<BORROWED>
for Supercow<'a, OWNED, BORROWED, SHARED>
where BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> {
    fn borrow(&self) -> &BORROWED {
        self.deref()
    }
}

impl<'a, OWNED, BORROWED : ?Sized, SHARED> AsRef<BORROWED>
for Supercow<'a, OWNED, BORROWED, SHARED>
where BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED> {
    fn as_ref(&self) -> &BORROWED {
        self.deref()
    }
}

#[cfg(test)]
mod test {
    use std::borrow::Cow;
    use std::sync::Arc;

    use super::*;

    #[test]
    fn ref_to_owned() {
        let x = 42u32;
        let a: Supercow<u32> = Supercow::borrowed(&x);
        assert_eq!(x, *a);
        assert_eq!(&x as *const u32 as usize,
                   (&*a) as *const u32 as usize);

        let mut b = a.clone();
        assert_eq!(x, *b);
        assert_eq!(&x as *const u32 as usize,
                   (&*b) as *const u32 as usize);

        *b.to_mut() = 56;
        assert_eq!(42, *a);
        assert_eq!(x, *a);
        assert_eq!(&x as *const u32 as usize,
                   (&*a) as *const u32 as usize);
        assert_eq!(56, *b);
    }

    #[test]
    fn supports_dst() {
        let a: Supercow<String, str> = Supercow::borrowed("hello");
        let b: Supercow<String, str> = Supercow::owned("hello".to_owned());
        assert_eq!(a, b);

        let mut c = a.clone();
        c.to_mut().push_str(" world");
        assert_eq!(a, b);
        assert_eq!(c, "hello world");
    }

    #[test]
    fn default_accepts_arc() {
        let x: Supercow<u32> = Supercow::shared(Arc::new(42u32));
        assert_eq!(42, *x);
    }

    #[test]
    fn ref_safe_even_if_forgotten() {
        let mut x: Supercow<String, str> = Supercow::owned("foo".to_owned());
        {
            let mut m = x.to_mut();
            // Add a bunch of characters to invalidate the allocation
            for _ in 0..65536 {
                m.push('x');
            }

            // Prevent the dtor from running but allow us to release the borrow
            ::std::mem::forget(m);
        }

        // While the value has been corrupted, we have been left with a *safe*
        // deref result nonetheless.
        assert_eq!("", &*x);
        // The actual String has not been lost so no memory has been leaked
        assert_eq!(65539, x.to_mut().len());
    }

    #[test]
    fn general_trait_delegs_work() {
        use std::borrow::Borrow;
        use std::collections::hash_map::DefaultHasher;
        use std::convert::AsRef;
        use std::cmp::*;
        use std::hash::*;

        macro_rules! test_fmt {
            ($fmt:expr, $x:expr) => {
                assert_eq!(format!($fmt, 42u32), format!($fmt, $x));
            }
        }

        let x: Supercow<u32> = Supercow::owned(42u32);
        test_fmt!("{}", x);
        test_fmt!("{:?}", x);
        test_fmt!("{:o}", x);
        test_fmt!("{:x}", x);
        test_fmt!("{:X}", x);
        test_fmt!("{:b}", x);

        assert!(x == 42);
        assert!(x != 43);
        assert!(x < 43);
        assert!(x <= 43);
        assert!(x > 41);
        assert!(x >= 41);
        assert_eq!(42.partial_cmp(&43), x.partial_cmp(&43));
        assert_eq!(42.cmp(&43), x.cmp(&Supercow::owned(43)));

        let mut expected_hash = DefaultHasher::new();
        42u32.hash(&mut expected_hash);
        let mut actual_hash = DefaultHasher::new();
        x.hash(&mut actual_hash);
        assert_eq!(expected_hash.finish(), actual_hash.finish());

        assert_eq!(42u32, *x.borrow());
        assert_eq!(42u32, *x.as_ref());
    }

    // This is where the asm in the Performance Notes section comes from.

    #[inline(never)]
    fn add_two_cow(a: &Cow<u32>, b: &Cow<u32>) -> u32 {
        **a + **b
    }

    #[inline(never)]
    fn add_two_supercow(a: &Supercow<u32>, b: &Supercow<u32>) -> u32 {
        **a + **b
    }

    #[test]
    fn do_add_two() {
        // Need to call `add_two_cow` twice to prevent LLVM from specialising
        // it.
        assert_eq!(42, add_two_cow(&Cow::Owned(40), &Cow::Owned(2)));
        assert_eq!(44, add_two_cow(&Cow::Borrowed(&38), &Cow::Borrowed(&6)));
        assert_eq!(42, add_two_supercow(&Supercow::owned(40),
                                        &Supercow::owned(2)));
    }
}

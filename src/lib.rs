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
//!   assert_eq!(42, *some_api_function(Arc::new(21)));
//! }
//! ```
//!
//! ## Chosing the right variant
//!
//! `Supercow` is extremely flexible as to how it internally stores and manages
//! data. There are four variants provided by default: `Supercow`,
//! `NonSyncSupercow`, `InlineSupercow`, and `InlineNonSyncSupercow`. Here is a
//! quick reference on the trade-offs:
//!
//! | Variant           | Send+Sync?    | `Rc`? | Size  | Init  | Deref      |
//! |-------------------|---------------|-------|-------|-------|------------|
//! | (Default)         | Yes           | No    | Small | Slow  | Very Fast  |
//! | `NonSync`         | No            | Yes   | Small | Slow  | Very Fast  |
//! | `Inline`          | Yes           | No    | Big   | Fast  | Fast       |
//! | `InlineNonSync`   | No            | Yes   | Big   | Fast  | Fast       |
//!
//! "Init" above specifically refers to initialisation with an owned value or
//! shared reference. Supercows constructed with mundane references always
//! construct extremely quickly.
//!
//! The only difference between the `NonSync` variant and the default is that
//! the default is to require the shared pointer type (eg, `Arc`) to be `Send`
//! and `Sync` (which thus prohibits using `Rc`), whereas `NonSync` does not
//! and so allows `Rc`.
//!
//! By default, `Supercow` boxes any owned value or shared reference. This
//! makes the `Deref` implementation faster since it does not need to account
//! for internal pointers, but more importantly, means that the `Supercow` does
//! not need to reserve space for the owned and shared values, so the default
//! `Supercow` is only one pointer wider than a bare reference. (Note that if
//! you are looking to eliminate allocation entirely, you will also need to
//! tinker with the `SHARED` type, which by default has its own `Box` as well.)
//!
//! The obvious problem with boxing values is that it makes construction of the
//! `Supercow` slower, as one must pay for an allocation. If you want to avoid
//! the allocation, you can use the `Inline` variants instead, which store the
//! values inline inside the `Supercow`. Note that this of course makes the
//! `Supercow` much bigger; be particularly careful if you create a hierarchy
//! of things containing `InlineSupercow`s referencing each other, as each
//! would effectively have space for the entire tree above it inline.
//!
//! The default to box values was chosen on the grounds that it is generally
//! easier to use, less likely to cause confusing problems, and in many cases
//! the allocation doesn't affect performance:
//!
//! - In either choice, creating a `Supercow` with a borrowed reference incurs
//! no allocation. The boxed option will actually be slightly faster since it
//! does not need to initialise as much memory and results in better locality
//! due to being smaller.
//!
//! - The value contained usually is reasonably expensive to construct anyway,
//! or else there would be less incentive to pass it around as a reference when
//! possible. In these cases, the extra allocation likely is a minor impact on
//! performance.
//!
//! - Overuse of boxed values results in a "uniform slowness" that can be
//! identified reasonably easily, and results in a linear performance
//! degradation relative to overuse. Overuse of `InlineSupercow`s at best
//! results in linear memory bloat, but if `InlineSupercow`s reference
//! structures containing other `InlineSupercow`s, the result can even be
//! exponential bloat to the structures. At best, this is a harder problem to
//! track down; at worst, it can result in entirely non-obvious stack
//! overflows.
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
//!     let table = Table::new(db.clone());
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
//! The default is `Box<DefaultFeatures<'static>>`, which is a boxed trait
//! object describing the features a shared reference type must have while
//! allowing any such reference to be used without needing a generic type
//! argument.
//!
//! An alternate feature set can be found in `NonSyncFeatures`, which is also
//! usable through the `NonSyncSupercow` typedef (which also makes it
//! `'static`). You can create custom feature traits in this style with
//! `supercow_features!`.
//!
//! It is perfectly legal to use a non-`'static` shared reference type. In
//! fact, the original design for `Supercow<'a>` used `DefaultFeatures<'a>`.
//! However, a non-`'static` lifetime makes the system harder to use, and if
//! entangled with `'a` on `Supercow`, makes the structure lifetime-invariant,
//! which makes it much harder to treat as a reference.
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
//! # Conversions
//!
//! To facilitate client API designs, `Supercow` converts (via `From`/`Into`)
//! from a number of things. Unfortunately, due to trait coherence rules, this
//! does not yet apply in all cases where one might hope. The currently
//! available conversions are:
//!
//! - The `OWNED` type into an owned `Supercow`. This applies without
//! restriction.
//!
//! - A reference to the `OWNED` type. References to a different `BORROWED`
//! type are currently not convertable; `Supercow::borrowed()` will be needed
//! to construct the `Supercow` explicitly.
//!
//! - `Rc<OWNED>` and `Arc<OWNED>` for `Supercow`s where `OWNED` and `BORROWED`
//! are the exact same type, and where the `Rc` or `Arc` can be converted into
//! `SHARED` via `supercow::aux::SharedFrom`. If `OWNED` and `BORROWED` are
//! different types, `Supercow::shared()` will be needed to construct the
//! `Supercow` explicitly.
//!
//! # Storage Type
//!
//! When in owned or shared mode, a `Supercow` needs someplace to store the
//! `OWNED` or `SHARED` value itself. This can be customised with the fourth
//! type parameter and the `OwnedStorage` trait. Two strategies are provided by
//! this crate:
//!
//! - `BoxedStorage` puts everything behind `Box`es. This has the advantage
//! that the `Supercow` structure is only one pointer wider than a basic
//! reference, and results in a faster `Deref`. The obvious drawback is that
//! you pay for allocations on construction. This is the default with
//! `Supercow` and `NonSyncSupercow`.
//!
//! - `InlineStorage` uses an `enum` to store the values inline in the
//! `Supercow`, thus incurring no allocation, but making the `Supercow` itself
//! bigger. This is easily available via the `InlineSupercow` and
//! `InlineNonSyncSupercow` types.
//!
//! If you find some need, you can define custom storage types, though note
//! that the trait is quite unsafe and somewhat subtle.
//!
//! # Advanced
//!
//! ## Variance
//!
//! `Supercow` is covariant on its lifetime and all its type parameters, except
//! for `SHARED` which is invariant. The default `SHARED` type for both
//! `Supercow` and `NonSyncSupercow` uses the `'static` lifetime, so simple
//! `Supercow`s are in general covariant.
//!
//! ```
//! use std::rc::Rc;
//!
//! use supercow::Supercow;
//!
//! fn assert_covariance<'a, 'b: 'a>(
//!   imm: Supercow<'b, u32>,
//!   bor: &'b Supercow<'b, u32>)
//! {
//!   let _imm_a: Supercow<'a, u32> = imm;
//!   let _bor_aa: &'a Supercow<'a, u32> = bor;
//!   let _bor_ab: &'a Supercow<'b, u32> = bor;
//!   // Invalid, since the external `&'b` reference is declared to live longer
//!   // than the internal `&'a` reference.
//!   // let _bor_ba: &'b Supercow<'a, u32> = bor;
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
//! Constructing any kind of `Supercow` with a normal reference is very fast,
//! only requiring a bit of internal memory initialisation besides setting the
//! reference itself.
//!
//! The defual `Supercow` type boxes the owned type and double-boxes the shared
//! type. This obviously dominates construction cost in those cases.
//!
//! `InlineSupercow` eliminates one box layer. This means that constructing an
//! owned instance is simply a move of the owned structure plus the common
//! reference initialisation. Shared values still by default require one boxing
//! level as well as virtual dispatch on certain operations; as described
//! above, this property too can be dealt with by using a custom `SHARED` type.
//!
//! ## Destruction Cost
//!
//! Destroying a `Supercow` is roughly the same proportional cost of creating
//! it.
//!
//! ## `Deref` Cost
//!
//! For the default `Supercow` type, the `Deref` is exactly equivalent to
//! dereferencing an `&&BORROWED`.
//!
//! For `InlineSupercow`, the implementation is a bit slower, comparable to
//! `std::borrow::Cow`.
//!
//! In all cases, the `Deref` implementation is not dependent on the ownership
//! mode of the `Supercow`, and so is not affected by the shared reference
//! type, most importantly, making no virtual function calls even under the
//! default boxed shared reference type. However, the way it works colud
//! prevent LLVM optimisations from applying in particular circumstances.
//!
//! For those wanting specifics, the function
//!
//! ```ignore
//! // Substitute Cow with InlineSupercow for the other case.
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
//!  lea    rcx,[rdi+0x4]               xor    eax,eax
//!  cmovne rcx,QWORD PTR [rdi+0x8]     cmp    rcx,0x800
//!  cmp    DWORD PTR [rsi],0x1         cmovae rdi,rax
//!  lea    rax,[rsi+0x4]               mov    rdx,QWORD PTR [rsi]
//!  cmovne rax,QWORD PTR [rsi+0x8]     cmp    rdx,0x800
//!  mov    eax,DWORD PTR [rax]         cmovb  rax,rsi
//!  add    eax,DWORD PTR [rcx]         mov    eax,DWORD PTR [rax+rdx]
//!  ret                                add    eax,DWORD PTR [rdi+rcx]
//!                                     ret
//! ```
//!
//! The same code on ARM v7l and Rust 1.12.1:
//!
//! TODO UPDATE
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
//! If the default `Supercow` is used above instead of `InlineSupercow`, the
//! function actually compiles to the same thing as one taking two `&u32`
//! arguments. (This is partially due to optimisations eliminating one level of
//! indirection; if the optimiser did not do as much, it would be equivalent to
//! taking two `&&u32` arguments.)
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
//! The default `Supercow` is only one pointer wider than a mundane reference.
//!
//! ```
//! use std::mem;
//!
//! use supercow::Supercow;
//!
//! assert_eq!(mem::size_of::<&'static u32>() + mem::size_of::<*const ()>(),
//!            mem::size_of::<Supercow<'static, u32>>());
//!
//! assert_eq!(mem::size_of::<&'static str>() + mem::size_of::<*const ()>(),
//!            mem::size_of::<Supercow<'static, String, str>>());
//! ```
//!
//! Of course, you also pay for heap space in this case when using owned or
//! shared `Supercow`s.
//!
//! `InlineSupercow` can be quite large in comparison to a normal reference.
//! You need to be particularly careful that structures you reference don't
//! themselves contain `InlineSupercow`s or you can end up with
//! quadratically-sized or even exponentially-sized structures.
//!
//! ```
//! use std::mem;
//!
//! use supercow::InlineSupercow;
//!
//! // Define our structures
//! // (The extra lifetimes are needed for intra-function lifetime inference to
//! // succeed.)
//! struct Big([u8;1024]);
//! struct A<'a>(InlineSupercow<'a, Big>);
//! struct B<'b,'a:'b>(InlineSupercow<'b, A<'a>>);
//! struct C<'b,'a:'b>(InlineSupercow<'b, B<'a,'a>>);
//!
//! // Now say an API consumer, etc, decides to use references
//! let big = Big([0u8;1024]);
//! let a = A((&big).into());
//! let b = B((&a).into());
//! let c = C((&b).into());
//!
//! // Well, we've now allocated space for four `Big`s on the stack, despite
//! // only really needing one.
//! assert!(mem::size_of_val(&big) + mem::size_of_val(&a) +
//!         mem::size_of_val(&b) + mem::size_of_val(&c) >
//!         4 * mem::size_of::<Big>());
//! ```
//!
//! # Other Notes
//!
//! Using `Supercow` will not give your application `apt-get`-style Super Cow
//! Powers.

pub mod ext;

use std::borrow::Borrow;
use std::cmp;
use std::convert::AsRef;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem;
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::rc::Rc;
use std::sync::Arc;

use self::ext::*;

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
        pub trait $feature_name<'a>: $($req +)* $crate::ext::ConstDeref + 'a {
            /// Clone this value, and then immediately put it into a `Box`
            /// behind a trait object of this trait.
            fn clone_boxed
                (&self)
                 -> Box<$feature_name<'a, Target = Self::Target> + 'a>;
        }
        impl<'a, T : 'a + $($req +)* Clone + $crate::ext::ConstDeref>
        $feature_name<'a> for T {
            fn clone_boxed
                (&self)
                 -> Box<$feature_name<'a, Target = Self::Target> + 'a>
            {
                let cloned: T = self.clone();
                Box::new(cloned)
            }
        }
        impl<'a, T : $feature_name<'a>> $crate::ext::SharedFrom<T>
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
        pub trait $feature_name<'a>: $($req +)* $crate::ext::ConstDeref + 'a {
        }
        impl<'a, T : 'a + $($req +)* $crate::ext::ConstDeref>
        $feature_name<'a> for T {
        }
        impl<'a, T : $feature_name<'a>> $crate::ext::SharedFrom<T>
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
/// Note that the `SHARED` type must have `'static` lifetime, since this is
/// generally more convenient and makes the `Supercow` as a whole covariant.
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
             Box<NonSyncFeatures<'static, Target = BORROWED> + 'static>,
             BoxedStorage>;

/// `Supercow` with the default `STORAGE` changed to `InlineStorage`.
///
/// This reduces the number of allocations needed to construct an owned or
/// shared `Superow` (down to zero for owned, but note that the default
/// `SHARED` still has its own `Box`) at the cost of bloating the `Supercow`
/// itself, as it now needs to be able to fit a whole `OWNED` instance.
pub type InlineSupercow<'a, OWNED, BORROWED = OWNED,
                       SHARED = Box<DefaultFeatures<
                           'static, Target = BORROWED> + 'static>> =
    Supercow<'a, OWNED, BORROWED, SHARED, InlineStorage<OWNED, SHARED>>;

/// `NonSyncSupercow` with the `STORAGE` changed to `InlineStorage`.
///
/// This combines both properties of `NonSyncSupercow` and `InlineSupercow`.
pub type InlineNonSyncSupercow<'a, OWNED, BORROWED = OWNED> =
    Supercow<'a, OWNED, BORROWED,
             Box<NonSyncFeatures<'static, Target = BORROWED> + 'static>,
             InlineStorage<OWNED, Box<
                 NonSyncFeatures<'static, Target = BORROWED> + 'static>>>;

/// The actual generic reference type.
///
/// See the module documentation for most of the details.
///
/// The generics here may look somewhat frightening at first; try not to be too
/// alarmed, and remember that in most use-cases all you need to worry about is
/// the stuff concerning `OWNED`.
pub struct Supercow<'a, OWNED, BORROWED : ?Sized = OWNED,
                    SHARED = Box<DefaultFeatures<
                        'static, Target = BORROWED> + 'static>,
                    STORAGE = BoxedStorage>
where BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      STORAGE : OwnedStorage<OWNED, SHARED> {
    // This stores the precalculated `Deref` target, and is the only thing the
    // `Deref` implementation needs to inspect.
    //
    // Note that there are three cases with references:
    //
    // - A reference to an external value. In this case, we know that the
    // reference will not be invalidated by movement or for the lifetime of
    // `'a` and simply store the reference here as an absolute address.
    //
    // - A reference to a ZST at an "external" location, often address 1. We
    // don't need to handle this in any particular manner as long as we don't
    // accidentally make a null reference, since the only thing safe rust can
    // do with a ZST reference is inspect its address, and if we do "move" it
    // around, there's nothing unsafe from this fact being leaked.
    //
    // - A reference into this `Supercow`. In this case, the absolute address
    // will change whenever this `Supercow` is relocated. To handle this, we
    // instead store the offset from `&self` here, and adjust it at `Deref`
    // time. We differentiate between the two cases by inspecting the absolute
    // value of the address: If it is less than
    // `MAX_INTERNAL_BORROW_DISPLACEMENT*2`, we assume it is an internal
    // reference, since no modern system ever has virtual memory mapped between
    // 0 and 4kB (and any code elsewhere involving this region is presumably
    // too low-level to be using `Supercow`).
    //
    // One pecularity is that this is declared as a reference even though it
    // does not necessarily reference anything. This is so that it works with
    // DSTs, which have references larger than pointers. We assume the first
    // pointer-sized value is the actual address (see `PointerFirstRef`).
    //
    // We do need to take care that we still don't create a null reference
    // here; there is code to check for Rust putting the internal storage first
    // in the struct and adding 1 if this happens.
    //
    // If `STORAGE` does not use internal pointers, we can skip all the
    // arithmetic and return this value unmodified.
    ptr: &'a BORROWED,
    // The current ownership mode of this `Supercow`.
    //
    // This has three states:
    //
    // - Null. The `Supercow` holds a `&'a BORROWED`.
    //
    // - Even alignment. The `Supercow` holds an `OWNED` accessible via
    // `STORAGE`, and this value is what is passed into the `STORAGE` methods.
    //
    // - Odd alignment. The `Supercow` holds a `SHARED`, behind a `Box` at the
    // address one less than this value. Note that since the default `SHARED`
    // is a `Box<DefaultFeatures>`, we actually end up with two levels of
    // boxing here. This is actually necessary so that the whole thing only
    // takes one immediate pointer.
    mode: *mut (),
    storage: STORAGE,

    _owned: PhantomData<OWNED>,
    _shared: PhantomData<Box<SHARED>>,
}

enum SupercowMode {
    Owned(*mut ()),
    Borrowed,
    Shared(*mut ()),
}

use self::SupercowMode::*;

macro_rules! defimpl {
    ($(@$us:tt)* [$($tparm:ident $(: ?$tparmsized:ident)*),*] ($($spec:tt)*)
     where { $($wo:tt)* } $body:tt) => {
        $($us)* impl<'a, $($tparm $(: ?$tparmsized)*,)* OWNED,
             BORROWED : ?Sized, SHARED, STORAGE>
            $($spec)* Supercow<'a, OWNED, BORROWED, SHARED, STORAGE>
        where BORROWED : 'a,
              &'a BORROWED : PointerFirstRef,
              STORAGE : OwnedStorage<OWNED, SHARED>,
              $($wo)*
            $body
    }
}

defimpl! {[] (Drop for) where { } {
    fn drop(&mut self) {
        match self.mode() {
            Owned(ptr) => unsafe { self.storage.deallocate_a(ptr) },
            Shared(ptr) => unsafe { self.storage.deallocate_b(ptr) },
            Borrowed => (),
        }
    }
} }

defimpl! {@unsafe [] (Send for) where {
    OWNED : Send,
    SHARED : Send,
    STORAGE : Send,
} { } }

defimpl! {@unsafe [] (Sync for) where {
    OWNED : Sync,
    SHARED : Sync,
    STORAGE : Sync,
} { } }

defimpl! {[] () where { } {
    /// Creates a new `Supercow` which owns the given value.
    ///
    /// This can create a `Supercow` with a `'static` lifetime.
    pub fn owned(inner: OWNED) -> Self
    where OWNED : SafeBorrow<BORROWED> {
        let mut this = unsafe { Self::empty() };
        this.mode = this.storage.allocate_a(inner);
        // This line could panic, but `this` doesn't have anything that would
        // run destructors at this point other than `storage`, which was
        // initialised in an ordinary way.
        unsafe { this.borrow_owned(); }
        this
    }

    /// Creates a new `Supercow` which borrows the given value.
    pub fn borrowed<T : Borrow<BORROWED> + ?Sized>(inner: &'a T) -> Self {
        let mut this = unsafe { Self::empty() };
        this.ptr = inner.borrow();
        this
    }

    /// Creates a new `Supercow` using the given shared reference.
    ///
    /// The reference must be convertable to `SHARED` via `SharedFrom`.
    pub fn shared<T>(inner: T) -> Self
    where SHARED : SharedFrom<T> + ConstDeref<Target = BORROWED> {
        Self::shared_nocvt(SHARED::shared_from(inner))
    }

    fn shared_nocvt(shared: SHARED) -> Self
    where SHARED : ConstDeref<Target = BORROWED> {
        let mut this = unsafe { Self::empty() };
        this.ptr = unsafe {
            &*(shared.const_deref() as *const BORROWED)
        };

        let nominal_mode = this.storage.allocate_b(shared);
        this.mode = (1usize | (nominal_mode as usize)) as *mut ();
        this
    }

    /// If `this` is non-owned, clone `this` and return it.
    ///
    /// Otherwise, return `None`.
    ///
    /// ## Example
    ///
    /// ```
    /// use supercow::Supercow;
    ///
    /// struct SomeNonCloneThing;
    ///
    /// let owned: Supercow<SomeNonCloneThing> = SomeNonCloneThing.into();
    /// assert!(Supercow::clone_non_owned(&owned).is_none());
    ///
    /// let the_thing = SomeNonCloneThing;
    /// let borrowed: Supercow<SomeNonCloneThing> = (&the_thing).into();
    /// let also_borrowed = Supercow::clone_non_owned(&borrowed).unwrap();
    /// ```
    pub fn clone_non_owned(this: &Self) -> Option<Self>
    where SHARED : Clone + ConstDeref<Target = BORROWED> {
        match this.mode() {
            Owned(_) => None,

            Borrowed => Some(Supercow {
                ptr: this.ptr,
                mode: this.mode,
                storage: Default::default(),
                _owned: PhantomData,
                _shared: PhantomData,
            }),

            Shared(s) => Some(Self::shared_nocvt(unsafe {
                this.storage.get_ptr_b(s)
            }.clone())),
        }
    }

    /// If `this` is borrowed, return the underlying reference with the
    /// original lifetime. Otherwise, return `None`.
    ///
    /// The returned reference has a lifetime independent of `this`.
    ///
    /// This can be used to bridge between `Supercow` APIs and mundane
    /// reference APIs without needing to restrict the lifetime to the
    /// `Supercow`, but as a result is only available if the contained
    /// reference is actually independent.
    ///
    /// ## Example
    ///
    /// ```
    /// use std::sync::Arc;
    ///
    /// use supercow::Supercow;
    ///
    /// let fourty_two: u32 = 42;
    ///
    /// let borrowed: Supercow<u32> = (&fourty_two).into();
    /// assert_eq!(Some(&fourty_two), Supercow::extract_ref(&borrowed));
    ///
    /// let owned: Supercow<u32> = fourty_two.into();
    /// assert_eq!(None, Supercow::extract_ref(&owned));
    ///
    /// let shared: Supercow<u32> = Arc::new(fourty_two).into();
    /// assert_eq!(None, Supercow::extract_ref(&shared));
    /// ```
    pub fn extract_ref(this: &Self) -> Option<&'a BORROWED> {
        match this.mode() {
            Borrowed => Some(this.ptr),
            _ => None,
        }
    }

    /// Takes ownership of the underling value if needed, then returns it,
    /// consuming `self`.
    pub fn into_inner(mut this: Self) -> OWNED
    where OWNED : Borrow<BORROWED>,
          BORROWED : ToOwned<Owned = OWNED> {
        match this.mode() {
            Owned(ptr) => {
                unsafe { this.storage.deallocate_into_a(ptr) }
            },
            _ => (*this).to_owned(),
        }
    }

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
    pub fn to_mut<'b>
        (&'b mut self)
         -> Ref<'a, 'b, OWNED, BORROWED, SHARED, STORAGE>
    where OWNED : SafeBorrow<BORROWED>,
          BORROWED : ToOwned<Owned = OWNED>,
    {
        // Become owned if not already.
        match self.mode() {
            Owned(_) => (),
            _ => *self = Self::owned((*self).to_owned()),
        }

        // Clear out `ptr` if it points somewhere unstable
        self.ptr = OWNED::borrow_replacement(self.ptr);

        Ref {
            r: unsafe { self.storage.get_mut_a(self.mode) } as *mut OWNED,
            parent: self,
        }
    }

    unsafe fn borrow_owned(&mut self)
    where OWNED : SafeBorrow<BORROWED> {
        // There's no safe way to propagate `borrowed_ptr` into
        // `ptr` since the former has a borrow scoped to this
        // function.
        {
            let borrowed_ptr = self.storage.get_ptr_a(self.mode).borrow();
            self.ptr = &*(borrowed_ptr as *const BORROWED);
        }

        // Adjust the pointer if needed
        if STORAGE::is_internal_storage() {
            let self_start = self as *mut Self as usize;
            let self_end = self_start + mem::size_of::<Self>();
            let bias = self.relative_pointer_bias();

            let ptr_address: &mut usize = mem::transmute(&mut self.ptr);

            if *ptr_address >= self_start && *ptr_address < self_end {
                debug_assert!(*ptr_address - self_start <
                              MAX_INTERNAL_BORROW_DISPLACEMENT * 3/2,
                              "Borrowed pointer displaced too far from \
                               base address (supercow at {:x}, self at {:x}, \
                               borrowed to {:x}", self_start,
                              &self.storage as *const STORAGE as usize,
                              *ptr_address);

                *ptr_address -= self_start - bias;
            }
        }
    }

    unsafe fn empty() -> Self {
        Supercow {
            ptr: mem::uninitialized(),
            mode: ptr::null_mut(),
            storage: Default::default(),
            _owned: PhantomData,
            _shared: PhantomData,
        }
    }

    fn mode(&self) -> SupercowMode {
        if self.mode.is_null() {
            Borrowed
        } else if 0 == (self.mode as usize & 1) {
            Owned(self.mode)
        } else {
            Shared((self.mode as usize & !1usize) as *mut ())
        }
    }

    /// Returns the bias to use for relative pointers to avoid creating null
    /// references.
    ///
    /// If rust lays this structure out such that `storage_address` is at the
    /// base of `self`, returns 1. Otherwise, no bias is needed and it returns
    /// 0.
    #[inline(always)]
    fn relative_pointer_bias(&self) -> usize {
        let self_address = self as *const Self as usize;
        let storage_address = &self.storage as *const STORAGE as usize;
        if self_address == storage_address {
            1
        } else {
            0
        }
    }
} }

// Separate `impl` as rustc doesn't seem to like having multiple `&'x Type`
// constraints in one place.
impl<'a, OWNED, BORROWED : ?Sized, SHARED, STORAGE>
Supercow<'a, OWNED, BORROWED, SHARED, STORAGE>
where OWNED : SafeBorrow<BORROWED>,
      BORROWED : 'a + ToOwned<Owned = OWNED>,
      for<'l> &'l BORROWED : PointerFirstRef,
      SHARED : ConstDeref<Target = BORROWED>,
      STORAGE : OwnedStorage<OWNED, SHARED> {
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
        (mut this: Self) -> Supercow<'static, OWNED, BORROWED, NS, STORAGE>
    where STORAGE : OwnedStorage<OWNED, NS> {
        let static_ptr: &'static BORROWED =
            unsafe { &*(this.ptr as *const BORROWED) };

        match this.mode() {
            Owned(_) => Supercow {
                ptr: static_ptr,
                mode: this.mode,
                storage: mem::replace(&mut this.storage, Default::default()),
                _owned: PhantomData,
                _shared: PhantomData,
            },

            _ => Supercow::owned((*this).to_owned()),
        }
    }
}

/// Provides mutable access to an owned value within a `Supercow`.
///
/// This is similar to the `Ref` used with `RefCell`.
pub struct Ref<'a, 'b, OWNED, BORROWED : ?Sized, SHARED, STORAGE>
where 'a: 'b,
      OWNED : SafeBorrow<BORROWED> + 'b,
      BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : 'b,
      STORAGE : OwnedStorage<OWNED, SHARED> + 'b {
    r: *mut OWNED,
    parent: &'b mut Supercow<'a, OWNED, BORROWED, SHARED, STORAGE>,
}


impl<'a, 'b, OWNED, BORROWED : ?Sized, SHARED, STORAGE> Deref
for Ref<'a, 'b, OWNED, BORROWED, SHARED, STORAGE>
where 'a: 'b,
      OWNED : SafeBorrow<BORROWED> + 'b,
      BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : 'b,
      STORAGE : OwnedStorage<OWNED, SHARED> + 'b {
    type Target = OWNED;

    #[inline]
    fn deref(&self) -> &OWNED {
        unsafe { &*self.r }
    }
}

impl<'a, 'b, OWNED, BORROWED : ?Sized, SHARED, STORAGE> DerefMut
for Ref<'a, 'b, OWNED, BORROWED, SHARED, STORAGE>
where 'a: 'b,
      OWNED : SafeBorrow<BORROWED> + 'b,
      BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : 'b,
      STORAGE : OwnedStorage<OWNED, SHARED> + 'b {
    #[inline]
    fn deref_mut(&mut self) -> &mut OWNED {
        unsafe { &mut*self.r }
    }
}

impl<'a, 'b, OWNED, BORROWED : ?Sized, SHARED, STORAGE> Drop
for Ref<'a, 'b, OWNED, BORROWED, SHARED, STORAGE>
where 'a: 'b,
      OWNED : SafeBorrow<BORROWED> + 'b,
      BORROWED : 'a,
      &'a BORROWED : PointerFirstRef,
      SHARED : 'b,
      STORAGE : OwnedStorage<OWNED, SHARED> + 'b {
    #[inline]
    fn drop(&mut self) {
        // The value of `OWNED::borrow()` may have changed, so recompute
        // everything instead of backing the old values up.
        unsafe { self.parent.borrow_owned() }
    }
}

defimpl! {[] (Deref for) where { } {
    type Target = BORROWED;
    #[inline]
    fn deref(&self) -> &BORROWED {
        let self_address = self as *const Self as usize;

        let mut target_ref = self.ptr;
        unsafe {
            let target_address: &mut usize = mem::transmute(&mut target_ref);
            let nominal_address = *target_address;
            if STORAGE::is_internal_storage() &&
                nominal_address < MAX_INTERNAL_BORROW_DISPLACEMENT
            {
                *target_address = nominal_address + self_address -
                    self.relative_pointer_bias();
            }
        }
        target_ref
    }
} }

defimpl! {[] (Borrow<BORROWED> for) where { } {
    fn borrow(&self) -> &BORROWED {
        self.deref()
    }
} }

defimpl! {[] (AsRef<BORROWED> for) where { } {
    fn as_ref(&self) -> &BORROWED {
        self.deref()
    }
} }

defimpl! {[] (Clone for) where {
    OWNED : Clone + SafeBorrow<BORROWED>,
    SHARED : Clone + ConstDeref<Target = BORROWED>,
} {
    fn clone(&self) -> Self {
        match self.mode() {
            Owned(ptr) => Self::owned(unsafe {
                self.storage.get_ptr_a(ptr)
            }.clone()),

            Borrowed => Supercow {
                ptr: self.ptr,
                mode: self.mode,
                storage: Default::default(),
                _owned: PhantomData,
                _shared: PhantomData,
            },

            Shared(s) => Self::shared_nocvt(unsafe {
                self.storage.get_ptr_b(s)
            }.clone()),
        }
    }
} }

defimpl! {[] (From<OWNED> for) where {
    OWNED : SafeBorrow<BORROWED>,
} {
    fn from(inner: OWNED) -> Self {
        Self::owned(inner)
    }
} }

// For now, we can't accept `&BORROWED` because it's theoretically possible for
// someone to make `<BORROWED as ToOwned>::Owned = &BORROWED`, in which case
// the `OWNED` version above would apply.
//
// Maybe once specialisation lands in stable, we can make `From` do what we
// want everywhere.
defimpl! {[] (From<&'a OWNED> for) where {
    // Does not need to be `SafeBorrow` since it's not embedded inside us.
    OWNED : Borrow<BORROWED>,
} {
    fn from(inner: &'a OWNED) -> Self {
        Self::borrowed(inner.borrow())
    }
} }

// Similarly, we can't support arbitrary types here, and need to require
// `BORROWED == OWNED` for `Rc` and `Arc`. Ideally, we'd support anything that
// coerces into `SHARED`. Again, maybe one day after specialisation..
impl<'a, OWNED, SHARED, STORAGE> From<Rc<OWNED>>
for Supercow<'a, OWNED, OWNED, SHARED, STORAGE>
where SHARED : ConstDeref<Target = OWNED> + SharedFrom<Rc<OWNED>>,
      STORAGE : OwnedStorage<OWNED, SHARED>,
      OWNED : 'a,
      &'a OWNED : PointerFirstRef {
    fn from(rc: Rc<OWNED>) -> Self {
        Self::shared(rc)
    }
}
impl<'a, OWNED, SHARED, STORAGE> From<Arc<OWNED>>
for Supercow<'a, OWNED, OWNED, SHARED, STORAGE>
where SHARED : ConstDeref<Target = OWNED> + SharedFrom<Arc<OWNED>>,
      STORAGE : OwnedStorage<OWNED, SHARED>,
      OWNED : 'a,
      &'a OWNED : PointerFirstRef {
    fn from(rc: Arc<OWNED>) -> Self {
        Self::shared(rc)
    }
}

macro_rules! deleg_fmt { ($tr:ident) => {
    defimpl! {[] (fmt::$tr for) where {
        BORROWED : fmt::$tr
    } {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            (**self).fmt(f)
        }
    } }
} }

deleg_fmt!(Binary);
deleg_fmt!(Debug);
deleg_fmt!(Display);
deleg_fmt!(LowerExp);
deleg_fmt!(LowerHex);
deleg_fmt!(Octal);
deleg_fmt!(Pointer);
deleg_fmt!(UpperExp);
deleg_fmt!(UpperHex);

defimpl! {[T] (cmp::PartialEq<T> for) where {
    T : Borrow<BORROWED>,
    BORROWED : PartialEq<BORROWED>,
} {
    fn eq(&self, other: &T) -> bool {
        **self == *other.borrow()
    }

    fn ne(&self, other: &T) -> bool {
        **self != *other.borrow()
    }
} }

defimpl! {[] (cmp::Eq for) where {
    BORROWED : Eq
} { } }

defimpl! {[T] (cmp::PartialOrd<T> for) where {
    T : Borrow<BORROWED>,
    BORROWED : cmp::PartialOrd<BORROWED>,
} {
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
} }

defimpl! {[] (cmp::Ord for) where {
    BORROWED : cmp::Ord
} {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        (**self).cmp(other)
    }
} }

defimpl! {[] (Hash for) where {
    BORROWED : Hash
} {
    fn hash<H : Hasher>(&self, h: &mut H) {
        (**self).hash(h)
    }
} }

#[cfg(test)]
mod misc_tests {
    use std::borrow::Cow;

    use super::*;

    // This is where the asm in the Performance Notes section comes from.
    #[inline(never)]
    fn add_two_cow(a: &Cow<u32>, b: &Cow<u32>) -> u32 {
        **a + **b
    }

    #[inline(never)]
    fn add_two_supercow(a: &InlineSupercow<u32>,
                        b: &InlineSupercow<u32>) -> u32 {
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

macro_rules! tests { ($modname:ident, $stype:ident) => {
#[cfg(test)]
mod $modname {
    use std::sync::Arc;

    use super::*;

    #[test]
    fn ref_to_owned() {
        let x = 42u32;
        let a: $stype<u32> = Supercow::borrowed(&x);
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
        let a: $stype<String, str> = Supercow::borrowed("hello");
        let b: $stype<String, str> = Supercow::owned("hello".to_owned());
        assert_eq!(a, b);

        let mut c = a.clone();
        c.to_mut().push_str(" world");
        assert_eq!(a, b);
        assert_eq!(c, "hello world");
    }

    #[test]
    fn default_accepts_arc() {
        let x: $stype<u32> = Supercow::shared(Arc::new(42u32));
        assert_eq!(42, *x);
    }

    #[test]
    fn ref_safe_even_if_forgotten() {
        let mut x: $stype<String, str> = Supercow::owned("foo".to_owned());
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
        use std::convert::AsRef;
        use std::cmp::*;
        use std::hash::*;

        macro_rules! test_fmt {
            ($fmt:expr, $x:expr) => {
                assert_eq!(format!($fmt, 42u32), format!($fmt, $x));
            }
        }

        let x: $stype<u32> = Supercow::owned(42u32);
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

        let mut expected_hash = SipHasher::new();
        42u32.hash(&mut expected_hash);
        let mut actual_hash = SipHasher::new();
        x.hash(&mut actual_hash);
        assert_eq!(expected_hash.finish(), actual_hash.finish());

        assert_eq!(42u32, *x.borrow());
        assert_eq!(42u32, *x.as_ref());
    }

    #[test]
    fn owned_mode_survives_moving() {
        // Using a `HashMap` here because it means the optimiser can't reason
        // about which one will eventually be chosen, and so one of the values
        // is guaranteed to eventually be moved off the heap onto the stack.
        #[inline(never)]
        fn pick_one() -> $stype<'static, String> {
            use std::collections::HashMap;

            let mut hm = HashMap::new();
            hm.insert("hello", Supercow::owned("hello".to_owned()));
            hm.insert("world", Supercow::owned("world".to_owned()));
            hm.into_iter().map(|(_, v)| v).next().unwrap()
        }

        let s = pick_one();
        assert!("hello".to_owned() == *s ||
                "world".to_owned() == *s);
    }

    #[test]
    fn dst_string_str() {
        let mut s: $stype<'static, String, str> = String::new().into();
        let mut expected = String::new();
        for i in 0..1024 {
            assert_eq!(expected.as_str(), &*s);
            expected.push_str(&format!("{}", i));
            s.to_mut().push_str(&format!("{}", i));
            assert_eq!(expected.as_str(), &*s);
        }
    }

    #[test]
    fn dst_vec_u8s() {
        let mut s: $stype<'static, Vec<u8>, [u8]> = Vec::new().into();
        let mut expected = Vec::<u8>::new();
        for i in 0..1024 {
            assert_eq!(&expected[..], &*s);
            expected.push((i & 0xFF) as u8);
            s.to_mut().push((i & 0xFF) as u8);
            assert_eq!(&expected[..], &*s);
        }
    }

    #[test]
    fn dst_osstring_osstr() {
        use std::ffi::{OsStr, OsString};

        let mut s: $stype<'static, OsString, OsStr> = OsString::new().into();
        let mut expected = OsString::new();
        for i in 0..1024 {
            assert_eq!(expected.as_os_str(), &*s);
            expected.push(&format!("{}", i));
            s.to_mut().push(&format!("{}", i));
            assert_eq!(expected.as_os_str(), &*s);
        }
    }

    #[test]
    fn dst_cstring_cstr() {
        use std::ffi::{CStr, CString};
        use std::mem;
        use std::ops::Deref;

        let mut s: $stype<'static, CString, CStr> =
            CString::new("").unwrap().into();
        let mut expected = CString::new("").unwrap();
        for i in 0..1024 {
            assert_eq!(expected.deref(), &*s);
            {
                let mut ve = expected.into_bytes_with_nul();
                ve.pop();
                ve.push(((i & 0xFF) | 1) as u8);
                ve.push(0);
                expected = unsafe {
                    CString::from_vec_unchecked(ve)
                };
            }
            {
                let mut m = s.to_mut();
                let mut vs = mem::replace(&mut *m, CString::new("").unwrap())
                    .into_bytes_with_nul();
                vs.pop();
                vs.push(((i & 0xFF) | 1) as u8);
                vs.push(0);
                *m = unsafe {
                    CString::from_vec_unchecked(vs)
                };
            }
            assert_eq!(expected.deref(), &*s);
        }
    }

    #[test]
    fn dst_pathbuf_path() {
        use std::path::{Path, PathBuf};

        let mut s: $stype<'static, PathBuf, Path> = PathBuf::new().into();
        let mut expected = PathBuf::new();
        for i in 0..1024 {
            assert_eq!(expected.as_path(), &*s);
            expected.push(format!("{}", i));
            s.to_mut().push(format!("{}", i));
            assert_eq!(expected.as_path(), &*s);
        }
    }
} } }

tests!(inline_sync_tests, InlineSupercow);
tests!(inline_nonsync_tests, InlineNonSyncSupercow);
tests!(boxed_sync_tests, Supercow);
tests!(boxed_nonsync_tests, NonSyncSupercow);

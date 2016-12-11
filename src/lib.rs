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
//! `Supercow` provides a mechanism for making APIs that accept or return very
//! general references while maintaining very low overhead for usages not
//! involving heavy-weight references (e.g, `Arc`). Though nominally similar to
//! `Cow` in structure (and being named after it), `Supercow` does not require
//! the containee to be `Clone` or `ToOwned` unless operations inherently
//! depending on either are invoked.
//!
//! `Supercow` allows you to
//!
//! - Return values with ownership semantics decided at run-time;
//!
//! - Write APIs that allow client code to manage its resources however it
//! wants;
//!
//! - Perform efficient copy-on-write and data sharing;
//!
//! - Avoid cloning until absolutely necessary, even if the point at which it
//! becomes necessary is determined dynamically.
//!
//! # Quick Start
//!
//! ## Simple Types
//!
//! In many cases, you can think of a `Supercow` as having only one lifetime
//! parameter and one type parameter, corresponding to the lifetime and type of
//! an immutable reference, i.e., `Supercow<'a, Type>` ⇒ `&'a Type`.
//!
//! ```
//! extern crate supercow;
//!
//! use std::sync::Arc;
//! use supercow::Supercow;
//!
//! // This takes a `Supercow`, so it can accept owned, borrowed, or shared
//! // values with the same API. The calls to it are annotated below.
//! //
//! // Normally a function like this would elide the lifetime and/or use an
//! // `Into` conversion, but here it is written out for clarity.
//! fn assert_is_forty_two<'a>(s: Supercow<'a, u32>) {
//!   // `Supercow` can be dereferenced just like a normal reference.
//!   assert_eq!(42, *s);
//! }
//!
//! # fn main() {
//! // Declare some data we want to reference.
//! let forty_two = 42u32;
//! // Make a Supercow referencing the above.
//! let mut a = Supercow::borrowed(&forty_two);
//! // It dereferences to the value of `forty_two`.
//! assert_is_forty_two(a.clone());             // borrowed
//! // And we can see that it actually still *points* to forty_two as well.
//! assert_eq!(&forty_two as *const u32, &*a as *const u32);
//!
//! // Clone `a` so that `b` also points to `forty_two`.
//! let mut b = a.clone();
//! assert_is_forty_two(b.clone());             // borrowed
//! assert_eq!(&forty_two as *const u32, &*b as *const u32);
//!
//! // `to_mut()` can be used to mutate `a` and `b` independently, taking
//! // ownership as needed.
//! *a.to_mut() += 2;
//! // Our immutable variable hasn't been changed...
//! assert_eq!(42, forty_two);
//! // ...but `a` now stores the new value...
//! assert_eq!(44, *a);
//! // ...and `b` still points to the unmodified variable.
//! assert_eq!(42, *b);
//! assert_eq!(&forty_two as *const u32, &*b as *const u32);
//!
//! // And now we modify `b` as well, which as before affects nothing else.
//! *b.to_mut() = 56;
//! assert_eq!(44, *a);
//! assert_eq!(56, *b);
//! assert_eq!(42, forty_two);
//!
//! // We can call `assert_is_forty_two` with an owned value as well.
//! assert_is_forty_two(Supercow::owned(42));   // owned
//!
//! // We can also use `Arc` transparently.
//! let mut c = Supercow::shared(Arc::new(42));
//! assert_is_forty_two(c.clone());             // shared
//! *c.to_mut() += 1;
//! assert_eq!(43, *c);
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
//! ## Choosing the right variant
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
//! the default is to require the shared pointer type (e.g., `Arc`) to be
//! `Send` and `Sync` (which thus prohibits using `Rc`), whereas `NonSync` does
//! not and so allows `Rc`. Note that a side-effect of the default `Send +
//! Sync` requirement is that the type of `BORROWED` also needs to be `Send`
//! and `Sync` when using `Arc` as the shared reference type; if it is not
//! `Send` and `Sync`, use `NonSyncSupercow` instead.
//!
//! By default, `Supercow` boxes any owned value or shared reference. This
//! makes the `Deref` implementation faster since it does not need to account
//! for internal pointers, but more importantly, means that the `Supercow` does
//! not need to reserve space for the owned and shared values, so the default
//! `Supercow` is only one pointer wider than a bare reference.
//!
//! The obvious problem with boxing values is that it makes construction of the
//! `Supercow` slower, as one must pay for an allocation. If you want to avoid
//! the allocation, you can use the `Inline` variants instead, which store the
//! values inline inside the `Supercow`. (Note that if you are looking to
//! eliminate allocation entirely, you will also need to tinker with the
//! `SHARED` type, which by default has its own `Box` as well.) Note that this
//! of course makes the `Supercow` much bigger; be particularly careful if you
//! create a hierarchy of things containing `InlineSupercow`s referencing each
//! other, as each would effectively have space for the entire tree above it
//! inline.
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
//! ```no_run
//! struct Database;
//! impl Database {
//!   fn new() -> Self {
//!     // Computation...
//!     Database
//!   }
//!   fn close(self) -> bool {
//!     // E.g., it returns an error on failure or something
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
//! #     // E.g., it returns an error on failure or something
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
//!     // E.g., it returns an error on failure or something
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
//! type are currently not convertible; `Supercow::borrowed()` will be needed
//! to construct the `Supercow` explicitly.
//!
//! - `Rc<OWNED>` and `Arc<OWNED>` for `Supercow`s where `OWNED` and `BORROWED`
//! are the exact same type, and where the `Rc` or `Arc` can be converted into
//! `SHARED` via `supercow::ext::SharedFrom`. If `OWNED` and `BORROWED` are
//! different types, `Supercow::shared()` will be needed to construct the
//! `Supercow` explicitly.
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
//! ## Shared Reference Type
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
//! Note that you may need to provide an identity `supercow::ext::SharedFrom`
//! implementation if you have a custom reference type.
//!
//! ## Storage Type
//!
//! When in owned or shared mode, a `Supercow` needs someplace to store the
//! `OWNED` or `SHARED` value itself. This can be customised with the fourth
//! type parameter (`STORAGE`), and the `OwnedStorage` trait. Two strategies
//! are provided by this crate:
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
//! ## `PTR` type
//!
//! The `PTR` type is used to consolidate the implementations of `Supercow` and
//! `Phantomcow`; there is likely little, if any, use for ever using anything
//! other than `*const BORROWED` or `()` here.
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
//! The default `Supercow` type boxes the owned type and double-boxes the shared
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
//! `std::borrow::Cow` but with fewer memory accesses..
//!
//! In all cases, the `Deref` implementation is not dependent on the ownership
//! mode of the `Supercow`, and so is not affected by the shared reference
//! type, most importantly, making no virtual function calls even under the
//! default boxed shared reference type. However, the way it works could
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
//! ```text
//!  Cow                                Supercow
//!  push       {fp, lr}                ldr     r2, [r0]
//!  mov        r2, r0                  ldr     r3, [r1]
//!  ldr        r3, [r2, #4]!           cmp     r2, #2048
//!  ldr        ip, [r0]                addcc   r2, r2, r0
//!  mov        r0, r1                  cmp     r3, #2048
//!  ldr        lr, [r0, #4]!           addcc   r3, r3, r1
//!  ldr        r1, [r1]                ldr     r0, [r2]
//!  cmp        ip, #1                  ldr     r1, [r3]
//!  moveq      r3, r2                  add     r0, r1, r0
//!  cmp        r1, #1                  bx      lr
//!  ldr        r2, [r3]
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
//! The default `Supercow` is only one pointer wider than a mundane reference
//! on Rust 1.13.0 and later. Earlier Rust versions have an extra word due to
//! the drop flag.
//!
//! ```
//! use std::mem::size_of;
//!
//! use supercow::Supercow;
//!
//! // Determine the size of the drop flag including alignment padding.
//! // On Rust 0.13.0+, `dflag` will be zero.
//! struct DropFlag(*const ());
//! impl Drop for DropFlag { fn drop(&mut self) { } }
//! let dflag = size_of::<DropFlag>() - size_of::<*const ()>();
//!
//! assert_eq!(size_of::<&'static u32>() + size_of::<*const ()>() + dflag,
//!            size_of::<Supercow<'static, u32>>());
//!
//! assert_eq!(size_of::<&'static str>() + size_of::<*const ()>() + dflag,
//!            size_of::<Supercow<'static, String, str>>());
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
//! struct Big([u8;1024]);
//! struct A<'a>(InlineSupercow<'a, Big>);
//! struct B<'a>(InlineSupercow<'a, A<'a>>);
//! struct C<'a>(InlineSupercow<'a, B<'a>>);
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
///   pub trait FeatureName2: SomeTrait, Clone, AnotherTrait);
///
/// # fn main() { }
/// ```
///
/// ## Semantics
///
/// A public trait named `FeatureName` is defined which extends all the listed
/// traits, minus special cases below.
///
/// If `Clone` is listed, the trait gains a `clone_boxed()` method and
/// `Box<FeatureName>` is `Clone`.
///
/// If `TwoStepShared(SomeType)` is listed, the boxed type will implement
/// `TwoStepShared` for all `OWNED`/`BORROWED` pairs where
/// `SomeType<OWNED,BORROWED>` implements the feature a whole and
/// `OWNED: SafeBorrow<BORROWED>`.
///
/// All types which implement all the listed traits (including special cases)
/// implement `FeatureName`.

// Historical note: Originally, the shared type was required to implement
// `ConstDeref`, and so the shared type was `Box<$feature<Target = BORROWED>>`.
// This mostly worked, but it confused lifetime inference in a number of
// cases, particularly surrounding variance. Because of that, we instead have
// stricter requirements on a number of traits (including making `SharedFrom`
// unsafe) so that we can pull the pointer out of the non-boxed shared
// reference and hold onto it thereon out, thus obviating the need for `SHARED`
// to carry that part of the type information.
#[macro_export]
macro_rules! supercow_features {
    ($(#[$meta:meta])* pub trait $feature_name:ident: $($stuff:tt)*) => {
        supercow_features!(@_ACCUM $(#[$meta])* pub trait $feature_name:
                           [] [] [] $($stuff)*);
    };

    (@_ACCUM $(#[$meta:meta])* pub trait $feature_name:ident:
     $clone:tt $twostep:tt [$($others:tt),*] Clone $($more:tt)*) => {
        supercow_features!(@_ACCUM $(#[$meta])* pub trait $feature_name:
                           [Clone clone_boxed] $twostep [$($others)*]
                           $($more)*);
    };

    (@_ACCUM $(#[$meta:meta])* pub trait $feature_name:ident:
     $clone:tt $twostep:tt [$($others:tt),*]
     TwoStepShared($($inner:tt)*)
     $($more:tt)*) => {
        supercow_features!(@_ACCUM $(#[$meta])* pub trait $feature_name:
                           $clone [$($inner)*] [$($others)*]
                           $($more)*);
    };

    (@_ACCUM $(#[$meta:meta])* pub trait $feature_name:ident:
     $clone:tt $twostep:tt [$($others:tt),*], $($more:tt)*) => {
        supercow_features!(@_ACCUM $(#[$meta])* pub trait $feature_name:
                           $clone $twostep [$($others)*] $($more)*);
    };

    (@_ACCUM $(#[$meta:meta])* pub trait $feature_name:ident:
     $clone:tt $twostep:tt [$($others:ident),*] $other:ident $($more:tt)*) => {
        supercow_features!(@_ACCUM $(#[$meta])* pub trait $feature_name:
                           $clone $twostep [$($others, )* $other]
                           $($more)*);
    };

    (@_ACCUM $(#[$meta:meta])* pub trait $feature_name:ident:
     $clone:tt $twostep:tt [$($others:ident),*]) => {
        supercow_features!(@_DEFINE $(#[$meta])* pub trait $feature_name:
                           $clone $twostep [$($others),*]);
    };

    (@_DEFINE $(#[$meta:meta])*
     pub trait $feature_name:ident:
     [$($clone:ident $clone_boxed:ident)*]
     [$($twostep_inner:ident)*]
     [$($req:ident),*]) => {
        $(#[$meta])*
        pub trait $feature_name<'a>: $($req +)* 'a {
            $(
            /// Clone this value, and then immediately put it into a `Box`
            /// behind a trait object of this trait.
            fn $clone_boxed(&self) -> Box<$feature_name<'a> + 'a>;
            )*

            /// Returns the address of `self`.
            ///
            /// This is used to disassemble trait objects of this trait without
            /// resorting to transmuting or the unstable `TraitObject` type.
            fn self_address_mut(&mut self) -> *mut ();
        }
        impl<'a, T : 'a + $($req +)* $($clone +)* Sized>
        $feature_name<'a> for T {
            $(
            fn $clone_boxed(&self) -> Box<$feature_name<'a> + 'a> {
                let cloned: T = self.clone();
                Box::new(cloned)
            }
            )*

            fn self_address_mut(&mut self) -> *mut () {
                self as *mut Self as *mut ()
            }
        }
        unsafe impl<'a, T : $feature_name<'a>> $crate::ext::SharedFrom<T>
        for Box<$feature_name<'a> + 'a> {
            fn shared_from(t: T) -> Self {
                Box::new(t)
            }
        }
        $(
        impl<'a> $clone for Box<$feature_name<'a> + 'a> {
            fn clone(&self) -> Self {
                $feature_name::clone_boxed(&**self)
            }
        }
        )*
        $(
        impl<'a, S : 'a + ?Sized, T : 'a> $crate::ext::TwoStepShared<T, S>
        for Box<$feature_name<'a> + 'a>
        where T : $crate::ext::SafeBorrow<S>,
              $twostep_inner<T,S> : $feature_name<'a> {
            fn new_two_step() -> Self {
                Box::new(
                    <$twostep_inner<T,S> as $crate::ext::TwoStepShared<T, S>>::
                    new_two_step())
            }

            unsafe fn deref_holder(&mut self) -> &mut Option<T> {
                <$twostep_inner<T,S> as $crate::ext::TwoStepShared<T, S>>::
                deref_holder(
                    &mut* ($feature_name::self_address_mut(&mut **self)
                           as *mut $twostep_inner<T,S>))
            }
        }
        )*
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
    pub trait DefaultFeatures: Clone, TwoStepShared(TwoStepArc), Send, Sync);
supercow_features!(
    /// The shared reference type for `NonSyncSupercow`.
    ///
    /// Unlike `DefaultFeatures`, this only requires the shared reference type
    /// to be `Clone`, thus permitting `Rc`.
    pub trait NonSyncFeatures: Clone, TwoStepShared(TwoStepRc));

/// `Supercow` with the default `SHARED` changed to `NonSyncFeatures`, enabling
/// the use of `Rc` as a shared reference type as well as making it possible to
/// use non-`Send` or non-`Sync` `BORROWED` types easily.
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
             Box<NonSyncFeatures<'static> + 'static>,
             BoxedStorage>;

/// `Supercow` with the default `STORAGE` changed to `InlineStorage`.
///
/// This reduces the number of allocations needed to construct an owned or
/// shared `Supercow` (down to zero for owned, but note that the default
/// `SHARED` still has its own `Box`) at the cost of bloating the `Supercow`
/// itself, as it now needs to be able to fit a whole `OWNED` instance.
pub type InlineSupercow<'a, OWNED, BORROWED = OWNED,
                       SHARED = Box<DefaultFeatures<'static> + 'static>> =
    Supercow<'a, OWNED, BORROWED, SHARED, InlineStorage<OWNED, SHARED>>;

/// `NonSyncSupercow` with the `STORAGE` changed to `InlineStorage`.
///
/// This combines both properties of `NonSyncSupercow` and `InlineSupercow`.
pub type InlineNonSyncSupercow<'a, OWNED, BORROWED = OWNED> =
    Supercow<'a, OWNED, BORROWED,
             Box<NonSyncFeatures<'static> + 'static>,
             InlineStorage<OWNED, Box<NonSyncFeatures<'static> + 'static>>>;

/// The actual generic reference type.
///
/// See the module documentation for most of the details.
///
/// Most of the generics requirements you don't need to pay too much attention
/// to if you aren't making custom `SHARED` or `STORAGE` types, etc. In
/// general:
///
/// - `OWNED` may be constrained to be `Clone` and/or `BORROWED` as `ToOwned`
/// if cloning an inner value is needed.
///
/// - External traits are defined against `BORROWED`.
///
/// - `PTR : PtrRead<BORROWED>` means the operation is not available on
/// `Phantomcow`.
pub struct Supercow<'a, OWNED, BORROWED : ?Sized = OWNED,
                    SHARED = Box<DefaultFeatures<'static> + 'static>,
                    STORAGE = BoxedStorage, PTR = *const BORROWED>
where BORROWED : 'a,
      *const BORROWED : PointerFirstRef,
      STORAGE : OwnedStorage<OWNED, SHARED>,
      PTR : PtrWrite<BORROWED> {
    // This stores the precalculated `Deref` target, and is the only thing the
    // `Deref` implementation needs to inspect.
    //
    // Note that there are three cases with this pointer:
    //
    // - A pointer to an external value. In this case, we know that the pointer
    // will not be invalidated by movement or for the lifetime of `'a` and
    // simply store the reference here as an absolute address.
    //
    // - A pointer to a ZST at an "external" location, often address 1. We
    // don't need to handle this in any particular manner as long as we don't
    // accidentally make a null reference during deref(), since the only thing
    // safe rust can do with a ZST reference is inspect its address, and if we
    // do "move" it around, there's nothing unsafe from this fact being leaked.
    //
    // - A pointer into this `Supercow`. In this case, the absolute address
    // will change whenever this `Supercow` is relocated. To handle this, we
    // instead store the offset from `&self` here, and adjust it at `Deref`
    // time. We differentiate between the two cases by inspecting the absolute
    // value of the address: If it is less than
    // `MAX_INTERNAL_BORROW_DISPLACEMENT*2`, we assume it is an internal
    // pointer, since no modern system ever has virtual memory mapped between 0
    // and 4kB (and any code elsewhere involving this region is presumably too
    // low-level to be using `Supercow`).
    //
    // One peculiarity is that this is declared as a typed pointer even though
    // it does not necessarily point to anything (due to internal pointers).
    // This is so that it works with DSTs, which have pointers larger than
    // simple machine pointers. We assume the first pointer-sized value is the
    // actual address (see `PointerFirstRef`).
    //
    // If `STORAGE` does not use internal pointers, we can skip all the
    // arithmetic and return this value unmodified.
    ptr: PTR,
    // The current ownership mode of this `Supercow`.
    //
    // This has three states:
    //
    // - Null. The `Supercow` holds a `&'a BORROWED`.
    //
    // - Even alignment. The `Supercow` holds an `OWNED` accessible via
    // `STORAGE` field a, and this value is what is passed into the `STORAGE`
    // methods.
    //
    // - Odd alignment. The `Supercow` holds a `SHARED`, accessible via
    // `STORAGE` field b, with a pointer value one less than this one. Note
    // that since the default `SHARED` is a `Box<DefaultFeatures>`, we actually
    // end up with two levels of boxing here for `BoxedStorage`. This is
    // actually necessary so that the whole thing only takes one immediate
    // pointer.
    mode: *mut (),
    storage: STORAGE,

    _owned: PhantomData<OWNED>,
    _borrowed: PhantomData<&'a BORROWED>,
    _shared: PhantomData<SHARED>,
}

/// `Phantomcow<'a, Type>` is to `Supercow<'a, Type>` as
/// `PhantomData<&'a Type>` is to `&'a Type`.
///
/// That is, `Phantomcow` effects a lifetime dependency on the borrowed value,
/// while still permitting the owned and shared modes of `Supercow`, and
/// keeping the underlying objects alive as necessary.
///
/// There is not much one can do with a `Phantomcow`; it can be moved around,
/// and in some cases cloned. Its main use is in FFI wrappers, where `BORROWED`
/// maintains some external state or resource that will be destroyed when it
/// is, and which the owner of the `Phantomcow` depends on to function.
///
/// The size of a `Phantomcow` is generally equal to the size of the
/// corresponding `Supercow` type minus the size of `&'a BORROWED`, though this
/// may not be exact depending on `STORAGE` alignment, etc.
pub type Phantomcow<'a, OWNED, BORROWED = OWNED,
                    SHARED = Box<DefaultFeatures<'static> + 'static>,
                    STORAGE = BoxedStorage> =
    Supercow<'a, OWNED, BORROWED, SHARED, STORAGE, ()>;

/// The `Phantomcow` variant corresponding to `NonSyncSupercow`.
pub type NonSyncPhantomcow<'a, OWNED, BORROWED = OWNED> =
    Phantomcow<'a, OWNED, BORROWED, Box<NonSyncFeatures<'static> + 'static>,
               BoxedStorage>;

/// The `Phantomcow` variant corresponding to `InlineStorage`.
pub type InlinePhantomcow<'a, OWNED, BORROWED = OWNED,
                          SHARED = Box<DefaultFeatures<'static> + 'static>> =
    Phantomcow<'a, OWNED, BORROWED, SHARED, InlineStorage<OWNED, SHARED>>;

/// The `Phantomcow` variant corresponding to `InlineNonSyncSupercow`.
pub type InlineNonSyncPhantomcow<'a, OWNED, BORROWED = OWNED> =
    Phantomcow<'a, OWNED, BORROWED, Box<NonSyncFeatures<'static> + 'static>,
             InlineStorage<OWNED, Box<NonSyncFeatures<'static> + 'static>>>;

enum SupercowMode {
    Owned(*mut ()),
    Borrowed,
    Shared(*mut ()),
}

impl SupercowMode {
    fn from_ptr(mode: *mut ()) -> Self {
        if mode.is_null() {
            Borrowed
        } else if mode.is_2_aligned() {
            Owned(mode)
        } else {
            Shared(mode.align2())
        }
    }
}

use self::SupercowMode::*;

macro_rules! defimpl {
    ($(@$us:tt)* [$($tparm:ident $(: ?$tparmsized:ident)*),*] ($($spec:tt)*)
     where { $($wo:tt)* } $body:tt) => {
        $($us)* impl<'a, $($tparm $(: ?$tparmsized)*,)* OWNED,
             BORROWED : ?Sized, SHARED, STORAGE, PTR>
            $($spec)* Supercow<'a, OWNED, BORROWED, SHARED, STORAGE, PTR>
        where BORROWED : 'a,
              *const BORROWED : PointerFirstRef,
              STORAGE : OwnedStorage<OWNED, SHARED>,
              PTR : PtrWrite<BORROWED>,
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
    &'a BORROWED : Send,
    SHARED : Send,
    STORAGE : Send,
} { } }

defimpl! {@unsafe [] (Sync for) where {
    OWNED : Sync,
    &'a BORROWED : Sync,
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
        // This line could panic, but the only thing that has not yet been
        // initialised properly is `ptr`, which is immaterial since the
        // `Supercow` will not escape this frame if this panics, and `Drop`
        // does not care about `ptr`.
        unsafe { this.borrow_owned(); }
        this
    }

    /// Creates a new `Supercow` which borrows the given value.
    pub fn borrowed<T : Borrow<BORROWED> + ?Sized>(inner: &'a T) -> Self {
        let mut this = unsafe { Self::empty() };
        // No need to write to `mode`; `empty()` returns a borrowed-mode
        // `Supercow`.
        this.ptr.store_ptr(inner.borrow() as *const BORROWED);
        this
    }

    /// Creates a new `Supercow` using the given shared reference.
    ///
    /// The reference must be convertible to `SHARED` via `SharedFrom`.
    pub fn shared<T>(inner: T) -> Self
    where T : ConstDeref<Target = BORROWED>,
          SHARED : SharedFrom<T> {
        let mut ptr = PTR::new();
        ptr.store_ptr(inner.const_deref());
        Self::shared_nocvt(SHARED::shared_from(inner), ptr)
    }

    fn shared_nocvt(shared: SHARED, ptr: PTR) -> Self {
        let mut this = unsafe { Self::empty() };
        // If something panics below, `ptr` is may become a dangling pointer.
        // That's fine, though, because the `Supercow` will not escape the
        // frame and `Drop` does not inspect `ptr`.
        this.ptr = ptr;
        this.mode = this.storage.allocate_b(shared).unalign2() as *mut ();
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
    where SHARED : Clone {
        match this.mode() {
            Owned(_) => None,

            Borrowed => Some(Supercow {
                ptr: this.ptr,
                mode: this.mode,
                storage: Default::default(),
                _owned: PhantomData,
                _borrowed: PhantomData,
                _shared: PhantomData,
            }),

            Shared(s) => Some(Self::shared_nocvt(unsafe {
                this.storage.get_ptr_b(s)
            }.clone(), this.ptr)),
        }
    }

    /// Logically clone `this` without needing to clone `OWNED`.
    ///
    /// If this `Supercow` is in owned mode, the owned value is first moved
    /// into a new shared reference so that `OWNED` does not need to be cloned.
    ///
    /// ## Example
    ///
    /// ```
    /// use supercow::Supercow;
    ///
    /// struct NonCloneType(u32);
    ///
    /// let mut first: Supercow<NonCloneType> =
    ///   Supercow::owned(NonCloneType(42));
    /// let second = Supercow::share(&mut first);
    ///
    /// assert_eq!(42, (*first).0);
    /// assert_eq!(42, (*second).0);
    /// ```
    pub fn share(this: &mut Self) -> Self
    where OWNED : SafeBorrow<BORROWED>,
          SHARED : Clone + TwoStepShared<OWNED, BORROWED> {
        match this.mode() {
            Owned(ptr) => {
                let unboxed = SHARED::new_two_step();
                let mut new_storage: STORAGE = Default::default();
                let shared_ptr = new_storage.allocate_b(unboxed);
                let internal_ptr: *const BORROWED = {
                    // `deref_holder` is technically allowed to panic. In
                    // practise it isn't expected to since any implementation
                    // would be trivial. If it *does*, we're still safe, but we
                    // may leak the storage allocated above.
                    let holder = unsafe {
                        new_storage.get_mut_b(shared_ptr)
                            .deref_holder()
                    };

                    // The natural way to determine `internal_ptr` below would
                    // be to first write into holder, then do
                    // internal_ptr = holder.as_ref().unwrap().borrow();
                    //
                    // But this isn't safe since `borrow()` could panic and we
                    // have dangling pointers everywhere.
                    //
                    // But we can take advantage of three facts:
                    //
                    // - The memory returned by `borrow()` the last time we
                    // called it must remain valid during these operations
                    // since the owner is not being mutated.
                    //
                    // - Moving the owned value is just a `memcpy()`. This
                    // means anything outside of it remains valid and at the
                    // same address.
                    //
                    // - Anything _inside_ the owned value will be valid at the
                    // same relative position at whatever new address the value
                    // obtains below.
                    //
                    // So what we do instead is determine whether the borrowed
                    // value is internal or external and the calculate what the
                    // new borrowed address is by hand.
                    let owned_base = unsafe {
                        this.storage.get_ptr_a(ptr)
                    }.address();
                    let owned_size = mem::size_of::<OWNED>();
                    // Call borrow() again instead of using our own deref()
                    // since `Phantomcow` can't do the latter.
                    let borrowed_ptr = unsafe {
                        this.storage.get_ptr_a(ptr)
                    }.borrow() as *const BORROWED;

                    // These steps need to be uninterrupted by safe function
                    // calls, as any panics would result in dangling pointers.
                    // Specifically:
                    //
                    // - `mode` is a dangling pointer until we both it and
                    // `storage` below. But we can't set storage until we've
                    // moved the value out of it.
                    //
                    // - `ptr` is a dangling pointer until we borrow the shared
                    // value below. Because of this, we can't eliminate the
                    // `mode` case by setting it to null, since we don't have
                    // anything `ptr` can legally point to.
                    *holder = Some(unsafe {
                        this.storage.deallocate_into_a(ptr)
                    });

                    if borrowed_ptr.within(owned_base, owned_size) {
                        // unwrap() won't panic since we just wrote `Some`
                        // above.
                        let new_base = holder.as_ref().unwrap().address();
                        borrowed_ptr.rebase(owned_base, new_base)
                    } else {
                        borrowed_ptr
                    }
                };
                this.storage = new_storage;
                this.mode = shared_ptr.unalign2() as *mut ();
                this.ptr.store_ptr(internal_ptr);
                // End uninterrupted section

                Self::shared_nocvt(unsafe {
                    this.storage.get_ptr_b(shared_ptr)
                }.clone(), this.ptr)
            },

            Borrowed => Supercow {
                ptr: this.ptr,
                mode: this.mode,
                storage: Default::default(),
                _owned: PhantomData,
                _borrowed: PhantomData,
                _shared: PhantomData,
            },

            Shared(s) => Self::shared_nocvt(unsafe {
                this.storage.get_ptr_b(s)
            }.clone(), this.ptr),
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
    /// let forty_two: u32 = 42;
    ///
    /// let borrowed: Supercow<u32> = (&forty_two).into();
    /// assert_eq!(Some(&forty_two), Supercow::extract_ref(&borrowed));
    ///
    /// let owned: Supercow<u32> = forty_two.into();
    /// assert_eq!(None, Supercow::extract_ref(&owned));
    ///
    /// let shared: Supercow<u32> = Arc::new(forty_two).into();
    /// assert_eq!(None, Supercow::extract_ref(&shared));
    /// ```
    pub fn extract_ref(this: &Self) -> Option<&'a BORROWED>
    where PTR : PtrRead<BORROWED> {
        match this.mode() {
            Borrowed => Some(unsafe { &*this.ptr.get_ptr() }),
            _ => None,
        }
    }

    /// Takes ownership of the underling value if needed, then returns it,
    /// consuming `self`.
    pub fn into_inner(mut this: Self) -> OWNED
    where OWNED : Borrow<BORROWED>,
          BORROWED : ToOwned<Owned = OWNED>,
          PTR : PtrRead<BORROWED> {
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
    pub fn to_mut<'b>(&'b mut self) -> Ref<'b, Self>
    where OWNED : SafeBorrow<BORROWED>,
          BORROWED : ToOwned<Owned = OWNED>,
          PTR : PtrRead<BORROWED>
    {
        // Become owned if not already.
        match self.mode() {
            Owned(_) => (),
            _ => *self = Self::owned((*self).to_owned()),
        }

        // Clear out `ptr` if it points somewhere unstable
        let old_ptr = self.ptr.get_ptr();
        self.ptr.store_ptr(OWNED::borrow_replacement(
            unsafe { &*old_ptr }) as *const BORROWED);

        Ref {
            r: unsafe { self.storage.get_mut_a(self.mode) } as *mut OWNED,
            parent: self,
        }
    }

    /// If `this` is borrowed, clone the inner value so that the new `Supercow`
    /// has a `'static` lifetime.
    ///
    /// If the inner value is owned or borrowed, this simply returns the input
    /// unchanged.
    ///
    /// ## Example
    ///
    /// ```
    /// use supercow::Supercow;
    ///
    /// let s = {
    ///   let forty_two = 42u32;
    ///   let by_ref: Supercow<u32> = Supercow::borrowed(&forty_two);
    ///   // We can't return `by_ref` because it holds a reference to
    ///   // `forty_two`. However, we can change that lifetime parameter
    ///   // to `'static` and then move that out of the block.
    ///   let by_val: Supercow<'static, u32> = Supercow::unborrow(by_ref);
    ///   by_val
    /// };
    /// assert_eq!(42, *s);
    /// ```
    pub fn unborrow(mut this: Self)
                    -> Supercow<'static, OWNED, BORROWED, SHARED, STORAGE, PTR>
    where OWNED : SafeBorrow<BORROWED>,
          BORROWED : ToOwned<Owned = OWNED>,
          PTR : PtrRead<BORROWED> {
        match this.mode() {
            Owned(_) | Shared(_) => Supercow {
                ptr: this.ptr,
                mode: mem::replace(&mut this.mode, ptr::null_mut()),
                storage: mem::replace(&mut this.storage, Default::default()),
                _owned: PhantomData,
                _borrowed: PhantomData,
                _shared: PhantomData,
            },

            Borrowed => Supercow::owned((*this).to_owned()),
        }
    }

    /// Takes ownership of the underlying value, so that this `Supercow` has a
    /// `'static` lifetime.
    ///
    /// This may also change the `SHARED` type parameter arbitrarily.
    ///
    /// ## Example
    ///
    /// ```
    /// use supercow::Supercow;
    ///
    /// let s = {
    ///   let forty_two = 42u32;
    ///   let by_ref: Supercow<u32> = Supercow::borrowed(&forty_two);
    ///   // We can't return `by_ref` because it holds a reference to
    ///   // `forty_two`. However, we can change that lifetime parameter
    ///   // to `'static` and then move that out of the block.
    ///   let by_val: Supercow<'static, u32> =
    ///     Supercow::take_ownership(by_ref);
    ///   by_val
    /// };
    /// assert_eq!(42, *s);
    /// ```
    pub fn take_ownership<NS>
        (mut this: Self) -> Supercow<'static, OWNED, BORROWED, NS, STORAGE, PTR>
    where OWNED : SafeBorrow<BORROWED>,
          BORROWED : ToOwned<Owned = OWNED>,
          STORAGE : OwnedStorage<OWNED, NS>,
          PTR : PtrRead<BORROWED> {
        match this.mode() {
            // We can't just return `this` since we are changing the lifetime
            // and possibly `STORAGE`.
            Owned(_) => Supercow {
                ptr: this.ptr,
                mode: mem::replace(&mut this.mode, ptr::null_mut()),
                storage: mem::replace(&mut this.storage, Default::default()),
                _owned: PhantomData,
                _borrowed: PhantomData,
                _shared: PhantomData,
            },

            _ => Supercow::owned((*this).to_owned()),
        }
    }

    /// Converts this `Supercow` into a `Phantomcow`.
    pub fn phantom(mut this: Self)
                   -> Phantomcow<'a, OWNED, BORROWED, SHARED, STORAGE> {
        let ret = Supercow {
            ptr: (),
            mode: mem::replace(&mut this.mode, ptr::null_mut()),
            storage: mem::replace(&mut this.storage, Default::default()),
            _owned: PhantomData,
            _borrowed: PhantomData,
            _shared: PhantomData,
        };
        ret
    }

    unsafe fn borrow_owned(&mut self)
    where OWNED : SafeBorrow<BORROWED> {
        let mut borrowed_ptr = self.storage.get_ptr_a(self.mode).borrow()
            as *const BORROWED;

        // We have a strong assumption that nothing ever gets allocated below
        // MAX_INTERNAL_BORROW_DISPLACEMENT, so check that in debug mode. Note
        // that ZSTs are frequently positioned in this range; as described in
        // the `Deref` implementation, we consider it OK to relocate them and
        // so ignore them.
        debug_assert!(
            0 == mem::size_of_val(&* borrowed_ptr) ||
            borrowed_ptr.address() >= MAX_INTERNAL_BORROW_DISPLACEMENT,
            "Supercow: Non-ZST allocated at {:p}, which is below the \
             minimum supported allocation address of {}",
            borrowed_ptr, MAX_INTERNAL_BORROW_DISPLACEMENT);

        // Adjust the pointer if needed. We only need to consider this case
        // when internal storage may be in use.
        if STORAGE::is_internal_storage() {
            let self_start = self.address();
            let self_size = mem::size_of::<Self>();

            // If not an internal pointer, nothing to adjust.
            if borrowed_ptr.within(self_start, self_size) {
                // In debug mode, ensure that both `OWNED::borrow()` and
                // `STORAGE` fulfilled their maximum offset contract.
                //
                // Note that the actual threshold is greater than the sum of
                // the permitted offsets; here, we strictly check the maximum
                // that the two together may produce. (Note <= and not <.)
                debug_assert!(borrowed_ptr.address() - self_start <=
                              MAX_INTERNAL_BORROW_DISPLACEMENT * 3/2,
                              "Borrowed pointer displaced too far from \
                               base address (supercow at {:x}, self at {:x}, \
                               borrowed to {:x}", self_start,
                              (&self.storage).address(),
                              borrowed_ptr.address());

                // Move the pointer from being based on `self` to being based
                // on NULL. We identify this later in `Deref` by seeing that
                // the nominal address is less than
                // MAX_INTERNAL_BORROW_DISPLACEMENT.
                borrowed_ptr = borrowed_ptr.rebase(self_start, 0);
            }
        }

        self.ptr.store_ptr(borrowed_ptr);
    }

    /// Create an "empty" `Supercow`.
    ///
    /// The value must not be exposed to the outside world as it has a null
    /// `ptr`. However, it is safe to drop as-is as it is returned in reference
    /// mode and has no uninitialised content as far as the compiler is
    /// concerned.
    unsafe fn empty() -> Self {
        Supercow {
            ptr: PTR::new(),
            mode: ptr::null_mut(),
            storage: Default::default(),
            _owned: PhantomData,
            _borrowed: PhantomData,
            _shared: PhantomData,
        }
    }

    fn mode(&self) -> SupercowMode {
        SupercowMode::from_ptr(self.mode)
    }
} }

defimpl! {[] (RefParent for) where {
    OWNED : SafeBorrow<BORROWED>
} {
    type Owned = OWNED;

    unsafe fn supercow_ref_drop(&mut self) {
        self.borrow_owned()
    }
} }

/// Provides mutable access to an owned value within a `Supercow`.
///
/// This is similar to the `Ref` used with `RefCell`.
pub struct Ref<'a, P>
where P : RefParent + 'a {
    // This is a pointer and not a reference as otherwise we would have two
    // `&mut` references into the parent, which is illegal.
    r: *mut P::Owned,
    parent: &'a mut P,
}


impl<'a, P> Deref for Ref<'a, P>
where P : RefParent + 'a {
    type Target = P::Owned;

    #[inline]
    fn deref(&self) -> &P::Owned {
        unsafe { &*self.r }
    }
}

impl<'a, P> DerefMut for Ref<'a, P>
where P : RefParent + 'a {
    #[inline]
    fn deref_mut(&mut self) -> &mut P::Owned {
        unsafe { &mut*self.r }
    }
}

impl<'a, P> Drop for Ref<'a, P>
where P : RefParent + 'a {
    #[inline]
    fn drop(&mut self) {
        // The value of `OWNED::borrow()` may have changed, so recompute
        // everything instead of backing the old values up.
        unsafe { self.parent.supercow_ref_drop() }
    }
}

defimpl! {[] (Deref for) where {
    PTR : PtrRead<BORROWED>
} {
    type Target = BORROWED;
    #[inline]
    fn deref(&self) -> &BORROWED {
        let mut target_ref = self.ptr.get_ptr();
        unsafe {
            // If pointers may be stored internally to `self` and the nominal
            // pointer is based on NULL (as positioned by `borrow_owned()`),
            // move the pointer to be based on `self`.
            if STORAGE::is_internal_storage() &&
                target_ref.within(0, MAX_INTERNAL_BORROW_DISPLACEMENT)
            {
                target_ref = target_ref.rebase(0, self.address());
            }
            &*target_ref
        }
    }
} }

defimpl! {[] (Borrow<BORROWED> for) where {
    PTR : PtrRead<BORROWED>,
} {
    fn borrow(&self) -> &BORROWED {
        self.deref()
    }
} }

defimpl! {[] (AsRef<BORROWED> for) where {
    PTR : PtrRead<BORROWED>,
} {
    fn as_ref(&self) -> &BORROWED {
        self.deref()
    }
} }

defimpl! {[] (Clone for) where {
    OWNED : Clone + SafeBorrow<BORROWED>,
    SHARED : Clone,
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
                _borrowed: PhantomData,
                _shared: PhantomData,
            },

            Shared(s) => Self::shared_nocvt(unsafe {
                self.storage.get_ptr_b(s)
            }.clone(), self.ptr),
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
where SHARED : SharedFrom<Rc<OWNED>>,
      STORAGE : OwnedStorage<OWNED, SHARED>,
      OWNED : 'a,
      *const OWNED : PointerFirstRef {
    fn from(rc: Rc<OWNED>) -> Self {
        Self::shared(rc)
    }
}
impl<'a, OWNED, SHARED, STORAGE> From<Arc<OWNED>>
for Supercow<'a, OWNED, OWNED, SHARED, STORAGE>
where SHARED : SharedFrom<Arc<OWNED>>,
      STORAGE : OwnedStorage<OWNED, SHARED>,
      OWNED : 'a,
      *const OWNED : PointerFirstRef {
    fn from(rc: Arc<OWNED>) -> Self {
        Self::shared(rc)
    }
}

macro_rules! deleg_fmt { ($tr:ident) => {
    defimpl! {[] (fmt::$tr for) where {
        BORROWED : fmt::$tr,
        PTR : PtrRead<BORROWED>,
    } {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            (**self).fmt(f)
        }
    } }
} }

deleg_fmt!(Binary);
deleg_fmt!(Display);
deleg_fmt!(LowerExp);
deleg_fmt!(LowerHex);
deleg_fmt!(Octal);
deleg_fmt!(Pointer);
deleg_fmt!(UpperExp);
deleg_fmt!(UpperHex);

impl<'a, OWNED, BORROWED : ?Sized, SHARED, STORAGE>
fmt::Debug for Supercow<'a, OWNED, BORROWED, SHARED, STORAGE, ()>
where BORROWED : 'a,
      *const BORROWED : PointerFirstRef,
      STORAGE : OwnedStorage<OWNED, SHARED> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<Phantomcow>")
    }
}

impl<'a, OWNED, BORROWED : ?Sized, SHARED, STORAGE>
fmt::Debug for Supercow<'a, OWNED, BORROWED, SHARED, STORAGE, *const BORROWED>
where BORROWED : fmt::Debug + 'a,
      *const BORROWED : PointerFirstRef,
      STORAGE : OwnedStorage<OWNED, SHARED> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

defimpl! {[T] (cmp::PartialEq<T> for) where {
    T : Borrow<BORROWED>,
    BORROWED : PartialEq<BORROWED>,
    PTR : PtrRead<BORROWED>,
} {
    fn eq(&self, other: &T) -> bool {
        **self == *other.borrow()
    }

    fn ne(&self, other: &T) -> bool {
        **self != *other.borrow()
    }
} }

defimpl! {[] (cmp::Eq for) where {
    BORROWED : Eq,
    PTR : PtrRead<BORROWED>,
} { } }

defimpl! {[T] (cmp::PartialOrd<T> for) where {
    T : Borrow<BORROWED>,
    BORROWED : cmp::PartialOrd<BORROWED>,
    PTR : PtrRead<BORROWED>,
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
    BORROWED : cmp::Ord,
    PTR : PtrRead<BORROWED>,
} {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        (**self).cmp(other)
    }
} }

defimpl! {[] (Hash for) where {
    BORROWED : Hash,
    PTR : PtrRead<BORROWED>,
} {
    fn hash<H : Hasher>(&self, h: &mut H) {
        (**self).hash(h)
    }
} }

trait ReferenceExt {
    fn address(&self) -> usize;
}
impl<'a, T : ?Sized + 'a> ReferenceExt for &'a T {
    #[inline]
    fn address(&self) -> usize {
        (*self) as *const T as *const () as usize
    }
}
impl<'a, T : ?Sized + 'a> ReferenceExt for &'a mut T {
    #[inline]
    fn address(&self) -> usize {
        (*self) as *const T as *const () as usize
    }
}

unsafe trait PfrExt : Copy {
    /// Returns the address of this pointer.
    #[inline]
    fn address(self) -> usize {
        let saddr: &usize = unsafe {
            mem::transmute(&self)
        };
        *saddr
    }

    /// Returns a pointer with the same extra data as `self`, but with the
    /// given new `address`.
    #[inline]
    fn with_address(mut self, address: usize) -> Self {
        let saddr: &mut usize = unsafe {
            mem::transmute(&mut self)
        };
        *saddr = address;

        let saddr: &mut Self = unsafe {
            mem::transmute(saddr)
        };
        *saddr
    }

    /// Returns whether this pointer is within the allocation starting at
    /// `base` and with size `size` (bytes).
    #[inline]
    fn within(self, base: usize, size: usize) -> bool {
        let a = self.address();
        a >= base && a < (base + size)
    }

    /// Adjusts this pointer from being based at `old_base` to being based at
    /// `new_base` (assuming this pointer is within the allocation starting at
    /// `old_base`).
    #[inline]
    fn rebase(self, old_base: usize, new_base: usize) -> Self {
        self.with_address(new_base + (self.address() - old_base))
    }

    /// Returns whether this pointer has 2-byte alignment.
    #[inline]
    fn is_2_aligned(self) -> bool {
        0 == (self.address() & 1usize)
    }

    /// Clears bit 0 of this pointer.
    #[inline]
    fn align2(self) -> Self {
        self.with_address(self.address() & !1usize)
    }

    /// Sets bit 0 of this pointer.
    #[inline]
    fn unalign2(self) -> Self {
        self.with_address(self.address() | 1usize)
    }
}
unsafe impl<T : PointerFirstRef> PfrExt for T { }
unsafe impl<T : ?Sized> PfrExt for *mut T { }

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

macro_rules! tests { ($modname:ident, $stype:ident, $ptype:ident) => {
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
    // `SipHasher` is deprecated, but its replacement `DefaultHasher` doesn't
    // exist in Rust 1.12.1.
    #[allow(deprecated)]
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

    #[test]
    fn unborrow_owned() {
        let orig: Supercow<String, str> =
            Supercow::owned("hello world".to_owned());
        let unborrowed = Supercow::unborrow(orig);
        assert_eq!(unborrowed, "hello world");
    }

    #[test]
    fn unborrow_borrowed() {
        let orig: Supercow<String, str> =
            Supercow::borrowed("hello world");
        let unborrowed = Supercow::unborrow(orig);
        assert_eq!(unborrowed, "hello world");
    }

    #[test]
    fn unborrow_shared() {
        let orig: Supercow<String> =
            Supercow::shared(Arc::new("hello world".to_owned()));
        let unborrowed = Supercow::unborrow(orig);
        assert_eq!(unborrowed, "hello world".to_owned());
    }

    #[test]
    fn take_ownership_owned() {
        let orig: Supercow<String, str> =
            Supercow::owned("hello world".to_owned());
        let owned: Supercow<String, str> = Supercow::take_ownership(orig);
        assert_eq!(owned, "hello world");
    }

    #[test]
    fn take_ownership_borrowed() {
        let orig: Supercow<String, str> =
            Supercow::borrowed("hello world");
        let owned: Supercow<String, str> = Supercow::take_ownership(orig);
        assert_eq!(owned, "hello world");
    }

    #[test]
    fn take_ownership_shared() {
        let orig: Supercow<String> =
            Supercow::shared(Arc::new("hello world".to_owned()));
        let owned: Supercow<String> = Supercow::take_ownership(orig);
        assert_eq!(owned, "hello world".to_owned());
    }

    struct MockNativeResource(*mut u32);
    impl Drop for MockNativeResource {
        fn drop(&mut self) {
            unsafe { *self.0 = 0 };
        }
    }
    // Not truly safe, but we're not crossing threads here and we need
    // something for the Sync tests either way.
    unsafe impl Send for MockNativeResource { }
    unsafe impl Sync for MockNativeResource { }

    struct MockDependentResource<'a> {
        ptr: *mut u32,
        _handle: $ptype<'a, MockNativeResource>,
    }

    fn check_dependent_ok(mdr: MockDependentResource) {
        assert_eq!(42, unsafe { *mdr.ptr });
    }

    #[test]
    fn borrowed_phantomcow() {
        let mut forty_two = 42u32;

        let native = MockNativeResource(&mut forty_two);
        let sc: $stype<MockNativeResource> = Supercow::borrowed(&native);
        check_dependent_ok(MockDependentResource {
            ptr: &mut forty_two,
            _handle: Supercow::phantom(sc),
        });
    }

    #[test]
    fn owned_phantomcow() {
        let mut forty_two = 42u32;

        let native = MockNativeResource(&mut forty_two);
        let sc: $stype<MockNativeResource> = Supercow::owned(native);
        check_dependent_ok(MockDependentResource {
            ptr: &mut forty_two,
            _handle: Supercow::phantom(sc),
        });
    }

    #[test]
    fn shared_phantomcow() {
        let mut forty_two = 42u32;

        let native = MockNativeResource(&mut forty_two);
        let sc: $stype<MockNativeResource> =
            Supercow::shared(Arc::new(native));
        check_dependent_ok(MockDependentResource {
            ptr: &mut forty_two,
            _handle: Supercow::phantom(sc),
        });
    }

    #[test]
    fn clone_owned_phantomcow() {
        let sc: $stype<String> = Supercow::owned("hello world".to_owned());
        let p1 = Supercow::phantom(sc);
        assert!(Supercow::clone_non_owned(&p1).is_none());
        let _p2 = p1.clone();
    }

    #[test]
    fn clone_borrowed_phantomcow() {
        let sc: $stype<String, str> = Supercow::borrowed("hello world");
        let p1 = Supercow::phantom(sc);
        assert!(Supercow::clone_non_owned(&p1).is_some());
        let _p2 = p1.clone();
    }

    #[test]
    fn clone_shared_phantomcow() {
        let sc: $stype<String> = Supercow::shared(
            Arc::new("hello world".to_owned()));
        let p1 = Supercow::phantom(sc);
        assert!(Supercow::clone_non_owned(&p1).is_some());
        let _p2 = p1.clone();
    }

    struct NotCloneable(u32);
    impl Drop for NotCloneable {
        fn drop(&mut self) {
            self.0 = 0;
        }
    }

    #[test]
    fn share_owned_supercow() {
        let mut a: $stype<NotCloneable> = Supercow::owned(NotCloneable(42));
        let b = Supercow::share(&mut a);

        assert_eq!(42, (*a).0);
        assert_eq!(42, (*b).0);
    }

    #[test]
    fn share_borrowed_supercow() {
        let nc = NotCloneable(42);
        let mut a: $stype<NotCloneable> = Supercow::borrowed(&nc);
        let b = Supercow::share(&mut a);

        assert_eq!(42, (*a).0);
        assert_eq!(42, (*b).0);
    }

    #[test]
    fn share_shared_supercow() {
        let mut a: $stype<NotCloneable> = Supercow::shared(
            Arc::new(NotCloneable(42)));
        let b = Supercow::share(&mut a);

        assert_eq!(42, (*a).0);
        assert_eq!(42, (*b).0);
    }

    #[test]
    fn share_owned_dst_supercow() {
        let mut a: $stype<String, str> = Supercow::owned("hello world".into());
        let b = Supercow::share(&mut a);

        assert_eq!("hello world", &*a);
        assert_eq!("hello world", &*b);
    }

    #[test]
    fn share_owned_phantomcow() {
        let sc: $stype<NotCloneable> = Supercow::owned(NotCloneable(42));
        let mut a: $ptype<NotCloneable> = Supercow::phantom(sc);
        let _b = Supercow::share(&mut a);
    }

    #[test]
    fn share_borrowed_phantomcow() {
        let nc = NotCloneable(42);
        let sc: $stype<NotCloneable> = Supercow::borrowed(&nc);
        let mut a: $ptype<NotCloneable> = Supercow::phantom(sc);
        let _b = Supercow::share(&mut a);
    }

    #[test]
    fn share_shared_phantomcow() {
        let sc: $stype<NotCloneable> =
            Supercow::shared(Arc::new(NotCloneable(42)));
        let mut a: $ptype<NotCloneable> = Supercow::phantom(sc);
        let _b = Supercow::share(&mut a);
    }

    #[test]
    fn share_owned_dst_phantomcow() {
        let sc: $stype<String, str> = Supercow::owned("hello world".into());
        let mut a: $ptype<String, str> = Supercow::phantom(sc);
        let _b = Supercow::share(&mut a);
    }
} } }

tests!(inline_sync_tests, InlineSupercow, InlinePhantomcow);
tests!(inline_nonsync_tests, InlineNonSyncSupercow, InlineNonSyncPhantomcow);
tests!(boxed_sync_tests, Supercow, Phantomcow);
tests!(boxed_nonsync_tests, NonSyncSupercow, NonSyncPhantomcow);

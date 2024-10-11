An approach for verifying compliance with Tree Borrows in VeriFast
==================================================================

For Tree Borrows, see the work by [Neven Villani and Ralf Jung](https://perso.crans.org/vanille/treebor/index.html).

# Mutable references

In VeriFast, currently, the expression `&mut *x` simply evaluates to `x`. In this proposal, instead it will evaluate to a fresh pointer value `p` (whose address equals that of `x` but whose provenance is different). (The range of valid addresses of the new provenance equals that of the old one, though.) This means existing heap chunks do not provide any access via the new pointer `p`. Therefore, symbolic evaluation of this expression also consumes the (full) points-to chunk at `x` and produces it at `p`. Furthermore, it produces a `ref_mut_end_token(p, x)`. A ghost command `end_ref_mut(p)` consumes the `ref_mut_end_token(p, ?x)` and `*p |-> ?v` and produces `*x |-> v`.

### Example

Consider the following piece of Rust code:
```rust
let mut x = 42;
let y = &mut x;
*y += 1;
x += 1;
```
Here is how this is executed symbolically by VeriFast. We insert assertions showing the intermediate states, as well a call of `end_ref_mut` indicating the end of the mutable reference:
```rust
let mut x = 42;
//@ assert x |-> 42;
let y = &mut x;
//@ assert y |-> ?p &*& *p |-> 42 &*& ref_mut_end_token(p, &x);
*y += 1;
//@ assert y |-> p &*& *p |-> 43 &*& ref_mut_end_token(p, &x);
//@ end_ref_mut(p);
//@ assert y |-> p &*& x |-> 43;
*x += 1;
//@ assert y |-> p &*& x |-> 44;
```
Note: in VeriFast, `LHS |-> RHS` denotes exclusive ownership of *place* (lvalue) LHS whose current value is RHS. `&*&` is separating conjunction. `?p` introduces a new ghost variable `p` and binds it to the matched value for the remainder of the current scope.

## Function arguments

Tree Borrows says that references passed as function arguments must not become disabled while the function call executes. We can enforce this for mutable references by temporarily consuming, at the call site, some fraction of `ref_mut_end_token` for each argument that is a mutable reference for the duration of the call. (Note: it does not work to temporarily consume this chunk fully, because the same reference may be passed as an argument to any number of nested function calls. A fraction of this chunk must therefore travel with the mutable reference wherever it goes. Therefore, it should probably be kept inside a fractured borrow at the same lifetime as the mutable reference.)

# Shared references (simple case)

Symbolically evaluating the expression `& *x`, where `*x` is of type `T`, evaluates to a fresh pointer value `p` and produces a `ref_init_perm::<T>(p, x)`. If `T` is a simple primitive scalar type (e.g. `i32`), ghost command `init_ref(p, frac)` consumes `ref_init_perm::<T>(p, ?x)` and `[frac]*x |-> ?v` and produces `[frac]*p |-> v` as well as `ref_end_token::<T>(p, x, frac)` and `ref_initialized::<T>(p)`.

(Note, occurrences of `&` inside assertions simply denote the pure address-of operator, not the mutable/shared reference creation operator.)

VeriFast will check that `ref_initialized::<T>(p)` exists before the next (non-ghost) instruction following the `& *x` instruction is executed. (Indeed, Tree Borrows requires that shared references be readable immediately upon creation.) (We call this check the "ref init check".)

## Ending a shared reference

Ghost command `end_ref(p)`, where `p` is of type `&T` and `T` is a simple primitive scalar type, consumes `ref_initialized(p)` and `ref_end_token(p, ?x, ?frac)` and `[frac]*p |-> ?v` and produces `[frac]*x |-> v`.

### Example (simple case)

Consider the following Rust code:
```rust
let mut x = 42;
let y = &x;
let z = &x;
print(*y);
print(*z);
x += 1;
```

Here is a version with VeriFast annotations sufficient to verify this program under the proposed approach (as well as assertions that show the intermediate states):
```rust
let mut x = 42;
//@ assert x |-> 42;
let y = &x;
//@ assert x |-> 42 &*& y |-> ?p &*& ref_init_perm::<i32>(p, &x);
//@ init_ref(p, 1/2);
//@ assert [1/2]x |-> 42 &*& y |-> p &*& [1/2]*p |-> 42 &*& ref_end_token::<i32>(p, &x, 1/2) &*& ref_initialized::<i32>(p);
// Ref init check succeeds: ref_initialized(p) exists.
let z = &x;
//@ assert [1/2]x |-> 42 &*& y |-> p &*& z |-> ?q &*& [1/2]*p |-> 42 &*& ref_init_perm(q, &x) &*& ref_end_token(p, &x, 1/2) &*& ref_initialized(p);
//@ init_ref(q, 1/2);
//@ assert y |-> p &*& z |-> q &*& [1/2]*p |-> 42 &*& [1/2]*q |-> 42 &*& ref_end_token(p, &x, 1/2) &*& ref_end_token(q, &x, 1/2) &*& ref_initialized(p) &*& ref_initialized(q);
// Ref init check succeeds: ref_initialized(q) exists.
print(*y);
print(*z);
//@ end_ref(p);
//@ assert [1/2]x |-> 42 &*& y |-> p &*& z |-> q &*& [1/2]*q |-> 42 &*& ref_end_token(q, &x, 1/2) &*& ref_initialized(q);
//@ end_ref(q);
//@ assert x |-> 42 &*& y |-> p &*& z |-> q;
x += 1;
//@ assert x |-> 43 &*& y |-> p &*& z |-> q;
```

## Function arguments

For each function argument `p` of shared reference type, some fraction of the `ref_initialized(p)` token is consumed for the duration of the call.

### Compound function arguments

The [Rustonomicon](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) says

<blockquote>When a reference (but not a Box!) is passed to a function, it is live at least as long as that function call, again except if the `&T` contains an `UnsafeCell<U>`.
All this also applies when values of these types are passed in a (nested) field of a compound type, but not behind pointer indirections.</blockquote>

Since structs may be abstraction boundaries, we introduce a multi-step process. Before the first (non-ghost) instruction of a function, for each argument value `v` of type T a `protected::<T>(v, ?info)` chunk is consumed. `info` is of type `frac_tree = ft_unit | ft_single(real) | ft_pair(frac_tree, frac_tree)`. This chunk can be obtained as follows:

- If `v` is a simple scalar value (like `i32`), `protect_scalar(v)` produces `protected(v, ft_unit)`.
- If `v` is a mutable reference, `protect_ref_mut(v, frac)` consumes `[frac]ref_mut_end_token(v, _)` and produces `protected(v, ft_single(frac))`.
- If `v` is a shared reference, `protect_ref(v, frac)` consumes `[frac]ref_initialized(v)` and produces `protected(v, ft_single(frac))`.
- If `v` is a struct with two fields, with values `v1` and `v2`, `protect_struct(v)` consumes `protected(v1, ?info1)` and `protected(v2, ?info2)` and produces `protected(v, ft_pair(info1, info2))`. (This generalizes straightforwardly to structs with a different number of fields.)

After the last (non-ghost) instruction before a function returns, these chunks are produced again. Ghost commands `unprotect_ref`, `unprotect_ref_mut`, and `unprotect_struct` are the inverse of the corresponding `protect_XYZ` commands and can be used to recover the `ref_mut_end_token` and `ref_initialized` fractions consumed by the protection process.

# Shared references to structs

If `T` is a struct, ghost command `open_ref_init_perm::<T>(p)` consumes `ref_init_perm::<T>(p, ?x)` and produces `ref_init_perm::<Ti>(&(*p).fi, &(*x).fi)` for each field `fi` of type `Ti` of struct `T` whose type is not of the form `UnsafeCell<_>`. Ghost command `close_ref_initialized::<T>(p)` where `T` is a struct consumes `ref_initialized::<Ti>(&(*p).fi)` for each field `fi` of struct `T` whose type is not of the form `UnsafeCell<_>` and produces `ref_initialized::<T>(p)`.

Ghost command `open_ref_initialized(p)` where `p` is of type `&T` and `T` is a struct consumes `ref_initialized(p)` and produces `ref_initialized(&(*p).fi)` for each field `fi` of struct `T` whose type is not of the form `UnsafeCell<_>`.

### Example (no UnsafeCell)

Consider the following piece of Rust code:
```rust
mod points {

    pub struct Point { x: i32, y: i32 }

    impl Point {
        pub fn new() -> Point {
            Point { x: 13, y: 31 }
        }
        pub fn print(&self) {
            print(self.x);
            print(self.y);
        }
        pub fn flip(&mut self) {
            std::mem::swap(&mut self.x, &mut self.y);
        }
    }

}

use points::*;

let a = Point::new();
let b = &a;
let c = &a;
b.print();
c.print();
a.flip();
```
Notice that the internal structure of struct Point is not visible to the client code; the client code's proof should therefore not depend on struct Point's internal structure.

Here's how to verify this program under the proposed approach. (Note: for simplicity, we're not using the lifetime logic here. Also, we're not bothering to specify functional correctness properties; we're just verifying absence of Undefined Behavior.)
```rust
mod points {

    pub struct Point { x: i32, y: i32 }

    /*@
    pred Point_share(p: *Point) = p.x |-> _ &*& p.y |-> _;
    pred end_ref_Point_token(p: *Point, a: *Point, frac: real) = end_ref_token(&(*p).x, &(*a).x, frac) &*& end_ref_token(&(*p).y, &(*a).y, frac);

    lem init_ref_Point(p: *Point, a: *Point, frac: real)
        req ref_init_perm::<Point>(p, a) &*& [frac]a |-> _;
        ens ref_initialized::<Point>(p) &*& [frac]Point_share(p) &*& end_ref_Point_token(p, a, frac);
    {
        open_ref_init_perm(p);
        open [frac]a |-> _;
        ref_init(&(*p).x, frac);
        ref_init(&(*p).y, frac);
        close_ref_initialized(p);
    }
    lem end_ref_Point(p: *Point)
        req end_ref_Point_token(p, ?a, ?frac) &*& [frac]Point_share(p) &*& ref_initialized(p);
        ens [frac]a |-> _;
    {
        open_ref_initialized(p);
        end_ref(&(*p).x);
        end_ref(&(*p).y);
        close [frac]a |-> _;
    }
    @*/

    impl Point {
        pub fn new() -> Point {
            Point { x: 13, y: 31 }
        }
        pub fn print(&self)
        //@ req [?frac]Point_share(self);
        //@ ens [frac]Point_share(self);
        {
            print(self.x);
            print(self.y);
        }
        pub fn flip(&mut self)
        //@ req *self |-> _;
        //@ ens *self |-> _;
        {
            std::mem::swap(&mut self.x, &mut self.y);
        }
    }

}

use points::*;

let a = Point::new();
//@ assert a |-> _;
let b = &a;
//@ assert a |-> _ &*& b |-> ?p &*& ref_init_perm::<Point>(p, &a);
//@ init_ref_Point(p, &a, 1/2);
//@ assert [1/2]a |-> _ &*& b |-> p &*& [1/2]Point_share(p) &*& ref_initialized(p) &*& end_ref_Point_token(p, &a, 1/2);
// Ref init check succeeds: ref_initialized(p) exists.
let c = &a;
//@ assert [1/2]a |-> _ &*& b |-> p &*& c |-> ?q &*& [1/2]Point_share(p) &*& ref_initialized(p) &*& end_ref_Point_token(p, &a, 1/2) &*& ref_init_perm(q, &a);
//@ init_ref_Point(q, &a, 1/2);
//@ assert b |-> p &*& c |-> q &*& [1/2]Point_share(p) &*& [1/2]Point_share(q) &*& ref_initialized(p) &*& ref_initialized(q) &*& end_ref_Point_token(p, &a, 1/2) &*& end_ref_Point_token(q, &a, 1/2);
// Ref init check succeeds: ref_initialized(q) exists.
b.print();
c.print();
//@ end_ref_Point(b);
//@ end_ref_Point(c);
//@ assert a |-> _ &*& b |-> p &*& c |-> q;
a.flip();
//@ assert a |-> _ &*& b |-> p &*& c |-> q;
```

## UnsafeCell

If `x` is of type `&mut T`, the symbolic evaluation of `& *x` also produces the pure fact `ref_origin(p) == x`. If `x` is of type `&T`, it produces the pure fact that `ref_origin(p) == ref_origin(x)`. If `p` is not a shared reference, we have `ref_origin(p) == p`.

`UnsafeCell::get(p)` returns `ref_origin(p)`. `open_ref_init_perm` propagates this to the fields of a struct.

### Example

Consider the following Rust program:
```rust
module cell {

    pub struct Cell<T> { value: UnsafeCell<T> }

    impl<T> Cell<T> {
        fn new(value: T) -> Cell<T> {
            Cell { value: UnsafeCell::new(value) }
        }
        fn replace(&self, mut other: T) -> T {
            std::mem::swap(&mut *(*self).value.get(), &mut other);
            other
        }
    }

}

use cell::*;

let x = Cell::new(42);
let y = &x;
let z = &x;
y.replace(24);
z.replace(31);
```
Here's how to verify it:
```rust
module cell {

    pub struct Cell<T> { value: UnsafeCell<T> }

    /*@
    pred Cell_share_core<T>(t: thread_id_t, value: *T) = nonatomic_inv(t, *value |-> _);
    pred Cell_share<T>(t: thread_id_t, cell: *Cell<T>) = Cell_share_core(t, ref_origin(&(*cell).value));
    pred ref_Cell_end_token<T>(p: *Cell<T>, x: *Cell<T>, frac: real) = ref_origin(p) == ref_origin(x);
    lem share_Cell<T>(x: *Cell<T>)
        req thread_token(?t) &*& *ref_origin(x) |-> _;
        ens thread_token(t) &*& Cell_share(t, x);
    {
        create_nonatomic_inv(t, &(*cell).value |-> _);
    }
    lem unshare_Cell<T>(x: *Cell<T>)
        req thread_token(?t) &*& Cell_share(t, x);
        ens thread_token(t) &*& *ref_origin(x) |-> _;
    {
        destroy_nonatomic_inv();
    }
    lem init_ref_Cell<T>(p: *Cell<T>, x: *Cell<T>, frac: real)
        req thread_token(?t) &*& [frac]Cell_share(t, x) &*& ref_init_token(p, x);
        ens thread_token(t) &*& [frac]Cell_share(t, p) &*& ref_initialized(p) &*& ref_Cell_end_token(p, x, frac);
    {
        open_ref_init_token(p);
        close_ref_initialized(p);
    }
    lem end_ref_Cell<T>(p: *Cell<T>)
        req thread_token(?t) &*& ref_Cell_end_token(p, ?x, ?frac) &*& [frac]Cell_share(t, p);
        ens thread_token(t) &*& [frac]Cell_share(t, x);
    {
    }
    @*/

    impl<T> Cell<T> {
        fn new(value: T) -> Cell<T> {
            Cell { value: UnsafeCell::new(value) }
        }
        fn replace(&self, mut other: T) -> T
        //@ req thread_token(?t) &*& [?frac]Cell_share(t, self);
        //@ ens thread_token(t) &*& [frac]Cell_share(t, self);
        {
            //@ open_nonatomic_inv();
            std::mem::swap(&mut *(*self).value.get(), &mut other);
            //@ close_nonatomic_inv();
            other
        }
    }

}

use cell::*;

let x = Cell::new(42);
//@ assert thread_token(?t) &*& x |-> _ &*& ref_origin(&x) == &x;
let y = &x;
//@ assert thread_token(t) &*& x |-> _ &*& y |-> ?p &*& ref_init_perm::<Cell<i32>>(p, &x) &*& ref_origin(p) == &x;
//@ share_Cell(&x);
//@ assert thread_token(t) &*& Cell_share(t, &x) &*& y |-> p &*& ref_init_perm(p, &x);
//@ init_ref_Cell(p, &x, 1/2);
//@ assert thread_token(t) &*& [1/2]Cell_share(t, &x) &*& y |-> p &*& [1/2]Cell_share(t, p) &*& ref_initialized(p) &*& ref_Cell_end_token(p, &x, 1/2);
// Ref init check succeeds: ref_initialized(p) exists.
let z = &x;
//@ assert thread_token(t) &*& [1/2]Cell_share(t, &x) &*& y |-> p &*& z |-> ?q &*& [1/2]Cell_share(t, p) &*& ref_initialized(p) &*& ref_Cell_end_token(p, &x, 1/2) &*& ref_init_perm(q, &x) &*& ref_origin(q) == &x;
//@ init_ref_Cell(q, &x, 1/2);
//@ assert thread_token(t) &*& y |-> p &*& z |-> q &*& [1/2]Cell_share(t, p) &*& [1/2]Cell_share(t, q) &*& ref_initialized(p) &*& ref_initialized(q) &*& ref_Cell_end_token(p, &x, 1/2) &*& ref_Cell_end_token(q, &x, 1/2);
// Ref init check succeeds: ref_initialized(q) exists.
y.replace(24);
z.replace(31);
//@ end_ref_Cell(p);
//@ end_ref_Cell(q);
//@ assert thread_token(t) &*& Cell_share(t, &x) &*& y |-> p &*& z |-> q;
//@ unshare_Cell(&x);
//@ assert thread_token(t) &*& x |-> _ &*& y |-> p &*& z |-> q;
```

## Shared references to references

The [Rustonomicon](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) says

<blockquote>Moreover, the bytes pointed to by a shared reference, including transitively through other references (both shared and mutable) and Boxes, are immutable; transitivity includes those references stored in fields of compound types.</blockquote>

If `p` is of type `&T` and `T` is of the form `&U` or `&mut U` or `Box<U>`, ghost command `init_ref(p, frac)` consumes `ref_init_perm::<T>(p, ?x)` and `[frac]*x |-> ?y`, and produces `[frac]*p |-> y` as well as `initializing_ref_ref::<T>(p, x, frac, ?q)` and `ref_init_perm::<U>(q, y)`, and the fact `ref_origin(q) == ref_origin(y)`. `q` is a fresh pointer value with the same address as `y`. It is as if a new shared reference to `y` is being created, but note that there is no way for `q` to ever end up in a program variable so it is never actually used. This simply reuses the mechanism for shared reference initialization to "freeze" recursive references until the original reference is ended.

At this point, `q` must be recursively initialized, producing `ref_initialized::<U>(q)`.

Then, ghost command `finish_init_ref_ref(p)` consumes `initializing_ref_ref::<T>(p, ?x, ?frac, ?q)` and `[1/2]ref_initialized::<U>(q)` and produces `ref_ref_end_token(p, x, frac, q)` and `ref_initialized::<T>(p)`.

This blocks `q` from being ended before `p` is ended.

Ghost command `end_ref_ref(p)` consumes `ref_ref_end_token(p, ?x, ?frac, ?q)` and `ref_initialized::<T>(p)` and produces `[frac]*x |-> y` and `[1/2]ref_initialized::<U>(q)`.

At this point, `q` can also be ended.

# Summary of assertions and ghost commands

## Assertions

| Assertion | Meaning |
|-----------|---------|
| `LHS \|-> RHS` | Denotes exclusive ownership of place LHS and that the place currently stores value RHS |
| `[frac]P` | Denotes a fraction `frac` (a real number greater than zero and not greater than 1) of the ownership asserted by P |
| `ref_mut_end_token(p, x)` | Denotes permission to end the mutable reference `p` which was derived from `x` |
| `init_ref_perm(p, x)` | Denotes permission to initialize shared reference `p` which was derived from `x` |
| `ref_initialized(p)` | Denotes the fact that shared reference `p` has been fully initialized. This implies that any part of `p` that is not inside an `UnsafeCell` is readable (but owning this assertion is neither necessary nor sufficient for a thread to be allowed to read `p`; to do so, it (only) needs a fractional points-to assertion, as usual). |
| `ref_end_token(p, x, frac)` | When combined with `ref_initialized(p)`, denotes permission to end shared reference `p`, which was derived from `x` and which was initialized with a fraction `frac` of `x`. |
| `initializing_ref_ref(p, x, frac, q)` | Denotes that shared reference `p`, derived from `x` and initialized with fraction `frac` of `x`, points to a reference or `Box` `y`. A "virtual" shared reference `q` has been derived from `y` and is being initialized. |
| `ref_ref_end_token(p, x, frac, q)` | Denotes that shared reference `p`, derived from `x` and initialized with fraction `frac` of `x`, points to a reference or `Box` `y`. A "virtual" shared reference `q` has been derived and initialized from `y`. |
| `protected(v, info)` | Denotes that (component of) function argument `v` has been protected against being ended before the end of the function call. |

## Ghost commands

| Ghost command | Effect |
|---------------|--------|
| `end_ref_mut(p)` | Consumes `ref_mut_end_token(p, ?x, ?frac)` and `*p \|-> ?v` and produces `*x \|-> v` |
| `init_ref(p, frac)` | Applicable if `p` is of type `&T` where `T` is a simple scalar primitive type (like `i32`). Consumes `ref_init_perm(p, ?x)` and `[frac]*x \|-> ?v` and produces `[frac]*p \|-> v` and `ref_initialized(p)` and `ref_end_token(p, x, frac)`. |
| `open_ref_init_perm(p)` | Applicable if `p` is of type `&T` where `T` is a struct. Consumes `ref_init_perm(p, ?x)` and, for each field `fi` of T whose type is not of the form `UnsafeCell<_>`, produces `ref_init_perm(&(*p).fi, &(*x).fi)`. |
| `close_ref_initialized(p)` | Applicable if `p` is of type `&T` where `T` is a struct. Consumes, for each field `fi` of T whose type is not of the form `UnsafeCell<_>`, `ref_initialized(&(*p).fi)`, and produces `ref_initialized(p)`. |
| `open_ref_initialized(p)` | Applicable if `p` is of type `&T` where `T` is a struct. Consumes `ref_initialized(p)` and produces, for each field `fi` of T whose type is not of the form `UnsafeCell<_>`, `ref_initialized(&(*p).fi)`. |
| `end_ref(p)` | Applicable if `p` is of type `&T` where `T` is a simple scalar primitive type. Consumes `ref_initialized(p)` and `ref_end_token(p, ?x, ?frac)` and `[frac]*p \|-> ?v` and produces `[frac]*x \|-> v`. |
| `finish_init_ref_ref(p)` | Consumes `initializing_ref_ref::<T>(p, ?x, ?frac, ?q)` and `[1/2]ref_initialized::<U>(q)` and produces `ref_ref_end_token(p, x, frac, q)` and `ref_initialized::<T>(p)`. |
| `end_ref_ref(p)` | Consumes `ref_ref_end_token(p, ?x, ?frac, ?q)` and `ref_initialized::<T>(p)` and produces `[frac]*x \|-> y` and `[1/2]ref_initialized::<U>(q)`. |
| `protect_scalar(v)` | Applicable if `v` is of simple scalar type (e.g. `i32`). Produces `protected(v, ft_unit)`. |
| `protect_ref_mut(v, frac)` | Applicable if `v` is a mutable reference. Consumes `[frac]ref_mut_end_token(v, _)` and produces `protected(v, ft_single(frac))`. |
| `protect_ref(v, frac)` | Applicable if `v` is a shared reference. Consumes `[frac]ref_initialized(v)` and produces `protected(v, ft_single(frac))`. |
| `protect_struct(v)` | Applicable if `v` is a struct. Consumes `protected(vi, ?infoi)` for each component `vi` of `v`, and produces `protected(v, ft_pair(info1, ft_pair(info2, ... ft_unit ...)))`. |
| `unprotect_ref_mut(v)` | Applicable if `v` is a mutable reference. Consumes `protected(v, ft_single(?frac))` and produces `[frac]ref_mut_end_token(v, _)`. |
| `unprotect_ref(v)` | Applicable if `v` is a shared reference. Consumes `protected(v, ft_single(?frac))` and produces `[frac]ref_initialized(v)`. |
| `unprotect_struct(v)` | Applicable if `v` is a struct. Consumes `protected(v, ft_pair(?info1, ft_pair(?info2, ...)))` and produces, for each component value `vi` of `v`, `protected(vi, infoi)`. |

# Verifying the borrow checker

The above ghost commands can be applied manually by the user when verifying Rust modules using VeriFast. But what about safe Rust code not verified using VeriFast, i.e. verified only by the Rust borrow checker?

In particular, when the user defines a struct with a custom RustBelt type interpretation, it must be checked that it is compatible with unverified clients creating shared references to instances of that struct. In particular, the SHR predicate must support this. To enforce this, for each such struct T, the user must define a lemma `init_ref_T`, defined as follows:

```
pred_ctor ref_initialized_<T>(p: *T)() = ref_initialized(p);

lem init_ref_T(p: *T, x: *T)
    requires [_]T_share(?k, ?t, x) &*& [?q]lifetime_token(k) &*& ref_init_perm(p, x);
    ensures [q]lifetime_token(k) &*& [_]T_share(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{ ... }
```

This rules out, for example, that the SHR predicate at `x` asserts full permission for `x` in an invariant, unless an `UnsafeCell` is involved. Note: proving such a lemma generally requires a lifetime logic axiom `frac-acc-strong` similar to `bor-acc-strong`, to allow stealing some permissions at `x` and transferring them to `p`, provided they are transferred back to `x` when the lifetime ends. During the "restoring viewshift" that is run when the lifetime ends, the ghost commands for ending the shared reference must be executed.

Note: `ref_initialized(p)` must be available when this happens. But it must also be available to the client when it passes the shared reference as an argument in a function call, because a fraction of the `ref_initialized(p)` chunk is consumed temporarily by Tree Borrows at the call site. Therefore, it must be produced in a separate fractured borrow at the same lifetime.

## frac-acc-strong

For reference, recall the definition of `open_full_borrow_strong` and `close_full_borrow_strong`:

```
// LftL-bor-acc-strong
pred close_full_borrow_token_strong(k1: lifetime_t, P: pred(), q: real, k: lifetime_t);

lem open_full_borrow_strong(k: lifetime_t, P: pred(), q: real) -> lifetime_t;
    nonghost_callers_only
    req full_borrow(k, P) &*& [q]lifetime_token(k);
    ens lifetime_inclusion(k, result) == true &*& P() &*& close_full_borrow_token_strong(result, P, q, k);

lem_type full_borrow_convert_strong(Ctx: pred(), Q: pred(), k1: lifetime_t, P: pred()) = lem();
    req Ctx() &*& Q() &*& [_]lifetime_dead_token(k1); // Empty mask
    ens P();

lem close_full_borrow_strong(k1: lifetime_t, P: pred(), Q: pred());
    nonghost_callers_only
    req close_full_borrow_token_strong(k1, P, ?q, ?k) &*& is_full_borrow_convert_strong(?f, ?Ctx, Q, k1, P) &*& Ctx() &*& Q();
    ens full_borrow(k1, Q) &*& [q]lifetime_token(k) &*& is_full_borrow_convert_strong(f, Ctx, Q, k1, P);
```

(TODO: extend this definition so that a user mask is available in the restoring viewshift.)

It seems like the following variant for fractured borrows would be sound:

```
// LftL-frac-acc-strong (does not exist in RustBelt!)
pred close_frac_borrow_token_strong(k1: lifetime_t, P: pred(;), q: real, k: lifetime_t, f: real);

lem open_frac_borrow_strong(k: lifetime_t, P: pred(;), q: real) -> lifetime_t;
    nonghost_callers_only
    req [_]frac_borrow(k, P) &*& [q]lifetime_token(k);
    ens lifetime_inclusion(k, result) == true &*& [?f]P() &*& close_frac_borrow_token_strong(result, P, q, k, f);

lem_type frac_borrow_convert_strong(Ctx: pred(), Q: pred(), k1: lifetime_t, f: real, P: pred()) = lem();
    req Ctx() &*& Q() &*& [_]lifetime_dead_token(k1); // Empty mask
    ens [f]P();

lem close_frac_borrow_strong(k1: lifetime_t, P: pred(;), Q: pred());
    nonghost_callers_only
    req close_frac_borrow_token_strong(k1, P, ?q, ?k, ?f) &*& is_frac_borrow_convert_strong(?c, ?Ctx, Q, k1, f, P) &*& Ctx() &*& Q();
    ens full_borrow(k1, Q) &*& [q]lifetime_token(k) &*& is_frac_borrow_convert_strong(c, Ctx, Q, k1, f, P);
```

Notice that it produces a full borrow. To prove `init_ref_T`, one would split this full borrow into a part that is turned into a fractured borrow and that goes into the SHR predicate at `p`, and the `ref_initialized` token that is also turned into a fractured borrow.

## The meaning of references in RustBelt

In conclusion, the meaning of mutable and shared references in RustBelt must be updated slightly, so that any recipient can pass the reference as an argument in a function call:
- The meaning of a mutable reference `p : &mut 'a T` at thread `t` changes as follows:
  - from `full_borrow(a, full_borrow_content::<T>(t, p))`
  - to `full_borrow(a, full_borrow_content::<T>(t, p)) &*& [_]frac_borrow(a, ref_mut_end_token_(p))`.
- The meaning of a shared reference `p : &'a T` at thread `t` changes as follows:
  - from `[_]T_share(a, t, p)`
  - to `[_]T_share(a, t, p) &*& [_]frac_borrow(a, ref_initialized_(p))`.

## Protection of structs

For each struct S with a user-defined OWN predicate, the following proof obligation must be proven to ensure values of S can be passed as arguments to unverified typechecked functions:

```
lem protect_S(k: lifetime_t, t: thread_id_t, v: S)
    req <S>.own(t, v) &*& type_outlives_lifetime::<S>(k) == true;
    ens <S>.own(t, v) &*& [_]frac_borrow(k, protected_(v));
```

That is, from the OWN predicate we must be able to derive a `protected(v, _)` fact that lives as long as the function call to which the `S` value is passed (which is necessarily a lifetime included in the lifetimes involved in type S). Notice that this is trivially the case if `S` has the default interpretation, given the meaning of references defined above, where a value `p` of type `&'a mut T` travels with a `[_]frac_borrow(a, ref_mut_end_token_(p))` and a value `p` of type `&'a T` travels with a `[_]frac_borrow(a, ref_initialized_(p))`.

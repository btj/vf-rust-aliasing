An approach for verifying compliance with Tree Borrows in VeriFast
==================================================================

For Tree Borrows, see the work by [Neven Villani and Ralf Jung](https://perso.crans.org/vanille/treebor/index.html).

# Mutable references

In VeriFast, currently, the expression `&mut *x` simply evaluates to `x`. In this proposal, instead it will evaluate to a fresh pointer value `p` (whose address equals that of `x` but whose provenance is different). (The range of valid addresses of the new provenance equals that of the old one, though.) This means existing heap chunks do not provide any access via the new pointer `p`. Therefore, symbolic evaluation of this expression also consumes the (full) points-to chunk at `x` and produces it at `p`. Furthermore, it produces a `ref_mut_end_token(p, x)`. A ghost command `end_ref_mut(p)` consumes the `ref_mut_end_token(p, ?x)` and `*p |-> ?v` and produces `*x |-> v`.

## Function arguments

Tree Borrows says that references passed as function arguments must not become disabled while the function call executes. We can enforce this for mutable references by temporarily consuming, at the call site, some fraction of `ref_mut_end_token` for each argument that is a mutable reference for the duration of the call. (Note: it does not work to temporarily consume this chunk fully, because the same reference may be passed as an argument to any number of nested function calls.)

# Shared references

Symbolically evaluating the expression `& *x`, where `*x` is of type `T`, evaluates to a fresh pointer value `p` and produces a `ref_init_perm::<T>(p, x)`. If `T` is a simple primitive scalar type (e.g. `i32`), ghost command `init_ref(p, frac)` consumes `ref_init_perm::<T>(p, ?x)` and `[frac]*x |-> ?v` and produces `[frac]*p |-> v` as well as `ref_end_token::<T>(p, x, frac)` and `ref_initialized::<T>(p)`. If `T` is a struct, ghost command `open_ref_init_perm::<T>(p)` consumes `ref_init_perm::<T>(p, ?x)` and produces `ref_init_perm::<Ti>(&(*p).fi, &(*x).fi)` for each field `fi` of type `Ti` of struct `T` whose type is not of the form `UnsafeCell<_>`. Ghost command `close_ref_initialized::<T>(p)` where `T` is a struct consumes `ref_initialized::<Ti>(&(*p).fi)` for each field `fi` of struct `T` and produces `ref_initialized::<T>(p)`.

(Note, occurrences of `&` inside assertions simply denote the pure address-of operator, not the mutable/shared reference creation operator.)

VeriFast will check that `ref_initialized::<T>(p)` exists before the next (non-ghost) instruction following the `& *x` instruction is executed. (Indeed, Tree Borrows requires that shared references be readable immediately upon creation.)

## UnsafeCell

If `x` is of type `&mut T`, the symbolic evaluation of `& *x` also produces the pure fact `ref_origin(p) == x`. If `x` is of type `&T`, it produces the pure fact that `ref_origin(p) == ref_origin(x)`. `UnsafeCell::get(p)` returns `ref_origin(p)`.

## Ending a shared reference

Ghost command `open_ref_initialized(p)` where `p` is of type `&T` and `T` is a struct consumes `ref_initialized(p)` and produces `ref_initialized(&(*p).fi)` for each field `fi` of struct `T` whose type is not of the form `UnsafeCell<_>`.

Ghost command `end_ref(p)`, where `p` is of type `&T` and `T` is a simple primitive scalar type, consumes `ref_initialized(p)` and `ref_end_token(p, ?x, ?frac)` and `[frac]*p |-> ?v` and produces `[frac]*x |-> v`.

## Function arguments

For each function argument `p` of shared reference type, some fraction of the `ref_initialized(p)` token is consumed for the duration of the call.

# Verifying the borrow checker

The above ghost commands can be applied manually by the user when verifying Rust modules using VeriFast. But what about safe Rust code not verified using VeriFast, i.e. verified only by the Rust borrow checker?

In particular, when the user defines a struct with a custom RustBelt type interpretation, it must be checked that it is compatible with unverified clients creating shared references to instances of that struct. In particular, the SHR predicate must support this. To enforce this, for each such struct T, the user must define a lemma `init_ref_T`, defined as follows:

```
lemma void init_ref_T(p: *T, x: *T)
    requires [_]T_share(?k, ?t, x) &*& ref_init_perm(p, x);
    ensures [_]T_share(k, t, p) &*& ref_initialized(p);
{ ... }
```

This rules out, for example, that the SHR predicate at `x` asserts full permission for `x` in an invariant, unless an `UnsafeCell` is involved. Note: proving such a lemma generally requires a lifetime logic axiom `frac-acc-strong` similar to `bor-acc-strong`, to allow stealing some permissions at `x` and transferring them to `p`, provided they are transferred back to `x` when the lifetime ends. During the "restoring viewshift" that is run when the lifetime ends, the ghost commands for ending the shared reference must be executed. Note: `ref_initialized(p)` must be available when this happens. (Maybe `ref_initialized` should be inside the borrow?)
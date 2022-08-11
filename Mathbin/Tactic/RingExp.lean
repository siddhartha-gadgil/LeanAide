/-
Copyright (c) 2019 Tim Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baanen
-/
import Mathbin.Tactic.NormNum
import Mathbin.Control.Traversable.Basic

/-!
# `ring_exp` tactic

A tactic for solving equations in commutative (semi)rings,
where the exponents can also contain variables.

More precisely, expressions of the following form are supported:
- constants (non-negative integers)
- variables
- coefficients (any rational number, embedded into the (semi)ring)
- addition of expressions
- multiplication of expressions
- exponentiation of expressions (the exponent must have type `ℕ`)
- subtraction and negation of expressions (if the base is a full ring)

The motivating example is proving `2 * 2^n * b = b * 2^(n+1)`,
something that the `ring` tactic cannot do, but `ring_exp` can.

## Implementation notes

The basic approach to prove equalities is to normalise both sides and check for equality.
The normalisation is guided by building a value in the type `ex` at the meta level,
together with a proof (at the base level) that the original value is equal to
the normalised version.
The normalised version and normalisation proofs are also stored in the `ex` type.

The outline of the file:
- Define an inductive family of types `ex`, parametrised over `ex_type`,
  which can represent expressions with `+`, `*`, `^` and rational numerals.
  The parametrisation over `ex_type` ensures that associativity and distributivity are applied,
  by restricting which kinds of subexpressions appear as arguments to the various operators.
- Represent addition, multiplication and exponentiation in the `ex` type,
  thus allowing us to map expressions to `ex` (the `eval` function drives this).
  We apply associativity and distributivity of the operators here (helped by `ex_type`)
  and commutativity as well (by sorting the subterms; unfortunately not helped by anything).
  Any expression not of the above formats is treated as an atom (the same as a variable).

There are some details we glossed over which make the plan more complicated:
- The order on atoms is not initially obvious.
  We construct a list containing them in order of initial appearance in the expression,
  then use the index into the list as a key to order on.
- In the tactic, a normalized expression `ps : ex` lives in the meta-world,
  but the normalization proofs live in the real world.
  Thus, we cannot directly say `ps.orig = ps.pretty` anywhere,
  but we have to carefully construct the proof when we compute `ps`.
  This was a major source of bugs in development!
- For `pow`, the exponent must be a natural number, while the base can be any semiring `α`.
  We swap out operations for the base ring `α` with those for the exponent ring `ℕ`
  as soon as we deal with exponents.
  This is accomplished by the `in_exponent` function and is relatively painless since
  we work in a `reader` monad.
- The normalized form of an expression is the one that is useful for the tactic,
  but not as nice to read. To remedy this, the user-facing normalization calls `ex.simp`.

## Caveats and future work

Subtraction cancels out identical terms, but division does not.
That is: `a - a = 0 := by ring_exp` solves the goal,
but `a / a := 1 by ring_exp` doesn't.
Note that `0 / 0` is generally defined to be `0`,
so division cancelling out is not true in general.

Multiplication of powers can be simplified a little bit further:
`2 ^ n * 2 ^ n = 4 ^ n := by ring_exp` could be implemented
in a similar way that `2 * a + 2 * a = 4 * a := by ring_exp` already works.
This feature wasn't needed yet, so it's not implemented yet.

## Tags

ring, semiring, exponent, power
-/


-- The base ring `α` will have a universe level `u`.
-- We do not introduce `α` as a variable yet,
-- in order to make it explicit or implicit as required.
universe u

namespace Tactic.RingExp

open Nat

/-- The `atom` structure is used to represent atomic expressions:
those which `ring_exp` cannot parse any further.

For instance, `a + (a % b)` has `a` and `(a % b)` as atoms.
The `ring_exp_eq` tactic does not normalize the subexpressions in atoms,
but `ring_exp` does if `ring_exp_eq` was not sufficient.

Atoms in fact represent equivalence classes of expressions,
modulo definitional equality.
The field `index : ℕ` should be a unique number for each class,
while `value : expr` contains a representative of this class.
The function `resolve_atom` determines the appropriate atom
for a given expression.
-/
unsafe structure atom : Type where
  value : expr
  index : ℕ

namespace Atom

/-- The `eq` operation on `atom`s works modulo definitional equality,
ignoring their `value`s.
The invariants on `atom` ensure indices are unique per value.
Thus, `eq` indicates equality as long as the `atom`s come from the same context.
-/
unsafe def eq (a b : atom) : Bool :=
  a.index = b.index

/-- We order `atom`s on the order of appearance in the main expression.
-/
unsafe def lt (a b : atom) : Bool :=
  a.index < b.index

unsafe instance : HasRepr atom :=
  ⟨fun x => "(atom " ++ reprₓ x.2 ++ ")"⟩

end Atom

section Expression

/-!
### `expression` section

In this section, we define the `ex` type and its basic operations.

First, we introduce the supporting types `coeff`, `ex_type` and `ex_info`.
For understanding the code, it's easier to check out `ex` itself first,
then refer back to the supporting types.

The arithmetic operations on `ex` need additional definitions,
so they are defined in a later section.
-/


/-- Coefficients in the expression are stored in a wrapper structure,
allowing for easier modification of the data structures.
The modifications might be caching of the result of `expr.of_rat`,
or using a different meta representation of numerals.
-/
structure Coeff : Type where
  value : ℚ
  deriving DecidableEq, Inhabited

/-- The values in `ex_type` are used as parameters to `ex` to control the expression's structure. -/
inductive ExType : Type
  | base : ex_type
  | Sum : ex_type
  | Prod : ex_type
  | exp : ex_type
  deriving DecidableEq, Inhabited

open ExType

/-- Each `ex` stores information for its normalization proof.

The `orig` expression is the expression that was passed to `eval`.

The `pretty` expression is the normalised form that the `ex` represents.
(I didn't call this something like `norm`, because there are already
too many things called `norm` in mathematics!)

The field `proof` contains an optional proof term of type `%%orig = %%pretty`.
The value `none` for the proof indicates that everything reduces to reflexivity.
(Which saves space in quite a lot of cases.)
-/
unsafe structure ex_info : Type where
  orig : expr
  pretty : expr
  Proof : Option expr

/-- The `ex` type is an abstract representation of an expression with `+`, `*` and `^`.
Those operators are mapped to the `sum`, `prod` and `exp` constructors respectively.

The `zero` constructor is the base case for `ex sum`, e.g. `1 + 2` is represented
by (something along the lines of) `sum 1 (sum 2 zero)`.

The `coeff` constructor is the base case for `ex prod`, and is used for numerals.
The code maintains the invariant that the coefficient is never `0`.

The `var` constructor is the base case for `ex exp`, and is used for atoms.

The `sum_b` constructor allows for addition in the base of an exponentiation;
it serves a similar purpose as the parentheses in `(a + b)^c`.
The code maintains the invariant that the argument to `sum_b` is not `zero`
or `sum _ zero`.

All of the constructors contain an `ex_info` field,
used to carry around (arguments to) proof terms.

While the `ex_type` parameter enforces some simplification invariants,
the following ones must be manually maintained at the risk of insufficient power:
- the argument to `coeff` must be nonzero (to ensure `0 = 0 * 1`)
- the argument to `sum_b` must be of the form `sum a (sum b bs)` (to ensure `(a + 0)^n = a^n`)
- normalisation proofs of subexpressions must be `refl ps.pretty`
- if we replace `sum` with `cons` and `zero` with `nil`, the resulting list is sorted
  according to the `lt` relation defined further down; similarly for `prod` and `coeff`
  (to ensure `a + b = b + a`).

The first two invariants could be encoded in a subtype of `ex`,
but aren't (yet) to spare some implementation burden.
The other invariants cannot be encoded because we need the `tactic` monad to check them.
(For example, the correct equality check of `expr` is `is_def_eq : expr → expr → tactic unit`.)
-/
unsafe inductive ex : ExType → Type
  | zero (info : ex_info) : ex Sum
  | Sum (info : ex_info) : ex Prod → ex Sum → ex Sum
  | coeff (info : ex_info) : Coeff → ex Prod
  | Prod (info : ex_info) : ex exp → ex Prod → ex Prod
  | var (info : ex_info) : atom → ex base
  | sum_b (info : ex_info) : ex Sum → ex base
  | exp (info : ex_info) : ex base → ex Prod → ex exp

/-- Return the proof information associated to the `ex`.
-/
unsafe def ex.info : ∀ {et : ExType} (ps : ex et), ex_info
  | Sum, ex.zero i => i
  | Sum, ex.sum i _ _ => i
  | Prod, ex.coeff i _ => i
  | Prod, ex.prod i _ _ => i
  | base, ex.var i _ => i
  | base, ex.sum_b i _ => i
  | exp, ex.exp i _ _ => i

/-- Return the original, non-normalized version of this `ex`.

Note that arguments to another `ex` are always "pre-normalized":
their `orig` and `pretty` are equal, and their `proof` is reflexivity.
-/
unsafe def ex.orig {et : ExType} (ps : ex et) : expr :=
  ps.info.orig

/-- Return the normalized version of this `ex`.
-/
unsafe def ex.pretty {et : ExType} (ps : ex et) : expr :=
  ps.info.pretty

/-- Return the normalisation proof of the given expression.
If the proof is `refl`, we give `none` instead,
which helps to control the size of proof terms.
To get an actual term, use `ex.proof_term`,
or use `mk_proof` with the correct set of arguments.
-/
unsafe def ex.proof {et : ExType} (ps : ex et) : Option expr :=
  ps.info.Proof

/-- Update the `orig` and `proof` fields of the `ex_info`.
Intended for use in `ex.set_info`.
-/
unsafe def ex_info.set (i : ex_info) (o : Option expr) (pf : Option expr) : ex_info :=
  { i with orig := o.getOrElse i.pretty, Proof := pf }

/-- Update the `ex_info` of the given expression.

We use this to combine intermediate normalisation proofs.
Since `pretty` only depends on the subexpressions,
which do not change, we do not set `pretty`.
-/
unsafe def ex.set_info : ∀ {et : ExType} (ps : ex et), Option expr → Option expr → ex et
  | Sum, ex.zero i, o, pf => ex.zero (i.Set o pf)
  | Sum, ex.sum i p ps, o, pf => ex.sum (i.Set o pf) p ps
  | Prod, ex.coeff i x, o, pf => ex.coeff (i.Set o pf) x
  | Prod, ex.prod i p ps, o, pf => ex.prod (i.Set o pf) p ps
  | base, ex.var i x, o, pf => ex.var (i.Set o pf) x
  | base, ex.sum_b i ps, o, pf => ex.sum_b (i.Set o pf) ps
  | exp, ex.exp i p ps, o, pf => ex.exp (i.Set o pf) p ps

instance coeffHasRepr : HasRepr Coeff :=
  ⟨fun x => reprₓ x.1⟩

/-- Convert an `ex` to a `string`. -/
unsafe def ex.repr : ∀ {et : ExType}, ex et → Stringₓ
  | Sum, ex.zero _ => "0"
  | Sum, ex.sum _ p ps => ex.repr p ++ " + " ++ ex.repr ps
  | Prod, ex.coeff _ x => reprₓ x
  | Prod, ex.prod _ p ps => ex.repr p ++ " * " ++ ex.repr ps
  | base, ex.var _ x => reprₓ x
  | base, ex.sum_b _ ps => "(" ++ ex.repr ps ++ ")"
  | exp, ex.exp _ p ps => ex.repr p ++ " ^ " ++ ex.repr ps

unsafe instance {et : ExType} : HasRepr (ex et) :=
  ⟨ex.repr⟩

/-- Equality test for expressions.

Since equivalence of `atom`s is not the same as equality,
we cannot make a true `(=)` operator for `ex` either.
-/
unsafe def ex.eq : ∀ {et : ExType}, ex et → ex et → Bool
  | Sum, ex.zero _, ex.zero _ => true
  | Sum, ex.zero _, ex.sum _ _ _ => false
  | Sum, ex.sum _ _ _, ex.zero _ => false
  | Sum, ex.sum _ p ps, ex.sum _ q qs => p.Eq q && ps.Eq qs
  | Prod, ex.coeff _ x, ex.coeff _ y => x = y
  | Prod, ex.coeff _ _, ex.prod _ _ _ => false
  | Prod, ex.prod _ _ _, ex.coeff _ _ => false
  | Prod, ex.prod _ p ps, ex.prod _ q qs => p.Eq q && ps.Eq qs
  | base, ex.var _ x, ex.var _ y => x.Eq y
  | base, ex.var _ _, ex.sum_b _ _ => false
  | base, ex.sum_b _ _, ex.var _ _ => false
  | base, ex.sum_b _ ps, ex.sum_b _ qs => ps.Eq qs
  | exp, ex.exp _ p ps, ex.exp _ q qs => p.Eq q && ps.Eq qs

/-- The ordering on expressions.

As for `ex.eq`, this is a linear order only in one context.
-/
unsafe def ex.lt : ∀ {et : ExType}, ex et → ex et → Bool
  | Sum, _, ex.zero _ => false
  | Sum, ex.zero _, _ => true
  | Sum, ex.sum _ p ps, ex.sum _ q qs => p.lt q || p.Eq q && ps.lt qs
  | Prod, ex.coeff _ x, ex.coeff _ y => x.1 < y.1
  | Prod, ex.coeff _ _, _ => true
  | Prod, _, ex.coeff _ _ => false
  | Prod, ex.prod _ p ps, ex.prod _ q qs => p.lt q || p.Eq q && ps.lt qs
  | base, ex.var _ x, ex.var _ y => x.lt y
  | base, ex.var _ _, ex.sum_b _ _ => true
  | base, ex.sum_b _ _, ex.var _ _ => false
  | base, ex.sum_b _ ps, ex.sum_b _ qs => ps.lt qs
  | exp, ex.exp _ p ps, ex.exp _ q qs => p.lt q || p.Eq q && ps.lt qs

end Expression

section Operations

/-!
### `operations` section

This section defines the operations (on `ex`) that use tactics.
They live in the `ring_exp_m` monad,
which adds a cache and a list of encountered atoms to the `tactic` monad.

Throughout this section, we will be constructing proof terms.
The lemmas used in the construction are all defined over a commutative semiring α.
-/


variable {α : Type u} [CommSemiringₓ α]

open Tactic

open ExType

/-- Stores the information needed in the `eval` function and its dependencies,
so they can (re)construct expressions.

The `eval_info` structure stores this information for one type,
and the `context` combines the two types, one for bases and one for exponents.
-/
unsafe structure eval_info where
  α : expr
  Univ : level
  -- Cache the instances for optimization and consistency
  csr_instance : expr
  ha_instance : expr
  hm_instance : expr
  hp_instance : expr
  -- Optional instances (only required for (-) and (/) respectively)
  ring_instance : Option expr
  dr_instance : Option expr
  -- Cache common constants.
  zero : expr
  one : expr

/-- The `context` contains the full set of information needed for the `eval` function.

This structure has two copies of `eval_info`:
one is for the base (typically some semiring `α`) and another for the exponent (always `ℕ`).
When evaluating an exponent, we put `info_e` in `info_b`.
-/
unsafe structure context where
  info_b : eval_info
  info_e : eval_info
  transp : Transparency

/-- The `ring_exp_m` monad is used instead of `tactic` to store the context.
-/
unsafe def ring_exp_m (α : Type) : Type :=
  ReaderTₓ context (StateTₓ (List atom) tactic) α deriving Monadₓ, Alternativeₓ

/-- Access the instance cache.
-/
unsafe def get_context : ring_exp_m context :=
  ReaderTₓ.read

/-- Lift an operation in the `tactic` monad to the `ring_exp_m` monad.

This operation will not access the cache.
-/
unsafe def lift {α} (m : tactic α) : ring_exp_m α :=
  ReaderTₓ.lift (StateTₓ.lift m)

/-- Change the context of the given computation,
so that expressions are evaluated in the exponent ring,
instead of the base ring.
-/
unsafe def in_exponent {α} (mx : ring_exp_m α) : ring_exp_m α := do
  let ctx ← get_context
  ReaderTₓ.lift <| mx ⟨ctx, ctx, ctx⟩

/-- Specialized version of `mk_app` where the first two arguments are `{α}` `[some_class α]`.
Should be faster because it can use the cached instances.
-/
unsafe def mk_app_class (f : Name) (inst : expr) (args : List expr) : ring_exp_m expr := do
  let ctx ← get_context
  pure <| (@expr.const tt f [ctx] ctx inst).mk_app args

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `ctx
/-- Specialized version of `mk_app` where the first two arguments are `{α}` `[comm_semiring α]`.
Should be faster because it can use the cached instances.
 -/
unsafe def mk_app_csr (f : Name) (args : List expr) : ring_exp_m expr := do
  let ctx ← get_context
  mk_app_class f (ctx ctx.info_b.csr_instance) args

/-- Specialized version of `mk_app ``has_add.add`.
Should be faster because it can use the cached instances.
-/
unsafe def mk_add (args : List expr) : ring_exp_m expr := do
  let ctx ← get_context
  mk_app_class `` Add.add ctx args

/-- Specialized version of `mk_app ``has_mul.mul`.
Should be faster because it can use the cached instances.
-/
unsafe def mk_mul (args : List expr) : ring_exp_m expr := do
  let ctx ← get_context
  mk_app_class `` Mul.mul ctx args

/-- Specialized version of `mk_app ``has_pow.pow`.
Should be faster because it can use the cached instances.
-/
unsafe def mk_pow (args : List expr) : ring_exp_m expr := do
  let ctx ← get_context
  pure <| (@expr.const tt `` Pow.pow [ctx, ctx] ctx ctx ctx).mk_app args

/-- Construct a normalization proof term or return the cached one. -/
unsafe def ex_info.proof_term (ps : ex_info) : ring_exp_m expr :=
  match ps.Proof with
  | none => lift <| tactic.mk_eq_refl ps.pretty
  | some p => pure p

/-- Construct a normalization proof term or return the cached one. -/
unsafe def ex.proof_term {et : ExType} (ps : ex et) : ring_exp_m expr :=
  ps.info.proof_term

/-- If all `ex_info` have trivial proofs, return a trivial proof.
Otherwise, construct all proof terms.

Useful in applications where trivial proofs combine to another trivial proof,
most importantly to pass to `mk_proof_or_refl`.
-/
unsafe def none_or_proof_term : List ex_info → ring_exp_m (Option (List expr))
  | [] => pure none
  | x :: xs => do
    let xs_pfs ← none_or_proof_term xs
    match (x, xs_pfs) with
      | (none, none) => pure none
      | (some x_pf, none) => do
        let xs_pfs ← traverse ex_info.proof_term xs
        pure (some (x_pf :: xs_pfs))
      | (_, some xs_pfs) => do
        let x_pf ← x
        pure (some (x_pf :: xs_pfs))

/-- Use the proof terms as arguments to the given lemma.
If the lemma could reduce to reflexivity, consider using `mk_proof_or_refl.`
-/
unsafe def mk_proof (lem : Name) (args : List expr) (hs : List ex_info) : ring_exp_m expr := do
  let hs' ← traverse ex_info.proof_term hs
  mk_app_csr lem (args ++ hs')

/-- Use the proof terms as arguments to the given lemma.
Often, we construct a proof term using congruence where reflexivity suffices.
To solve this, the following function tries to get away with reflexivity.
-/
unsafe def mk_proof_or_refl (term : expr) (lem : Name) (args : List expr) (hs : List ex_info) : ring_exp_m expr := do
  let hs_full ← none_or_proof_term hs
  match hs_full with
    | none => lift <| mk_eq_refl term
    | some hs' => mk_app_csr lem (args ++ hs')

/-- A shortcut for adding the original terms of two expressions. -/
unsafe def add_orig {et et'} (ps : ex et) (qs : ex et') : ring_exp_m expr :=
  mk_add [ps.orig, qs.orig]

/-- A shortcut for multiplying the original terms of two expressions. -/
unsafe def mul_orig {et et'} (ps : ex et) (qs : ex et') : ring_exp_m expr :=
  mk_mul [ps.orig, qs.orig]

/-- A shortcut for exponentiating the original terms of two expressions. -/
unsafe def pow_orig {et et'} (ps : ex et) (qs : ex et') : ring_exp_m expr :=
  mk_pow [ps.orig, qs.orig]

/-- Congruence lemma for constructing `ex.sum`. -/
theorem sum_congr {p p' ps ps' : α} : p = p' → ps = ps' → p + ps = p' + ps' := by
  cc

/-- Congruence lemma for constructing `ex.prod`. -/
theorem prod_congr {p p' ps ps' : α} : p = p' → ps = ps' → p * ps = p' * ps' := by
  cc

/-- Congruence lemma for constructing `ex.exp`. -/
theorem exp_congr {p p' : α} {ps ps' : ℕ} : p = p' → ps = ps' → p ^ ps = p' ^ ps' := by
  cc

/-- Constructs `ex.zero` with the correct arguments. -/
unsafe def ex_zero : ring_exp_m (ex Sum) := do
  let ctx ← get_context
  pure <| ex.zero ⟨ctx, ctx, none⟩

/-- Constructs `ex.sum` with the correct arguments. -/
unsafe def ex_sum (p : ex Prod) (ps : ex Sum) : ring_exp_m (ex Sum) := do
  let pps_o ← add_orig p ps
  let pps_p ← mk_add [p.pretty, ps.pretty]
  let pps_pf ← mk_proof_or_refl pps_p `` sum_congr [p.orig, p.pretty, ps.orig, ps.pretty] [p.info, ps.info]
  pure (ex.sum ⟨pps_o, pps_p, pps_pf⟩ (p none none) (ps none none))

/-- Constructs `ex.coeff` with the correct arguments.

There are more efficient constructors for specific numerals:
if `x = 0`, you should use `ex_zero`; if `x = 1`, use `ex_one`.
-/
unsafe def ex_coeff (x : Rat) : ring_exp_m (ex Prod) := do
  let ctx ← get_context
  let x_p ← lift <| expr.of_rat ctx.info_b.α x
  pure (ex.coeff ⟨x_p, x_p, none⟩ ⟨x⟩)

/-- Constructs `ex.coeff 1` with the correct arguments.
This is a special case for optimization purposes.
-/
unsafe def ex_one : ring_exp_m (ex Prod) := do
  let ctx ← get_context
  pure <| ex.coeff ⟨ctx, ctx, none⟩ ⟨1⟩

/-- Constructs `ex.prod` with the correct arguments. -/
unsafe def ex_prod (p : ex exp) (ps : ex Prod) : ring_exp_m (ex Prod) := do
  let pps_o ← mul_orig p ps
  let pps_p ← mk_mul [p.pretty, ps.pretty]
  let pps_pf ← mk_proof_or_refl pps_p `` prod_congr [p.orig, p.pretty, ps.orig, ps.pretty] [p.info, ps.info]
  pure (ex.prod ⟨pps_o, pps_p, pps_pf⟩ (p none none) (ps none none))

/-- Constructs `ex.var` with the correct arguments. -/
unsafe def ex_var (p : atom) : ring_exp_m (ex base) :=
  pure (ex.var ⟨p.1, p.1, none⟩ p)

/-- Constructs `ex.sum_b` with the correct arguments. -/
unsafe def ex_sum_b (ps : ex Sum) : ring_exp_m (ex base) :=
  pure (ex.sum_b ps.info (ps.set_info none none))

/-- Constructs `ex.exp` with the correct arguments. -/
unsafe def ex_exp (p : ex base) (ps : ex Prod) : ring_exp_m (ex exp) := do
  let ctx ← get_context
  let pps_o ← pow_orig p ps
  let pps_p ← mk_pow [p.pretty, ps.pretty]
  let pps_pf ← mk_proof_or_refl pps_p `` exp_congr [p.orig, p.pretty, ps.orig, ps.pretty] [p.info, ps.info]
  pure (ex.exp ⟨pps_o, pps_p, pps_pf⟩ (p none none) (ps none none))

theorem base_to_exp_pf {p p' : α} : p = p' → p = p' ^ 1 := by
  simp

/-- Conversion from `ex base` to `ex exp`. -/
unsafe def base_to_exp (p : ex base) : ring_exp_m (ex exp) := do
  let o ← in_exponent <| ex_one
  let ps ← ex_exp p o
  let pf ← mk_proof `` base_to_exp_pf [p.orig, p.pretty] [p.info]
  pure <| ps p pf

theorem exp_to_prod_pf {p p' : α} : p = p' → p = p' * 1 := by
  simp

/-- Conversion from `ex exp` to `ex prod`. -/
unsafe def exp_to_prod (p : ex exp) : ring_exp_m (ex Prod) := do
  let o ← ex_one
  let ps ← ex_prod p o
  let pf ← mk_proof `` exp_to_prod_pf [p.orig, p.pretty] [p.info]
  pure <| ps p pf

theorem prod_to_sum_pf {p p' : α} : p = p' → p = p' + 0 := by
  simp

/-- Conversion from `ex prod` to `ex sum`. -/
unsafe def prod_to_sum (p : ex Prod) : ring_exp_m (ex Sum) := do
  let z ← ex_zero
  let ps ← ex_sum p z
  let pf ← mk_proof `` prod_to_sum_pf [p.orig, p.pretty] [p.info]
  pure <| ps p pf

theorem atom_to_sum_pf (p : α) : p = p ^ 1 * 1 + 0 := by
  simp

/-- A more efficient conversion from `atom` to `ex sum`.

The result should be the same as `ex_var p >>= base_to_exp >>= exp_to_prod >>= prod_to_sum`,
except we need to calculate less intermediate steps.
-/
unsafe def atom_to_sum (p : atom) : ring_exp_m (ex Sum) := do
  let p' ← ex_var p
  let o ← in_exponent <| ex_one
  let p' ← ex_exp p' o
  let o ← ex_one
  let p' ← ex_prod p' o
  let z ← ex_zero
  let p' ← ex_sum p' z
  let pf ← mk_proof `` atom_to_sum_pf [p.1] []
  pure <| p' p.1 pf

/-- Compute the sum of two coefficients.
Note that the result might not be a valid expression:
if `p = -q`, then the result should be `ex.zero : ex sum` instead.
The caller must detect when this happens!

The returned value is of the form `ex.coeff _ (p + q)`,
with the proof of `expr.of_rat p + expr.of_rat q = expr.of_rat (p + q)`.
-/
unsafe def add_coeff (p_p q_p : expr) (p q : Coeff) : ring_exp_m (ex Prod) := do
  let ctx ← get_context
  let pq_o ← mk_add [p_p, q_p]
  let (pq_p, pq_pf) ← lift <| norm_num.eval_field pq_o
  pure <| ex.coeff ⟨pq_o, pq_p, pq_pf⟩ ⟨p.1 + q.1⟩

theorem mul_coeff_pf_one_mul (q : α) : 1 * q = q :=
  one_mulₓ q

theorem mul_coeff_pf_mul_one (p : α) : p * 1 = p :=
  mul_oneₓ p

/-- Compute the product of two coefficients.

The returned value is of the form `ex.coeff _ (p * q)`,
with the proof of `expr.of_rat p * expr.of_rat q = expr.of_rat (p * q)`.
-/
unsafe def mul_coeff (p_p q_p : expr) (p q : Coeff) : ring_exp_m (ex Prod) :=
  match p.1, q.1 with
  |-- Special case to speed up multiplication with 1.
    ⟨1, 1, _, _⟩,
    _ => do
    let ctx ← get_context
    let pq_o ← mk_mul [p_p, q_p]
    let pf ← mk_app_csr `` mul_coeff_pf_one_mul [q_p]
    pure <| ex.coeff ⟨pq_o, q_p, pf⟩ ⟨q.1⟩
  | _, ⟨1, 1, _, _⟩ => do
    let ctx ← get_context
    let pq_o ← mk_mul [p_p, q_p]
    let pf ← mk_app_csr `` mul_coeff_pf_mul_one [p_p]
    pure <| ex.coeff ⟨pq_o, p_p, pf⟩ ⟨p.1⟩
  | _, _ => do
    let ctx ← get_context
    let pq' ← mk_mul [p_p, q_p]
    let (pq_p, pq_pf) ← lift <| norm_num.eval_field pq'
    pure <| ex.coeff ⟨pq_p, pq_p, pq_pf⟩ ⟨p.1 * q.1⟩

section Rewrite

/-! ### `rewrite` section

In this section we deal with rewriting terms to fit in the basic grammar of `eval`.
For example, `nat.succ n` is rewritten to `n + 1` before it is evaluated further.
-/


/-- Given a proof that the expressions `ps_o` and `ps'.orig` are equal,
show that `ps_o` and `ps'.pretty` are equal.

Useful to deal with aliases in `eval`. For instance, `nat.succ p` can be handled
as an alias of `p + 1` as follows:
```
| ps_o@`(nat.succ %%p_o) := do
  ps' ← eval `(%%p_o + 1),
  pf ← lift $ mk_app ``nat.succ_eq_add_one [p_o],
  rewrite ps_o ps' pf
```
-/
unsafe def rewrite (ps_o : expr) (ps' : ex Sum) (pf : expr) : ring_exp_m (ex Sum) := do
  let ps'_pf ← ps'.info.proof_term
  let pf ← lift <| mk_eq_trans pf ps'_pf
  pure <| ps' ps_o pf

end Rewrite

/-- Represents the way in which two products are equal except coefficient.

This type is used in the function `add_overlap`.
In order to deal with equations of the form `a * 2 + a = 3 * a`,
the `add` function will add up overlapping products,
turning `a * 2 + a` into `a * 3`.
We need to distinguish `a * 2 + a` from `a * 2 + b` in order to do this,
and the `overlap` type carries the information on how it overlaps.

The case `none` corresponds to non-overlapping products, e.g. `a * 2 + b`;
the case `nonzero` to overlapping products adding to non-zero, e.g. `a * 2 + a`
(the `ex prod` field will then look like `a * 3` with a proof that `a * 2 + a = a * 3`);
the case `zero` to overlapping products adding to zero, e.g. `a * 2 + a * -2`.
We distinguish those two cases because in the second, the whole product reduces to `0`.

A potential extension to the tactic would also do this for the base of exponents,
e.g. to show `2^n * 2^n = 4^n`.
-/
unsafe inductive overlap : Type
  | none : overlap
  | nonzero : ex Prod → overlap
  | zero : ex Sum → overlap

theorem add_overlap_pf {ps qs pq} (p : α) : ps + qs = pq → p * ps + p * qs = p * pq := fun pq_pf =>
  calc
    p * ps + p * qs = p * (ps + qs) := symm (mul_addₓ _ _ _)
    _ = p * pq := by
      rw [pq_pf]
    

theorem add_overlap_pf_zero {ps qs} (p : α) : ps + qs = 0 → p * ps + p * qs = 0 := fun pq_pf =>
  calc
    p * ps + p * qs = p * (ps + qs) := symm (mul_addₓ _ _ _)
    _ = p * 0 := by
      rw [pq_pf]
    _ = 0 := mul_zero _
    

/-- Given arguments `ps`, `qs` of the form `ps' * x` and `ps' * y` respectively
return `ps + qs = ps' * (x + y)` (with `x` and `y` arbitrary coefficients).
For other arguments, return `overlap.none`.
-/
unsafe def add_overlap : ex Prod → ex Prod → ring_exp_m overlap
  | ex.coeff x_i x, ex.coeff y_i y => do
    let xy@(ex.coeff _ xy_c) ← add_coeff x_i.pretty y_i.pretty x y |
      lift <| fail "internal error: add_coeff should return ex.coeff"
    if xy_c.1 = 0 then do
        let z ← ex_zero
        pure <| overlap.zero (z xy xy)
      else pure <| overlap.nonzero xy
  | ex.prod _ _ _, ex.coeff _ _ => pure overlap.none
  | ex.coeff _ _, ex.prod _ _ _ => pure overlap.none
  | pps@(ex.prod _ p ps), qqs@(ex.prod _ q qs) =>
    if p.Eq q then do
      let pq_ol ← add_overlap ps qs
      let pqs_o ← add_orig pps qqs
      match pq_ol with
        | overlap.none => pure overlap.none
        | overlap.nonzero pq => do
          let pqs ← ex_prod p pq
          let pf ← mk_proof `` add_overlap_pf [ps, qs, pq, p] [pq]
          pure <| overlap.nonzero (pqs pqs_o pf)
        | overlap.zero pq => do
          let z ← ex_zero
          let pf ← mk_proof `` add_overlap_pf_zero [ps, qs, p] [pq]
          pure <| overlap.zero (z pqs_o pf)
    else pure overlap.none

section Addition

theorem add_pf_z_sum {ps qs qs' : α} : ps = 0 → qs = qs' → ps + qs = qs' := fun ps_pf qs_pf =>
  calc
    ps + qs = 0 + qs' := by
      rw [ps_pf, qs_pf]
    _ = qs' := zero_addₓ _
    

theorem add_pf_sum_z {ps ps' qs : α} : ps = ps' → qs = 0 → ps + qs = ps' := fun ps_pf qs_pf =>
  calc
    ps + qs = ps' + 0 := by
      rw [ps_pf, qs_pf]
    _ = ps' := add_zeroₓ _
    

theorem add_pf_sum_overlap {pps p ps qqs q qs pq pqs : α} :
    pps = p + ps → qqs = q + qs → p + q = pq → ps + qs = pqs → pps + qqs = pq + pqs := by
  cc

theorem add_pf_sum_overlap_zero {pps p ps qqs q qs pqs : α} :
    pps = p + ps → qqs = q + qs → p + q = 0 → ps + qs = pqs → pps + qqs = pqs := fun pps_pf qqs_pf pq_pf pqs_pf =>
  calc
    pps + qqs = p + ps + (q + qs) := by
      rw [pps_pf, qqs_pf]
    _ = p + q + (ps + qs) := by
      cc
    _ = 0 + pqs := by
      rw [pq_pf, pqs_pf]
    _ = pqs := zero_addₓ _
    

theorem add_pf_sum_lt {pps p ps qqs pqs : α} : pps = p + ps → ps + qqs = pqs → pps + qqs = p + pqs := by
  cc

theorem add_pf_sum_gt {pps qqs q qs pqs : α} : qqs = q + qs → pps + qs = pqs → pps + qqs = q + pqs := by
  cc

/-- Add two expressions.

* `0 + qs = 0`
* `ps + 0 = 0`
* `ps * x + ps * y = ps * (x + y)` (for `x`, `y` coefficients; uses `add_overlap`)
* `(p + ps) + (q + qs) = p + (ps + (q + qs))` (if `p.lt q`)
* `(p + ps) + (q + qs) = q + ((p + ps) + qs)` (if not `p.lt q`)
-/
unsafe def add : ex Sum → ex Sum → ring_exp_m (ex Sum)
  | ps@(ex.zero ps_i), qs => do
    let pf ← mk_proof `` add_pf_z_sum [ps.orig, qs.orig, qs.pretty] [ps.info, qs.info]
    let pqs_o ← add_orig ps qs
    pure <| qs pqs_o pf
  | ps, qs@(ex.zero qs_i) => do
    let pf ← mk_proof `` add_pf_sum_z [ps.orig, ps.pretty, qs.orig] [ps.info, qs.info]
    let pqs_o ← add_orig ps qs
    pure <| ps pqs_o pf
  | pps@(ex.sum pps_i p ps), qqs@(ex.sum qqs_i q qs) => do
    let ol ← add_overlap p q
    let ppqqs_o ← add_orig pps qqs
    match ol with
      | overlap.nonzero pq => do
        let pqs ← add ps qs
        let pqqs ← ex_sum pq pqs
        let qqs_pf ← qqs
        let pf ← mk_proof `` add_pf_sum_overlap [pps, p, ps, qqs, q, qs, pq, pqs] [pps, qqs, pq, pqs]
        pure <| pqqs ppqqs_o pf
      | overlap.zero pq => do
        let pqs ← add ps qs
        let pf ← mk_proof `` add_pf_sum_overlap_zero [pps, p, ps, qqs, q, qs, pqs] [pps, qqs, pq, pqs]
        pure <| pqs ppqqs_o pf
      | overlap.none =>
        if p q then do
          let pqs ← add ps qqs
          let ppqs ← ex_sum p pqs
          let pf ← mk_proof `` add_pf_sum_lt [pps, p, ps, qqs, pqs] [pps, pqs]
          pure <| ppqs ppqqs_o pf
        else do
          let pqs ← add pps qs
          let pqqs ← ex_sum q pqs
          let pf ← mk_proof `` add_pf_sum_gt [pps, qqs, q, qs, pqs] [qqs, pqs]
          pure <| pqqs ppqqs_o pf

end Addition

section Multiplication

theorem mul_pf_c_c {ps ps' qs qs' pq : α} : ps = ps' → qs = qs' → ps' * qs' = pq → ps * qs = pq := by
  cc

theorem mul_pf_c_prod {ps qqs q qs pqs : α} : qqs = q * qs → ps * qs = pqs → ps * qqs = q * pqs := by
  cc

theorem mul_pf_prod_c {pps p ps qs pqs : α} : pps = p * ps → ps * qs = pqs → pps * qs = p * pqs := by
  cc

theorem mul_pp_pf_overlap {pps p_b ps qqs qs psqs : α} {p_e q_e : ℕ} :
    pps = p_b ^ p_e * ps → qqs = p_b ^ q_e * qs → p_b ^ (p_e + q_e) * (ps * qs) = psqs → pps * qqs = psqs :=
  fun ps_pf qs_pf psqs_pf => by
  simp [← symm psqs_pf, ← pow_addₓ, ← ps_pf, ← qs_pf] <;> ac_rfl

theorem mul_pp_pf_prod_lt {pps p ps qqs pqs : α} : pps = p * ps → ps * qqs = pqs → pps * qqs = p * pqs := by
  cc

theorem mul_pp_pf_prod_gt {pps qqs q qs pqs : α} : qqs = q * qs → pps * qs = pqs → pps * qqs = q * pqs := by
  cc

/-- Multiply two expressions.

* `x * y = (x * y)` (for `x`, `y` coefficients)
* `x * (q * qs) = q * (qs * x)` (for `x` coefficient)
* `(p * ps) * y = p * (ps * y)` (for `y` coefficient)
* `(p_b^p_e * ps) * (p_b^q_e * qs) = p_b^(p_e + q_e) * (ps * qs)`
    (if `p_e` and `q_e` are identical except coefficient)
* `(p * ps) * (q * qs) = p * (ps * (q * qs))` (if `p.lt q`)
* `(p * ps) * (q * qs) = q * ((p * ps) * qs)` (if not `p.lt q`)
-/
unsafe def mul_pp : ex Prod → ex Prod → ring_exp_m (ex Prod)
  | ps@(ex.coeff _ x), qs@(ex.coeff _ y) => do
    let pq ← mul_coeff ps.pretty qs.pretty x y
    let pq_o ← mul_orig ps qs
    let pf ←
      mk_proof_or_refl pq.pretty `` mul_pf_c_c [ps.orig, ps.pretty, qs.orig, qs.pretty, pq.pretty]
          [ps.info, qs.info, pq.info]
    pure <| pq pq_o pf
  | ps@(ex.coeff _ x), qqs@(ex.prod _ q qs) => do
    let pqs ← mul_pp ps qs
    let pqqs ← ex_prod q pqs
    let pqqs_o ← mul_orig ps qqs
    let pf ← mk_proof `` mul_pf_c_prod [ps.orig, qqs.orig, q.pretty, qs.pretty, pqs.pretty] [qqs.info, pqs.info]
    pure <| pqqs pqqs_o pf
  | pps@(ex.prod _ p ps), qs@(ex.coeff _ y) => do
    let pqs ← mul_pp ps qs
    let ppqs ← ex_prod p pqs
    let ppqs_o ← mul_orig pps qs
    let pf ← mk_proof `` mul_pf_prod_c [pps.orig, p.pretty, ps.pretty, qs.orig, pqs.pretty] [pps.info, pqs.info]
    pure <| ppqs ppqs_o pf
  | pps@(ex.prod _ (p@(ex.exp _ p_b p_e)) ps), qqs@(ex.prod _ (q@(ex.exp _ q_b q_e)) qs) => do
    let ppqqs_o ← mul_orig pps qqs
    let pq_ol ← in_exponent <| add_overlap p_e q_e
    match pq_ol, p_b q_b with
      | overlap.nonzero pq_e, tt => do
        let psqs ← mul_pp ps qs
        let pq ← ex_exp p_b pq_e
        let ppsqqs ← ex_prod pq psqs
        let pf ← mk_proof `` mul_pp_pf_overlap [pps, p_b, ps, qqs, qs, ppsqqs, p_e, q_e] [pps, qqs, ppsqqs]
        pure <| ppsqqs ppqqs_o pf
      | _, _ =>
        if p q then do
          let pqs ← mul_pp ps qqs
          let ppqs ← ex_prod p pqs
          let pf ← mk_proof `` mul_pp_pf_prod_lt [pps, p, ps, qqs, pqs] [pps, pqs]
          pure <| ppqs ppqqs_o pf
        else do
          let pqs ← mul_pp pps qs
          let pqqs ← ex_prod q pqs
          let pf ← mk_proof `` mul_pp_pf_prod_gt [pps, qqs, q, qs, pqs] [qqs, pqs]
          pure <| pqqs ppqqs_o pf

theorem mul_p_pf_zero {ps qs : α} : ps = 0 → ps * qs = 0 := fun ps_pf => by
  rw [ps_pf, zero_mul]

theorem mul_p_pf_sum {pps p ps qs ppsqs : α} : pps = p + ps → p * qs + ps * qs = ppsqs → pps * qs = ppsqs :=
  fun pps_pf ppsqs_pf =>
  calc
    pps * qs = (p + ps) * qs := by
      rw [pps_pf]
    _ = p * qs + ps * qs := add_mulₓ _ _ _
    _ = ppsqs := ppsqs_pf
    

/-- Multiply two expressions.

* `0 * qs = 0`
* `(p + ps) * qs = (p * qs) + (ps * qs)`
-/
unsafe def mul_p : ex Sum → ex Prod → ring_exp_m (ex Sum)
  | ps@(ex.zero ps_i), qs => do
    let z ← ex_zero
    let z_o ← mul_orig ps qs
    let pf ← mk_proof `` mul_p_pf_zero [ps.orig, qs.orig] [ps.info]
    pure <| z z_o pf
  | pps@(ex.sum pps_i p ps), qs => do
    let pqs ← mul_pp p qs >>= prod_to_sum
    let psqs ← mul_p ps qs
    let ppsqs ← add pqs psqs
    let pps_pf ← pps.proof_term
    let ppsqs_o ← mul_orig pps qs
    let ppsqs_pf ← ppsqs.proof_term
    let pf ← mk_proof `` mul_p_pf_sum [pps.orig, p.pretty, ps.pretty, qs.orig, ppsqs.pretty] [pps.info, ppsqs.info]
    pure <| ppsqs ppsqs_o pf

theorem mul_pf_zero {ps qs : α} : qs = 0 → ps * qs = 0 := fun qs_pf => by
  rw [qs_pf, mul_zero]

theorem mul_pf_sum {ps qqs q qs psqqs : α} : qqs = q + qs → ps * q + ps * qs = psqqs → ps * qqs = psqqs :=
  fun qs_pf psqqs_pf =>
  calc
    ps * qqs = ps * (q + qs) := by
      rw [qs_pf]
    _ = ps * q + ps * qs := mul_addₓ _ _ _
    _ = psqqs := psqqs_pf
    

/-- Multiply two expressions.

* `ps * 0 = 0`
* `ps * (q + qs) = (ps * q) + (ps * qs)`
-/
unsafe def mul : ex Sum → ex Sum → ring_exp_m (ex Sum)
  | ps, qs@(ex.zero qs_i) => do
    let z ← ex_zero
    let z_o ← mul_orig ps qs
    let pf ← mk_proof `` mul_pf_zero [ps.orig, qs.orig] [qs.info]
    pure <| z z_o pf
  | ps, qqs@(ex.sum qqs_i q qs) => do
    let psq ← mul_p ps q
    let psqs ← mul ps qs
    let psqqs ← add psq psqs
    let psqqs_o ← mul_orig ps qqs
    let pf ← mk_proof `` mul_pf_sum [ps.orig, qqs.orig, q.orig, qs.orig, psqqs.pretty] [qqs.info, psqqs.info]
    pure <| psqqs psqqs_o pf

end Multiplication

section Exponentiation

theorem pow_e_pf_exp {pps p : α} {ps qs psqs : ℕ} : pps = p ^ ps → ps * qs = psqs → pps ^ qs = p ^ psqs :=
  fun pps_pf psqs_pf =>
  calc
    pps ^ qs = (p ^ ps) ^ qs := by
      rw [pps_pf]
    _ = p ^ (ps * qs) := symm (pow_mulₓ _ _ _)
    _ = p ^ psqs := by
      rw [psqs_pf]
    

/-- Compute the exponentiation of two coefficients.

The returned value is of the form `ex.coeff _ (p ^ q)`,
with the proof of `expr.of_rat p ^ expr.of_rat q = expr.of_rat (p ^ q)`.
-/
unsafe def pow_coeff (p_p q_p : expr) (p q : Coeff) : ring_exp_m (ex Prod) := do
  let ctx ← get_context
  let pq' ← mk_pow [p_p, q_p]
  let (pq_p, pq_pf) ← lift <| norm_num.eval_pow pq'
  pure <| ex.coeff ⟨pq_p, pq_p, pq_pf⟩ ⟨p.1 * q.1⟩

/-- Exponentiate two expressions.

* `(p ^ ps) ^ qs = p ^ (ps * qs)`
-/
unsafe def pow_e : ex exp → ex Prod → ring_exp_m (ex exp)
  | pps@(ex.exp pps_i p ps), qs => do
    let psqs ← in_exponent <| mul_pp ps qs
    let ppsqs ← ex_exp p psqs
    let ppsqs_o ← pow_orig pps qs
    let pf ← mk_proof `` pow_e_pf_exp [pps.orig, p.pretty, ps.pretty, qs.orig, psqs.pretty] [pps.info, psqs.info]
    pure <| ppsqs ppsqs_o pf

theorem pow_pp_pf_one {ps : α} {qs : ℕ} : ps = 1 → ps ^ qs = 1 := fun ps_pf => by
  rw [ps_pf, one_pow]

theorem pow_pf_c_c {ps ps' pq : α} {qs qs' : ℕ} : ps = ps' → qs = qs' → ps' ^ qs' = pq → ps ^ qs = pq := by
  cc

theorem pow_pp_pf_c {ps ps' pqs : α} {qs qs' : ℕ} : ps = ps' → qs = qs' → ps' ^ qs' = pqs → ps ^ qs = pqs * 1 := by
  simp <;> cc

theorem pow_pp_pf_prod {pps p ps pqs psqs : α} {qs : ℕ} :
    pps = p * ps → p ^ qs = pqs → ps ^ qs = psqs → pps ^ qs = pqs * psqs := fun pps_pf pqs_pf psqs_pf =>
  calc
    pps ^ qs = (p * ps) ^ qs := by
      rw [pps_pf]
    _ = p ^ qs * ps ^ qs := mul_powₓ _ _ _
    _ = pqs * psqs := by
      rw [pqs_pf, psqs_pf]
    

/-- Exponentiate two expressions.

* `1 ^ qs = 1`
* `x ^ qs = x ^ qs` (for `x` coefficient)
* `(p * ps) ^ qs = p ^ qs + ps ^ qs`
-/
unsafe def pow_pp : ex Prod → ex Prod → ring_exp_m (ex Prod)
  | ps@(ex.coeff ps_i ⟨⟨1, 1, _, _⟩⟩), qs => do
    let o ← ex_one
    let o_o ← pow_orig ps qs
    let pf ← mk_proof `` pow_pp_pf_one [ps.orig, qs.orig] [ps.info]
    pure <| o o_o pf
  | ps@(ex.coeff ps_i x), qs@(ex.coeff qs_i y) => do
    let pq ← pow_coeff ps.pretty qs.pretty x y
    let pq_o ← pow_orig ps qs
    let pf ←
      mk_proof_or_refl pq.pretty `` pow_pf_c_c [ps.orig, ps.pretty, pq.pretty, qs.orig, qs.pretty]
          [ps.info, qs.info, pq.info]
    pure <| pq pq_o pf
  | ps@(ex.coeff ps_i x), qs => do
    let ps'' ← pure ps >>= prod_to_sum >>= ex_sum_b
    let pqs ← ex_exp ps'' qs
    let pqs_o ← pow_orig ps qs
    let pf ←
      mk_proof_or_refl pqs.pretty `` pow_pp_pf_c [ps.orig, ps.pretty, pqs.pretty, qs.orig, qs.pretty]
          [ps.info, qs.info, pqs.info]
    let pqs' ← exp_to_prod pqs
    pure <| pqs' pqs_o pf
  | pps@(ex.prod pps_i p ps), qs => do
    let pqs ← pow_e p qs
    let psqs ← pow_pp ps qs
    let ppsqs ← ex_prod pqs psqs
    let ppsqs_o ← pow_orig pps qs
    let pf ←
      mk_proof `` pow_pp_pf_prod [pps.orig, p.pretty, ps.pretty, pqs.pretty, psqs.pretty, qs.orig]
          [pps.info, pqs.info, psqs.info]
    pure <| ppsqs ppsqs_o pf

theorem pow_p_pf_one {ps ps' : α} {qs : ℕ} : ps = ps' → qs = succ zero → ps ^ qs = ps' := fun ps_pf qs_pf =>
  calc
    ps ^ qs = ps' ^ 1 := by
      rw [ps_pf, qs_pf]
    _ = ps' := pow_oneₓ _
    

theorem pow_p_pf_zero {ps : α} {qs qs' : ℕ} : ps = 0 → qs = succ qs' → ps ^ qs = 0 := fun ps_pf qs_pf =>
  calc
    ps ^ qs = 0 ^ succ qs' := by
      rw [ps_pf, qs_pf]
    _ = 0 := zero_pow (succ_posₓ qs')
    

theorem pow_p_pf_succ {ps pqqs : α} {qs qs' : ℕ} : qs = succ qs' → ps * ps ^ qs' = pqqs → ps ^ qs = pqqs :=
  fun qs_pf pqqs_pf =>
  calc
    ps ^ qs = ps ^ succ qs' := by
      rw [qs_pf]
    _ = ps * ps ^ qs' := pow_succₓ _ _
    _ = pqqs := by
      rw [pqqs_pf]
    

theorem pow_p_pf_singleton {pps p pqs : α} {qs : ℕ} : pps = p + 0 → p ^ qs = pqs → pps ^ qs = pqs :=
  fun pps_pf pqs_pf => by
  rw [pps_pf, add_zeroₓ, pqs_pf]

theorem pow_p_pf_cons {ps ps' : α} {qs qs' : ℕ} : ps = ps' → qs = qs' → ps ^ qs = ps' ^ qs' := by
  cc

/-- Exponentiate two expressions.

* `ps ^ 1 = ps`
* `0 ^ qs = 0` (note that this is handled *after* `ps ^ 0 = 1`)
* `(p + 0) ^ qs = p ^ qs`
* `ps ^ (qs + 1) = ps * ps ^ qs` (note that this is handled *after* `p + 0 ^ qs = p ^ qs`)
* `ps ^ qs = ps ^ qs` (otherwise)
-/
unsafe def pow_p : ex Sum → ex Prod → ring_exp_m (ex Sum)
  | ps, qs@(ex.coeff qs_i ⟨⟨1, 1, _, _⟩⟩) => do
    let ps_o ← pow_orig ps qs
    let pf ← mk_proof `` pow_p_pf_one [ps.orig, ps.pretty, qs.orig] [ps.info, qs.info]
    pure <| ps ps_o pf
  | ps@(ex.zero ps_i), qs@(ex.coeff qs_i ⟨⟨succ y, 1, _, _⟩⟩) => do
    let ctx ← get_context
    let z ← ex_zero
    let qs_pred ← lift <| expr.of_nat ctx.info_e.α y
    let pf ← mk_proof `` pow_p_pf_zero [ps.orig, qs.orig, qs_pred] [ps.info, qs.info]
    let z_o ← pow_orig ps qs
    pure <| z z_o pf
  | pps@(ex.sum pps_i p (ex.zero _)), qqs => do
    let pqs ← pow_pp p qqs
    let pqs_o ← pow_orig pps qqs
    let pf ← mk_proof `` pow_p_pf_singleton [pps.orig, p.pretty, pqs.pretty, qqs.orig] [pps.info, pqs.info]
    prod_to_sum <| pqs pqs_o pf
  | ps, qs@(ex.coeff qs_i ⟨⟨Int.ofNat (succ n), 1, den_pos, _⟩⟩) => do
    let qs' ← in_exponent <| ex_coeff ⟨Int.ofNat n, 1, den_pos, coprime_one_rightₓ _⟩
    let pqs ← pow_p ps qs'
    let pqqs ← mul ps pqs
    let pqqs_o ← pow_orig ps qs
    let pf ← mk_proof `` pow_p_pf_succ [ps.orig, pqqs.pretty, qs.orig, qs'.pretty] [qs.info, pqqs.info]
    pure <| pqqs pqqs_o pf
  | pps, qqs => do
    let pps'
      ←-- fallback: treat them as atoms
          ex_sum_b
          pps
    let psqs ← ex_exp pps' qqs
    let psqs_o ← pow_orig pps qqs
    let pf ←
      mk_proof_or_refl psqs.pretty `` pow_p_pf_cons [pps.orig, pps.pretty, qqs.orig, qqs.pretty] [pps.info, qqs.info]
    exp_to_prod (psqs psqs_o pf) >>= prod_to_sum

theorem pow_pf_zero {ps : α} {qs : ℕ} : qs = 0 → ps ^ qs = 1 := fun qs_pf =>
  calc
    ps ^ qs = ps ^ 0 := by
      rw [qs_pf]
    _ = 1 := pow_zeroₓ _
    

theorem pow_pf_sum {ps psqqs : α} {qqs q qs : ℕ} : qqs = q + qs → ps ^ q * ps ^ qs = psqqs → ps ^ qqs = psqqs :=
  fun qqs_pf psqqs_pf =>
  calc
    ps ^ qqs = ps ^ (q + qs) := by
      rw [qqs_pf]
    _ = ps ^ q * ps ^ qs := pow_addₓ _ _ _
    _ = psqqs := psqqs_pf
    

/-- Exponentiate two expressions.

* `ps ^ 0 = 1`
* `ps ^ (q + qs) = ps ^ q * ps ^ qs`
-/
unsafe def pow : ex Sum → ex Sum → ring_exp_m (ex Sum)
  | ps, qs@(ex.zero qs_i) => do
    let o ← ex_one
    let o_o ← pow_orig ps qs
    let pf ← mk_proof `` pow_pf_zero [ps.orig, qs.orig] [qs.info]
    prod_to_sum <| o o_o pf
  | ps, qqs@(ex.sum qqs_i q qs) => do
    let psq ← pow_p ps q
    let psqs ← pow ps qs
    let psqqs ← mul psq psqs
    let psqqs_o ← pow_orig ps qqs
    let pf ← mk_proof `` pow_pf_sum [ps.orig, psqqs.pretty, qqs.orig, q.pretty, qs.pretty] [qqs.info, psqqs.info]
    pure <| psqqs psqqs_o pf

end Exponentiation

theorem simple_pf_sum_zero {p p' : α} : p = p' → p + 0 = p' := by
  simp

theorem simple_pf_prod_one {p p' : α} : p = p' → p * 1 = p' := by
  simp

theorem simple_pf_prod_neg_one {α} [Ringₓ α] {p p' : α} : p = p' → p * -1 = -p' := by
  simp

theorem simple_pf_var_one (p : α) : p ^ 1 = p := by
  simp

theorem simple_pf_exp_one {p p' : α} : p = p' → p ^ 1 = p' := by
  simp

/-- Give a simpler, more human-readable representation of the normalized expression.

Normalized expressions might have the form `a^1 * 1 + 0`,
since the dummy operations reduce special cases in pattern-matching.
Humans prefer to read `a` instead.
This tactic gets rid of the dummy additions, multiplications and exponentiations.

Returns a normalized expression `e'` and a proof that `e.pretty = e'`.
-/
unsafe def ex.simple : ∀ {et : ExType}, ex et → ring_exp_m (expr × expr)
  | Sum, pps@(ex.sum pps_i p (ex.zero _)) => do
    let (p_p, p_pf) ← p.simple
    Prod.mk p_p <$> mk_app_csr `` simple_pf_sum_zero [p, p_p, p_pf]
  | Sum, ex.sum pps_i p ps => do
    let (p_p, p_pf) ← p.simple
    let (ps_p, ps_pf) ← ps.simple
    Prod.mk <$> mk_add [p_p, ps_p] <*> mk_app_csr `` sum_congr [p, p_p, ps, ps_p, p_pf, ps_pf]
  | Prod, ex.prod pps_i p (ex.coeff _ ⟨⟨1, 1, _, _⟩⟩) => do
    let (p_p, p_pf) ← p.simple
    Prod.mk p_p <$> mk_app_csr `` simple_pf_prod_one [p, p_p, p_pf]
  | Prod, pps@(ex.prod pps_i p (ex.coeff _ ⟨⟨-1, 1, _, _⟩⟩)) => do
    let ctx ← get_context
    match ctx with
      | none => Prod.mk pps <$> lift (mk_eq_refl pps)
      | some ringi => do
        let (p_p, p_pf) ← p
        Prod.mk <$> lift (mk_app `` Neg.neg [p_p]) <*> mk_app_class `` simple_pf_prod_neg_one ringi [p, p_p, p_pf]
  | Prod, ex.prod pps_i p ps => do
    let (p_p, p_pf) ← p.simple
    let (ps_p, ps_pf) ← ps.simple
    Prod.mk <$> mk_mul [p_p, ps_p] <*> mk_app_csr `` prod_congr [p, p_p, ps, ps_p, p_pf, ps_pf]
  | base, ex.sum_b pps_i ps => ps.simple
  | exp, ex.exp pps_i p (ex.coeff _ ⟨⟨1, 1, _, _⟩⟩) => do
    let (p_p, p_pf) ← p.simple
    Prod.mk p_p <$> mk_app_csr `` simple_pf_exp_one [p, p_p, p_pf]
  | exp, ex.exp pps_i p ps => do
    let (p_p, p_pf) ← p.simple
    let (ps_p, ps_pf) ← in_exponent <| ps.simple
    Prod.mk <$> mk_pow [p_p, ps_p] <*> mk_app_csr `` exp_congr [p, p_p, ps, ps_p, p_pf, ps_pf]
  | et, ps => Prod.mk ps.pretty <$> lift (mk_eq_refl ps.pretty)

/-- Performs a lookup of the atom `a` in the list of known atoms,
or allocates a new one.

If `a` is not definitionally equal to any of the list's entries,
a new atom is appended to the list and returned.
The index of this atom is kept track of in the second inductive argument.

This function is mostly useful in `resolve_atom`,
which updates the state with the new list of atoms.
-/
unsafe def resolve_atom_aux (a : expr) : List atom → ℕ → ring_exp_m (atom × List atom)
  | [], n =>
    let atm : atom := ⟨a, n⟩
    pure (atm, [atm])
  | bas@(b :: as), n => do
    let ctx ← get_context
    (lift <| is_def_eq a b ctx >> pure (b, bas)) <|> do
        let (atm, as') ← resolve_atom_aux as (succ n)
        pure (atm, b :: as')

/-- Convert the expression to an atom:
either look up a definitionally equal atom,
or allocate it as a new atom.

You probably want to use `eval_base` if `eval` doesn't work
instead of directly calling `resolve_atom`,
since `eval_base` can also handle numerals.
-/
unsafe def resolve_atom (a : expr) : ring_exp_m atom := do
  let atoms ← ReaderTₓ.lift <| StateTₓ.get
  let (atm, atoms') ← resolve_atom_aux a atoms 0
  ReaderTₓ.lift <| StateTₓ.put atoms'
  pure atm

/-- Treat the expression atomically: as a coefficient or atom.

Handles cases where `eval` cannot treat the expression as a known operation
because it is just a number or single variable.
-/
unsafe def eval_base (ps : expr) : ring_exp_m (ex Sum) :=
  match ps.to_rat with
  | some ⟨0, 1, _, _⟩ => ex_zero
  | some x => ex_coeff x >>= prod_to_sum
  | none => do
    let a ← resolve_atom ps
    atom_to_sum a

theorem negate_pf {α} [Ringₓ α] {ps ps' : α} : -1 * ps = ps' → -ps = ps' := by
  simp

/-- Negate an expression by multiplying with `-1`.

Only works if there is a `ring` instance; otherwise it will `fail`.
-/
unsafe def negate (ps : ex Sum) : ring_exp_m (ex Sum) := do
  let ctx ← get_context
  match ctx with
    | none => lift <| fail "internal error: negate called in semiring"
    | some ring_instance => do
      let minus_one ← ex_coeff (-1) >>= prod_to_sum
      let ps' ← mul minus_one ps
      let ps_pf ← ps'
      let pf ← mk_app_class `` negate_pf ring_instance [ps, ps', ps_pf]
      let ps'_o ← lift <| mk_app `` Neg.neg [ps]
      pure <| ps' ps'_o pf

theorem inverse_pf {α} [DivisionRing α] {ps ps_u ps_p e' e'' : α} :
    ps = ps_u → ps_u = ps_p → ps_p⁻¹ = e' → e' = e'' → ps⁻¹ = e'' := by
  cc

/-- Invert an expression by simplifying, applying `has_inv.inv` and treating the result as an atom.

Only works if there is a `division_ring` instance; otherwise it will `fail`.
-/
unsafe def inverse (ps : ex Sum) : ring_exp_m (ex Sum) := do
  let ctx ← get_context
  let dri ←
    match ctx.info_b.dr_instance with
      | none => lift <| fail "division is only supported in a division ring"
      | some dri => pure dri
  let (ps_simple, ps_simple_pf) ← ps.simple
  let e ← lift <| mk_app `` Inv.inv [ps_simple]
  let (e', e_pf) ← lift (norm_num.derive e) <|> (fun e_pf => (e, e_pf)) <$> lift (mk_eq_refl e)
  let e'' ← eval_base e'
  let ps_pf ← ps.proof_term
  let e''_pf ← e''.proof_term
  let pf ←
    mk_app_class `` inverse_pf dri [ps.orig, ps.pretty, ps_simple, e', e''.pretty, ps_pf, ps_simple_pf, e_pf, e''_pf]
  let e''_o ← lift <| mk_app `` Inv.inv [ps.orig]
  pure <| e'' e''_o pf

theorem sub_pf {α} [Ringₓ α] {ps qs psqs : α} (h : ps + -qs = psqs) : ps - qs = psqs := by
  rwa [sub_eq_add_neg]

theorem div_pf {α} [DivisionRing α] {ps qs psqs : α} (h : ps * qs⁻¹ = psqs) : ps / qs = psqs := by
  rwa [div_eq_mul_inv]

end Operations

section Wiring

/-!
### `wiring` section

This section deals with going from `expr` to `ex` and back.

The main attraction is `eval`, which uses `add`, `mul`, etc.
to calculate an `ex` from a given `expr`.
Other functions use `ex`es to produce `expr`s together with a proof,
or produce the context to run `ring_exp_m` from an `expr`.
-/


open Tactic

open ExType

/-- Compute a normalized form (of type `ex`) from an expression (of type `expr`).

This is the main driver of the `ring_exp` tactic,
calling out to `add`, `mul`, `pow`, etc. to parse the `expr`.
-/
unsafe def eval : expr → ring_exp_m (ex Sum)
  | e@(quote.1 ((%%ₓps) + %%ₓqs)) => do
    let ps' ← eval ps
    let qs' ← eval qs
    add ps' qs'
  | ps_o@(quote.1 (Nat.succ (%%ₓp_o))) => do
    let ps' ← eval (quote.1 ((%%ₓp_o) + 1))
    let pf ← lift <| mk_app `` Nat.succ_eq_add_one [p_o]
    rewrite ps_o ps' pf
  | e@(quote.1 ((%%ₓps) - %%ₓqs)) =>
    (do
        let ctx ← get_context
        let ri ←
          match ctx.info_b.ring_instance with
            | none => lift <| fail "subtraction is not directly supported in a semiring"
            | some ri => pure ri
        let ps' ← eval ps
        let qs' ← eval qs >>= negate
        let psqs ← add ps' qs'
        let psqs_pf ← psqs.proof_term
        let pf ← mk_app_class `` sub_pf ri [ps, qs, psqs.pretty, psqs_pf]
        pure (psqs e pf)) <|>
      eval_base e
  | e@(quote.1 (-%%ₓps)) => do
    let ps' ← eval ps
    negate ps' <|> eval_base e
  | e@(quote.1 ((%%ₓps) * %%ₓqs)) => do
    let ps' ← eval ps
    let qs' ← eval qs
    mul ps' qs'
  | e@(quote.1 (Inv.inv (%%ₓps))) => do
    let ps' ← eval ps
    inverse ps' <|> eval_base e
  | e@(quote.1 ((%%ₓps) / %%ₓqs)) => do
    let ctx ← get_context
    let dri ←
      match ctx.info_b.dr_instance with
        | none => lift <| fail "division is only directly supported in a division ring"
        | some dri => pure dri
    let ps' ← eval ps
    let qs' ← eval qs
    (do
          let qs'' ← inverse qs'
          let psqs ← mul ps' qs''
          let psqs_pf ← psqs
          let pf ← mk_app_class `` div_pf dri [ps, qs, psqs, psqs_pf]
          pure (psqs e pf)) <|>
        eval_base e
  | e@(quote.1 (@Pow.pow _ _ (%%ₓhp_instance) (%%ₓps) (%%ₓqs))) => do
    let ps' ← eval ps
    let qs' ← in_exponent <| eval qs
    let psqs ← pow ps' qs'
    let psqs_pf ← psqs.proof_term
    (do
          let has_pow_pf ←
            match hp_instance with
              | quote.1 Monoidₓ.hasPow => lift <| mk_eq_refl e
              | _ => lift <| fail "has_pow instance must be nat.has_pow or monoid.has_pow"
          let pf ← lift <| mk_eq_trans has_pow_pf psqs_pf
          pure <| psqs e pf) <|>
        eval_base e
  | ps => eval_base ps

/-- Run `eval` on the expression and return the result together with normalization proof.

See also `eval_simple` if you want something that behaves like `norm_num`.
-/
unsafe def eval_with_proof (e : expr) : ring_exp_m (ex Sum × expr) := do
  let e' ← eval e
  Prod.mk e' <$> e'

/-- Run `eval` on the expression and simplify the result.

Returns a simplified normalized expression, together with an equality proof.

See also `eval_with_proof` if you just want to check the equality of two expressions.
-/
unsafe def eval_simple (e : expr) : ring_exp_m (expr × expr) := do
  let (complicated, complicated_pf) ← eval_with_proof e
  let (simple, simple_pf) ← complicated.simple
  Prod.mk simple <$> lift (mk_eq_trans complicated_pf simple_pf)

/-- Compute the `eval_info` for a given type `α`. -/
unsafe def make_eval_info (α : expr) : tactic eval_info := do
  let u ← mk_meta_univ
  infer_type α >>= unify (expr.sort (level.succ u))
  let u ← get_univ_assignment u
  let csr_instance ← mk_app `` CommSemiringₓ [α] >>= mk_instance
  let ring_instance ← some <$> (mk_app `` Ringₓ [α] >>= mk_instance) <|> pure none
  let dr_instance ← some <$> (mk_app `` DivisionRing [α] >>= mk_instance) <|> pure none
  let ha_instance ← mk_app `` Add [α] >>= mk_instance
  let hm_instance ← mk_app `` Mul [α] >>= mk_instance
  let hp_instance ← mk_mapp `` Monoidₓ.hasPow [some α, none]
  let z ← mk_mapp `` Zero.zero [α, none]
  let o ← mk_mapp `` One.one [α, none]
  pure ⟨α, u, csr_instance, ha_instance, hm_instance, hp_instance, ring_instance, dr_instance, z, o⟩

/-- Use `e` to build the context for running `mx`. -/
unsafe def run_ring_exp {α} (transp : Transparency) (e : expr) (mx : ring_exp_m α) : tactic α := do
  let info_b ← infer_type e >>= make_eval_info
  let info_e ← mk_const `` Nat >>= make_eval_info
  (fun x : _ × _ => x.1) <$> StateTₓ.run (ReaderTₓ.run mx ⟨info_b, info_e, transp⟩) []

/-- Repeatedly apply `eval_simple` on (sub)expressions. -/
unsafe def normalize (transp : Transparency) (e : expr) : tactic (expr × expr) := do
  let (_, e', pf') ←
    ext_simplify_core () {  } simp_lemmas.mk (fun _ => failed)
        (fun _ _ _ _ e => do
          let (e'', pf) ← run_ring_exp transp e <| eval_simple e
          guardₓ ¬expr.alpha_eqv e'' e
          return ((), e'', some pf, ff))
        (fun _ _ _ _ _ => failed) `eq e
  pure (e', pf')

end Wiring

end Tactic.RingExp

namespace Tactic.Interactive

open Interactive Interactive.Types Lean.Parser Tactic Tactic.RingExp

-- mathport name: «expr ?»
local postfix:1024 "?" => optionalₓ

/-- Tactic for solving equations of *commutative* (semi)rings,
allowing variables in the exponent.
This version of `ring_exp` fails if the target is not an equality.

The variant `ring_exp_eq!` will use a more aggressive reducibility setting
to determine equality of atoms.
-/
unsafe def ring_exp_eq (red : parse (tk "!")?) : tactic Unit := do
  let quote.1 (Eq (%%ₓps) (%%ₓqs)) ← target >>= whnf
  let transp := if red.isSome then semireducible else reducible
  let ((ps', ps_pf), (qs', qs_pf)) ← run_ring_exp transp ps <| Prod.mk <$> eval_with_proof ps <*> eval_with_proof qs
  if ps' qs' then do
      let qs_pf_inv ← mk_eq_symm qs_pf
      let pf ← mk_eq_trans ps_pf qs_pf_inv
      tactic.interactive.exact (pquote.1 (%%ₓpf))
    else fail "ring_exp failed to prove equality"

/-- Tactic for evaluating expressions in *commutative* (semi)rings, allowing for variables in the
exponent.

This tactic extends `ring`: it should solve every goal that `ring` can solve.
Additionally, it knows how to evaluate expressions with complicated exponents
(where `ring` only understands constant exponents).
The variants `ring_exp!` and `ring_exp_eq!` use a more aggessive reducibility setting to determine
equality of atoms.

For example:
```lean
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring_exp
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring_exp
example (x y : ℕ) : x + id y = y + id x := by ring_exp!
```
-/
unsafe def ring_exp (red : parse (tk "!")?) (loc : parse location) : tactic Unit :=
  (match loc with
    | Interactive.Loc.ns [none] => ring_exp_eq red
    | _ => failed) <|>
    do
    let ns ← loc.get_locals
    let transp := if red.isSome then semireducible else reducible
    let tt ← tactic.replace_at (normalize transp) ns loc.include_goal | fail "ring_exp failed to simplify"
    when loc <| try tactic.reflexivity

add_tactic_doc
  { Name := "ring_exp", category := DocCategory.tactic, declNames := [`tactic.interactive.ring_exp],
    tags := ["arithmetic", "simplification", "decision procedure"] }

end Tactic.Interactive

namespace Conv.Interactive

open Conv Interactive

open Tactic

open Tactic.Interactive (ring_exp_eq)

open Tactic.RingExp (normalize)

-- mathport name: «expr ?»
local postfix:1024 "?" => optionalₓ

/-- Normalises expressions in commutative (semi-)rings inside of a `conv` block using the tactic
`ring_exp`.
-/
unsafe def ring_exp (red : parse (lean.parser.tk "!")?) : conv Unit :=
  let transp := if red.isSome then semireducible else reducible
  discharge_eq_lhs (ring_exp_eq red) <|> replace_lhs (normalize transp) <|> fail "ring_exp failed to simplify"

end Conv.Interactive


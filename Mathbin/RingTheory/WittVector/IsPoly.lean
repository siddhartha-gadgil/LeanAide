/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathbin.Algebra.Ring.Ulift
import Mathbin.RingTheory.WittVector.Basic
import Mathbin.Data.MvPolynomial.Funext

/-!
# The `is_poly` predicate

`witt_vector.is_poly` is a (type-valued) predicate on functions `f : Π R, 𝕎 R → 𝕎 R`.
It asserts that there is a family of polynomials `φ : ℕ → mv_polynomial ℕ ℤ`,
such that the `n`th coefficient of `f x` is equal to `φ n` evaluated on the coefficients of `x`.
Many operations on Witt vectors satisfy this predicate (or an analogue for higher arity functions).
We say that such a function `f` is a *polynomial function*.

The power of satisfying this predicate comes from `is_poly.ext`.
It shows that if `φ` and `ψ` witness that `f` and `g` are polynomial functions,
then `f = g` not merely when `φ = ψ`, but in fact it suffices to prove
```
∀ n, bind₁ φ (witt_polynomial p _ n) = bind₁ ψ (witt_polynomial p _ n)
```
(in other words, when evaluating the Witt polynomials on `φ` and `ψ`, we get the same values)
which will then imply `φ = ψ` and hence `f = g`.

Even though this sufficient condition looks somewhat intimidating,
it is rather pleasant to check in practice;
more so than direct checking of `φ = ψ`.

In practice, we apply this technique to show that the composition of `witt_vector.frobenius`
and `witt_vector.verschiebung` is equal to multiplication by `p`.

## Main declarations

* `witt_vector.is_poly`, `witt_vector.is_poly₂`:
  two predicates that assert that a unary/binary function on Witt vectors
  is polynomial in the coefficients of the input values.
* `witt_vector.is_poly.ext`, `witt_vector.is_poly₂.ext`:
  two polynomial functions are equal if their families of polynomials are equal
  after evaluating the Witt polynomials on them.
* `witt_vector.is_poly.comp` (+ many variants) show that unary/binary compositions
  of polynomial functions are polynomial.
* `witt_vector.id_is_poly`, `witt_vector.neg_is_poly`,
  `witt_vector.add_is_poly₂`, `witt_vector.mul_is_poly₂`:
  several well-known operations are polynomial functions
  (for Verschiebung, Frobenius, and multiplication by `p`, see their respective files).

## On higher arity analogues

Ideally, there should be a predicate `is_polyₙ` for functions of higher arity,
together with `is_polyₙ.comp` that shows how such functions compose.
Since mathlib does not have a library on composition of higher arity functions,
we have only implemented the unary and binary variants so far.
Nullary functions (a.k.a. constants) are treated
as constant functions and fall under the unary case.

## Tactics

There are important metaprograms defined in this file:
the tactics `ghost_simp` and `ghost_calc` and the attributes `@[is_poly]` and `@[ghost_simps]`.
These are used in combination to discharge proofs of identities between polynomial functions.

Any atomic proof of `is_poly` or `is_poly₂` (i.e. not taking additional `is_poly` arguments)
should be tagged as `@[is_poly]`.

Any lemma doing "ring equation rewriting" with polynomial functions should be tagged
`@[ghost_simps]`, e.g.
```lean
@[ghost_simps]
lemma bind₁_frobenius_poly_witt_polynomial (n : ℕ) :
  bind₁ (frobenius_poly p) (witt_polynomial p ℤ n) = (witt_polynomial p ℤ (n+1))
```

Proofs of identities between polynomial functions will often follow the pattern
```lean
begin
  ghost_calc _,
  <minor preprocessing>,
  ghost_simp
end
```

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


/-
### Simplification tactics

`ghost_simp` is used later in the development for certain simplifications.
We define it here so it is a shared import.
-/
mk_simp_attribute ghost_simps := "Simplification rules for ghost equations"

namespace Tactic

namespace Interactive

setup_tactic_parser

/-- A macro for a common simplification when rewriting with ghost component equations. -/
unsafe def ghost_simp (lems : parse simp_arg_list) : tactic Unit := do
  tactic.try tactic.intro1
  simp none none tt (lems ++ [simp_arg_type.symm_expr (pquote.1 sub_eq_add_neg)]) [`ghost_simps] (loc.ns [none])

/-- `ghost_calc` is a tactic for proving identities between polynomial functions.
Typically, when faced with a goal like
```lean
∀ (x y : 𝕎 R), verschiebung (x * frobenius y) = verschiebung x * y
```
you can
1. call `ghost_calc`
2. do a small amount of manual work -- maybe nothing, maybe `rintro`, etc
3. call `ghost_simp`

and this will close the goal.

`ghost_calc` cannot detect whether you are dealing with unary or binary polynomial functions.
You must give it arguments to determine this.
If you are proving a universally quantified goal like the above,
call `ghost_calc _ _`.
If the variables are introduced already, call `ghost_calc x y`.
In the unary case, use `ghost_calc _` or `ghost_calc x`.

`ghost_calc` is a light wrapper around type class inference.
All it does is apply the appropriate extensionality lemma and try to infer the resulting goals.
This is subtle and Lean's elaborator doesn't like it because of the HO unification involved,
so it is easier (and prettier) to put it in a tactic script.
-/
unsafe def ghost_calc (ids' : parse ident_*) : tactic Unit := do
  let ids ← ids'.mmap fun n => get_local n <|> tactic.intro n
  let quote.1 (@Eq (WittVector _ (%%ₓR)) _ _) ← target
  match ids with
    | [x] => refine (ppquote.1 (is_poly.ext _ _ _ _ (%%ₓx)))
    | [x, y] => refine (ppquote.1 (is_poly₂.ext _ _ _ _ (%%ₓx) (%%ₓy)))
    | _ => fail "ghost_calc takes one or two arguments"
  let nm ←
    match R with
      | expr.local_const _ nm _ _ => return nm
      | _ => get_unused_name `R
  iterate_exactly 2 apply_instance
  unfreezingI (tactic.clear' tt [R])
  introsI <| [nm, mkStrName nm "_inst"] ++ ids'
  skip

end Interactive

end Tactic

namespace WittVector

universe u

variable {p : ℕ} {R S : Type u} {σ idx : Type _} [hp : Fact p.Prime] [CommRingₓ R] [CommRingₓ S]

-- mathport name: «expr𝕎»
local notation "𝕎" => WittVector p

-- type as `\bbW`
open MvPolynomial

open Function (uncurry)

include hp

variable (p)

noncomputable section

/-!
### The `is_poly` predicate
-/


theorem poly_eq_of_witt_polynomial_bind_eq' (f g : ℕ → MvPolynomial (idx × ℕ) ℤ)
    (h : ∀ n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomial p _ n)) : f = g := by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← Function.funext_iffₓ] at h
  replace h := congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom ℚ) ∘ fam) (xInTermsOfW p ℚ n)) h
  simpa only [← Function.comp, ← map_bind₁, ← map_witt_polynomial, bind₁_bind₁, ← bind₁_witt_polynomial_X_in_terms_of_W,
    ← bind₁_X_right] using h

theorem poly_eq_of_witt_polynomial_bind_eq (f g : ℕ → MvPolynomial ℕ ℤ)
    (h : ∀ n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomial p _ n)) : f = g := by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← Function.funext_iffₓ] at h
  replace h := congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom ℚ) ∘ fam) (xInTermsOfW p ℚ n)) h
  simpa only [← Function.comp, ← map_bind₁, ← map_witt_polynomial, bind₁_bind₁, ← bind₁_witt_polynomial_X_in_terms_of_W,
    ← bind₁_X_right] using h

omit hp

/-- A function `f : Π R, 𝕎 R → 𝕎 R` that maps Witt vectors to Witt vectors over arbitrary base rings
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x` is given by evaluating `φₙ` at the coefficients of `x`.

See also `witt_vector.is_poly₂` for the binary variant.

The `ghost_calc` tactic treats `is_poly` as a type class,
and the `@[is_poly]` attribute derives certain specialized composition instances
for declarations of type `is_poly f`.
For the most part, users are not expected to treat `is_poly` as a class.
-/
-- Ideally, we would generalise this to n-ary functions
-- But we don't have a good theory of n-ary compositions in mathlib
class IsPoly (f : ∀ ⦃R⦄ [CommRingₓ R], WittVector p R → 𝕎 R) : Prop where mk' ::
  poly : ∃ φ : ℕ → MvPolynomial ℕ ℤ, ∀ ⦃R⦄ [CommRingₓ R] (x : 𝕎 R), (f x).coeff = fun n => aeval x.coeff (φ n)

/-- The identity function on Witt vectors is a polynomial function. -/
instance id_is_poly : IsPoly p fun _ _ => id :=
  ⟨⟨x, by
      intros
      simp only [← aeval_X, ← id]⟩⟩

instance id_is_poly_i' : IsPoly p fun _ _ a => a :=
  WittVector.id_is_poly _

namespace IsPoly

instance : Inhabited (IsPoly p fun _ _ => id) :=
  ⟨WittVector.id_is_poly p⟩

variable {p}

include hp

theorem ext {f g} (hf : IsPoly p f) (hg : IsPoly p g)
    (h : ∀ (R : Type u) [_Rcr : CommRingₓ R] (x : 𝕎 R) (n : ℕ), ghost_component n (f x) = ghost_component n (g x)) :
    ∀ (R : Type u) [_Rcr : CommRingₓ R] (x : 𝕎 R), f x = g x := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  intros
  ext n
  rw [hf, hg, poly_eq_of_witt_polynomial_bind_eq p φ ψ]
  intro k
  apply MvPolynomial.funext
  intro x
  simp only [← hom_bind₁]
  specialize h (ULift ℤ) ((mk p) fun i => ⟨x i⟩) k
  simp only [← ghost_component_apply, ← aeval_eq_eval₂_hom] at h
  apply (ulift.ring_equiv.symm : ℤ ≃+* _).Injective
  simp only [RingEquiv.coe_to_ring_hom, ← map_eval₂_hom]
  convert h using 1
  all_goals
    funext i
    simp only [← hf, ← hg, ← MvPolynomial.eval, ← map_eval₂_hom]
    apply eval₂_hom_congr (RingHom.ext_int _ _) _ rfl
    ext1
    apply eval₂_hom_congr (RingHom.ext_int _ _) _ rfl
    simp only [← coeff_mk]
    rfl

omit hp

/-- The composition of polynomial functions is polynomial. -/
theorem comp {g f} (hg : IsPoly p g) (hf : IsPoly p f) : IsPoly p fun R _Rcr => @g R _Rcr ∘ @f R _Rcr := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [← aeval_bind₁, ← Function.comp, ← hg, ← hf]

end IsPoly

/-- A binary function `f : Π R, 𝕎 R → 𝕎 R → 𝕎 R` on Witt vectors
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x y` is given by evaluating `φₙ` at the coefficients of `x` and `y`.

See also `witt_vector.is_poly` for the unary variant.

The `ghost_calc` tactic treats `is_poly₂` as a type class,
and the `@[is_poly]` attribute derives certain specialized composition instances
for declarations of type `is_poly₂ f`.
For the most part, users are not expected to treat `is_poly₂` as a class.
-/
class IsPoly₂ (f : ∀ ⦃R⦄ [CommRingₓ R], WittVector p R → 𝕎 R → 𝕎 R) : Prop where mk' ::
  poly :
    ∃ φ : ℕ → MvPolynomial (Finₓ 2 × ℕ) ℤ,
      ∀ ⦃R⦄ [CommRingₓ R] (x y : 𝕎 R), (f x y).coeff = fun n => peval (φ n) ![x.coeff, y.coeff]

variable {p}

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
/-- The composition of polynomial functions is polynomial. -/
theorem IsPoly₂.comp {h f g} (hh : IsPoly₂ p h) (hf : IsPoly p f) (hg : IsPoly p g) :
    IsPoly₂ p fun R _Rcr x y => h (f x) (g y) := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  obtain ⟨χ, hh⟩ := hh
  refine'
    ⟨⟨fun n =>
        bind₁ (uncurry <| ![fun k => rename (Prod.mk (0 : Finₓ 2)) (φ k), fun k => rename (Prod.mk (1 : Finₓ 2)) (ψ k)])
          (χ n),
        _⟩⟩
  intros
  funext n
  simp only [← peval, ← aeval_bind₁, ← Function.comp, ← hh, ← hf, ← hg, ← uncurry]
  apply eval₂_hom_congr rfl _ rfl
  ext ⟨i, n⟩
  fin_cases i <;>
    simp only [← aeval_eq_eval₂_hom, ← eval₂_hom_rename, ← Function.comp, ← Matrix.cons_val_zero, ← Matrix.head_cons, ←
      Matrix.cons_val_one]

/-- The composition of a polynomial function with a binary polynomial function is polynomial. -/
theorem IsPoly.comp₂ {g f} (hg : IsPoly p g) (hf : IsPoly₂ p f) : IsPoly₂ p fun R _Rcr x y => g (f x y) := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [← peval, ← aeval_bind₁, ← Function.comp, ← hg, ← hf]

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
/-- The diagonal `λ x, f x x` of a polynomial function `f` is polynomial. -/
theorem IsPoly₂.diag {f} (hf : IsPoly₂ p f) : IsPoly p fun R _Rcr x => f x x := by
  obtain ⟨φ, hf⟩ := hf
  refine' ⟨⟨fun n => bind₁ (uncurry ![X, X]) (φ n), _⟩⟩
  intros
  funext n
  simp only [← hf, ← peval, ← uncurry, ← aeval_bind₁]
  apply eval₂_hom_congr rfl _ rfl
  ext ⟨i, k⟩
  fin_cases i <;> simp only [← Matrix.head_cons, ← aeval_X, ← Matrix.cons_val_zero, ← Matrix.cons_val_one]

open Tactic

namespace Tactic

/-!
### The `@[is_poly]` attribute

This attribute is used to derive specialized composition instances
for `is_poly` and `is_poly₂` declarations.
-/


/-- If `n` is the name of a lemma with opened type `∀ vars, is_poly p _`,
`mk_poly_comp_lemmas n vars p` adds composition instances to the environment
`n.comp_i` and `n.comp₂_i`.
-/
unsafe def mk_poly_comp_lemmas (n : Name) (vars : List expr) (p : expr) : tactic Unit := do
  let c ← mk_const n
  let appd := vars.foldl expr.app c
  let tgt_bod ←
    to_expr (pquote.1 fun f [hf : IsPoly (%%ₓp) f] => IsPoly.comp (%%ₓappd) hf) >>= replace_univ_metas_with_univ_params
  let tgt_bod ← lambdas vars tgt_bod
  let tgt_tp ← infer_type tgt_bod
  let nm := mkStrName n "comp_i"
  add_decl <| mk_definition nm tgt_tp tgt_tp tgt_bod
  set_attribute `instance nm
  let tgt_bod ←
    to_expr (pquote.1 fun f [hf : IsPoly₂ (%%ₓp) f] => IsPoly.comp₂ (%%ₓappd) hf) >>=
        replace_univ_metas_with_univ_params
  let tgt_bod ← lambdas vars tgt_bod
  let tgt_tp ← infer_type tgt_bod
  let nm := mkStrName n "comp₂_i"
  add_decl <| mk_definition nm tgt_tp tgt_tp tgt_bod
  set_attribute `instance nm

/-- If `n` is the name of a lemma with opened type `∀ vars, is_poly₂ p _`,
`mk_poly₂_comp_lemmas n vars p` adds composition instances to the environment
`n.comp₂_i` and `n.comp_diag`.
-/
unsafe def mk_poly₂_comp_lemmas (n : Name) (vars : List expr) (p : expr) : tactic Unit := do
  let c ← mk_const n
  let appd := vars.foldl expr.app c
  let tgt_bod ←
    to_expr (pquote.1 fun {f g} [hf : IsPoly (%%ₓp) f] [hg : IsPoly (%%ₓp) g] => IsPoly₂.comp (%%ₓappd) hf hg) >>=
        replace_univ_metas_with_univ_params
  let tgt_bod ← lambdas vars tgt_bod
  let tgt_tp ← infer_type tgt_bod >>= simp_lemmas.mk.dsimplify
  let nm := mkStrName n "comp₂_i"
  add_decl <| mk_definition nm tgt_tp tgt_tp tgt_bod
  set_attribute `instance nm
  let tgt_bod ←
    to_expr
          (pquote.1 fun {f g} [hf : IsPoly (%%ₓp) f] [hg : IsPoly (%%ₓp) g] => (IsPoly₂.comp (%%ₓappd) hf hg).diag) >>=
        replace_univ_metas_with_univ_params
  let tgt_bod ← lambdas vars tgt_bod
  let tgt_tp ← infer_type tgt_bod >>= simp_lemmas.mk.dsimplify
  let nm := mkStrName n "comp_diag"
  add_decl <| mk_definition nm tgt_tp tgt_tp tgt_bod
  set_attribute `instance nm

/-- The `after_set` function for `@[is_poly]`. Calls `mk_poly(₂)_comp_lemmas`.
-/
unsafe def mk_comp_lemmas (n : Name) : tactic Unit := do
  let d ← get_decl n
  let (vars, tp) ← open_pis d.type
  match tp with
    | quote.1 (IsPoly (%%ₓp) _) => mk_poly_comp_lemmas n vars p
    | quote.1 (IsPoly₂ (%%ₓp) _) => mk_poly₂_comp_lemmas n vars p
    | _ => fail "@[is_poly] should only be applied to terms of type `is_poly _ _` or `is_poly₂ _ _`"

/-- `@[is_poly]` is applied to lemmas of the form `is_poly f φ` or `is_poly₂ f φ`.
These lemmas should *not* be tagged as instances, and only atomic `is_poly` defs should be tagged:
composition lemmas should not. Roughly speaking, lemmas that take `is_poly` proofs as arguments
should not be tagged.

Type class inference struggles with function composition, and the higher order unification problems
involved in inferring `is_poly` proofs are complex. The standard style writing these proofs by hand
doesn't work very well. Instead, we construct the type class hierarchy "under the hood", with
limited forms of composition.

Applying `@[is_poly]` to a lemma creates a number of instances. Roughly, if the tagged lemma is a
proof of `is_poly f φ`, the instances added have the form
```lean
∀ g ψ, [is_poly g ψ] → is_poly (f ∘ g) _
```
Since `f` is fixed in this instance, it restricts the HO unification needed when the instance is
applied. Composition lemmas relating `is_poly` with `is_poly₂` are also added.
`id_is_poly` is an atomic instance.

The user-written lemmas are not instances. Users should be able to assemble `is_poly` proofs by hand
"as normal" if the tactic fails.
-/
@[user_attribute]
unsafe def is_poly_attr : user_attribute where
  Name := `is_poly
  descr := "Lemmas with this attribute describe the polynomial structure of functions"
  after_set := some fun n _ _ => mk_comp_lemmas n

end Tactic

include hp

/-!
### `is_poly` instances

These are not declared as instances at the top level,
but the `@[is_poly]` attribute adds instances based on each one.
Users are expected to use the non-instance versions manually.
-/


-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
/-- The additive negation is a polynomial function on Witt vectors. -/
@[is_poly]
theorem neg_is_poly : IsPoly p fun R _ => @Neg.neg (𝕎 R) _ :=
  ⟨⟨fun n => rename Prod.snd (wittNeg p n), by
      intros
      funext n
      rw [neg_coeff, aeval_eq_eval₂_hom, eval₂_hom_rename]
      apply eval₂_hom_congr rfl _ rfl
      ext ⟨i, k⟩
      fin_cases i
      rfl⟩⟩

section ZeroOne

/-- The function that is constantly zero on Witt vectors is a polynomial function. -/
/- To avoid a theory of 0-ary functions (a.k.a. constants)
we model them as constant unary functions. -/
instance zero_is_poly : IsPoly p fun _ _ _ => 0 :=
  ⟨⟨0, by
      intros
      funext n
      simp only [← Pi.zero_apply, ← AlgHom.map_zero, ← zero_coeff]⟩⟩

@[simp]
theorem bind₁_zero_witt_polynomial (n : ℕ) : bind₁ (0 : ℕ → MvPolynomial ℕ R) (wittPolynomial p R n) = 0 := by
  rw [← aeval_eq_bind₁, aeval_zero, constant_coeff_witt_polynomial, RingHom.map_zero]

omit hp

/-- The coefficients of `1 : 𝕎 R` as polynomials. -/
def onePoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  if n = 0 then 1 else 0

include hp

@[simp]
theorem bind₁_one_poly_witt_polynomial (n : ℕ) : bind₁ onePoly (wittPolynomial p ℤ n) = 1 := by
  rw [witt_polynomial_eq_sum_C_mul_X_pow, AlgHom.map_sum, Finset.sum_eq_single 0]
  · simp only [← one_poly, ← one_pow, ← one_mulₓ, ← AlgHom.map_pow, ← C_1, ← pow_zeroₓ, ← bind₁_X_right, ← if_true, ←
      eq_self_iff_true]
    
  · intro i hi hi0
    simp only [← one_poly, ← if_neg hi0, ← zero_pow (pow_pos hp.1.Pos _), ← mul_zero, ← AlgHom.map_pow, ← bind₁_X_right,
      ← AlgHom.map_mul]
    
  · rw [Finset.mem_range]
    decide
    

/-- The function that is constantly one on Witt vectors is a polynomial function. -/
instance one_is_poly : IsPoly p fun _ _ _ => 1 :=
  ⟨⟨onePoly, by
      intros
      funext n
      cases n
      · simp only [← one_poly, ← if_true, ← eq_self_iff_true, ← one_coeff_zero, ← AlgHom.map_one]
        
      · simp only [← one_poly, ← Nat.succ_pos', ← one_coeff_eq_of_pos, ← if_neg n.succ_ne_zero, ← AlgHom.map_zero]
        ⟩⟩

end ZeroOne

omit hp

/-- Addition of Witt vectors is a polynomial function. -/
@[is_poly]
theorem add_is_poly₂ [Fact p.Prime] : IsPoly₂ p fun _ _ => (· + ·) :=
  ⟨⟨wittAdd p, by
      intros
      dunfold WittVector.hasAdd
      simp [← eval]⟩⟩

/-- Multiplication of Witt vectors is a polynomial function. -/
@[is_poly]
theorem mul_is_poly₂ [Fact p.Prime] : IsPoly₂ p fun _ _ => (· * ·) :=
  ⟨⟨wittMul p, by
      intros
      dunfold WittVector.hasMul
      simp [← eval]⟩⟩

include hp

-- unfortunately this is not universe polymorphic, merely because `f` isn't
theorem IsPoly.map {f} (hf : IsPoly p f) (g : R →+* S) (x : 𝕎 R) : map g (f x) = f (map g x) := by
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  -- see `is_poly₂.map` for a slightly more general proof strategy
  obtain ⟨φ, hf⟩ := hf
  ext n
  simp only [← map_coeff, ← hf, ← map_aeval]
  apply eval₂_hom_congr (RingHom.ext_int _ _) _ rfl
  simp only [← map_coeff]

namespace IsPoly₂

omit hp

instance [Fact p.Prime] : Inhabited (IsPoly₂ p _) :=
  ⟨add_is_poly₂⟩

variable {p}

/-- The composition of a binary polynomial function
 with a unary polynomial function in the first argument is polynomial. -/
theorem comp_left {g f} (hg : IsPoly₂ p g) (hf : IsPoly p f) : IsPoly₂ p fun R _Rcr x y => g (f x) y :=
  hg.comp hf (WittVector.id_is_poly _)

/-- The composition of a binary polynomial function
 with a unary polynomial function in the second argument is polynomial. -/
theorem comp_right {g f} (hg : IsPoly₂ p g) (hf : IsPoly p f) : IsPoly₂ p fun R _Rcr x y => g x (f y) :=
  hg.comp (WittVector.id_is_poly p) hf

include hp

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
theorem ext {f g} (hf : IsPoly₂ p f) (hg : IsPoly₂ p g)
    (h :
      ∀ (R : Type u) [_Rcr : CommRingₓ R] (x y : 𝕎 R) (n : ℕ), ghost_component n (f x y) = ghost_component n (g x y)) :
    ∀ (R) [_Rcr : CommRingₓ R] (x y : 𝕎 R), f x y = g x y := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  intros
  ext n
  rw [hf, hg, poly_eq_of_witt_polynomial_bind_eq' p φ ψ]
  clear x y
  intro k
  apply MvPolynomial.funext
  intro x
  simp only [← hom_bind₁]
  specialize h (ULift ℤ) ((mk p) fun i => ⟨x (0, i)⟩) ((mk p) fun i => ⟨x (1, i)⟩) k
  simp only [← ghost_component_apply, ← aeval_eq_eval₂_hom] at h
  apply (ulift.ring_equiv.symm : ℤ ≃+* _).Injective
  simp only [RingEquiv.coe_to_ring_hom, ← map_eval₂_hom]
  convert h using 1
  all_goals
    funext i
    simp only [← hf, ← hg, ← MvPolynomial.eval, ← map_eval₂_hom]
    apply eval₂_hom_congr (RingHom.ext_int _ _) _ rfl
    ext1
    apply eval₂_hom_congr (RingHom.ext_int _ _) _ rfl
    ext ⟨b, _⟩
    fin_cases b <;> simp only [← coeff_mk, ← uncurry] <;> rfl

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- unfortunately this is not universe polymorphic, merely because `f` isn't
theorem map {f} (hf : IsPoly₂ p f) (g : R →+* S) (x y : 𝕎 R) : map g (f x y) = f (map g x) (map g y) := by
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  obtain ⟨φ, hf⟩ := hf
  ext n
  simp only [← map_coeff, ← hf, ← map_aeval, ← peval, ← uncurry]
  apply eval₂_hom_congr (RingHom.ext_int _ _) _ rfl
  try
    ext ⟨i, k⟩
    fin_cases i
  all_goals
    simp only [← map_coeff, ← Matrix.cons_val_zero, ← Matrix.head_cons, ← Matrix.cons_val_one]

end IsPoly₂

attribute [ghost_simps]
  AlgHom.map_zero AlgHom.map_one AlgHom.map_add AlgHom.map_mul AlgHom.map_sub AlgHom.map_neg AlgHom.id_apply map_nat_cast RingHom.map_zero RingHom.map_one RingHom.map_mul RingHom.map_add RingHom.map_sub RingHom.map_neg RingHom.id_apply mul_addₓ add_mulₓ add_zeroₓ zero_addₓ mul_oneₓ one_mulₓ mul_zero zero_mul Nat.succ_ne_zero add_tsub_cancel_right Nat.succ_eq_add_one if_true eq_self_iff_true if_false forall_true_iff forall_2_true_iff forall_3_true_iff

end WittVector


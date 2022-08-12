/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathbin.Data.MvPolynomial.Counit
import Mathbin.Data.MvPolynomial.Invertible
import Mathbin.RingTheory.WittVector.Defs

/-!
# Witt vectors

This file verifies that the ring operations on `witt_vector p R`
satisfy the axioms of a commutative ring.

## Main definitions

* `witt_vector.map`: lifts a ring homomorphism `R →+* S` to a ring homomorphism `𝕎 R →+* 𝕎 S`.
* `witt_vector.ghost_component n x`: evaluates the `n`th Witt polynomial
  on the first `n` coefficients of `x`, producing a value in `R`.
  This is a ring homomorphism.
* `witt_vector.ghost_map`: a ring homomorphism `𝕎 R →+* (ℕ → R)`, obtained by packaging
  all the ghost components together.
  If `p` is invertible in `R`, then the ghost map is an equivalence,
  which we use to define the ring operations on `𝕎 R`.
* `witt_vector.comm_ring`: the ring structure induced by the ghost components.

## Notation

We use notation `𝕎 R`, entered `\bbW`, for the Witt vectors over `R`.

## Implementation details

As we prove that the ghost components respect the ring operations, we face a number of repetitive
proofs. To avoid duplicating code we factor these proofs into a custom tactic, only slightly more
powerful than a tactic macro. This tactic is not particularly useful outside of its applications
in this file.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]

-/


noncomputable section

open MvPolynomial Function

open BigOperators

variable {p : ℕ} {R S T : Type _} [hp : Fact p.Prime] [CommRingₓ R] [CommRingₓ S] [CommRingₓ T]

variable {α : Type _} {β : Type _}

-- mathport name: «expr𝕎»
local notation "𝕎" => WittVector p

-- type as `\bbW`
open Witt

namespace WittVector

/-- `f : α → β` induces a map from `𝕎 α` to `𝕎 β` by applying `f` componentwise.
If `f` is a ring homomorphism, then so is `f`, see `witt_vector.map f`. -/
def mapFun (f : α → β) : 𝕎 α → 𝕎 β := fun x => mk _ (f ∘ x.coeff)

namespace MapFun

theorem injective (f : α → β) (hf : Injective f) : Injective (mapFun f : 𝕎 α → 𝕎 β) := fun x y h =>
  ext fun n => hf (congr_arg (fun x => coeff x n) h : _)

theorem surjective (f : α → β) (hf : Surjective f) : Surjective (mapFun f : 𝕎 α → 𝕎 β) := fun x =>
  ⟨mk _ fun n => Classical.some <| hf <| x.coeff n, by
    ext n
    dsimp' [← map_fun]
    rw [Classical.some_spec (hf (x.coeff n))]⟩

variable (f : R →+* S) (x y : 𝕎 R)

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- Auxiliary tactic for showing that `map_fun` respects the ring operations. -/
unsafe def map_fun_tac : tactic Unit :=
  sorry

include hp

-- We do not tag these lemmas as `@[simp]` because they will be bundled in `map` later on.
theorem zero : mapFun f (0 : 𝕎 R) = 0 := by
  run_tac
    map_fun_tac

theorem one : mapFun f (1 : 𝕎 R) = 1 := by
  run_tac
    map_fun_tac

theorem add : mapFun f (x + y) = mapFun f x + mapFun f y := by
  run_tac
    map_fun_tac

theorem sub : mapFun f (x - y) = mapFun f x - mapFun f y := by
  run_tac
    map_fun_tac

theorem mul : mapFun f (x * y) = mapFun f x * mapFun f y := by
  run_tac
    map_fun_tac

theorem neg : mapFun f (-x) = -mapFun f x := by
  run_tac
    map_fun_tac

theorem nsmul (n : ℕ) : mapFun f (n • x) = n • mapFun f x := by
  run_tac
    map_fun_tac

theorem zsmul (z : ℤ) : mapFun f (z • x) = z • mapFun f x := by
  run_tac
    map_fun_tac

theorem pow (n : ℕ) : mapFun f (x ^ n) = mapFun f x ^ n := by
  run_tac
    map_fun_tac

theorem nat_cast (n : ℕ) : mapFun f (n : 𝕎 R) = n :=
  show mapFun f n.unaryCast = coe n by
    induction n <;> simp [*, ← Nat.unaryCast, ← add, ← one, ← zero] <;> rfl

theorem int_cast (n : ℤ) : mapFun f (n : 𝕎 R) = n :=
  show mapFun f n.castDef = coe n by
    cases n <;> simp [*, ← Int.castDef, ← add, ← one, ← neg, ← zero, ← nat_cast] <;> rfl

end MapFun

end WittVector

section Tactic

setup_tactic_parser

open Tactic

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- An auxiliary tactic for proving that `ghost_fun` respects the ring operations. -/
unsafe def tactic.interactive.ghost_fun_tac (φ fn : parse parser.pexpr) : tactic Unit := do
  let fn ← to_expr (ppquote.1 (%%ₓfn : Finₓ _ → ℕ → R))
  let quote.1 (Finₓ (%%ₓk) → _ → _) ← infer_type fn
  sorry
  sorry
  to_expr (ppquote.1 (congr_fun (congr_arg (@peval R _ (%%ₓk)) (witt_structure_int_prop p (%%ₓφ) n)) (%%ₓfn))) >>=
      note `this none
  sorry

end Tactic

namespace WittVector

/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`.
This function will be bundled as the ring homomorphism `witt_vector.ghost_map`
once the ring structure is available,
but we rely on it to set up the ring structure in the first place. -/
private def ghost_fun : 𝕎 R → ℕ → R := fun x n => aeval x.coeff (W_ ℤ n)

section GhostFun

include hp

-- The following lemmas are not `@[simp]` because they will be bundled in `ghost_map` later on.
variable (x y : 𝕎 R)

omit hp

@[local simp]
theorem matrix_vec_empty_coeff {R} (i j) : @coeff p R (Matrix.vecEmpty i) j = (Matrix.vecEmpty i : ℕ → R) j := by
  rcases i with ⟨_ | _ | _ | _ | i_val, ⟨⟩⟩

include hp

private theorem ghost_fun_zero : ghostFun (0 : 𝕎 R) = 0 := by
  ghost_fun_tac 0, ![]

private theorem ghost_fun_one : ghostFun (1 : 𝕎 R) = 1 := by
  ghost_fun_tac 1, ![]

private theorem ghost_fun_add : ghostFun (x + y) = ghostFun x + ghostFun y := by
  ghost_fun_tac X 0 + X 1, ![x.coeff, y.coeff]

private theorem ghost_fun_nat_cast (i : ℕ) : ghostFun (i : 𝕎 R) = i :=
  show ghostFun i.unaryCast = _ by
    induction i <;> simp [*, ← Nat.unaryCast, ← ghost_fun_zero, ← ghost_fun_one, ← ghost_fun_add, -Pi.coe_nat]

private theorem ghost_fun_sub : ghostFun (x - y) = ghostFun x - ghostFun y := by
  ghost_fun_tac X 0 - X 1, ![x.coeff, y.coeff]

private theorem ghost_fun_mul : ghostFun (x * y) = ghostFun x * ghostFun y := by
  ghost_fun_tac X 0 * X 1, ![x.coeff, y.coeff]

private theorem ghost_fun_neg : ghostFun (-x) = -ghostFun x := by
  ghost_fun_tac -X 0, ![x.coeff]

private theorem ghost_fun_int_cast (i : ℤ) : ghostFun (i : 𝕎 R) = i :=
  show ghostFun i.castDef = _ by
    cases i <;> simp [*, ← Int.castDef, ← ghost_fun_nat_cast, ← ghost_fun_neg, -Pi.coe_nat, -Pi.coe_int]

private theorem ghost_fun_nsmul (m : ℕ) : ghostFun (m • x) = m • ghostFun x := by
  ghost_fun_tac m • X 0, ![x.coeff]

private theorem ghost_fun_zsmul (m : ℤ) : ghostFun (m • x) = m • ghostFun x := by
  ghost_fun_tac m • X 0, ![x.coeff]

private theorem ghost_fun_pow (m : ℕ) : ghostFun (x ^ m) = ghostFun x ^ m := by
  ghost_fun_tac X 0 ^ m, ![x.coeff]

end GhostFun

variable (p) (R)

/-- The bijection between `𝕎 R` and `ℕ → R`, under the assumption that `p` is invertible in `R`.
In `witt_vector.ghost_equiv` we upgrade this to an isomorphism of rings. -/
private def ghost_equiv' [Invertible (p : R)] : 𝕎 R ≃ (ℕ → R) where
  toFun := ghostFun
  invFun := fun x => (mk p) fun n => aeval x (xInTermsOfW p R n)
  left_inv := by
    intro x
    ext n
    have := bind₁_witt_polynomial_X_in_terms_of_W p R n
    apply_fun aeval x.coeff  at this
    simpa only [← aeval_bind₁, ← aeval_X, ← ghost_fun, ← aeval_witt_polynomial]
  right_inv := by
    intro x
    ext n
    have := bind₁_X_in_terms_of_W_witt_polynomial p R n
    apply_fun aeval x  at this
    simpa only [← aeval_bind₁, ← aeval_X, ← ghost_fun, ← aeval_witt_polynomial]

include hp

@[local instance]
private def comm_ring_aux₁ : CommRingₓ (𝕎 (MvPolynomial R ℚ)) := by
  let this : CommRingₓ (MvPolynomial R ℚ) := MvPolynomial.commRing <;>
    exact
      (ghost_equiv' p (MvPolynomial R ℚ)).Injective.CommRing ghost_fun ghost_fun_zero ghost_fun_one ghost_fun_add
        ghost_fun_mul ghost_fun_neg ghost_fun_sub ghost_fun_nsmul ghost_fun_zsmul ghost_fun_pow ghost_fun_nat_cast
        ghost_fun_int_cast

@[local instance]
private def comm_ring_aux₂ : CommRingₓ (𝕎 (MvPolynomial R ℤ)) :=
  (mapFun.injective _ <| map_injective (Int.castRingHom ℚ) Int.cast_injective).CommRing _ (mapFun.zero _) (mapFun.one _)
    (mapFun.add _) (mapFun.mul _) (mapFun.neg _) (mapFun.sub _) (mapFun.nsmul _) (mapFun.zsmul _) (mapFun.pow _)
    (mapFun.nat_cast _) (mapFun.int_cast _)

/-- The commutative ring structure on `𝕎 R`. -/
instance : CommRingₓ (𝕎 R) :=
  (mapFun.surjective _ <| counit_surjective _).CommRing (map_fun <| MvPolynomial.counit _) (mapFun.zero _)
    (mapFun.one _) (mapFun.add _) (mapFun.mul _) (mapFun.neg _) (mapFun.sub _) (mapFun.nsmul _) (mapFun.zsmul _)
    (mapFun.pow _) (mapFun.nat_cast _) (mapFun.int_cast _)

variable {p R}

/-- `witt_vector.map f` is the ring homomorphism `𝕎 R →+* 𝕎 S` naturally induced
by a ring homomorphism `f : R →+* S`. It acts coefficientwise. -/
noncomputable def map (f : R →+* S) : 𝕎 R →+* 𝕎 S where
  toFun := mapFun f
  map_zero' := mapFun.zero f
  map_one' := mapFun.one f
  map_add' := mapFun.add f
  map_mul' := mapFun.mul f

theorem map_injective (f : R →+* S) (hf : Injective f) : Injective (map f : 𝕎 R → 𝕎 S) :=
  mapFun.injective f hf

theorem map_surjective (f : R →+* S) (hf : Surjective f) : Surjective (map f : 𝕎 R → 𝕎 S) :=
  mapFun.surjective f hf

@[simp]
theorem map_coeff (f : R →+* S) (x : 𝕎 R) (n : ℕ) : (map f x).coeff n = f (x.coeff n) :=
  rfl

/-- `witt_vector.ghost_map` is a ring homomorphism that maps each Witt vector
to the sequence of its ghost components. -/
def ghostMap : 𝕎 R →+* ℕ → R where
  toFun := ghostFun
  map_zero' := ghost_fun_zero
  map_one' := ghost_fun_one
  map_add' := ghost_fun_add
  map_mul' := ghost_fun_mul

/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`. -/
def ghostComponent (n : ℕ) : 𝕎 R →+* R :=
  (Pi.evalRingHom _ n).comp ghostMap

theorem ghost_component_apply (n : ℕ) (x : 𝕎 R) : ghostComponent n x = aeval x.coeff (W_ ℤ n) :=
  rfl

@[simp]
theorem ghost_map_apply (x : 𝕎 R) (n : ℕ) : ghostMap x n = ghostComponent n x :=
  rfl

section Invertible

variable (p R) [Invertible (p : R)]

/-- `witt_vector.ghost_map` is a ring isomorphism when `p` is invertible in `R`. -/
def ghostEquiv : 𝕎 R ≃+* (ℕ → R) :=
  { (ghostMap : 𝕎 R →+* ℕ → R), ghostEquiv' p R with }

@[simp]
theorem ghost_equiv_coe : (ghostEquiv p R : 𝕎 R →+* ℕ → R) = ghost_map :=
  rfl

theorem ghostMap.bijective_of_invertible : Function.Bijective (ghostMap : 𝕎 R → ℕ → R) :=
  (ghostEquiv p R).Bijective

end Invertible

/-- `witt_vector.coeff x 0` as a `ring_hom` -/
@[simps]
noncomputable def constantCoeff : 𝕎 R →+* R where
  toFun := fun x => x.coeff 0
  map_zero' := by
    simp
  map_one' := by
    simp
  map_add' := add_coeff_zero
  map_mul' := mul_coeff_zero

instance [Nontrivial R] : Nontrivial (𝕎 R) :=
  constantCoeff.domain_nontrivial

end WittVector


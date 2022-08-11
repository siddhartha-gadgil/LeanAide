/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathbin.RingTheory.WittVector.StructurePolynomial

/-!
# Witt vectors

In this file we define the type of `p`-typical Witt vectors and ring operations on it.
The ring axioms are verified in `ring_theory/witt_vector/basic.lean`.

For a fixed commutative ring `R` and prime `p`,
a Witt vector `x : 𝕎 R` is an infinite sequence `ℕ → R` of elements of `R`.
However, the ring operations `+` and `*` are not defined in the obvious component-wise way.
Instead, these operations are defined via certain polynomials
using the machinery in `structure_polynomial.lean`.
The `n`th value of the sum of two Witt vectors can depend on the `0`-th through `n`th values
of the summands. This effectively simulates a “carrying” operation.

## Main definitions

* `witt_vector p R`: the type of `p`-typical Witt vectors with coefficients in `R`.
* `witt_vector.coeff x n`: projects the `n`th value of the Witt vector `x`.

## Notation

We use notation `𝕎 R`, entered `\bbW`, for the Witt vectors over `R`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


noncomputable section

-- ./././Mathport/Syntax/Translate/Basic.lean:1474:34: infer kinds are unsupported in Lean 4: mk []
/-- `witt_vector p R` is the ring of `p`-typical Witt vectors over the commutative ring `R`,
where `p` is a prime number.

If `p` is invertible in `R`, this ring is isomorphic to `ℕ → R` (the product of `ℕ` copies of `R`).
If `R` is a ring of characteristic `p`, then `witt_vector p R` is a ring of characteristic `0`.
The canonical example is `witt_vector p (zmod p)`,
which is isomorphic to the `p`-adic integers `ℤ_[p]`. -/
structure WittVector (p : ℕ) (R : Type _) where mk ::
  coeff : ℕ → R

variable {p : ℕ}

-- mathport name: «expr𝕎»
/- We cannot make this `localized` notation, because the `p` on the RHS doesn't occur on the left
Hiding the `p` in the notation is very convenient, so we opt for repeating the `local notation`
in other files that use Witt vectors. -/
local notation "𝕎" => WittVector p

-- type as `\bbW`
namespace WittVector

variable (p) {R : Type _}

/-- Construct a Witt vector `mk p x : 𝕎 R` from a sequence `x` of elements of `R`. -/
add_decl_doc WittVector.mk

/-- `x.coeff n` is the `n`th coefficient of the Witt vector `x`.

This concept does not have a standard name in the literature.
-/
add_decl_doc WittVector.coeff

@[ext]
theorem ext {x y : 𝕎 R} (h : ∀ n, x.coeff n = y.coeff n) : x = y := by
  cases x
  cases y
  simp only at h
  simp [← Function.funext_iffₓ, ← h]

theorem ext_iff {x y : 𝕎 R} : x = y ↔ ∀ n, x.coeff n = y.coeff n :=
  ⟨fun h n => by
    rw [h], ext⟩

theorem coeff_mk (x : ℕ → R) : (mk p x).coeff = x :=
  rfl

/- These instances are not needed for the rest of the development,
but it is interesting to establish early on that `witt_vector p` is a lawful functor. -/
instance : Functor (WittVector p) where
  map := fun α β f v => mk p (f ∘ v.coeff)
  mapConst := fun α β a v => mk p fun _ => a

instance : IsLawfulFunctor (WittVector p) where
  map_const_eq := fun α β => rfl
  id_map := fun α ⟨v, _⟩ => rfl
  comp_map := fun α β γ f g v => rfl

variable (p) [hp : Fact p.Prime] [CommRingₓ R]

include hp

open MvPolynomial

section RingOperations

/-- The polynomials used for defining the element `0` of the ring of Witt vectors. -/
def wittZero : ℕ → MvPolynomial (Finₓ 0 × ℕ) ℤ :=
  wittStructureInt p 0

/-- The polynomials used for defining the element `1` of the ring of Witt vectors. -/
def wittOne : ℕ → MvPolynomial (Finₓ 0 × ℕ) ℤ :=
  wittStructureInt p 1

/-- The polynomials used for defining the addition of the ring of Witt vectors. -/
def wittAdd : ℕ → MvPolynomial (Finₓ 2 × ℕ) ℤ :=
  wittStructureInt p (x 0 + x 1)

/-- The polynomials used for defining repeated addition of the ring of Witt vectors. -/
def wittNsmul (n : ℕ) : ℕ → MvPolynomial (Finₓ 1 × ℕ) ℤ :=
  wittStructureInt p (n • x 0)

/-- The polynomials used for defining repeated addition of the ring of Witt vectors. -/
def wittZsmul (n : ℤ) : ℕ → MvPolynomial (Finₓ 1 × ℕ) ℤ :=
  wittStructureInt p (n • x 0)

/-- The polynomials used for describing the subtraction of the ring of Witt vectors. -/
def wittSub : ℕ → MvPolynomial (Finₓ 2 × ℕ) ℤ :=
  wittStructureInt p (x 0 - x 1)

/-- The polynomials used for defining the multiplication of the ring of Witt vectors. -/
def wittMul : ℕ → MvPolynomial (Finₓ 2 × ℕ) ℤ :=
  wittStructureInt p (x 0 * x 1)

/-- The polynomials used for defining the negation of the ring of Witt vectors. -/
def wittNeg : ℕ → MvPolynomial (Finₓ 1 × ℕ) ℤ :=
  wittStructureInt p (-x 0)

/-- The polynomials used for defining repeated addition of the ring of Witt vectors. -/
def wittPow (n : ℕ) : ℕ → MvPolynomial (Finₓ 1 × ℕ) ℤ :=
  wittStructureInt p (x 0 ^ n)

variable {p}

omit hp

/-- An auxiliary definition used in `witt_vector.eval`.
Evaluates a polynomial whose variables come from the disjoint union of `k` copies of `ℕ`,
with a curried evaluation `x`.
This can be defined more generally but we use only a specific instance here. -/
def peval {k : ℕ} (φ : MvPolynomial (Finₓ k × ℕ) ℤ) (x : Finₓ k → ℕ → R) : R :=
  aeval (Function.uncurry x) φ

/-- Let `φ` be a family of polynomials, indexed by natural numbers, whose variables come from the
disjoint union of `k` copies of `ℕ`, and let `xᵢ` be a Witt vector for `0 ≤ i < k`.

`eval φ x` evaluates `φ` mapping the variable `X_(i, n)` to the `n`th coefficient of `xᵢ`.

Instantiating `φ` with certain polynomials defined in `structure_polynomial.lean` establishes the
ring operations on `𝕎 R`. For example, `witt_vector.witt_add` is such a `φ` with `k = 2`;
evaluating this at `(x₀, x₁)` gives us the sum of two Witt vectors `x₀ + x₁`.
-/
def eval {k : ℕ} (φ : ℕ → MvPolynomial (Finₓ k × ℕ) ℤ) (x : Finₓ k → 𝕎 R) : 𝕎 R :=
  (mk p) fun n => (peval (φ n)) fun i => (x i).coeff

variable (R) [Fact p.Prime]

instance : Zero (𝕎 R) :=
  ⟨eval (wittZero p) ![]⟩

instance : Inhabited (𝕎 R) :=
  ⟨0⟩

instance : One (𝕎 R) :=
  ⟨eval (wittOne p) ![]⟩

instance : Add (𝕎 R) :=
  ⟨fun x y => eval (wittAdd p) ![x, y]⟩

instance : Sub (𝕎 R) :=
  ⟨fun x y => eval (wittSub p) ![x, y]⟩

instance hasNatScalar : HasSmul ℕ (𝕎 R) :=
  ⟨fun n x => eval (wittNsmul p n) ![x]⟩

instance hasIntScalar : HasSmul ℤ (𝕎 R) :=
  ⟨fun n x => eval (wittZsmul p n) ![x]⟩

instance : Mul (𝕎 R) :=
  ⟨fun x y => eval (wittMul p) ![x, y]⟩

instance : Neg (𝕎 R) :=
  ⟨fun x => eval (wittNeg p) ![x]⟩

instance hasNatPow : Pow (𝕎 R) ℕ :=
  ⟨fun x n => eval (wittPow p n) ![x]⟩

instance : HasNatCast (𝕎 R) :=
  ⟨Nat.unaryCast⟩

instance : HasIntCast (𝕎 R) :=
  ⟨Int.castDef⟩

end RingOperations

section WittStructureSimplifications

@[simp]
theorem witt_zero_eq_zero (n : ℕ) : wittZero p n = 0 := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [← witt_zero, ← wittStructureRat, ← bind₁, ← aeval_zero', ← constant_coeff_X_in_terms_of_W, ←
    RingHom.map_zero, ← AlgHom.map_zero, ← map_witt_structure_int]

@[simp]
theorem witt_one_zero_eq_one : wittOne p 0 = 1 := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [← witt_one, ← wittStructureRat, ← X_in_terms_of_W_zero, ← AlgHom.map_one, ← RingHom.map_one, ←
    bind₁_X_right, ← map_witt_structure_int]

@[simp]
theorem witt_one_pos_eq_zero (n : ℕ) (hn : 0 < n) : wittOne p n = 0 := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [← witt_one, ← wittStructureRat, ← RingHom.map_zero, ← AlgHom.map_one, ← RingHom.map_one, ←
    map_witt_structure_int]
  revert hn
  apply Nat.strong_induction_onₓ n
  clear n
  intro n IH hn
  rw [X_in_terms_of_W_eq]
  simp only [← AlgHom.map_mul, ← AlgHom.map_sub, ← AlgHom.map_sum, ← AlgHom.map_pow, ← bind₁_X_right, ← bind₁_C_right]
  rw [sub_mul, one_mulₓ]
  rw [Finset.sum_eq_single 0]
  · simp only [← inv_of_eq_inv, ← one_mulₓ, ← inv_pow, ← tsub_zero, ← RingHom.map_one, ← pow_zeroₓ]
    simp only [← one_pow, ← one_mulₓ, ← X_in_terms_of_W_zero, ← sub_self, ← bind₁_X_right]
    
  · intro i hin hi0
    rw [Finset.mem_range] at hin
    rw [IH _ hin (Nat.pos_of_ne_zeroₓ hi0), zero_pow (pow_pos hp.1.Pos _), mul_zero]
    
  · rw [Finset.mem_range]
    intro
    contradiction
    

@[simp]
theorem witt_add_zero : wittAdd p 0 = x (0, 0) + x (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [← witt_add, ← wittStructureRat, ← AlgHom.map_add, ← RingHom.map_add, ← rename_X, ← X_in_terms_of_W_zero, ←
    map_X, ← witt_polynomial_zero, ← bind₁_X_right, ← map_witt_structure_int]

@[simp]
theorem witt_sub_zero : wittSub p 0 = x (0, 0) - x (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [← witt_sub, ← wittStructureRat, ← AlgHom.map_sub, ← RingHom.map_sub, ← rename_X, ← X_in_terms_of_W_zero, ←
    map_X, ← witt_polynomial_zero, ← bind₁_X_right, ← map_witt_structure_int]

@[simp]
theorem witt_mul_zero : wittMul p 0 = x (0, 0) * x (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [← witt_mul, ← wittStructureRat, ← rename_X, ← X_in_terms_of_W_zero, ← map_X, ← witt_polynomial_zero, ←
    RingHom.map_mul, ← bind₁_X_right, ← AlgHom.map_mul, ← map_witt_structure_int]

@[simp]
theorem witt_neg_zero : wittNeg p 0 = -x (0, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [← witt_neg, ← wittStructureRat, ← rename_X, ← X_in_terms_of_W_zero, ← map_X, ← witt_polynomial_zero, ←
    RingHom.map_neg, ← AlgHom.map_neg, ← bind₁_X_right, ← map_witt_structure_int]

@[simp]
theorem constant_coeff_witt_add (n : ℕ) : constantCoeff (wittAdd p n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [← add_zeroₓ, ← RingHom.map_add, ← constant_coeff_X]

@[simp]
theorem constant_coeff_witt_sub (n : ℕ) : constantCoeff (wittSub p n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [← sub_zero, ← RingHom.map_sub, ← constant_coeff_X]

@[simp]
theorem constant_coeff_witt_mul (n : ℕ) : constantCoeff (wittMul p n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [← mul_zero, ← RingHom.map_mul, ← constant_coeff_X]

@[simp]
theorem constant_coeff_witt_neg (n : ℕ) : constantCoeff (wittNeg p n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [← neg_zero, ← RingHom.map_neg, ← constant_coeff_X]

@[simp]
theorem constant_coeff_witt_nsmul (m : ℕ) (n : ℕ) : constantCoeff (wittNsmul p m n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [← smul_zero, ← map_nsmul, ← constant_coeff_X]

@[simp]
theorem constant_coeff_witt_zsmul (z : ℤ) (n : ℕ) : constantCoeff (wittZsmul p z n) = 0 := by
  apply constant_coeff_witt_structure_int p _ _ n
  simp only [← smul_zero, ← map_zsmul, ← constant_coeff_X]

end WittStructureSimplifications

section Coeff

variable (p R)

@[simp]
theorem zero_coeff (n : ℕ) : (0 : 𝕎 R).coeff n = 0 :=
  show (aeval _ (wittZero p n) : R) = 0 by
    simp only [← witt_zero_eq_zero, ← AlgHom.map_zero]

@[simp]
theorem one_coeff_zero : (1 : 𝕎 R).coeff 0 = 1 :=
  show (aeval _ (wittOne p 0) : R) = 1 by
    simp only [← witt_one_zero_eq_one, ← AlgHom.map_one]

@[simp]
theorem one_coeff_eq_of_pos (n : ℕ) (hn : 0 < n) : coeff (1 : 𝕎 R) n = 0 :=
  show (aeval _ (wittOne p n) : R) = 0 by
    simp only [← hn, ← witt_one_pos_eq_zero, ← AlgHom.map_zero]

variable {p R}

omit hp

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
@[simp]
theorem v2_coeff {p' R'} (x y : WittVector p' R') (i : Finₓ 2) : (![x, y] i).coeff = ![x.coeff, y.coeff] i := by
  fin_cases i <;> simp

include hp

theorem add_coeff (x y : 𝕎 R) (n : ℕ) : (x + y).coeff n = peval (wittAdd p n) ![x.coeff, y.coeff] := by
  simp [← (· + ·), ← eval]

theorem sub_coeff (x y : 𝕎 R) (n : ℕ) : (x - y).coeff n = peval (wittSub p n) ![x.coeff, y.coeff] := by
  simp [← Sub.sub, ← eval]

theorem mul_coeff (x y : 𝕎 R) (n : ℕ) : (x * y).coeff n = peval (wittMul p n) ![x.coeff, y.coeff] := by
  simp [← (· * ·), ← eval]

theorem neg_coeff (x : 𝕎 R) (n : ℕ) : (-x).coeff n = peval (wittNeg p n) ![x.coeff] := by
  simp [← Neg.neg, ← eval, ← Matrix.cons_fin_one]

theorem nsmul_coeff (m : ℕ) (x : 𝕎 R) (n : ℕ) : (m • x).coeff n = peval (wittNsmul p m n) ![x.coeff] := by
  simp [← HasSmul.smul, ← eval, ← Matrix.cons_fin_one]

theorem zsmul_coeff (m : ℤ) (x : 𝕎 R) (n : ℕ) : (m • x).coeff n = peval (wittZsmul p m n) ![x.coeff] := by
  simp [← HasSmul.smul, ← eval, ← Matrix.cons_fin_one]

theorem pow_coeff (m : ℕ) (x : 𝕎 R) (n : ℕ) : (x ^ m).coeff n = peval (wittPow p m n) ![x.coeff] := by
  simp [← Pow.pow, ← eval, ← Matrix.cons_fin_one]

theorem add_coeff_zero (x y : 𝕎 R) : (x + y).coeff 0 = x.coeff 0 + y.coeff 0 := by
  simp [← add_coeff, ← peval]

theorem mul_coeff_zero (x y : 𝕎 R) : (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  simp [← mul_coeff, ← peval]

end Coeff

theorem witt_add_vars (n : ℕ) : (wittAdd p n).vars ⊆ Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_sub_vars (n : ℕ) : (wittSub p n).vars ⊆ Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_mul_vars (n : ℕ) : (wittMul p n).vars ⊆ Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_neg_vars (n : ℕ) : (wittNeg p n).vars ⊆ Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_nsmul_vars (m : ℕ) (n : ℕ) : (wittNsmul p m n).vars ⊆ Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_zsmul_vars (m : ℤ) (n : ℕ) : (wittZsmul p m n).vars ⊆ Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

theorem witt_pow_vars (m : ℕ) (n : ℕ) : (wittPow p m n).vars ⊆ Finset.univ.product (Finset.range (n + 1)) :=
  witt_structure_int_vars _ _ _

end WittVector


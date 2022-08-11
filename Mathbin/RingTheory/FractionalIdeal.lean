/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Filippo A. E. Nuccio
-/
import Mathbin.Algebra.BigOperators.Finprod
import Mathbin.RingTheory.IntegralClosure
import Mathbin.RingTheory.Localization.Integer
import Mathbin.RingTheory.Localization.Submodule
import Mathbin.RingTheory.Noetherian
import Mathbin.RingTheory.PrincipalIdealDomain
import Mathbin.Tactic.FieldSimp

/-!
# Fractional ideals

This file defines fractional ideals of an integral domain and proves basic facts about them.

## Main definitions
Let `S` be a submonoid of an integral domain `R`, `P` the localization of `R` at `S`, and `f` the
natural ring hom from `R` to `P`.
 * `is_fractional` defines which `R`-submodules of `P` are fractional ideals
 * `fractional_ideal S P` is the type of fractional ideals in `P`
 * `has_coe_t (ideal R) (fractional_ideal S P)` instance
 * `comm_semiring (fractional_ideal S P)` instance:
   the typical ideal operations generalized to fractional ideals
 * `lattice (fractional_ideal S P)` instance
 * `map` is the pushforward of a fractional ideal along an algebra morphism

Let `K` be the localization of `R` at `R⁰ = R \ {0}` (i.e. the field of fractions).
 * `fractional_ideal R⁰ K` is the type of fractional ideals in the field of fractions
 * `has_div (fractional_ideal R⁰ K)` instance:
   the ideal quotient `I / J` (typically written $I : J$, but a `:` operator cannot be defined)

## Main statements

  * `mul_left_mono` and `mul_right_mono` state that ideal multiplication is monotone
  * `prod_one_self_div_eq` states that `1 / I` is the inverse of `I` if one exists
  * `is_noetherian` states that every fractional ideal of a noetherian integral domain is noetherian

## Implementation notes

Fractional ideals are considered equal when they contain the same elements,
independent of the denominator `a : R` such that `a I ⊆ R`.
Thus, we define `fractional_ideal` to be the subtype of the predicate `is_fractional`,
instead of having `fractional_ideal` be a structure of which `a` is a field.

Most definitions in this file specialize operations from submodules to fractional ideals,
proving that the result of this operation is fractional if the input is fractional.
Exceptions to this rule are defining `(+) := (⊔)` and `⊥ := 0`,
in order to re-use their respective proof terms.
We can still use `simp` to show `↑I + ↑J = ↑(I + J)` and `↑⊥ = ↑0`.

Many results in fact do not need that `P` is a localization, only that `P` is an
`R`-algebra. We omit the `is_localization` parameter whenever this is practical.
Similarly, we don't assume that the localization is a field until we need it to
define ideal quotients. When this assumption is needed, we replace `S` with `R⁰`,
making the localization a field.

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/


open IsLocalization

open Pointwise

open nonZeroDivisors

section Defs

variable {R : Type _} [CommRingₓ R] {S : Submonoid R} {P : Type _} [CommRingₓ P]

variable [Algebra R P]

variable (S)

/-- A submodule `I` is a fractional ideal if `a I ⊆ R` for some `a ≠ 0`. -/
def IsFractional (I : Submodule R P) :=
  ∃ a ∈ S, ∀, ∀ b ∈ I, ∀, IsInteger R (a • b)

variable (S P)

/-- The fractional ideals of a domain `R` are ideals of `R` divided by some `a ∈ R`.

  More precisely, let `P` be a localization of `R` at some submonoid `S`,
  then a fractional ideal `I ⊆ P` is an `R`-submodule of `P`,
  such that there is a nonzero `a : R` with `a I ⊆ R`.
-/
def FractionalIdeal :=
  { I : Submodule R P // IsFractional S I }

end Defs

namespace FractionalIdeal

open Set

open Submodule

variable {R : Type _} [CommRingₓ R] {S : Submonoid R} {P : Type _} [CommRingₓ P]

variable [Algebra R P] [loc : IsLocalization S P]

/-- Map a fractional ideal `I` to a submodule by forgetting that `∃ a, a I ⊆ R`.

This coercion is typically called `coe_to_submodule` in lemma names
(or `coe` when the coercion is clear from the context),
not to be confused with `is_localization.coe_submodule : ideal R → submodule R P`
(which we use to define `coe : ideal R → fractional_ideal S P`,
referred to as `coe_ideal` in theorem names).
-/
instance : Coe (FractionalIdeal S P) (Submodule R P) :=
  ⟨fun I => I.val⟩

protected theorem is_fractional (I : FractionalIdeal S P) : IsFractional S (I : Submodule R P) :=
  I.Prop

section SetLike

instance : SetLike (FractionalIdeal S P) P where
  coe := fun I => ↑(I : Submodule R P)
  coe_injective' := SetLike.coe_injective.comp Subtype.coe_injective

@[simp]
theorem mem_coe {I : FractionalIdeal S P} {x : P} : x ∈ (I : Submodule R P) ↔ x ∈ I :=
  Iff.rfl

@[ext]
theorem ext {I J : FractionalIdeal S P} : (∀ x, x ∈ I ↔ x ∈ J) → I = J :=
  SetLike.ext

/-- Copy of a `fractional_ideal` with a new underlying set equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : FractionalIdeal S P :=
  ⟨Submodule.copy p s hs, by
    convert p.is_fractional
    ext
    simp only [← hs]
    rfl⟩

end SetLike

@[simp]
theorem val_eq_coe (I : FractionalIdeal S P) : I.val = I :=
  rfl

@[simp, norm_cast]
theorem coe_mk (I : Submodule R P) (hI : IsFractional S I) : (Subtype.mk I hI : Submodule R P) = I :=
  rfl

theorem coe_to_submodule_injective : Function.Injective (coe : FractionalIdeal S P → Submodule R P) :=
  Subtype.coe_injective

theorem is_fractional_of_le_one (I : Submodule R P) (h : I ≤ 1) : IsFractional S I := by
  use 1, S.one_mem
  intro b hb
  rw [one_smul]
  obtain ⟨b', b'_mem, rfl⟩ := h hb
  exact Set.mem_range_self b'

theorem is_fractional_of_le {I : Submodule R P} {J : FractionalIdeal S P} (hIJ : I ≤ J) : IsFractional S I := by
  obtain ⟨a, a_mem, ha⟩ := J.is_fractional
  use a, a_mem
  intro b b_mem
  exact ha b (hIJ b_mem)

/-- Map an ideal `I` to a fractional ideal by forgetting `I` is integral.

This is a bundled version of `is_localization.coe_submodule : ideal R → submodule R P`,
which is not to be confused with the `coe : fractional_ideal S P → submodule R P`,
also called `coe_to_submodule` in theorem names.

This map is available as a ring hom, called `fractional_ideal.coe_ideal_hom`.
-/
-- Is a `coe_t` rather than `coe` to speed up failing inference, see library note [use has_coe_t]
instance coeToFractionalIdeal : CoeTₓ (Ideal R) (FractionalIdeal S P) :=
  ⟨fun I =>
    ⟨coeSubmodule P I,
      is_fractional_of_le_one _
        (by
          simpa using coe_submodule_mono P (le_top : I ≤ ⊤))⟩⟩

@[simp, norm_cast]
theorem coe_coe_ideal (I : Ideal R) : ((I : FractionalIdeal S P) : Submodule R P) = coeSubmodule P I :=
  rfl

variable (S)

@[simp]
theorem mem_coe_ideal {x : P} {I : Ideal R} : x ∈ (I : FractionalIdeal S P) ↔ ∃ x', x' ∈ I ∧ algebraMap R P x' = x :=
  mem_coe_submodule _ _

theorem mem_coe_ideal_of_mem {x : R} {I : Ideal R} (hx : x ∈ I) : algebraMap R P x ∈ (I : FractionalIdeal S P) :=
  (mem_coe_ideal S).mpr ⟨x, hx, rfl⟩

theorem coe_ideal_le_coe_ideal' [IsLocalization S P] (h : S ≤ nonZeroDivisors R) {I J : Ideal R} :
    (I : FractionalIdeal S P) ≤ J ↔ I ≤ J :=
  coe_submodule_le_coe_submodule h

@[simp]
theorem coe_ideal_le_coe_ideal (K : Type _) [CommRingₓ K] [Algebra R K] [IsFractionRing R K] {I J : Ideal R} :
    (I : FractionalIdeal R⁰ K) ≤ J ↔ I ≤ J :=
  IsFractionRing.coe_submodule_le_coe_submodule

instance : Zero (FractionalIdeal S P) :=
  ⟨(0 : Ideal R)⟩

@[simp]
theorem mem_zero_iff {x : P} : x ∈ (0 : FractionalIdeal S P) ↔ x = 0 :=
  ⟨fun ⟨x', x'_mem_zero, x'_eq_x⟩ => by
    have x'_eq_zero : x' = 0 := x'_mem_zero
    simp [← x'_eq_x.symm, ← x'_eq_zero], fun hx =>
    ⟨0, rfl, by
      simp [← hx]⟩⟩

variable {S}

@[simp, norm_cast]
theorem coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : Submodule R P) :=
  Submodule.ext fun _ => mem_zero_iff S

@[simp, norm_cast]
theorem coe_to_fractional_ideal_bot : ((⊥ : Ideal R) : FractionalIdeal S P) = 0 :=
  rfl

variable (P)

include loc

@[simp]
theorem exists_mem_to_map_eq {x : R} {I : Ideal R} (h : S ≤ nonZeroDivisors R) :
    (∃ x', x' ∈ I ∧ algebraMap R P x' = algebraMap R P x) ↔ x ∈ I :=
  ⟨fun ⟨x', hx', Eq⟩ => IsLocalization.injective _ h Eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩

variable {P}

theorem coe_to_fractional_ideal_injective (h : S ≤ nonZeroDivisors R) :
    Function.Injective (coe : Ideal R → FractionalIdeal S P) := fun I J heq =>
  have : ∀ x : R, algebraMap R P x ∈ (I : FractionalIdeal S P) ↔ algebraMap R P x ∈ (J : FractionalIdeal S P) :=
    fun x => HEq ▸ Iff.rfl
  Ideal.ext
    (by
      simpa only [← mem_coe_ideal, ← exists_prop, ← exists_mem_to_map_eq P h] using this)

theorem coe_to_fractional_ideal_eq_zero {I : Ideal R} (hS : S ≤ nonZeroDivisors R) :
    (I : FractionalIdeal S P) = 0 ↔ I = (⊥ : Ideal R) :=
  ⟨fun h => coe_to_fractional_ideal_injective hS h, fun h => by
    rw [h, coe_to_fractional_ideal_bot]⟩

theorem coe_to_fractional_ideal_ne_zero {I : Ideal R} (hS : S ≤ nonZeroDivisors R) :
    (I : FractionalIdeal S P) ≠ 0 ↔ I ≠ (⊥ : Ideal R) :=
  not_iff_not.mpr (coe_to_fractional_ideal_eq_zero hS)

omit loc

theorem coe_to_submodule_eq_bot {I : FractionalIdeal S P} : (I : Submodule R P) = ⊥ ↔ I = 0 :=
  ⟨fun h =>
    coe_to_submodule_injective
      (by
        simp [← h]),
    fun h => by
    simp [← h]⟩

theorem coe_to_submodule_ne_bot {I : FractionalIdeal S P} : ↑I ≠ (⊥ : Submodule R P) ↔ I ≠ 0 :=
  not_iff_not.mpr coe_to_submodule_eq_bot

instance : Inhabited (FractionalIdeal S P) :=
  ⟨0⟩

instance : One (FractionalIdeal S P) :=
  ⟨(⊤ : Ideal R)⟩

variable (S)

@[simp, norm_cast]
theorem coe_ideal_top : ((⊤ : Ideal R) : FractionalIdeal S P) = 1 :=
  rfl

theorem mem_one_iff {x : P} : x ∈ (1 : FractionalIdeal S P) ↔ ∃ x' : R, algebraMap R P x' = x :=
  Iff.intro (fun ⟨x', _, h⟩ => ⟨x', h⟩) fun ⟨x', h⟩ => ⟨x', ⟨⟩, h⟩

theorem coe_mem_one (x : R) : algebraMap R P x ∈ (1 : FractionalIdeal S P) :=
  (mem_one_iff S).mpr ⟨x, rfl⟩

theorem one_mem_one : (1 : P) ∈ (1 : FractionalIdeal S P) :=
  (mem_one_iff S).mpr ⟨1, RingHom.map_one _⟩

variable {S}

/-- `(1 : fractional_ideal S P)` is defined as the R-submodule `f(R) ≤ P`.

However, this is not definitionally equal to `1 : submodule R P`,
which is proved in the actual `simp` lemma `coe_one`. -/
theorem coe_one_eq_coe_submodule_top : ↑(1 : FractionalIdeal S P) = coeSubmodule P (⊤ : Ideal R) :=
  rfl

@[simp, norm_cast]
theorem coe_one : (↑(1 : FractionalIdeal S P) : Submodule R P) = 1 := by
  rw [coe_one_eq_coe_submodule_top, coe_submodule_top]

section Lattice

/-!
### `lattice` section

Defines the order on fractional ideals as inclusion of their underlying sets,
and ports the lattice structure on submodules to fractional ideals.
-/


@[simp]
theorem coe_le_coe {I J : FractionalIdeal S P} : (I : Submodule R P) ≤ (J : Submodule R P) ↔ I ≤ J :=
  Iff.rfl

theorem zero_le (I : FractionalIdeal S P) : 0 ≤ I := by
  intro x hx
  convert Submodule.zero_mem _
  simpa using hx

instance orderBot : OrderBot (FractionalIdeal S P) where
  bot := 0
  bot_le := zero_le

@[simp]
theorem bot_eq_zero : (⊥ : FractionalIdeal S P) = 0 :=
  rfl

@[simp]
theorem le_zero_iff {I : FractionalIdeal S P} : I ≤ 0 ↔ I = 0 :=
  le_bot_iff

theorem eq_zero_iff {I : FractionalIdeal S P} : I = 0 ↔ ∀, ∀ x ∈ I, ∀, x = (0 : P) :=
  ⟨fun h x hx => by
    simpa [← h, ← mem_zero_iff] using hx, fun h => le_bot_iff.mp fun x hx => (mem_zero_iff S).mpr (h x hx)⟩

theorem _root_.is_fractional.sup {I J : Submodule R P} : IsFractional S I → IsFractional S J → IsFractional S (I⊔J)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩ =>
    ⟨aI * aJ, S.mul_mem haI haJ, fun b hb => by
      rcases mem_sup.mp hb with ⟨bI, hbI, bJ, hbJ, rfl⟩
      rw [smul_add]
      apply is_integer_add
      · rw [mul_smul, smul_comm]
        exact is_integer_smul (hI bI hbI)
        
      · rw [mul_smul]
        exact is_integer_smul (hJ bJ hbJ)
        ⟩

theorem _root_.is_fractional.inf_right {I : Submodule R P} : IsFractional S I → ∀ J, IsFractional S (I⊓J)
  | ⟨aI, haI, hI⟩, J =>
    ⟨aI, haI, fun b hb => by
      rcases mem_inf.mp hb with ⟨hbI, hbJ⟩
      exact hI b hbI⟩

instance : HasInf (FractionalIdeal S P) :=
  ⟨fun I J => ⟨I⊓J, I.IsFractional.inf_right J⟩⟩

@[simp, norm_cast]
theorem coe_inf (I J : FractionalIdeal S P) : ↑(I⊓J) = (I⊓J : Submodule R P) :=
  rfl

instance : HasSup (FractionalIdeal S P) :=
  ⟨fun I J => ⟨I⊔J, I.IsFractional.sup J.IsFractional⟩⟩

@[norm_cast]
theorem coe_sup (I J : FractionalIdeal S P) : ↑(I⊔J) = (I⊔J : Submodule R P) :=
  rfl

instance lattice : Lattice (FractionalIdeal S P) :=
  Function.Injective.lattice _ Subtype.coe_injective coe_sup coe_inf

instance : SemilatticeSup (FractionalIdeal S P) :=
  { FractionalIdeal.lattice with }

end Lattice

section Semiringₓ

instance : Add (FractionalIdeal S P) :=
  ⟨(·⊔·)⟩

@[simp]
theorem sup_eq_add (I J : FractionalIdeal S P) : I⊔J = I + J :=
  rfl

@[simp, norm_cast]
theorem coe_add (I J : FractionalIdeal S P) : (↑(I + J) : Submodule R P) = I + J :=
  rfl

@[simp, norm_cast]
theorem coe_ideal_sup (I J : Ideal R) : ↑(I⊔J) = (I + J : FractionalIdeal S P) :=
  coe_to_submodule_injective <| coe_submodule_sup _ _ _

theorem _root_.is_fractional.nsmul {I : Submodule R P} :
    ∀ n : ℕ, IsFractional S I → IsFractional S (n • I : Submodule R P)
  | 0, _ => by
    rw [zero_smul]
    convert ((0 : Ideal R) : FractionalIdeal S P).IsFractional
    simp
  | n + 1, h => by
    rw [succ_nsmul]
    exact h.sup (_root_.is_fractional.nsmul n h)

instance : HasSmul ℕ (FractionalIdeal S P) where smul := fun n I => ⟨n • I, I.IsFractional.nsmul n⟩

@[norm_cast]
theorem coe_nsmul (n : ℕ) (I : FractionalIdeal S P) : (↑(n • I) : Submodule R P) = n • I :=
  rfl

theorem _root_.is_fractional.mul {I J : Submodule R P} :
    IsFractional S I → IsFractional S J → IsFractional S (I * J : Submodule R P)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩ =>
    ⟨aI * aJ, S.mul_mem haI haJ, fun b hb => by
      apply Submodule.mul_induction_on hb
      · intro m hm n hn
        obtain ⟨n', hn'⟩ := hJ n hn
        rw [mul_smul, mul_comm m, ← smul_mul_assoc, ← hn', ← Algebra.smul_def]
        apply hI
        exact Submodule.smul_mem _ _ hm
        
      · intro x y hx hy
        rw [smul_add]
        apply is_integer_add hx hy
        ⟩

theorem _root_.is_fractional.pow {I : Submodule R P} (h : IsFractional S I) :
    ∀ n : ℕ, IsFractional S (I ^ n : Submodule R P)
  | 0 => is_fractional_of_le_one _ (pow_zeroₓ _).le
  | n + 1 => (pow_succₓ I n).symm ▸ h.mul (_root_.is_fractional.pow n)

/-- `fractional_ideal.mul` is the product of two fractional ideals,
used to define the `has_mul` instance.

This is only an auxiliary definition: the preferred way of writing `I.mul J` is `I * J`.

Elaborated terms involving `fractional_ideal` tend to grow quite large,
so by making definitions irreducible, we hope to avoid deep unfolds.
-/
irreducible_def mul (I J : FractionalIdeal S P) : FractionalIdeal S P :=
  ⟨I * J, I.IsFractional.mul J.IsFractional⟩

attribute [local semireducible] mul

instance : Mul (FractionalIdeal S P) :=
  ⟨fun I J => mul I J⟩

@[simp]
theorem mul_eq_mul (I J : FractionalIdeal S P) : mul I J = I * J :=
  rfl

@[simp, norm_cast]
theorem coe_mul (I J : FractionalIdeal S P) : (↑(I * J) : Submodule R P) = I * J :=
  rfl

@[simp, norm_cast]
theorem coe_ideal_mul (I J : Ideal R) : (↑(I * J) : FractionalIdeal S P) = I * J :=
  coe_to_submodule_injective <| coe_submodule_mul _ _ _

theorem mul_left_mono (I : FractionalIdeal S P) : Monotone ((· * ·) I) := fun J J' h =>
  mul_le.mpr fun x hx y hy => mul_mem_mul hx (h hy)

theorem mul_right_mono (I : FractionalIdeal S P) : Monotone fun J => J * I := fun J J' h =>
  mul_le.mpr fun x hx y hy => mul_mem_mul (h hx) hy

theorem mul_mem_mul {I J : FractionalIdeal S P} {i j : P} (hi : i ∈ I) (hj : j ∈ J) : i * j ∈ I * J :=
  Submodule.mul_mem_mul hi hj

theorem mul_le {I J K : FractionalIdeal S P} : I * J ≤ K ↔ ∀, ∀ i ∈ I, ∀, ∀ j ∈ J, ∀, i * j ∈ K :=
  Submodule.mul_le

instance : Pow (FractionalIdeal S P) ℕ :=
  ⟨fun I n => ⟨I ^ n, I.IsFractional.pow n⟩⟩

@[simp, norm_cast]
theorem coe_pow (I : FractionalIdeal S P) (n : ℕ) : ↑(I ^ n) = (I ^ n : Submodule R P) :=
  rfl

@[elab_as_eliminator]
protected theorem mul_induction_on {I J : FractionalIdeal S P} {C : P → Prop} {r : P} (hr : r ∈ I * J)
    (hm : ∀, ∀ i ∈ I, ∀, ∀ j ∈ J, ∀, C (i * j)) (ha : ∀ x y, C x → C y → C (x + y)) : C r :=
  Submodule.mul_induction_on hr hm ha

instance : HasNatCast (FractionalIdeal S P) :=
  ⟨Nat.unaryCast⟩

theorem coe_nat_cast (n : ℕ) : ((n : FractionalIdeal S P) : Submodule R P) = n :=
  show ↑n.unaryCast = ↑n by
    induction n <;> simp [*, ← Nat.unaryCast]

instance : CommSemiringₓ (FractionalIdeal S P) :=
  Function.Injective.commSemiring coe Subtype.coe_injective coe_zero coe_one coe_add coe_mul (fun _ _ => coe_nsmul _ _)
    coe_pow coe_nat_cast

section Order

theorem add_le_add_left {I J : FractionalIdeal S P} (hIJ : I ≤ J) (J' : FractionalIdeal S P) : J' + I ≤ J' + J :=
  sup_le_sup_left hIJ J'

theorem mul_le_mul_left {I J : FractionalIdeal S P} (hIJ : I ≤ J) (J' : FractionalIdeal S P) : J' * I ≤ J' * J :=
  mul_le.mpr fun k hk j hj => mul_mem_mul hk (hIJ hj)

theorem le_self_mul_self {I : FractionalIdeal S P} (hI : 1 ≤ I) : I ≤ I * I := by
  convert mul_left_mono I hI
  exact (mul_oneₓ I).symm

theorem mul_self_le_self {I : FractionalIdeal S P} (hI : I ≤ 1) : I * I ≤ I := by
  convert mul_left_mono I hI
  exact (mul_oneₓ I).symm

theorem coe_ideal_le_one {I : Ideal R} : (I : FractionalIdeal S P) ≤ 1 := fun x hx =>
  let ⟨y, _, hy⟩ := (FractionalIdeal.mem_coe_ideal S).mp hx
  (FractionalIdeal.mem_one_iff S).mpr ⟨y, hy⟩

theorem le_one_iff_exists_coe_ideal {J : FractionalIdeal S P} : J ≤ (1 : FractionalIdeal S P) ↔ ∃ I : Ideal R, ↑I = J :=
  by
  constructor
  · intro hJ
    refine' ⟨⟨{ x : R | algebraMap R P x ∈ J }, _, _, _⟩, _⟩
    · intro a b ha hb
      rw [mem_set_of_eq, RingHom.map_add]
      exact J.val.add_mem ha hb
      
    · rw [mem_set_of_eq, RingHom.map_zero]
      exact J.val.zero_mem
      
    · intro c x hx
      rw [smul_eq_mul, mem_set_of_eq, RingHom.map_mul, ← Algebra.smul_def]
      exact J.val.smul_mem c hx
      
    · ext x
      constructor
      · rintro ⟨y, hy, eq_y⟩
        rwa [← eq_y]
        
      · intro hx
        obtain ⟨y, eq_x⟩ := (FractionalIdeal.mem_one_iff S).mp (hJ hx)
        rw [← eq_x] at *
        exact ⟨y, hx, rfl⟩
        
      
    
  · rintro ⟨I, hI⟩
    rw [← hI]
    apply coe_ideal_le_one
    

variable (S P)

/-- `coe_ideal_hom (S : submonoid R) P` is `coe : ideal R → fractional_ideal S P` as a ring hom -/
@[simps]
def coeIdealHom : Ideal R →+* FractionalIdeal S P where
  toFun := coe
  map_add' := coe_ideal_sup
  map_mul' := coe_ideal_mul
  map_one' := by
    rw [Ideal.one_eq_top, coe_ideal_top]
  map_zero' := coe_to_fractional_ideal_bot

theorem coe_ideal_pow (I : Ideal R) (n : ℕ) : (↑(I ^ n) : FractionalIdeal S P) = I ^ n :=
  (FractionalIdeal.coeIdealHom S P).map_pow _ n

open BigOperators

theorem coe_ideal_finprod [IsLocalization S P] {α : Sort _} {f : α → Ideal R} (hS : S ≤ nonZeroDivisors R) :
    ((∏ᶠ a : α, f a : Ideal R) : FractionalIdeal S P) = ∏ᶠ a : α, (f a : FractionalIdeal S P) :=
  MonoidHom.map_finprod_of_injective (FractionalIdeal.coeIdealHom S P).toMonoidHom
    (FractionalIdeal.coe_to_fractional_ideal_injective hS) f

end Order

variable {P' : Type _} [CommRingₓ P'] [Algebra R P'] [loc' : IsLocalization S P']

variable {P'' : Type _} [CommRingₓ P''] [Algebra R P''] [loc'' : IsLocalization S P'']

theorem _root_.is_fractional.map (g : P →ₐ[R] P') {I : Submodule R P} :
    IsFractional S I → IsFractional S (Submodule.map g.toLinearMap I)
  | ⟨a, a_nonzero, hI⟩ =>
    ⟨a, a_nonzero, fun b hb => by
      obtain ⟨b', b'_mem, hb'⟩ := submodule.mem_map.mp hb
      obtain ⟨x, hx⟩ := hI b' b'_mem
      use x
      erw [← g.commutes, hx, g.map_smul, hb']⟩

/-- `I.map g` is the pushforward of the fractional ideal `I` along the algebra morphism `g` -/
def map (g : P →ₐ[R] P') : FractionalIdeal S P → FractionalIdeal S P' := fun I =>
  ⟨Submodule.map g.toLinearMap I, I.IsFractional.map g⟩

@[simp, norm_cast]
theorem coe_map (g : P →ₐ[R] P') (I : FractionalIdeal S P) : ↑(map g I) = Submodule.map g.toLinearMap I :=
  rfl

@[simp]
theorem mem_map {I : FractionalIdeal S P} {g : P →ₐ[R] P'} {y : P'} : y ∈ I.map g ↔ ∃ x, x ∈ I ∧ g x = y :=
  Submodule.mem_map

variable (I J : FractionalIdeal S P) (g : P →ₐ[R] P')

@[simp]
theorem map_id : I.map (AlgHom.id _ _) = I :=
  coe_to_submodule_injective (Submodule.map_id I)

@[simp]
theorem map_comp (g' : P' →ₐ[R] P'') : I.map (g'.comp g) = (I.map g).map g' :=
  coe_to_submodule_injective (Submodule.map_comp g.toLinearMap g'.toLinearMap I)

@[simp, norm_cast]
theorem map_coe_ideal (I : Ideal R) : (I : FractionalIdeal S P).map g = I := by
  ext x
  simp only [← mem_coe_ideal]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, (g.commutes y).symm⟩
    
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, g.commutes y⟩
    

@[simp]
theorem map_one : (1 : FractionalIdeal S P).map g = 1 :=
  map_coe_ideal g ⊤

@[simp]
theorem map_zero : (0 : FractionalIdeal S P).map g = 0 :=
  map_coe_ideal g 0

@[simp]
theorem map_add : (I + J).map g = I.map g + J.map g :=
  coe_to_submodule_injective (Submodule.map_sup _ _ _)

@[simp]
theorem map_mul : (I * J).map g = I.map g * J.map g :=
  coe_to_submodule_injective (Submodule.map_mul _ _ _)

@[simp]
theorem map_map_symm (g : P ≃ₐ[R] P') : (I.map (g : P →ₐ[R] P')).map (g.symm : P' →ₐ[R] P) = I := by
  rw [← map_comp, g.symm_comp, map_id]

@[simp]
theorem map_symm_map (I : FractionalIdeal S P') (g : P ≃ₐ[R] P') :
    (I.map (g.symm : P' →ₐ[R] P)).map (g : P →ₐ[R] P') = I := by
  rw [← map_comp, g.comp_symm, map_id]

theorem map_mem_map {f : P →ₐ[R] P'} (h : Function.Injective f) {x : P} {I : FractionalIdeal S P} :
    f x ∈ map f I ↔ x ∈ I :=
  mem_map.trans ⟨fun ⟨x', hx', x'_eq⟩ => h x'_eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩

theorem map_injective (f : P →ₐ[R] P') (h : Function.Injective f) :
    Function.Injective (map f : FractionalIdeal S P → FractionalIdeal S P') := fun I J hIJ =>
  FractionalIdeal.ext fun x => (FractionalIdeal.map_mem_map h).symm.trans (hIJ.symm ▸ FractionalIdeal.map_mem_map h)

/-- If `g` is an equivalence, `map g` is an isomorphism -/
def mapEquiv (g : P ≃ₐ[R] P') : FractionalIdeal S P ≃+* FractionalIdeal S P' where
  toFun := map g
  invFun := map g.symm
  map_add' := fun I J => map_add I J _
  map_mul' := fun I J => map_mul I J _
  left_inv := fun I => by
    rw [← map_comp, AlgEquiv.symm_comp, map_id]
  right_inv := fun I => by
    rw [← map_comp, AlgEquiv.comp_symm, map_id]

@[simp]
theorem coe_fun_map_equiv (g : P ≃ₐ[R] P') : (mapEquiv g : FractionalIdeal S P → FractionalIdeal S P') = map g :=
  rfl

@[simp]
theorem map_equiv_apply (g : P ≃ₐ[R] P') (I : FractionalIdeal S P) : mapEquiv g I = map (↑g) I :=
  rfl

@[simp]
theorem map_equiv_symm (g : P ≃ₐ[R] P') : ((mapEquiv g).symm : FractionalIdeal S P' ≃+* _) = mapEquiv g.symm :=
  rfl

@[simp]
theorem map_equiv_refl : mapEquiv AlgEquiv.refl = RingEquiv.refl (FractionalIdeal S P) :=
  RingEquiv.ext fun x => by
    simp

theorem is_fractional_span_iff {s : Set P} :
    IsFractional S (span R s) ↔ ∃ a ∈ S, ∀ b : P, b ∈ s → IsInteger R (a • b) :=
  ⟨fun ⟨a, a_mem, h⟩ => ⟨a, a_mem, fun b hb => h b (subset_span hb)⟩, fun ⟨a, a_mem, h⟩ =>
    ⟨a, a_mem, fun b hb =>
      span_induction hb h
        (by
          rw [smul_zero]
          exact is_integer_zero)
        (fun x y hx hy => by
          rw [smul_add]
          exact is_integer_add hx hy)
        fun s x hx => by
        rw [smul_comm]
        exact is_integer_smul hx⟩⟩

include loc

theorem is_fractional_of_fg {I : Submodule R P} (hI : I.Fg) : IsFractional S I := by
  rcases hI with ⟨I, rfl⟩
  rcases exist_integer_multiples_of_finset S I with ⟨⟨s, hs1⟩, hs⟩
  rw [is_fractional_span_iff]
  exact ⟨s, hs1, hs⟩

omit loc

theorem mem_span_mul_finite_of_mem_mul {I J : FractionalIdeal S P} {x : P} (hx : x ∈ I * J) :
    ∃ T T' : Finset P, (T : Set P) ⊆ I ∧ (T' : Set P) ⊆ J ∧ x ∈ span R (T * T' : Set P) :=
  Submodule.mem_span_mul_finite_of_mem_mul
    (by
      simpa using mem_coe.mpr hx)

variable (S)

theorem coe_ideal_fg (inj : Function.Injective (algebraMap R P)) (I : Ideal R) :
    Fg ((I : FractionalIdeal S P) : Submodule R P) ↔ I.Fg :=
  coe_submodule_fg _ inj _

variable {S}

theorem fg_unit (I : (FractionalIdeal S P)ˣ) : Fg (I : Submodule R P) := by
  have : (1 : P) ∈ (I * ↑I⁻¹ : FractionalIdeal S P) := by
    rw [Units.mul_inv]
    exact one_mem_one _
  obtain ⟨T, T', hT, hT', one_mem⟩ := mem_span_mul_finite_of_mem_mul this
  refine' ⟨T, Submodule.span_eq_of_le _ hT _⟩
  rw [← one_mulₓ ↑I, ← mul_oneₓ (span R ↑T)]
  conv_rhs => rw [← FractionalIdeal.coe_one, ← Units.mul_inv I, FractionalIdeal.coe_mul, mul_comm ↑↑I, ← mul_assoc]
  refine' Submodule.mul_le_mul_left (le_transₓ _ (Submodule.mul_le_mul_right (submodule.span_le.mpr hT')))
  rwa [Submodule.one_le, Submodule.span_mul_span]

theorem fg_of_is_unit (I : FractionalIdeal S P) (h : IsUnit I) : Fg (I : Submodule R P) := by
  rcases h with ⟨I, rfl⟩
  exact fg_unit I

theorem _root_.ideal.fg_of_is_unit (inj : Function.Injective (algebraMap R P)) (I : Ideal R)
    (h : IsUnit (I : FractionalIdeal S P)) : I.Fg := by
  rw [← coe_ideal_fg S inj I]
  exact fg_of_is_unit I h

variable (S P P')

include loc loc'

/-- `canonical_equiv f f'` is the canonical equivalence between the fractional
ideals in `P` and in `P'` -/
noncomputable irreducible_def canonicalEquiv : FractionalIdeal S P ≃+* FractionalIdeal S P' :=
  mapEquiv
    { ringEquivOfRingEquiv P P' (RingEquiv.refl R)
        (show S.map _ = S by
          rw [RingEquiv.to_monoid_hom_refl, Submonoid.map_id]) with
      commutes' := fun r => ring_equiv_of_ring_equiv_eq _ _ }

@[simp]
theorem mem_canonical_equiv_apply {I : FractionalIdeal S P} {x : P'} :
    x ∈ canonicalEquiv S P P' I ↔
      ∃ y ∈ I,
        IsLocalization.map P' (RingHom.id R) (fun y (hy : y ∈ S) => show RingHom.id R y ∈ S from hy) (y : P) = x :=
  by
  rw [canonical_equiv, map_equiv_apply, mem_map]
  exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩

@[simp]
theorem canonical_equiv_symm : (canonicalEquiv S P P').symm = canonicalEquiv S P' P :=
  RingEquiv.ext fun I =>
    SetLike.ext_iff.mpr fun x => by
      rw [mem_canonical_equiv_apply, canonical_equiv, map_equiv_symm, map_equiv, RingEquiv.coe_mk, mem_map]
      exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩

@[simp]
theorem canonical_equiv_flip (I) : canonicalEquiv S P P' (canonicalEquiv S P' P I) = I := by
  rw [← canonical_equiv_symm, RingEquiv.symm_apply_apply]

end Semiringₓ

section IsFractionRing

/-!
### `is_fraction_ring` section

This section concerns fractional ideals in the field of fractions,
i.e. the type `fractional_ideal R⁰ K` where `is_fraction_ring R K`.
-/


variable {K K' : Type _} [Field K] [Field K']

variable [Algebra R K] [IsFractionRing R K] [Algebra R K'] [IsFractionRing R K']

variable {I J : FractionalIdeal R⁰ K} (h : K →ₐ[R] K')

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ≠ » (0 : R))
/-- Nonzero fractional ideals contain a nonzero integer. -/
theorem exists_ne_zero_mem_is_integer [Nontrivial R] (hI : I ≠ 0) : ∃ (x : _)(_ : x ≠ (0 : R)), algebraMap R K x ∈ I :=
  by
  obtain ⟨y, y_mem, y_not_mem⟩ :=
    SetLike.exists_of_lt
      (by
        simpa only using bot_lt_iff_ne_bot.mpr hI)
  have y_ne_zero : y ≠ 0 := by
    simpa using y_not_mem
  obtain ⟨z, ⟨x, hx⟩⟩ := exists_integer_multiple R⁰ y
  refine' ⟨x, _, _⟩
  · rw [Ne.def, ← @IsFractionRing.to_map_eq_zero_iff R _ K, hx, Algebra.smul_def]
    exact mul_ne_zero (IsFractionRing.to_map_ne_zero_of_mem_non_zero_divisors z.2) y_ne_zero
    
  · rw [hx]
    exact smul_mem _ _ y_mem
    

theorem map_ne_zero [Nontrivial R] (hI : I ≠ 0) : I.map h ≠ 0 := by
  obtain ⟨x, x_ne_zero, hx⟩ := exists_ne_zero_mem_is_integer hI
  contrapose! x_ne_zero with map_eq_zero
  refine' is_fraction_ring.to_map_eq_zero_iff.mp (eq_zero_iff.mp map_eq_zero _ (mem_map.mpr _))
  exact ⟨algebraMap R K x, hx, h.commutes x⟩

@[simp]
theorem map_eq_zero_iff [Nontrivial R] : I.map h = 0 ↔ I = 0 :=
  ⟨imp_of_not_imp_not _ _ (map_ne_zero _), fun hI => hI.symm ▸ map_zero h⟩

theorem coe_ideal_injective : Function.Injective (coe : Ideal R → FractionalIdeal R⁰ K) :=
  injective_of_le_imp_le _ fun _ _ => (coe_ideal_le_coe_ideal _).mp

@[simp]
theorem coe_ideal_eq_zero_iff {I : Ideal R} : (I : FractionalIdeal R⁰ K) = 0 ↔ I = ⊥ :=
  coe_ideal_injective.eq_iff

theorem coe_ideal_ne_zero_iff {I : Ideal R} : (I : FractionalIdeal R⁰ K) ≠ 0 ↔ I ≠ ⊥ :=
  not_iff_not.mpr coe_ideal_eq_zero_iff

theorem coe_ideal_ne_zero {I : Ideal R} (hI : I ≠ ⊥) : (I : FractionalIdeal R⁰ K) ≠ 0 :=
  coe_ideal_ne_zero_iff.mpr hI

@[simp]
theorem coe_ideal_eq_one_iff {I : Ideal R} : (I : FractionalIdeal R⁰ K) = 1 ↔ I = 1 := by
  simpa only [← Ideal.one_eq_top] using coe_ideal_injective.eq_iff

end IsFractionRing

section Quotientₓ

/-!
### `quotient` section

This section defines the ideal quotient of fractional ideals.

In this section we need that each non-zero `y : R` has an inverse in
the localization, i.e. that the localization is a field. We satisfy this
assumption by taking `S = non_zero_divisors R`, `R`'s localization at which
is a field because `R` is a domain.
-/


open Classical

variable {R₁ : Type _} [CommRingₓ R₁] {K : Type _} [Field K]

variable [Algebra R₁ K] [frac : IsFractionRing R₁ K]

instance : Nontrivial (FractionalIdeal R₁⁰ K) :=
  ⟨⟨0, 1, fun h =>
      have this : (1 : K) ∈ (0 : FractionalIdeal R₁⁰ K) := by
        rw [← (algebraMap R₁ K).map_one]
        simpa only [← h] using coe_mem_one R₁⁰ 1
      one_ne_zero ((mem_zero_iff _).mp this)⟩⟩

theorem ne_zero_of_mul_eq_one (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : I ≠ 0 := fun hI =>
  @zero_ne_one (FractionalIdeal R₁⁰ K) _ _
    (by
      convert h
      simp [← hI])

variable [IsDomain R₁]

include frac

theorem _root_.is_fractional.div_of_nonzero {I J : Submodule R₁ K} :
    IsFractional R₁⁰ I → IsFractional R₁⁰ J → J ≠ 0 → IsFractional R₁⁰ (I / J)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩, h => by
    obtain ⟨y, mem_J, not_mem_zero⟩ :=
      SetLike.exists_of_lt
        (by
          simpa only using bot_lt_iff_ne_bot.mpr h)
    obtain ⟨y', hy'⟩ := hJ y mem_J
    use aI * y'
    constructor
    · apply (nonZeroDivisors R₁).mul_mem haI (mem_non_zero_divisors_iff_ne_zero.mpr _)
      intro y'_eq_zero
      have : algebraMap R₁ K aJ * y = 0 := by
        rw [← Algebra.smul_def, ← hy', y'_eq_zero, RingHom.map_zero]
      have y_zero :=
        (mul_eq_zero.mp this).resolve_left
          (mt ((injective_iff_map_eq_zero (algebraMap R₁ K)).1 (IsFractionRing.injective _ _) _)
            (mem_non_zero_divisors_iff_ne_zero.mp haJ))
      apply not_mem_zero
      simpa only using (mem_zero_iff R₁⁰).mpr y_zero
      
    intro b hb
    convert hI _ (hb _ (Submodule.smul_mem _ aJ mem_J)) using 1
    rw [← hy', mul_comm b, ← Algebra.smul_def, mul_smul]

theorem fractional_div_of_nonzero {I J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    IsFractional R₁⁰ (I / J : Submodule R₁ K) :=
  (I.IsFractional.div_of_nonzero J.IsFractional) fun H => h <| coe_to_submodule_injective <| H.trans coe_zero.symm

noncomputable instance fractionalIdealHasDiv : Div (FractionalIdeal R₁⁰ K) :=
  ⟨fun I J => if h : J = 0 then 0 else ⟨I / J, fractional_div_of_nonzero h⟩⟩

variable {I J : FractionalIdeal R₁⁰ K} [J ≠ 0]

@[simp]
theorem div_zero {I : FractionalIdeal R₁⁰ K} : I / 0 = 0 :=
  dif_pos rfl

theorem div_nonzero {I J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) : I / J = ⟨I / J, fractional_div_of_nonzero h⟩ :=
  dif_neg h

@[simp]
theorem coe_div {I J : FractionalIdeal R₁⁰ K} (hJ : J ≠ 0) : (↑(I / J) : Submodule R₁ K) = ↑I / (↑J : Submodule R₁ K) :=
  congr_arg _ (dif_neg hJ)

theorem mem_div_iff_of_nonzero {I J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) {x} : x ∈ I / J ↔ ∀, ∀ y ∈ J, ∀, x * y ∈ I :=
  by
  rw [div_nonzero h]
  exact Submodule.mem_div_iff_forall_mul_mem

theorem mul_one_div_le_one {I : FractionalIdeal R₁⁰ K} : I * (1 / I) ≤ 1 := by
  by_cases' hI : I = 0
  · rw [hI, div_zero, mul_zero]
    exact zero_le 1
    
  · rw [← coe_le_coe, coe_mul, coe_div hI, coe_one]
    apply Submodule.mul_one_div_le_one
    

theorem le_self_mul_one_div {I : FractionalIdeal R₁⁰ K} (hI : I ≤ (1 : FractionalIdeal R₁⁰ K)) : I ≤ I * (1 / I) := by
  by_cases' hI_nz : I = 0
  · rw [hI_nz, div_zero, mul_zero]
    exact zero_le 0
    
  · rw [← coe_le_coe, coe_mul, coe_div hI_nz, coe_one]
    rw [← coe_le_coe, coe_one] at hI
    exact Submodule.le_self_mul_one_div hI
    

theorem le_div_iff_of_nonzero {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' ≠ 0) :
    I ≤ J / J' ↔ ∀, ∀ x ∈ I, ∀, ∀ y ∈ J', ∀, x * y ∈ J :=
  ⟨fun h x hx => (mem_div_iff_of_nonzero hJ').mp (h hx), fun h x hx => (mem_div_iff_of_nonzero hJ').mpr (h x hx)⟩

theorem le_div_iff_mul_le {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' ≠ 0) : I ≤ J / J' ↔ I * J' ≤ J := by
  rw [div_nonzero hJ']
  convert Submodule.le_div_iff_mul_le using 1
  rw [← coe_mul, coe_le_coe]

@[simp]
theorem div_one {I : FractionalIdeal R₁⁰ K} : I / 1 = I := by
  rw [div_nonzero (@one_ne_zero (FractionalIdeal R₁⁰ K) _ _)]
  ext
  constructor <;> intro h
  · simpa using mem_div_iff_forall_mul_mem.mp h 1 ((algebraMap R₁ K).map_one ▸ coe_mem_one R₁⁰ 1)
    
  · apply mem_div_iff_forall_mul_mem.mpr
    rintro y ⟨y', _, rfl⟩
    rw [mul_comm]
    convert Submodule.smul_mem _ y' h
    exact (Algebra.smul_def _ _).symm
    

theorem eq_one_div_of_mul_eq_one_right (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : J = 1 / I := by
  have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J h
  suffices h' : I * (1 / I) = 1
  · exact congr_arg Units.inv <| @Units.ext _ _ (Units.mkOfMulEqOne _ _ h) (Units.mkOfMulEqOne _ _ h') rfl
    
  apply le_antisymmₓ
  · apply mul_le.mpr _
    intro x hx y hy
    rw [mul_comm]
    exact (mem_div_iff_of_nonzero hI).mp hy x hx
    
  rw [← h]
  apply mul_left_mono I
  apply (le_div_iff_of_nonzero hI).mpr _
  intro y hy x hx
  rw [mul_comm]
  exact mul_mem_mul hx hy

theorem mul_div_self_cancel_iff {I : FractionalIdeal R₁⁰ K} : I * (1 / I) = 1 ↔ ∃ J, I * J = 1 :=
  ⟨fun h => ⟨1 / I, h⟩, fun ⟨J, hJ⟩ => by
    rwa [← eq_one_div_of_mul_eq_one_right I J hJ]⟩

variable {K' : Type _} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']

@[simp]
theorem map_div (I J : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') : (I / J).map (h : K →ₐ[R₁] K') = I.map h / J.map h :=
  by
  by_cases' H : J = 0
  · rw [H, div_zero, map_zero, div_zero]
    
  · apply coe_to_submodule_injective
    simp [← div_nonzero H, ← div_nonzero (map_ne_zero _ H), ← Submodule.map_div]
    

@[simp]
theorem map_one_div (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') : (1 / I).map (h : K →ₐ[R₁] K') = 1 / I.map h := by
  rw [map_div, map_one]

end Quotientₓ

section Field

variable {R₁ K L : Type _} [CommRingₓ R₁] [IsDomain R₁] [Field K] [Field L]

variable [Algebra R₁ K] [IsFractionRing R₁ K] [Algebra K L] [IsFractionRing K L]

theorem eq_zero_or_one (I : FractionalIdeal K⁰ L) : I = 0 ∨ I = 1 := by
  rw [or_iff_not_imp_left]
  intro hI
  simp_rw [@SetLike.ext_iff _ _ _ I 1, FractionalIdeal.mem_one_iff]
  intro x
  constructor
  · intro x_mem
    obtain ⟨n, d, rfl⟩ := IsLocalization.mk'_surjective K⁰ x
    refine' ⟨n / d, _⟩
    rw [RingHom.map_div, IsFractionRing.mk'_eq_div]
    
  · rintro ⟨x, rfl⟩
    obtain ⟨y, y_ne, y_mem⟩ := FractionalIdeal.exists_ne_zero_mem_is_integer hI
    rw [← div_mul_cancel x y_ne, RingHom.map_mul, ← Algebra.smul_def]
    exact Submodule.smul_mem I _ y_mem
    

theorem eq_zero_or_one_of_is_field (hF : IsField R₁) (I : FractionalIdeal R₁⁰ K) : I = 0 ∨ I = 1 := by
  let this : Field R₁ := hF.to_field
  -- TODO can this be less ugly?
  exact
    @eq_zero_or_one R₁ K _ _ _
      (by
        cases _inst_4
        convert _inst_9)
      I

end Field

section PrincipalIdealRing

variable {R₁ : Type _} [CommRingₓ R₁] {K : Type _} [Field K]

variable [Algebra R₁ K] [IsFractionRing R₁ K]

open Classical

variable (R₁)

/-- `fractional_ideal.span_finset R₁ s f` is the fractional ideal of `R₁` generated by `f '' s`. -/
@[simps]
def spanFinset {ι : Type _} (s : Finset ι) (f : ι → K) : FractionalIdeal R₁⁰ K :=
  ⟨Submodule.span R₁ (f '' s), by
    obtain ⟨a', ha'⟩ := IsLocalization.exist_integer_multiples R₁⁰ s f
    refine' ⟨a', a'.2, fun x hx => Submodule.span_induction hx _ _ _ _⟩
    · rintro _ ⟨i, hi, rfl⟩
      exact ha' i hi
      
    · rw [smul_zero]
      exact IsLocalization.is_integer_zero
      
    · intro x y hx hy
      rw [smul_add]
      exact IsLocalization.is_integer_add hx hy
      
    · intro c x hx
      rw [smul_comm]
      exact IsLocalization.is_integer_smul hx
      ⟩

variable {R₁}

@[simp]
theorem span_finset_eq_zero {ι : Type _} {s : Finset ι} {f : ι → K} : spanFinset R₁ s f = 0 ↔ ∀, ∀ j ∈ s, ∀, f j = 0 :=
  by
  simp only [coe_to_submodule_injective.eq_iff, ← span_finset_coe, ← coe_zero, ← Submodule.span_eq_bot, ← Set.mem_image,
    ← Finset.mem_coe, ← forall_exists_index, ← and_imp, ← forall_apply_eq_imp_iff₂]

theorem span_finset_ne_zero {ι : Type _} {s : Finset ι} {f : ι → K} : spanFinset R₁ s f ≠ 0 ↔ ∃ j ∈ s, f j ≠ 0 := by
  simp

open Submodule.IsPrincipal

include loc

theorem is_fractional_span_singleton (x : P) : IsFractional S (span R {x} : Submodule R P) :=
  let ⟨a, ha⟩ := exists_integer_multiple S x
  is_fractional_span_iff.mpr ⟨a, a.2, fun x' hx' => (Set.mem_singleton_iff.mp hx').symm ▸ ha⟩

variable (S)

/-- `span_singleton x` is the fractional ideal generated by `x` if `0 ∉ S` -/
irreducible_def spanSingleton (x : P) : FractionalIdeal S P :=
  ⟨span R {x}, is_fractional_span_singleton x⟩

attribute [local semireducible] span_singleton

@[simp]
theorem coe_span_singleton (x : P) : (spanSingleton S x : Submodule R P) = span R {x} :=
  rfl

@[simp]
theorem mem_span_singleton {x y : P} : x ∈ spanSingleton S y ↔ ∃ z : R, z • y = x :=
  Submodule.mem_span_singleton

theorem mem_span_singleton_self (x : P) : x ∈ spanSingleton S x :=
  (mem_span_singleton S).mpr ⟨1, one_smul _ _⟩

variable {S}

theorem span_singleton_eq_span_singleton [NoZeroSmulDivisors R P] {x y : P} :
    spanSingleton S x = spanSingleton S y ↔ ∃ z : Rˣ, z • x = y := by
  rw [← Submodule.span_singleton_eq_span_singleton]
  exact Subtype.mk_eq_mk

theorem eq_span_singleton_of_principal (I : FractionalIdeal S P) [IsPrincipal (I : Submodule R P)] :
    I = spanSingleton S (generator (I : Submodule R P)) :=
  coe_to_submodule_injective (span_singleton_generator ↑I).symm

theorem is_principal_iff (I : FractionalIdeal S P) : IsPrincipal (I : Submodule R P) ↔ ∃ x, I = spanSingleton S x :=
  ⟨fun h => ⟨@generator _ _ _ _ _ (↑I) h, @eq_span_singleton_of_principal _ _ _ _ _ _ _ I h⟩, fun ⟨x, hx⟩ =>
    { principal := ⟨x, trans (congr_arg _ hx) (coe_span_singleton _ x)⟩ }⟩

@[simp]
theorem span_singleton_zero : spanSingleton S (0 : P) = 0 := by
  ext
  simp [← Submodule.mem_span_singleton, ← eq_comm]

theorem span_singleton_eq_zero_iff {y : P} : spanSingleton S y = 0 ↔ y = 0 :=
  ⟨fun h =>
    span_eq_bot.mp
      (by
        simpa using congr_arg Subtype.val h : span R {y} = ⊥)
      y (mem_singleton y),
    fun h => by
    simp [← h]⟩

theorem span_singleton_ne_zero_iff {y : P} : spanSingleton S y ≠ 0 ↔ y ≠ 0 :=
  not_congr span_singleton_eq_zero_iff

@[simp]
theorem span_singleton_one : spanSingleton S (1 : P) = 1 := by
  ext
  refine' (mem_span_singleton S).trans ((exists_congr _).trans (mem_one_iff S).symm)
  intro x'
  rw [Algebra.smul_def, mul_oneₓ]

@[simp]
theorem span_singleton_mul_span_singleton (x y : P) : spanSingleton S x * spanSingleton S y = spanSingleton S (x * y) :=
  by
  apply coe_to_submodule_injective
  simp only [← coe_mul, ← coe_span_singleton, ← span_mul_span, ← singleton_mul_singleton]

@[simp]
theorem span_singleton_pow (x : P) (n : ℕ) : spanSingleton S x ^ n = spanSingleton S (x ^ n) := by
  induction' n with n hn
  · rw [pow_zeroₓ, pow_zeroₓ, span_singleton_one]
    
  · rw [pow_succₓ, hn, span_singleton_mul_span_singleton, pow_succₓ]
    

@[simp]
theorem coe_ideal_span_singleton (x : R) :
    (↑(Ideal.span {x} : Ideal R) : FractionalIdeal S P) = spanSingleton S (algebraMap R P x) := by
  ext y
  refine' (mem_coe_ideal S).trans (Iff.trans _ (mem_span_singleton S).symm)
  constructor
  · rintro ⟨y', hy', rfl⟩
    obtain ⟨x', rfl⟩ := submodule.mem_span_singleton.mp hy'
    use x'
    rw [smul_eq_mul, RingHom.map_mul, Algebra.smul_def]
    
  · rintro ⟨y', rfl⟩
    refine' ⟨y' * x, submodule.mem_span_singleton.mpr ⟨y', rfl⟩, _⟩
    rw [RingHom.map_mul, Algebra.smul_def]
    

@[simp]
theorem canonical_equiv_span_singleton {P'} [CommRingₓ P'] [Algebra R P'] [IsLocalization S P'] (x : P) :
    canonicalEquiv S P P' (spanSingleton S x) =
      spanSingleton S
        (IsLocalization.map P' (RingHom.id R) (fun y (hy : y ∈ S) => show RingHom.id R y ∈ S from hy) x) :=
  by
  apply set_like.ext_iff.mpr
  intro y
  constructor <;> intro h
  · rw [mem_span_singleton]
    obtain ⟨x', hx', rfl⟩ := (mem_canonical_equiv_apply _ _ _).mp h
    obtain ⟨z, rfl⟩ := (mem_span_singleton _).mp hx'
    use z
    rw [IsLocalization.map_smul]
    rfl
    
  · rw [mem_canonical_equiv_apply]
    obtain ⟨z, rfl⟩ := (mem_span_singleton _).mp h
    use z • x
    use (mem_span_singleton _).mpr ⟨z, rfl⟩
    simp [← IsLocalization.map_smul]
    

theorem mem_singleton_mul {x y : P} {I : FractionalIdeal S P} : y ∈ spanSingleton S x * I ↔ ∃ y' ∈ I, y = x * y' := by
  constructor
  · intro h
    apply FractionalIdeal.mul_induction_on h
    · intro x' hx' y' hy'
      obtain ⟨a, ha⟩ := (mem_span_singleton S).mp hx'
      use a • y', Submodule.smul_mem I a hy'
      rw [← ha, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      
    · rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
      exact ⟨y + y', Submodule.add_mem I hy hy', (mul_addₓ _ _ _).symm⟩
      
    
  · rintro ⟨y', hy', rfl⟩
    exact mul_mem_mul ((mem_span_singleton S).mpr ⟨1, one_smul _ _⟩) hy'
    

omit loc

variable (K)

theorem mk'_mul_coe_ideal_eq_coe_ideal {I J : Ideal R₁} {x y : R₁} (hy : y ∈ R₁⁰) :
    spanSingleton R₁⁰ (IsLocalization.mk' K x ⟨y, hy⟩) * I = (J : FractionalIdeal R₁⁰ K) ↔
      Ideal.span {x} * I = Ideal.span {y} * J :=
  by
  have inj : Function.Injective (coe : Ideal R₁ → FractionalIdeal R₁⁰ K) := FractionalIdeal.coe_ideal_injective
  have : span_singleton R₁⁰ (IsLocalization.mk' _ (1 : R₁) ⟨y, hy⟩) * span_singleton R₁⁰ (algebraMap R₁ K y) = 1 := by
    rw [span_singleton_mul_span_singleton, mul_comm, ← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_self,
      span_singleton_one]
  let y' : (FractionalIdeal R₁⁰ K)ˣ := Units.mkOfMulEqOne _ _ this
  have coe_y' : ↑y' = span_singleton R₁⁰ (IsLocalization.mk' K (1 : R₁) ⟨y, hy⟩) := rfl
  refine' Iff.trans _ (y'.mul_right_inj.trans inj.eq_iff)
  rw [coe_y', coe_ideal_mul, coe_ideal_span_singleton, coe_ideal_mul, coe_ideal_span_singleton, ← mul_assoc,
    span_singleton_mul_span_singleton, ← mul_assoc, span_singleton_mul_span_singleton, mul_comm (mk' _ _ _), ←
    IsLocalization.mk'_eq_mul_mk'_one, mul_comm (mk' _ _ _), ← IsLocalization.mk'_eq_mul_mk'_one,
    IsLocalization.mk'_self, span_singleton_one, one_mulₓ]

variable {K}

theorem span_singleton_mul_coe_ideal_eq_coe_ideal {I J : Ideal R₁} {z : K} :
    spanSingleton R₁⁰ z * (I : FractionalIdeal R₁⁰ K) = J ↔
      Ideal.span {((IsLocalization.sec R₁⁰ z).1 : R₁)} * I = Ideal.span {(IsLocalization.sec R₁⁰ z).2} * J :=
  by
  -- `erw` to deal with the distinction between `y` and `⟨y.1, y.2⟩`
  erw [← mk'_mul_coe_ideal_eq_coe_ideal K (IsLocalization.sec R₁⁰ z).2.Prop, IsLocalization.mk'_sec K z]

variable [IsDomain R₁]

theorem one_div_span_singleton (x : K) : 1 / spanSingleton R₁⁰ x = spanSingleton R₁⁰ x⁻¹ :=
  if h : x = 0 then by
    simp [← h]
  else
    (eq_one_div_of_mul_eq_one_right _ _
        (by
          simp [← h])).symm

@[simp]
theorem div_span_singleton (J : FractionalIdeal R₁⁰ K) (d : K) : J / spanSingleton R₁⁰ d = spanSingleton R₁⁰ d⁻¹ * J :=
  by
  rw [← one_div_span_singleton]
  by_cases' hd : d = 0
  · simp only [← hd, ← span_singleton_zero, ← div_zero, ← zero_mul]
    
  have h_spand : span_singleton R₁⁰ d ≠ 0 := mt span_singleton_eq_zero_iff.mp hd
  apply le_antisymmₓ
  · intro x hx
    rw [← mem_coe, coe_div h_spand, Submodule.mem_div_iff_forall_mul_mem] at hx
    specialize hx d (mem_span_singleton_self R₁⁰ d)
    have h_xd : x = d⁻¹ * (x * d) := by
      field_simp
    rw [← mem_coe, coe_mul, one_div_span_singleton, h_xd]
    exact Submodule.mul_mem_mul (mem_span_singleton_self R₁⁰ _) hx
    
  · rw [le_div_iff_mul_le h_spand, mul_assoc, mul_left_commₓ, one_div_span_singleton, span_singleton_mul_span_singleton,
      inv_mul_cancel hd, span_singleton_one, mul_oneₓ]
    exact le_reflₓ J
    

theorem exists_eq_span_singleton_mul (I : FractionalIdeal R₁⁰ K) :
    ∃ (a : R₁)(aI : Ideal R₁), a ≠ 0 ∧ I = spanSingleton R₁⁰ (algebraMap R₁ K a)⁻¹ * aI := by
  obtain ⟨a_inv, nonzero, ha⟩ := I.is_fractional
  have nonzero := mem_non_zero_divisors_iff_ne_zero.mp nonzero
  have map_a_nonzero : algebraMap R₁ K a_inv ≠ 0 := mt is_fraction_ring.to_map_eq_zero_iff.mp nonzero
  refine'
    ⟨a_inv, Submodule.comap (Algebra.linearMap R₁ K) ↑(span_singleton R₁⁰ (algebraMap R₁ K a_inv) * I), nonzero,
      ext fun x => Iff.trans ⟨_, _⟩ mem_singleton_mul.symm⟩
  · intro hx
    obtain ⟨x', hx'⟩ := ha x hx
    rw [Algebra.smul_def] at hx'
    refine' ⟨algebraMap R₁ K x', (mem_coe_ideal _).mpr ⟨x', mem_singleton_mul.mpr _, rfl⟩, _⟩
    · exact ⟨x, hx, hx'⟩
      
    · rw [hx', ← mul_assoc, inv_mul_cancel map_a_nonzero, one_mulₓ]
      
    
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x', hx', rfl⟩ := (mem_coe_ideal _).mp hy
    obtain ⟨y', hy', hx'⟩ := mem_singleton_mul.mp hx'
    rw [Algebra.linear_map_apply] at hx'
    rwa [hx', ← mul_assoc, inv_mul_cancel map_a_nonzero, one_mulₓ]
    

instance is_principal {R} [CommRingₓ R] [IsDomain R] [IsPrincipalIdealRing R] [Algebra R K] [IsFractionRing R K]
    (I : FractionalIdeal R⁰ K) : (I : Submodule R K).IsPrincipal := by
  obtain ⟨a, aI, -, ha⟩ := exists_eq_span_singleton_mul I
  use (algebraMap R K a)⁻¹ * algebraMap R K (generator aI)
  suffices I = span_singleton R⁰ ((algebraMap R K a)⁻¹ * algebraMap R K (generator aI)) by
    exact congr_arg Subtype.val this
  conv_lhs => rw [ha, ← span_singleton_generator aI]
  rw [Ideal.submodule_span_eq, coe_ideal_span_singleton (generator aI), span_singleton_mul_span_singleton]

include loc

theorem le_span_singleton_mul_iff {x : P} {I J : FractionalIdeal S P} :
    I ≤ spanSingleton S x * J ↔ ∀, ∀ zI ∈ I, ∀, ∃ zJ ∈ J, x * zJ = zI :=
  show (∀ {zI} (hzI : zI ∈ I), zI ∈ spanSingleton _ x * J) ↔ ∀, ∀ zI ∈ I, ∀, ∃ zJ ∈ J, x * zJ = zI by
    simp only [← FractionalIdeal.mem_singleton_mul, ← eq_comm]

theorem span_singleton_mul_le_iff {x : P} {I J : FractionalIdeal S P} :
    spanSingleton _ x * I ≤ J ↔ ∀, ∀ z ∈ I, ∀, x * z ∈ J := by
  simp only [← FractionalIdeal.mul_le, ← FractionalIdeal.mem_singleton_mul, ← FractionalIdeal.mem_span_singleton]
  constructor
  · intro h zI hzI
    exact h x ⟨1, one_smul _ _⟩ zI hzI
    
  · rintro h _ ⟨z, rfl⟩ zI hzI
    rw [Algebra.smul_mul_assoc]
    exact Submodule.smul_mem J.1 _ (h zI hzI)
    

theorem eq_span_singleton_mul {x : P} {I J : FractionalIdeal S P} :
    I = spanSingleton _ x * J ↔ (∀, ∀ zI ∈ I, ∀, ∃ zJ ∈ J, x * zJ = zI) ∧ ∀, ∀ z ∈ J, ∀, x * z ∈ I := by
  simp only [← le_antisymm_iffₓ, ← FractionalIdeal.le_span_singleton_mul_iff, ←
    FractionalIdeal.span_singleton_mul_le_iff]

end PrincipalIdealRing

variable {R₁ : Type _} [CommRingₓ R₁]

variable {K : Type _} [Field K] [Algebra R₁ K] [frac : IsFractionRing R₁ K]

attribute [local instance] Classical.propDecidable

theorem is_noetherian_zero : IsNoetherian R₁ (0 : FractionalIdeal R₁⁰ K) :=
  is_noetherian_submodule.mpr fun I (hI : I ≤ (0 : FractionalIdeal R₁⁰ K)) => by
    rw [coe_zero] at hI
    rw [le_bot_iff.mp hI]
    exact fg_bot

theorem is_noetherian_iff {I : FractionalIdeal R₁⁰ K} : IsNoetherian R₁ I ↔ ∀, ∀ J ≤ I, ∀, (J : Submodule R₁ K).Fg :=
  is_noetherian_submodule.trans ⟨fun h J hJ => h _ hJ, fun h J hJ => h ⟨J, is_fractional_of_le hJ⟩ hJ⟩

theorem is_noetherian_coe_to_fractional_ideal [IsNoetherianRing R₁] (I : Ideal R₁) :
    IsNoetherian R₁ (I : FractionalIdeal R₁⁰ K) := by
  rw [is_noetherian_iff]
  intro J hJ
  obtain ⟨J, rfl⟩ := le_one_iff_exists_coe_ideal.mp (le_transₓ hJ coe_ideal_le_one)
  exact (IsNoetherian.noetherian J).map _

include frac

variable [IsDomain R₁]

theorem is_noetherian_span_singleton_inv_to_map_mul (x : R₁) {I : FractionalIdeal R₁⁰ K} (hI : IsNoetherian R₁ I) :
    IsNoetherian R₁ (spanSingleton R₁⁰ (algebraMap R₁ K x)⁻¹ * I : FractionalIdeal R₁⁰ K) := by
  by_cases' hx : x = 0
  · rw [hx, RingHom.map_zero, _root_.inv_zero, span_singleton_zero, zero_mul]
    exact is_noetherian_zero
    
  have h_gx : algebraMap R₁ K x ≠ 0 :=
    mt ((injective_iff_map_eq_zero (algebraMap R₁ K)).mp (IsFractionRing.injective _ _) x) hx
  have h_spanx : span_singleton R₁⁰ (algebraMap R₁ K x) ≠ 0 := span_singleton_ne_zero_iff.mpr h_gx
  rw [is_noetherian_iff] at hI⊢
  intro J hJ
  rw [← div_span_singleton, le_div_iff_mul_le h_spanx] at hJ
  obtain ⟨s, hs⟩ := hI _ hJ
  use s * {(algebraMap R₁ K x)⁻¹}
  rw [Finset.coe_mul, Finset.coe_singleton, ← span_mul_span, hs, ← coe_span_singleton R₁⁰, ← coe_mul, mul_assoc,
    span_singleton_mul_span_singleton, mul_inv_cancel h_gx, span_singleton_one, mul_oneₓ]

/-- Every fractional ideal of a noetherian integral domain is noetherian. -/
theorem is_noetherian [IsNoetherianRing R₁] (I : FractionalIdeal R₁⁰ K) : IsNoetherian R₁ I := by
  obtain ⟨d, J, h_nzd, rfl⟩ := exists_eq_span_singleton_mul I
  apply is_noetherian_span_singleton_inv_to_map_mul
  apply is_noetherian_coe_to_fractional_ideal

section Adjoin

include loc

omit frac

variable {R P} (S) (x : P) (hx : IsIntegral R x)

/-- `A[x]` is a fractional ideal for every integral `x`. -/
theorem is_fractional_adjoin_integral : IsFractional S (Algebra.adjoin R ({x} : Set P)).toSubmodule :=
  is_fractional_of_fg (fg_adjoin_singleton_of_integral x hx)

/-- `fractional_ideal.adjoin_integral (S : submonoid R) x hx` is `R[x]` as a fractional ideal,
where `hx` is a proof that `x : P` is integral over `R`. -/
@[simps]
def adjoinIntegral : FractionalIdeal S P :=
  ⟨_, is_fractional_adjoin_integral S x hx⟩

theorem mem_adjoin_integral_self : x ∈ adjoinIntegral S x hx :=
  Algebra.subset_adjoin (Set.mem_singleton x)

end Adjoin

end FractionalIdeal


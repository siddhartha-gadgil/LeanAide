/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathbin.Tactic.NoncommRing
import Mathbin.FieldTheory.IsAlgClosed.Basic
import Mathbin.Algebra.Star.Pointwise

/-!
# Spectrum of an element in an algebra
This file develops the basic theory of the spectrum of an element of an algebra.
This theory will serve as the foundation for spectral theory in Banach algebras.

## Main definitions

* `resolvent_set a : set R`: the resolvent set of an element `a : A` where
  `A` is an  `R`-algebra.
* `spectrum a : set R`: the spectrum of an element `a : A` where
  `A` is an  `R`-algebra.
* `resolvent : R → A`: the resolvent function is `λ r, ring.inverse (↑ₐr - a)`, and hence
  when `r ∈ resolvent R A`, it is actually the inverse of the unit `(↑ₐr - a)`.

## Main statements

* `spectrum.unit_smul_eq_smul` and `spectrum.smul_eq_smul`: units in the scalar ring commute
  (multiplication) with the spectrum, and over a field even `0` commutes with the spectrum.
* `spectrum.left_add_coset_eq`: elements of the scalar ring commute (addition) with the spectrum.
* `spectrum.unit_mem_mul_iff_mem_swap_mul` and `spectrum.preimage_units_mul_eq_swap_mul`: the
  units (of `R`) in `σ (a*b)` coincide with those in `σ (b*a)`.
* `spectrum.scalar_eq`: in a nontrivial algebra over a field, the spectrum of a scalar is
  a singleton.
* `spectrum.subset_polynomial_aeval`, `spectrum.map_polynomial_aeval_of_degree_pos`,
  `spectrum.map_polynomial_aeval_of_nonempty`: variations on the spectral mapping theorem.

## Notations

* `σ a` : `spectrum R a` of `a : A`
-/


open Set

universe u v

section Defs

variable (R : Type u) {A : Type v}

variable [CommSemiringₓ R] [Ringₓ A] [Algebra R A]

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap R A

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *resolvent set* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is a unit of the
algebra `A`.  -/
-- definition and basic properties
def ResolventSet (a : A) : Set R :=
  { r : R | IsUnit (↑ₐ r - a) }

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *spectrum* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is not a unit of the
algebra `A`.

The spectrum is simply the complement of the resolvent set.  -/
def Spectrum (a : A) : Set R :=
  ResolventSet R aᶜ

variable {R}

/-- Given an `a : A` where `A` is an `R`-algebra, the *resolvent* is
    a map `R → A` which sends `r : R` to `(algebra_map R A r - a)⁻¹` when
    `r ∈ resolvent R A` and `0` when `r ∈ spectrum R A`. -/
noncomputable def resolvent (a : A) (r : R) : A :=
  Ring.inverse (↑ₐ r - a)

/-- The unit `1 - r⁻¹ • a` constructed from `r • 1 - a` when the latter is a unit. -/
@[simps]
noncomputable def IsUnit.subInvSmul {r : Rˣ} {s : R} {a : A} (h : IsUnit <| r • ↑ₐ s - a) : Aˣ where
  val := ↑ₐ s - r⁻¹ • a
  inv := r • ↑h.Unit⁻¹
  val_inv := by
    rw [mul_smul_comm, ← smul_mul_assoc, smul_sub, smul_inv_smul, h.mul_coe_inv]
  inv_val := by
    rw [smul_mul_assoc, ← mul_smul_comm, smul_sub, smul_inv_smul, h.coe_inv_mul]

end Defs

namespace Spectrum

open Polynomial

section ScalarSemiring

variable {R : Type u} {A : Type v}

variable [CommSemiringₓ R] [Ringₓ A] [Algebra R A]

-- mathport name: «exprσ»
local notation "σ" => Spectrum R

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap R A

theorem mem_iff {r : R} {a : A} : r ∈ σ a ↔ ¬IsUnit (↑ₐ r - a) :=
  Iff.rfl

theorem not_mem_iff {r : R} {a : A} : r ∉ σ a ↔ IsUnit (↑ₐ r - a) := by
  apply not_iff_not.mp
  simp [← Set.not_not_mem, ← mem_iff]

theorem mem_resolvent_set_of_left_right_inverse {r : R} {a b c : A} (h₁ : (↑ₐ r - a) * b = 1)
    (h₂ : c * (↑ₐ r - a) = 1) : r ∈ ResolventSet R a :=
  Units.is_unit
    ⟨↑ₐ r - a, b, h₁, by
      rwa [← left_inv_eq_right_invₓ h₂ h₁]⟩

theorem mem_resolvent_set_iff {r : R} {a : A} : r ∈ ResolventSet R a ↔ IsUnit (↑ₐ r - a) :=
  Iff.rfl

@[simp]
theorem resolvent_set_of_subsingleton [Subsingleton A] (a : A) : ResolventSet R a = Set.Univ := by
  simp_rw [ResolventSet, Subsingleton.elimₓ (algebraMap R A _ - a) 1, is_unit_one, Set.set_of_true]

@[simp]
theorem of_subsingleton [Subsingleton A] (a : A) : Spectrum R a = ∅ := by
  rw [Spectrum, resolvent_set_of_subsingleton, Set.compl_univ]

theorem resolvent_eq {a : A} {r : R} (h : r ∈ ResolventSet R a) : resolvent a r = ↑h.Unit⁻¹ :=
  Ring.inverse_unit h.Unit

theorem units_smul_resolvent {r : Rˣ} {s : R} {a : A} : r • resolvent a (s : R) = resolvent (r⁻¹ • a) (r⁻¹ • s : R) :=
  by
  by_cases' h : s ∈ Spectrum R a
  · rw [mem_iff] at h
    simp only [← resolvent, ← Algebra.algebra_map_eq_smul_one] at *
    rw [smul_assoc, ← smul_sub]
    have h' : ¬IsUnit (r⁻¹ • (s • 1 - a)) := fun hu =>
      h
        (by
          simpa only [← smul_inv_smul] using IsUnit.smul r hu)
    simp only [← Ring.inverse_non_unit _ h, ← Ring.inverse_non_unit _ h', ← smul_zero]
    
  · simp only [← resolvent]
    have h' : IsUnit (r • algebraMap R A (r⁻¹ • s) - a) := by
      simpa [← Algebra.algebra_map_eq_smul_one, ← smul_assoc] using not_mem_iff.mp h
    rw [← h'.coe_sub_inv_smul, ← (not_mem_iff.mp h).unit_spec, Ring.inverse_unit, Ring.inverse_unit,
      h'.coe_inv_sub_inv_smul]
    simp only [← Algebra.algebra_map_eq_smul_one, ← smul_assoc, ← smul_inv_smul]
    

theorem units_smul_resolvent_self {r : Rˣ} {a : A} : r • resolvent a (r : R) = resolvent (r⁻¹ • a) (1 : R) := by
  simpa only [← Units.smul_def, ← Algebra.id.smul_eq_mul, ← Units.inv_mul] using @units_smul_resolvent _ _ _ _ _ r r a

/-- The resolvent is a unit when the argument is in the resolvent set. -/
theorem is_unit_resolvent {r : R} {a : A} : r ∈ ResolventSet R a ↔ IsUnit (resolvent a r) :=
  is_unit_ring_inverse.symm

theorem inv_mem_resolvent_set {r : Rˣ} {a : Aˣ} (h : (r : R) ∈ ResolventSet R (a : A)) :
    (↑r⁻¹ : R) ∈ ResolventSet R (↑a⁻¹ : A) := by
  rw [mem_resolvent_set_iff, Algebra.algebra_map_eq_smul_one, ← Units.smul_def] at h⊢
  rw [IsUnit.smul_sub_iff_sub_inv_smul, inv_invₓ, IsUnit.sub_iff]
  have h₁ : (a : A) * (r • (↑a⁻¹ : A) - 1) = r • 1 - a := by
    rw [mul_sub, mul_smul_comm, a.mul_inv, mul_oneₓ]
  have h₂ : (r • (↑a⁻¹ : A) - 1) * a = r • 1 - a := by
    rw [sub_mul, smul_mul_assoc, a.inv_mul, one_mulₓ]
  have hcomm : Commute (a : A) (r • (↑a⁻¹ : A) - 1) := by
    rwa [← h₂] at h₁
  exact (hcomm.is_unit_mul_iff.mp (h₁.symm ▸ h)).2

theorem inv_mem_iff {r : Rˣ} {a : Aˣ} : (r : R) ∈ σ (a : A) ↔ (↑r⁻¹ : R) ∈ σ (↑a⁻¹ : A) := by
  simp only [← mem_iff, ← not_iff_not, mem_resolvent_set_iff]
  exact
    ⟨fun h => inv_mem_resolvent_set h, fun h => by
      simpa using inv_mem_resolvent_set h⟩

theorem zero_mem_resolvent_set_of_unit (a : Aˣ) : 0 ∈ ResolventSet R (a : A) := by
  rw [mem_resolvent_set_iff, IsUnit.sub_iff]
  simp

theorem ne_zero_of_mem_of_unit {a : Aˣ} {r : R} (hr : r ∈ σ (a : A)) : r ≠ 0 := fun hn =>
  (hn ▸ hr) (zero_mem_resolvent_set_of_unit a)

theorem add_mem_iff {a : A} {r s : R} : r ∈ σ a ↔ r + s ∈ σ (↑ₐ s + a) := by
  apply not_iff_not.mpr
  simp only [← mem_resolvent_set_iff]
  have h_eq : ↑ₐ (r + s) - (↑ₐ s + a) = ↑ₐ r - a := by
    simp
    noncomm_ring
  rw [h_eq]

theorem smul_mem_smul_iff {a : A} {s : R} {r : Rˣ} : r • s ∈ σ (r • a) ↔ s ∈ σ a := by
  apply not_iff_not.mpr
  simp only [← mem_resolvent_set_iff, ← Algebra.algebra_map_eq_smul_one]
  have h_eq : (r • s) • (1 : A) = r • s • 1 := by
    simp
  rw [h_eq, ← smul_sub, is_unit_smul_iff]

open Pointwise Polynomial

theorem unit_smul_eq_smul (a : A) (r : Rˣ) : σ (r • a) = r • σ a := by
  ext
  have x_eq : x = r • r⁻¹ • x := by
    simp
  nth_rw 0[x_eq]
  rw [smul_mem_smul_iff]
  constructor
  · exact fun h =>
      ⟨r⁻¹ • x,
        ⟨h, by
          simp ⟩⟩
    
  · rintro ⟨_, _, x'_eq⟩
    simpa [x'_eq]
    

-- `r ∈ σ(a*b) ↔ r ∈ σ(b*a)` for any `r : Rˣ`
theorem unit_mem_mul_iff_mem_swap_mul {a b : A} {r : Rˣ} : ↑r ∈ σ (a * b) ↔ ↑r ∈ σ (b * a) := by
  apply not_iff_not.mpr
  simp only [← mem_resolvent_set_iff, ← Algebra.algebra_map_eq_smul_one]
  have coe_smul_eq : ↑r • 1 = r • (1 : A) := rfl
  rw [coe_smul_eq]
  simp only [← IsUnit.smul_sub_iff_sub_inv_smul]
  have right_inv_of_swap : ∀ {x y z : A} (h : (1 - x * y) * z = 1), (1 - y * x) * (1 + y * z * x) = 1 := fun x y z h =>
    calc
      (1 - y * x) * (1 + y * z * x) = 1 - y * x + y * ((1 - x * y) * z) * x := by
        noncomm_ring
      _ = 1 := by
        simp [← h]
      
  have left_inv_of_swap : ∀ {x y z : A} (h : z * (1 - x * y) = 1), (1 + y * z * x) * (1 - y * x) = 1 := fun x y z h =>
    calc
      (1 + y * z * x) * (1 - y * x) = 1 - y * x + y * (z * (1 - x * y)) * x := by
        noncomm_ring
      _ = 1 := by
        simp [← h]
      
  have is_unit_one_sub_mul_of_swap : ∀ {x y : A} (h : IsUnit (1 - x * y)), IsUnit (1 - y * x) := fun x y h => by
    let h₁ := right_inv_of_swap h.unit.val_inv
    let h₂ := left_inv_of_swap h.unit.inv_val
    exact ⟨⟨1 - y * x, 1 + y * h.unit.inv * x, h₁, h₂⟩, rfl⟩
  have is_unit_one_sub_mul_iff_swap : ∀ {x y : A}, IsUnit (1 - x * y) ↔ IsUnit (1 - y * x) := by
    intros
    constructor
    repeat'
      apply is_unit_one_sub_mul_of_swap
  rw [← smul_mul_assoc, ← mul_smul_comm r⁻¹ b a, is_unit_one_sub_mul_iff_swap]

theorem preimage_units_mul_eq_swap_mul {a b : A} : (coe : Rˣ → R) ⁻¹' σ (a * b) = coe ⁻¹' σ (b * a) := by
  ext
  exact unit_mem_mul_iff_mem_swap_mul

section Star

variable [HasInvolutiveStar R] [StarRing A] [StarModule R A]

theorem star_mem_resolvent_set_iff {r : R} {a : A} : star r ∈ ResolventSet R a ↔ r ∈ ResolventSet R (star a) := by
  refine' ⟨fun h => _, fun h => _⟩ <;>
    simpa only [← mem_resolvent_set_iff, ← Algebra.algebra_map_eq_smul_one, ← star_sub, ← star_smul, ← star_star, ←
      star_one] using IsUnit.star h

protected theorem map_star (a : A) : σ (star a) = star (σ a) := by
  ext
  simpa only [← Set.mem_star, ← mem_iff, ← not_iff_not] using star_mem_resolvent_set_iff.symm

end Star

end ScalarSemiring

section ScalarRing

variable {R : Type u} {A : Type v}

variable [CommRingₓ R] [Ringₓ A] [Algebra R A]

-- mathport name: «exprσ»
local notation "σ" => Spectrum R

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap R A

theorem left_add_coset_eq (a : A) (r : R) : LeftAddCoset r (σ a) = σ (↑ₐ r + a) := by
  ext
  rw [mem_left_add_coset_iff, neg_add_eq_sub, add_mem_iff]
  nth_rw 1[← sub_add_cancel x r]

open Polynomial

theorem exists_mem_of_not_is_unit_aeval_prod [IsDomain R] {p : R[X]} {a : A} (hp : p ≠ 0)
    (h : ¬IsUnit (aeval a (Multiset.map (fun x : R => X - c x) p.roots).Prod)) : ∃ k : R, k ∈ σ a ∧ eval k p = 0 := by
  rw [← Multiset.prod_to_list, AlgHom.map_list_prod] at h
  replace h := mt List.prod_is_unit h
  simp only [← not_forall, ← exists_prop, ← aeval_C, ← Multiset.mem_to_list, ← List.mem_mapₓ, ← aeval_X, ←
    exists_exists_and_eq_and, ← Multiset.mem_map, ← AlgHom.map_sub] at h
  rcases h with ⟨r, r_mem, r_nu⟩
  exact
    ⟨r, by
      rwa [mem_iff, ← IsUnit.sub_iff], by
      rwa [← is_root.def, ← mem_roots hp]⟩

end ScalarRing

section ScalarField

variable {𝕜 : Type u} {A : Type v}

variable [Field 𝕜] [Ringₓ A] [Algebra 𝕜 A]

-- mathport name: «exprσ»
local notation "σ" => Spectrum 𝕜

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap 𝕜 A

/-- Without the assumption `nontrivial A`, then `0 : A` would be invertible. -/
@[simp]
theorem zero_eq [Nontrivial A] : σ (0 : A) = {0} := by
  refine'
    Set.Subset.antisymm _
      (by
        simp [← Algebra.algebra_map_eq_smul_one, ← mem_iff])
  rw [Spectrum, Set.compl_subset_comm]
  intro k hk
  rw [Set.mem_compl_singleton_iff] at hk
  have : IsUnit (Units.mk0 k hk • (1 : A)) := IsUnit.smul (Units.mk0 k hk) is_unit_one
  simpa [← mem_resolvent_set_iff, ← Algebra.algebra_map_eq_smul_one]

@[simp]
theorem scalar_eq [Nontrivial A] (k : 𝕜) : σ (↑ₐ k) = {k} := by
  have coset_eq : LeftAddCoset k {0} = {k} := by
    ext
    constructor
    · intro hx
      simp [← LeftAddCoset] at hx
      exact hx
      
    · intro hx
      simp at hx
      exact
        ⟨0,
          ⟨Set.mem_singleton 0, by
            simp [← hx]⟩⟩
      
  calc σ (↑ₐ k) = σ (↑ₐ k + 0) := by
      simp _ = LeftAddCoset k (σ (0 : A)) := by
      rw [← left_add_coset_eq]_ = LeftAddCoset k {0} := by
      rw [zero_eq]_ = {k} := coset_eq

@[simp]
theorem one_eq [Nontrivial A] : σ (1 : A) = {1} :=
  calc
    σ (1 : A) = σ (↑ₐ 1) := by
      simp [← Algebra.algebra_map_eq_smul_one]
    _ = {1} := scalar_eq 1
    

open Pointwise

/-- the assumption `(σ a).nonempty` is necessary and cannot be removed without
    further conditions on the algebra `A` and scalar field `𝕜`. -/
theorem smul_eq_smul [Nontrivial A] (k : 𝕜) (a : A) (ha : (σ a).Nonempty) : σ (k • a) = k • σ a := by
  rcases eq_or_ne k 0 with (rfl | h)
  · simpa [← ha, ← zero_smul_set]
    
  · exact unit_smul_eq_smul a (Units.mk0 k h)
    

theorem nonzero_mul_eq_swap_mul (a b : A) : σ (a * b) \ {0} = σ (b * a) \ {0} := by
  suffices h : ∀ x y : A, σ (x * y) \ {0} ⊆ σ (y * x) \ {0}
  · exact Set.eq_of_subset_of_subset (h a b) (h b a)
    
  · rintro _ _ k ⟨k_mem, k_neq⟩
    change k with ↑(Units.mk0 k k_neq) at k_mem
    exact ⟨unit_mem_mul_iff_mem_swap_mul.mp k_mem, k_neq⟩
    

protected theorem map_inv (a : Aˣ) : (σ (a : A))⁻¹ = σ (↑a⁻¹ : A) := by
  refine' Set.eq_of_subset_of_subset (fun k hk => _) fun k hk => _
  · rw [Set.mem_inv] at hk
    have : k ≠ 0 := by
      simpa only [← inv_invₓ] using inv_ne_zero (ne_zero_of_mem_of_unit hk)
    lift k to 𝕜ˣ using is_unit_iff_ne_zero.mpr this
    rw [← Units.coe_inv k] at hk
    exact inv_mem_iff.mp hk
    
  · lift k to 𝕜ˣ using is_unit_iff_ne_zero.mpr (ne_zero_of_mem_of_unit hk)
    simpa only [← Units.coe_inv] using inv_mem_iff.mp hk
    

open Polynomial

/-- Half of the spectral mapping theorem for polynomials. We prove it separately
because it holds over any field, whereas `spectrum.map_polynomial_aeval_of_degree_pos` and
`spectrum.map_polynomial_aeval_of_nonempty` need the field to be algebraically closed. -/
theorem subset_polynomial_aeval (a : A) (p : 𝕜[X]) : (fun k => eval k p) '' σ a ⊆ σ (aeval a p) := by
  rintro _ ⟨k, hk, rfl⟩
  let q := C (eval k p) - p
  have hroot : is_root q k := by
    simp only [← eval_C, ← eval_sub, ← sub_self, ← is_root.def]
  rw [← mul_div_eq_iff_is_root, ← neg_mul_neg, neg_sub] at hroot
  have aeval_q_eq : ↑ₐ (eval k p) - aeval a p = aeval a q := by
    simp only [← aeval_C, ← AlgHom.map_sub, ← sub_left_inj]
  rw [mem_iff, aeval_q_eq, ← hroot, aeval_mul]
  have hcomm := (Commute.all (C k - X) (-(q / (X - C k)))).map (aeval a)
  apply mt fun h => (hcomm.is_unit_mul_iff.mp h).1
  simpa only [← aeval_X, ← aeval_C, ← AlgHom.map_sub] using hk

/-- The *spectral mapping theorem* for polynomials.  Note: the assumption `degree p > 0`
is necessary in case `σ a = ∅`, for then the left-hand side is `∅` and the right-hand side,
assuming `[nontrivial A]`, is `{k}` where `p = polynomial.C k`. -/
theorem map_polynomial_aeval_of_degree_pos [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X]) (hdeg : 0 < degree p) :
    σ (aeval a p) = (fun k => eval k p) '' σ a := by
  -- handle the easy direction via `spectrum.subset_polynomial_aeval`
  refine' Set.eq_of_subset_of_subset (fun k hk => _) (subset_polynomial_aeval a p)
  -- write `C k - p` product of linear factors and a constant; show `C k - p ≠ 0`.
  have hprod := eq_prod_roots_of_splits_id (IsAlgClosed.splits (C k - p))
  have h_ne : C k - p ≠ 0 :=
    ne_zero_of_degree_gt
      (by
        rwa [degree_sub_eq_right_of_degree_lt (lt_of_le_of_ltₓ degree_C_le hdeg)])
  have lead_ne := leading_coeff_ne_zero.mpr h_ne
  have lead_unit := (Units.map ↑ₐ.toMonoidHom (Units.mk0 _ lead_ne)).IsUnit
  /- leading coefficient is a unit so product of linear factors is not a unit;
    apply `exists_mem_of_not_is_unit_aeval_prod`. -/
  have p_a_eq : aeval a (C k - p) = ↑ₐ k - aeval a p := by
    simp only [← aeval_C, ← AlgHom.map_sub, ← sub_left_inj]
  rw [mem_iff, ← p_a_eq, hprod, aeval_mul, ((Commute.all _ _).map (aeval a)).is_unit_mul_iff, aeval_C] at hk
  replace hk := exists_mem_of_not_is_unit_aeval_prod h_ne (not_and.mp hk lead_unit)
  rcases hk with ⟨r, r_mem, r_ev⟩
  exact
    ⟨r, r_mem,
      symm
        (by
          simpa [← eval_sub, ← eval_C, ← sub_eq_zero] using r_ev)⟩

/-- In this version of the spectral mapping theorem, we assume the spectrum
is nonempty instead of assuming the degree of the polynomial is positive. Note: the
assumption `[nontrivial A]` is necessary for the same reason as in `spectrum.zero_eq`. -/
theorem map_polynomial_aeval_of_nonempty [IsAlgClosed 𝕜] [Nontrivial A] (a : A) (p : 𝕜[X]) (hnon : (σ a).Nonempty) :
    σ (aeval a p) = (fun k => eval k p) '' σ a := by
  refine' Or.elim (le_or_gtₓ (degree p) 0) (fun h => _) (map_polynomial_aeval_of_degree_pos a p)
  · rw [eq_C_of_degree_le_zero h]
    simp only [← Set.image_congr, ← eval_C, ← aeval_C, ← scalar_eq, ← Set.Nonempty.image_const hnon]
    

variable (𝕜)

/-- Every element `a` in a nontrivial finite-dimensional algebra `A`
over an algebraically closed field `𝕜` has non-empty spectrum. -/
-- We will use this both to show eigenvalues exist, and to prove Schur's lemma.
theorem nonempty_of_is_alg_closed_of_finite_dimensional [IsAlgClosed 𝕜] [Nontrivial A] [I : FiniteDimensional 𝕜 A]
    (a : A) : ∃ k : 𝕜, k ∈ σ a := by
  obtain ⟨p, ⟨h_mon, h_eval_p⟩⟩ := is_integral_of_noetherian (IsNoetherian.iff_fg.2 I) a
  have nu : ¬IsUnit (aeval a p) := by
    rw [← aeval_def] at h_eval_p
    rw [h_eval_p]
    simp
  rw [eq_prod_roots_of_monic_of_splits_id h_mon (IsAlgClosed.splits p)] at nu
  obtain ⟨k, hk, _⟩ := exists_mem_of_not_is_unit_aeval_prod (monic.ne_zero h_mon) nu
  exact ⟨k, hk⟩

end ScalarField

end Spectrum

namespace AlgHom

section CommSemiringₓ

variable {R : Type _} {A B : Type _} [CommRingₓ R] [Ringₓ A] [Algebra R A] [Ringₓ B] [Algebra R B]

-- mathport name: «exprσ»
local notation "σ" => Spectrum R

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap R A

theorem mem_resolvent_set_apply (φ : A →ₐ[R] B) {a : A} {r : R} (h : r ∈ ResolventSet R a) : r ∈ ResolventSet R (φ a) :=
  by
  simpa only [← map_sub, ← commutes] using h.map φ

theorem spectrum_apply_subset (φ : A →ₐ[R] B) (a : A) : σ (φ a) ⊆ σ a := fun _ => mt (mem_resolvent_set_apply φ)

end CommSemiringₓ

section CommRingₓ

variable {R : Type _} {A B : Type _} [CommRingₓ R] [Ringₓ A] [Algebra R A] [Ringₓ B] [Algebra R B]

-- mathport name: «exprσ»
local notation "σ" => Spectrum R

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap R A

theorem apply_mem_spectrum [Nontrivial R] (φ : A →ₐ[R] R) (a : A) : φ a ∈ σ a := by
  have h : ↑ₐ (φ a) - a ∈ φ.to_ring_hom.ker := by
    simp only [← RingHom.mem_ker, ← coe_to_ring_hom, ← commutes, ← Algebra.id.map_eq_id, ← to_ring_hom_eq_coe, ←
      RingHom.id_apply, ← sub_self, ← map_sub]
  simp only [← Spectrum.mem_iff, mem_nonunits_iff, ← coe_subset_nonunits φ.to_ring_hom.ker_ne_top h]

end CommRingₓ

end AlgHom


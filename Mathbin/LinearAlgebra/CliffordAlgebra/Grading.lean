/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.LinearAlgebra.CliffordAlgebra.Basic
import Mathbin.Data.Zmod.Basic
import Mathbin.RingTheory.GradedAlgebra.Basic

/-!
# Results about the grading structure of the clifford algebra

The main result is `clifford_algebra.graded_algebra`, which says that the clifford algebra is a
ℤ₂-graded algebra (or "superalgebra").
-/


namespace CliffordAlgebra

variable {R M : Type _} [CommRingₓ R] [AddCommGroupₓ M] [Module R M]

variable {Q : QuadraticForm R M}

open DirectSum

variable (Q)

/-- The even or odd submodule, defined as the supremum of the even or odd powers of
`(ι Q).range`. `even_odd 0` is the even submodule, and `even_odd 1` is the odd submodule. -/
def evenOdd (i : Zmod 2) : Submodule R (CliffordAlgebra Q) :=
  ⨆ j : { n : ℕ // ↑n = i }, (ι Q).range ^ (j : ℕ)

theorem one_le_even_odd_zero : 1 ≤ evenOdd Q 0 := by
  refine' le_transₓ _ (le_supr _ ⟨0, Nat.cast_zeroₓ⟩)
  exact (pow_zeroₓ _).Ge

theorem range_ι_le_even_odd_one : (ι Q).range ≤ evenOdd Q 1 := by
  refine' le_transₓ _ (le_supr _ ⟨1, Nat.cast_oneₓ⟩)
  exact (pow_oneₓ _).Ge

theorem ι_mem_even_odd_one (m : M) : ι Q m ∈ evenOdd Q 1 :=
  range_ι_le_even_odd_one Q <| LinearMap.mem_range_self _ m

theorem ι_mul_ι_mem_even_odd_zero (m₁ m₂ : M) : ι Q m₁ * ι Q m₂ ∈ evenOdd Q 0 :=
  Submodule.mem_supr_of_mem ⟨2, rfl⟩
    (by
      rw [Subtype.coe_mk, pow_two]
      exact Submodule.mul_mem_mul ((ι Q).mem_range_self m₁) ((ι Q).mem_range_self m₂))

theorem even_odd_mul_le (i j : Zmod 2) : evenOdd Q i * evenOdd Q j ≤ evenOdd Q (i + j) := by
  simp_rw [even_odd, Submodule.supr_eq_span, Submodule.span_mul_span]
  apply Submodule.span_mono
  intro z hz
  obtain ⟨x, y, hx, hy, rfl⟩ := hz
  obtain ⟨xi, hx'⟩ := set.mem_Union.mp hx
  obtain ⟨yi, hy'⟩ := set.mem_Union.mp hy
  refine'
    set.mem_Union.mpr
      ⟨⟨xi + yi, by
          simp only [← Nat.cast_addₓ, ← xi.prop, ← yi.prop]⟩,
        _⟩
  simp only [← Subtype.coe_mk, ← Nat.cast_addₓ, ← pow_addₓ]
  exact Submodule.mul_mem_mul hx' hy'

instance evenOdd.graded_monoid : SetLike.GradedMonoid (evenOdd Q) where
  one_mem := Submodule.one_le.mp (one_le_even_odd_zero Q)
  mul_mem := fun i j p q hp hq => Submodule.mul_le.mp (even_odd_mul_le Q _ _) _ hp _ hq

/-- A version of `clifford_algebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `clifford_algebra.graded_algebra`. -/
def GradedAlgebra.ι : M →ₗ[R] ⨁ i : Zmod 2, evenOdd Q i :=
  DirectSum.lof R (Zmod 2) (fun i => ↥(evenOdd Q i)) 1 ∘ₗ (ι Q).codRestrict _ (ι_mem_even_odd_one Q)

theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι Q m = DirectSum.of (fun i => ↥(evenOdd Q i)) 1 ⟨ι Q m, ι_mem_even_odd_one Q m⟩ :=
  rfl

theorem GradedAlgebra.ι_sq_scalar (m : M) : GradedAlgebra.ι Q m * GradedAlgebra.ι Q m = algebraMap R _ (Q m) := by
  rw [graded_algebra.ι_apply Q, DirectSum.of_mul_of, DirectSum.algebra_map_apply]
  refine' DirectSum.of_eq_of_graded_monoid_eq (Sigma.subtype_ext rfl <| ι_sq_scalar _ _)

theorem GradedAlgebra.lift_ι_eq (i' : Zmod 2) (x' : evenOdd Q i') :
    lift Q
        ⟨by
          apply graded_algebra.ι Q, GradedAlgebra.ι_sq_scalar Q⟩
        x' =
      DirectSum.of (fun i => evenOdd Q i) i' x' :=
  by
  cases' x' with x' hx'
  dsimp' only [← Subtype.coe_mk, ← DirectSum.lof_eq_of]
  refine' Submodule.supr_induction' _ (fun i x hx => _) _ (fun x y hx hy ihx ihy => _) hx'
  · obtain ⟨i, rfl⟩ := i
    dsimp' only [← Subtype.coe_mk]  at hx
    refine' Submodule.pow_induction_on_left' _ (fun r => _) (fun x y i hx hy ihx ihy => _) (fun m hm i x hx ih => _) hx
    · rw [AlgHom.commutes, DirectSum.algebra_map_apply]
      rfl
      
    · rw [AlgHom.map_add, ihx, ihy, ← map_add]
      rfl
      
    · obtain ⟨_, rfl⟩ := hm
      rw [AlgHom.map_mul, ih, lift_ι_apply, graded_algebra.ι_apply Q, DirectSum.of_mul_of]
      refine' DirectSum.of_eq_of_graded_monoid_eq (Sigma.subtype_ext _ _) <;>
        dsimp' only [← GradedMonoid.mk, ← Subtype.coe_mk]
      · rw [Nat.succ_eq_add_one, add_commₓ, Nat.cast_addₓ, Nat.cast_oneₓ]
        
      rfl
      
    
  · rw [AlgHom.map_zero]
    apply Eq.symm
    apply dfinsupp.single_eq_zero.mpr
    rfl
    
  · rw [AlgHom.map_add, ihx, ihy, ← map_add]
    rfl
    

/-- The clifford algebra is graded by the even and odd parts. -/
instance gradedAlgebra : GradedAlgebra (evenOdd Q) :=
  GradedAlgebra.ofAlgHom (evenOdd Q)
    (-- while not necessary, the `by apply` makes this elaborate faster
      lift
      Q
      ⟨by
        apply graded_algebra.ι Q, GradedAlgebra.ι_sq_scalar Q⟩)
    (-- the proof from here onward is mostly similar to the `tensor_algebra` case, with some extra
    -- handling for the `supr` in `even_odd`.
    by
      ext m
      dsimp' only [← LinearMap.comp_apply, ← AlgHom.to_linear_map_apply, ← AlgHom.comp_apply, ← AlgHom.id_apply]
      rw [lift_ι_apply, graded_algebra.ι_apply Q, DirectSum.coe_alg_hom_of, Subtype.coe_mk])
    (by
      apply graded_algebra.lift_ι_eq Q)

theorem supr_ι_range_eq_top : (⨆ i : ℕ, (ι Q).range ^ i) = ⊤ := by
  rw [← (DirectSum.Decomposition.is_internal (even_odd Q)).submodule_supr_eq_top, eq_comm]
  calc
    (⨆ (i : Zmod 2) (j : { n // ↑n = i }), (ι Q).range ^ ↑j) =
        ⨆ i : Σi : Zmod 2, { n : ℕ // ↑n = i }, (ι Q).range ^ (i.2 : ℕ) :=
      by
      rw [supr_sigma]_ = ⨆ i : ℕ, (ι Q).range ^ i :=
      Function.Surjective.supr_congr (fun i => i.2) (fun i => ⟨⟨_, i, rfl⟩, rfl⟩) fun _ => rfl

theorem even_odd_is_compl : IsCompl (evenOdd Q 0) (evenOdd Q 1) :=
  (DirectSum.Decomposition.is_internal (evenOdd Q)).IsCompl zero_ne_one <| by
    have : (Finset.univ : Finset (Zmod 2)) = {0, 1} := rfl
    simpa using congr_arg (coe : Finset (Zmod 2) → Set (Zmod 2)) this

/-- To show a property is true on the even or odd part, it suffices to show it is true on the
scalars or vectors (respectively), closed under addition, and under left-multiplication by a pair
of vectors. -/
@[elab_as_eliminator]
theorem even_odd_induction (n : Zmod 2) {P : ∀ x, x ∈ evenOdd Q n → Prop}
    (hr : ∀ (v) (h : v ∈ (ι Q).range ^ n.val), P v (Submodule.mem_supr_of_mem ⟨n.val, n.nat_cast_zmod_val⟩ h))
    (hadd : ∀ {x y hx hy}, P x hx → P y hy → P (x + y) (Submodule.add_mem _ hx hy))
    (hιι_mul :
      ∀ (m₁ m₂) {x hx},
        P x hx →
          P (ι Q m₁ * ι Q m₂ * x) (zero_addₓ n ▸ SetLike.GradedMonoid.mul_mem (ι_mul_ι_mem_even_odd_zero Q m₁ m₂) hx))
    (x : CliffordAlgebra Q) (hx : x ∈ evenOdd Q n) : P x hx := by
  apply Submodule.supr_induction' _ _ (hr 0 (Submodule.zero_mem _)) @hadd
  refine' Subtype.rec _
  simp_rw [Subtype.coe_mk, Zmod.nat_coe_zmod_eq_iff, add_commₓ n.val]
  rintro n' ⟨k, rfl⟩ xv
  simp_rw [pow_addₓ, pow_mulₓ]
  refine' Submodule.mul_induction_on' _ _
  · intro a ha b hb
    refine' Submodule.pow_induction_on_left' ((ι Q).range ^ 2) _ _ _ ha
    · intro r
      simp_rw [← Algebra.smul_def]
      exact hr _ (Submodule.smul_mem _ _ hb)
      
    · intro x y n hx hy
      simp_rw [add_mulₓ]
      apply hadd
      
    · intro x hx n y hy ihy
      revert hx
      simp_rw [pow_two]
      refine' Submodule.mul_induction_on' _ _
      · simp_rw [LinearMap.mem_range]
        rintro _ ⟨m₁, rfl⟩ _ ⟨m₂, rfl⟩
        simp_rw [mul_assoc _ y b]
        refine' hιι_mul _ _ ihy
        
      · intro x hx y hy ihx ihy
        simp_rw [add_mulₓ]
        apply hadd ihx ihy
        
      
    
  · intro x y hx hy
    apply hadd
    

/-- To show a property is true on the even parts, it suffices to show it is true on the
scalars, closed under addition, and under left-multiplication by a pair of vectors. -/
@[elab_as_eliminator]
theorem even_induction {P : ∀ x, x ∈ evenOdd Q 0 → Prop}
    (hr : ∀ r : R, P (algebraMap _ _ r) (SetLike.HasGradedOne.algebra_map_mem _ _))
    (hadd : ∀ {x y hx hy}, P x hx → P y hy → P (x + y) (Submodule.add_mem _ hx hy))
    (hιι_mul :
      ∀ (m₁ m₂) {x hx},
        P x hx →
          P (ι Q m₁ * ι Q m₂ * x) (zero_addₓ 0 ▸ SetLike.GradedMonoid.mul_mem (ι_mul_ι_mem_even_odd_zero Q m₁ m₂) hx))
    (x : CliffordAlgebra Q) (hx : x ∈ evenOdd Q 0) : P x hx := by
  refine' even_odd_induction Q 0 (fun rx => _) (@hadd) hιι_mul x hx
  simp_rw [Zmod.val_zero, pow_zeroₓ]
  rintro ⟨r, rfl⟩
  exact hr r

/-- To show a property is true on the odd parts, it suffices to show it is true on the
vectors, closed under addition, and under left-multiplication by a pair of vectors. -/
@[elab_as_eliminator]
theorem odd_induction {P : ∀ x, x ∈ evenOdd Q 1 → Prop} (hι : ∀ v, P (ι Q v) (ι_mem_even_odd_one _ _))
    (hadd : ∀ {x y hx hy}, P x hx → P y hy → P (x + y) (Submodule.add_mem _ hx hy))
    (hιι_mul :
      ∀ (m₁ m₂) {x hx},
        P x hx →
          P (ι Q m₁ * ι Q m₂ * x)
            (zero_addₓ (1 : Zmod 2) ▸ SetLike.GradedMonoid.mul_mem (ι_mul_ι_mem_even_odd_zero Q m₁ m₂) hx))
    (x : CliffordAlgebra Q) (hx : x ∈ evenOdd Q 1) : P x hx := by
  refine' even_odd_induction Q 1 (fun ιv => _) (@hadd) hιι_mul x hx
  simp_rw [Zmod.val_one, pow_oneₓ]
  rintro ⟨v, rfl⟩
  exact hι v

end CliffordAlgebra


/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.RingTheory.Noetherian
import Mathbin.RingTheory.ReesAlgebra
import Mathbin.RingTheory.Finiteness

/-!

# `I`-filtrations of modules

This file contains the definitions and basic results around (stable) `I`-filtrations of modules.

-/


universe u v

variable {R M : Type u} [CommRingₓ R] [AddCommGroupₓ M] [Module R M] (I : Ideal R)

open Polynomial

open Polynomial BigOperators

/-- An `I`-filtration on the module `M` is a sequence of decreasing submodules `N i` such that
`I • N ≤ I (i + 1)`. Note that we do not require the filtration to start from `⊤`. -/
@[ext]
structure Ideal.Filtration (M : Type u) [AddCommGroupₓ M] [Module R M] where
  n : ℕ → Submodule R M
  mono : ∀ i, N (i + 1) ≤ N i
  smul_le : ∀ i, I • N i ≤ N (i + 1)

variable (F F' : I.Filtration M) {I}

namespace Ideal.Filtration

theorem pow_smul_le (i j : ℕ) : I ^ i • F.n j ≤ F.n (i + j) := by
  induction i
  · simp
    
  · rw [pow_succₓ, mul_smul, Nat.succ_eq_add_one, add_assocₓ, add_commₓ 1, ← add_assocₓ]
    exact (Submodule.smul_mono_right i_ih).trans (F.smul_le _)
    

theorem pow_smul_le_pow_smul (i j k : ℕ) : I ^ (i + k) • F.n j ≤ I ^ k • F.n (i + j) := by
  rw [add_commₓ, pow_addₓ, mul_smul]
  exact Submodule.smul_mono_right (F.pow_smul_le i j)

protected theorem antitone : Antitone F.n :=
  antitone_nat_of_succ_le F.mono

/-- The trivial `I`-filtration of `N`. -/
@[simps]
def _root_.ideal.trivial_filtration (I : Ideal R) (N : Submodule R M) : I.Filtration M where
  n := fun i => N
  mono := fun i => le_of_eqₓ rfl
  smul_le := fun i => Submodule.smul_le_right

/-- The `sup` of two `I.filtration`s is an `I.filtration`. -/
instance : HasSup (I.Filtration M) :=
  ⟨fun F F' =>
    ⟨F.n⊔F'.n, fun i => sup_le_sup (F.mono i) (F'.mono i), fun i =>
      (le_of_eqₓ (Submodule.smul_sup _ _ _)).trans <| sup_le_sup (F.smul_le i) (F'.smul_le i)⟩⟩

/-- The `Sup` of a family of `I.filtration`s is an `I.filtration`. -/
instance : HasSupₓ (I.Filtration M) :=
  ⟨fun S =>
    { n := sup (Ideal.Filtration.n '' S),
      mono := fun i => by
        apply Sup_le_Sup_of_forall_exists_le _
        rintro _ ⟨⟨_, F, hF, rfl⟩, rfl⟩
        exact ⟨_, ⟨⟨_, F, hF, rfl⟩, rfl⟩, F.mono i⟩,
      smul_le := fun i => by
        rw [Sup_eq_supr', supr_apply, Submodule.smul_supr, supr_apply]
        apply supr_mono _
        rintro ⟨_, F, hF, rfl⟩
        exact F.smul_le i }⟩

/-- The `inf` of two `I.filtration`s is an `I.filtration`. -/
instance : HasInf (I.Filtration M) :=
  ⟨fun F F' =>
    ⟨F.n⊓F'.n, fun i => inf_le_inf (F.mono i) (F'.mono i), fun i =>
      (Submodule.smul_inf_le _ _ _).trans <| inf_le_inf (F.smul_le i) (F'.smul_le i)⟩⟩

/-- The `Inf` of a family of `I.filtration`s is an `I.filtration`. -/
instance : HasInfₓ (I.Filtration M) :=
  ⟨fun S =>
    { n := inf (Ideal.Filtration.n '' S),
      mono := fun i => by
        apply Inf_le_Inf_of_forall_exists_le _
        rintro _ ⟨⟨_, F, hF, rfl⟩, rfl⟩
        exact ⟨_, ⟨⟨_, F, hF, rfl⟩, rfl⟩, F.mono i⟩,
      smul_le := fun i => by
        rw [Inf_eq_infi', infi_apply, infi_apply]
        refine' submodule.smul_infi_le.trans _
        apply infi_mono _
        rintro ⟨_, F, hF, rfl⟩
        exact F.smul_le i }⟩

instance : HasTop (I.Filtration M) :=
  ⟨I.trivialFiltration ⊤⟩

instance : HasBot (I.Filtration M) :=
  ⟨I.trivialFiltration ⊥⟩

@[simp]
theorem sup_N : (F⊔F').n = F.n⊔F'.n :=
  rfl

@[simp]
theorem Sup_N (S : Set (I.Filtration M)) : (sup S).n = sup (Ideal.Filtration.n '' S) :=
  rfl

@[simp]
theorem inf_N : (F⊓F').n = F.n⊓F'.n :=
  rfl

@[simp]
theorem Inf_N (S : Set (I.Filtration M)) : (inf S).n = inf (Ideal.Filtration.n '' S) :=
  rfl

@[simp]
theorem top_N : (⊤ : I.Filtration M).n = ⊤ :=
  rfl

@[simp]
theorem bot_N : (⊥ : I.Filtration M).n = ⊥ :=
  rfl

@[simp]
theorem supr_N {ι : Sort _} (f : ι → I.Filtration M) : (supr f).n = ⨆ i, (f i).n :=
  congr_arg sup (Set.range_comp _ _).symm

@[simp]
theorem infi_N {ι : Sort _} (f : ι → I.Filtration M) : (infi f).n = ⨅ i, (f i).n :=
  congr_arg inf (Set.range_comp _ _).symm

instance : CompleteLattice (I.Filtration M) :=
  Function.Injective.completeLattice Ideal.Filtration.n Ideal.Filtration.ext sup_N inf_N (fun _ => Sup_image)
    (fun _ => Inf_image) top_N bot_N

instance : Inhabited (I.Filtration M) :=
  ⟨⊥⟩

/-- An `I` filtration is stable if `I • F.N n = F.N (n+1)` for large enough `n`. -/
def Stable : Prop :=
  ∃ n₀, ∀, ∀ n ≥ n₀, ∀, I • F.n n = F.n (n + 1)

/-- The trivial stable `I`-filtration of `N`. -/
@[simps]
def _root_.ideal.stable_filtration (I : Ideal R) (N : Submodule R M) : I.Filtration M where
  n := fun i => I ^ i • N
  mono := fun i => by
    rw [add_commₓ, pow_addₓ, mul_smul]
    exact Submodule.smul_le_right
  smul_le := fun i => by
    rw [add_commₓ, pow_addₓ, mul_smul, pow_oneₓ]
    exact le_reflₓ _

theorem _root_.ideal.stable_filtration_stable (I : Ideal R) (N : Submodule R M) : (I.stableFiltration N).Stable := by
  use 0
  intro n _
  dsimp'
  rw [add_commₓ, pow_addₓ, mul_smul, pow_oneₓ]

variable {F F'} (h : F.Stable)

include h

theorem Stable.exists_pow_smul_eq : ∃ n₀, ∀ k, F.n (n₀ + k) = I ^ k • F.n n₀ := by
  obtain ⟨n₀, hn⟩ := h
  use n₀
  intro k
  induction k
  · simp
    
  · rw [Nat.succ_eq_add_one, ← add_assocₓ, ← hn, k_ih, add_commₓ, pow_addₓ, mul_smul, pow_oneₓ]
    linarith
    

theorem Stable.exists_pow_smul_eq_of_ge : ∃ n₀, ∀, ∀ n ≥ n₀, ∀, F.n n = I ^ (n - n₀) • F.n n₀ := by
  obtain ⟨n₀, hn₀⟩ := h.exists_pow_smul_eq
  use n₀
  intro n hn
  convert hn₀ (n - n₀)
  rw [add_commₓ, tsub_add_cancel_of_le hn]

omit h

theorem stable_iff_exists_pow_smul_eq_of_ge : F.Stable ↔ ∃ n₀, ∀, ∀ n ≥ n₀, ∀, F.n n = I ^ (n - n₀) • F.n n₀ := by
  refine' ⟨stable.exists_pow_smul_eq_of_ge, fun h => ⟨h.some, fun n hn => _⟩⟩
  rw [h.some_spec n hn,
    h.some_spec (n + 1)
      (by
        linarith),
    smul_smul, ← pow_succₓ, tsub_add_eq_add_tsub hn]

theorem Stable.exists_forall_le (h : F.Stable) (e : F.n 0 ≤ F'.n 0) : ∃ n₀, ∀ n, F.n (n + n₀) ≤ F'.n n := by
  obtain ⟨n₀, hF⟩ := h
  use n₀
  intro n
  induction' n with n hn
  · refine' (F.antitone _).trans e
    simp
    
  · rw [Nat.succ_eq_one_add, add_assocₓ, add_commₓ, add_commₓ 1 n, ← hF]
    exact (Submodule.smul_mono_right hn).trans (F'.smul_le _)
    simp
    

theorem Stable.bounded_difference (h : F.Stable) (h' : F'.Stable) (e : F.n 0 = F'.n 0) :
    ∃ n₀, ∀ n, F.n (n + n₀) ≤ F'.n n ∧ F'.n (n + n₀) ≤ F.n n := by
  obtain ⟨n₁, h₁⟩ := h.exists_forall_le (le_of_eqₓ e)
  obtain ⟨n₂, h₂⟩ := h'.exists_forall_le (le_of_eqₓ e.symm)
  use max n₁ n₂
  intro n
  refine' ⟨(F.antitone _).trans (h₁ n), (F'.antitone _).trans (h₂ n)⟩ <;> simp

end Ideal.Filtration


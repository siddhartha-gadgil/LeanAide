/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Data.Matrix.Basis
import Mathbin.LinearAlgebra.Basis
import Mathbin.LinearAlgebra.Pi

/-!
# The standard basis

This file defines the standard basis `pi.basis (s : ∀ j, basis (ι j) R (M j))`,
which is the `Σ j, ι j`-indexed basis of Π j, M j`. The basis vectors are given by
`pi.basis s ⟨j, i⟩ j' = linear_map.std_basis R M j' (s j) i = if j = j' then s i else 0`.

The standard basis on `R^η`, i.e. `η → R` is called `pi.basis_fun`.

To give a concrete example, `linear_map.std_basis R (λ (i : fin 3), R) i 1`
gives the `i`th unit basis vector in `R³`, and `pi.basis_fun R (fin 3)` proves
this is a basis over `fin 3 → R`.

## Main definitions

 - `linear_map.std_basis R M`: if `x` is a basis vector of `M i`, then
   `linear_map.std_basis R M i x` is the `i`th standard basis vector of `Π i, M i`.
 - `pi.basis s`: given a basis `s i` for each `M i`, the standard basis on `Π i, M i`
 - `pi.basis_fun R η`: the standard basis on `R^η`, i.e. `η → R`, given by
   `pi.basis_fun R η i j = if i = j then 1 else 0`.
 - `matrix.std_basis R n m`: the standard basis on `matrix n m R`, given by
   `matrix.std_basis R n m (i, j) i' j' = if (i, j) = (i', j') then 1 else 0`.

-/


open Function Submodule

open BigOperators

open BigOperators

namespace LinearMap

variable (R : Type _) {ι : Type _} [Semiringₓ R] (φ : ι → Type _) [∀ i, AddCommMonoidₓ (φ i)] [∀ i, Module R (φ i)]
  [DecidableEq ι]

/-- The standard basis of the product of `φ`. -/
def stdBasis : ∀ i : ι, φ i →ₗ[R] ∀ i, φ i :=
  single

theorem std_basis_apply (i : ι) (b : φ i) : stdBasis R φ i b = update 0 i b :=
  rfl

theorem coe_std_basis (i : ι) : ⇑(stdBasis R φ i) = Pi.single i :=
  rfl

@[simp]
theorem std_basis_same (i : ι) (b : φ i) : stdBasis R φ i b i = b :=
  Pi.single_eq_same i b

theorem std_basis_ne (i j : ι) (h : j ≠ i) (b : φ i) : stdBasis R φ i b j = 0 :=
  Pi.single_eq_of_ne h b

theorem std_basis_eq_pi_diag (i : ι) : stdBasis R φ i = pi (diag i) := by
  ext x j
  convert (update_apply 0 x i j _).symm
  rfl

theorem ker_std_basis (i : ι) : ker (stdBasis R φ i) = ⊥ :=
  ker_eq_bot_of_injective <| Pi.single_injective _ _

theorem proj_comp_std_basis (i j : ι) : (proj i).comp (stdBasis R φ j) = diag j i := by
  rw [std_basis_eq_pi_diag, proj_pi]

theorem proj_std_basis_same (i : ι) : (proj i).comp (stdBasis R φ i) = id :=
  LinearMap.ext <| std_basis_same R φ i

theorem proj_std_basis_ne (i j : ι) (h : i ≠ j) : (proj i).comp (stdBasis R φ j) = 0 :=
  LinearMap.ext <| std_basis_ne R φ _ _ h

theorem supr_range_std_basis_le_infi_ker_proj (I J : Set ι) (h : Disjoint I J) :
    (⨆ i ∈ I, range (stdBasis R φ i)) ≤ ⨅ i ∈ J, ker (proj i) := by
  refine' supr_le fun i => supr_le fun hi => range_le_iff_comap.2 _
  simp only [← (ker_comp _ _).symm, ← eq_top_iff, ← SetLike.le_def, ← mem_ker, ← comap_infi, ← mem_infi]
  rintro b - j hj
  rw [proj_std_basis_ne R φ j i, zero_apply]
  rintro rfl
  exact h ⟨hi, hj⟩

theorem infi_ker_proj_le_supr_range_std_basis {I : Finset ι} {J : Set ι} (hu : Set.Univ ⊆ ↑I ∪ J) :
    (⨅ i ∈ J, ker (proj i)) ≤ ⨆ i ∈ I, range (stdBasis R φ i) :=
  SetLike.le_def.2
    (by
      intro b hb
      simp only [← mem_infi, ← mem_ker, ← proj_apply] at hb
      rw [←
        show (∑ i in I, std_basis R φ i (b i)) = b by
          ext i
          rw [Finset.sum_apply, ← std_basis_same R φ i (b i)]
          refine' Finset.sum_eq_single i (fun j hjI ne => std_basis_ne _ _ _ _ Ne.symm _) _
          intro hiI
          rw [std_basis_same]
          exact hb _ ((hu trivialₓ).resolve_left hiI)]
      exact sum_mem_bsupr fun i hi => (std_basis R φ i).mem_range_self (b i))

theorem supr_range_std_basis_eq_infi_ker_proj {I J : Set ι} (hd : Disjoint I J) (hu : Set.Univ ⊆ I ∪ J)
    (hI : Set.Finite I) : (⨆ i ∈ I, range (stdBasis R φ i)) = ⨅ i ∈ J, ker (proj i) := by
  refine' le_antisymmₓ (supr_range_std_basis_le_infi_ker_proj _ _ _ _ hd) _
  have : Set.Univ ⊆ ↑hI.to_finset ∪ J := by
    rwa [hI.coe_to_finset]
  refine' le_transₓ (infi_ker_proj_le_supr_range_std_basis R φ this) (supr_mono fun i => _)
  rw [Set.Finite.mem_to_finset]
  exact le_rfl

theorem supr_range_std_basis [Fintype ι] : (⨆ i : ι, range (stdBasis R φ i)) = ⊤ := by
  have : (Set.Univ : Set ι) ⊆ ↑(Finset.univ : Finset ι) ∪ ∅ := by
    rw [Finset.coe_univ, Set.union_empty]
  apply top_unique
  convert infi_ker_proj_le_supr_range_std_basis R φ this
  exact infi_emptyset.symm
  exact funext fun i => ((@supr_pos _ _ _ fun h => range (std_basis R φ i)) <| Finset.mem_univ i).symm

theorem disjoint_std_basis_std_basis (I J : Set ι) (h : Disjoint I J) :
    Disjoint (⨆ i ∈ I, range (stdBasis R φ i)) (⨆ i ∈ J, range (stdBasis R φ i)) := by
  refine'
    Disjoint.mono (supr_range_std_basis_le_infi_ker_proj _ _ _ _ <| disjoint_compl_right)
      (supr_range_std_basis_le_infi_ker_proj _ _ _ _ <| disjoint_compl_right) _
  simp only [← Disjoint, ← SetLike.le_def, ← mem_infi, ← mem_inf, ← mem_ker, ← mem_bot, ← proj_apply, ← funext_iff]
  rintro b ⟨hI, hJ⟩ i
  classical
  by_cases' hiI : i ∈ I
  · by_cases' hiJ : i ∈ J
    · exact (h ⟨hiI, hiJ⟩).elim
      
    · exact hJ i hiJ
      
    
  · exact hI i hiI
    

theorem std_basis_eq_single {a : R} :
    (fun i : ι => (stdBasis R (fun _ : ι => R) i) a) = fun i : ι => Finsupp.single i a :=
  funext fun i => (Finsupp.single_eq_pi_single i a).symm

end LinearMap

namespace Pi

open LinearMap

open Set

variable {R : Type _}

section Module

variable {η : Type _} {ιs : η → Type _} {Ms : η → Type _}

theorem linear_independent_std_basis [Ringₓ R] [∀ i, AddCommGroupₓ (Ms i)] [∀ i, Module R (Ms i)] [DecidableEq η]
    (v : ∀ j, ιs j → Ms j) (hs : ∀ i, LinearIndependent R (v i)) :
    LinearIndependent R fun ji : Σj, ιs j => stdBasis R Ms ji.1 (v ji.1 ji.2) := by
  have hs' : ∀ j : η, LinearIndependent R fun i : ιs j => std_basis R Ms j (v j i) := by
    intro j
    exact (hs j).map' _ (ker_std_basis _ _ _)
  apply linear_independent_Union_finite hs'
  · intro j J _ hiJ
    simp [← (Set.Union.equations._eqn_1 _).symm, ← Submodule.span_image, ← Submodule.span_Union]
    have h₀ : ∀ j, span R (range fun i : ιs j => std_basis R Ms j (v j i)) ≤ range (std_basis R Ms j) := by
      intro j
      rw [span_le, LinearMap.range_coe]
      apply range_comp_subset_range
    have h₁ : span R (range fun i : ιs j => std_basis R Ms j (v j i)) ≤ ⨆ i ∈ {j}, range (std_basis R Ms i) := by
      rw [@supr_singleton _ _ _ fun i => LinearMap.range (std_basis R (fun j : η => Ms j) i)]
      apply h₀
    have h₂ :
      (⨆ j ∈ J, span R (range fun i : ιs j => std_basis R Ms j (v j i))) ≤
        ⨆ j ∈ J, range (std_basis R (fun j : η => Ms j) j) :=
      supr₂_mono fun i _ => h₀ i
    have h₃ : Disjoint (fun i : η => i ∈ {j}) J := by
      convert Set.disjoint_singleton_left.2 hiJ using 0
    exact (disjoint_std_basis_std_basis _ _ _ _ h₃).mono h₁ h₂
    

variable [Semiringₓ R] [∀ i, AddCommMonoidₓ (Ms i)] [∀ i, Module R (Ms i)]

variable [Fintype η]

section

open LinearEquiv

/-- `pi.basis (s : ∀ j, basis (ιs j) R (Ms j))` is the `Σ j, ιs j`-indexed basis on `Π j, Ms j`
given by `s j` on each component.

For the standard basis over `R` on the finite-dimensional space `η → R` see `pi.basis_fun`.
-/
protected noncomputable def basis (s : ∀ j, Basis (ιs j) R (Ms j)) : Basis (Σj, ιs j) R (∀ j, Ms j) := by
  -- The `add_comm_monoid (Π j, Ms j)` instance was hard to find.
  -- Defining this in tactic mode seems to shake up instance search enough that it works by itself.
  refine' Basis.of_repr (_ ≪≫ₗ (Finsupp.sigmaFinsuppLequivPiFinsupp R).symm)
  exact LinearEquiv.piCongrRight fun j => (s j).repr

@[simp]
theorem basis_repr_std_basis [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) (j i) :
    (Pi.basis s).repr (stdBasis R _ j (s j i)) = Finsupp.single ⟨j, i⟩ 1 := by
  ext ⟨j', i'⟩
  by_cases' hj : j = j'
  · subst hj
    simp only [← Pi.basis, ← LinearEquiv.trans_apply, ← Basis.repr_self, ← std_basis_same, ←
      LinearEquiv.Pi_congr_right_apply, ← Finsupp.sigma_finsupp_lequiv_pi_finsupp_symm_apply]
    symm
    exact
      Basis.Finsupp.single_apply_left (fun i i' (h : (⟨j, i⟩ : Σj, ιs j) = ⟨j, i'⟩) => eq_of_heq (Sigma.mk.inj h).2) _ _
        _
    
  simp only [← Pi.basis, ← LinearEquiv.trans_apply, ← Finsupp.sigma_finsupp_lequiv_pi_finsupp_symm_apply, ←
    LinearEquiv.Pi_congr_right_apply]
  dsimp'
  rw [std_basis_ne _ _ _ _ (Ne.symm hj), LinearEquiv.map_zero, Finsupp.zero_apply, Finsupp.single_eq_of_ne]
  rintro ⟨⟩
  contradiction

@[simp]
theorem basis_apply [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) (ji) :
    Pi.basis s ji = stdBasis R _ ji.1 (s ji.1 ji.2) :=
  Basis.apply_eq_iff.mpr
    (by
      simp )

@[simp]
theorem basis_repr (s : ∀ j, Basis (ιs j) R (Ms j)) (x) (ji) : (Pi.basis s).repr x ji = (s ji.1).repr (x ji.1) ji.2 :=
  rfl

end

section

variable (R η)

/-- The basis on `η → R` where the `i`th basis vector is `function.update 0 i 1`. -/
noncomputable def basisFun : Basis η R (∀ j : η, R) :=
  Basis.ofEquivFun (LinearEquiv.refl _ _)

@[simp]
theorem basis_fun_apply [DecidableEq η] (i) : basisFun R η i = stdBasis R (fun i : η => R) i 1 := by
  simp only [← basis_fun, ← Basis.coe_of_equiv_fun, ← LinearEquiv.refl_symm, ← LinearEquiv.refl_apply, ←
    std_basis_apply]
  congr

-- Get rid of a `decidable_eq` mismatch.
@[simp]
theorem basis_fun_repr (x : η → R) (i : η) : (Pi.basisFun R η).repr x i = x i := by
  simp [← basis_fun]

end

end Module

end Pi

namespace Matrix

variable (R : Type _) (m n : Type _) [Fintype m] [Fintype n] [Semiringₓ R]

/-- The standard basis of `matrix m n R`. -/
noncomputable def stdBasis : Basis (m × n) R (Matrix m n R) :=
  Basis.reindex (Pi.basis fun i : m => Pi.basisFun R n) (Equivₓ.sigmaEquivProd _ _)

variable {n m}

theorem std_basis_eq_std_basis_matrix (i : n) (j : m) [DecidableEq n] [DecidableEq m] :
    stdBasis R n m (i, j) = stdBasisMatrix i j (1 : R) := by
  ext a b
  by_cases' hi : i = a <;> by_cases' hj : j = b
  · simp [← std_basis, ← hi, ← hj]
    
  · simp [← std_basis, ← hi, ← hj, ← Ne.symm hj, ← LinearMap.std_basis_ne]
    
  · simp [← std_basis, ← hi, ← hj, ← Ne.symm hi, ← LinearMap.std_basis_ne]
    
  · simp [← std_basis, ← hi, ← hj, ← Ne.symm hj, ← Ne.symm hi, ← LinearMap.std_basis_ne]
    

end Matrix


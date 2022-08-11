/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.LinearAlgebra.Dimension
import Mathbin.RingTheory.PrincipalIdealDomain
import Mathbin.RingTheory.Finiteness

/-! # Free modules over PID

A free `R`-module `M` is a module with a basis over `R`,
equivalently it is an `R`-module linearly equivalent to `ι →₀ R` for some `ι`.

This file proves a submodule of a free `R`-module of finite rank is also
a free `R`-module of finite rank, if `R` is a principal ideal domain (PID),
i.e. we have instances `[is_domain R] [is_principal_ideal_ring R]`.
We express "free `R`-module of finite rank" as a module `M` which has a basis
`b : ι → R`, where `ι` is a `fintype`.
We call the cardinality of `ι` the rank of `M` in this file;
it would be equal to `finrank R M` if `R` is a field and `M` is a vector space.

## Main results

In this section, `M` is a free and finitely generated `R`-module, and
`N` is a submodule of `M`.

 - `submodule.induction_on_rank`: if `P` holds for `⊥ : submodule R M` and if
  `P N` follows from `P N'` for all `N'` that are of lower rank, then `P` holds
   on all submodules

 - `submodule.exists_basis_of_pid`: if `R` is a PID, then `N : submodule R M` is
   free and finitely generated. This is the first part of the structure theorem
   for modules.

- `submodule.smith_normal_form`: if `R` is a PID, then `M` has a basis
  `bM` and `N` has a basis `bN` such that `bN i = a i • bM i`.
  Equivalently, a linear map `f : M →ₗ M` with `range f = N` can be written as
  a matrix in Smith normal form, a diagonal matrix with the coefficients `a i`
  along the diagonal.

## Tags

free module, finitely generated module, rank, structure theorem

-/


open BigOperators

universe u v

section Ringₓ

variable {R : Type u} {M : Type v} [Ringₓ R] [AddCommGroupₓ M] [Module R M]

variable {ι : Type _} (b : Basis ι R M)

open Submodule.IsPrincipal Submodule

theorem eq_bot_of_generator_maximal_map_eq_zero (b : Basis ι R M) {N : Submodule R M} {ϕ : M →ₗ[R] R}
    (hϕ : ∀ ψ : M →ₗ[R] R, N.map ϕ ≤ N.map ψ → N.map ψ = N.map ϕ) [(N.map ϕ).IsPrincipal]
    (hgen : generator (N.map ϕ) = 0) : N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  refine' b.ext_elem fun i => _
  rw [(eq_bot_iff_generator_eq_zero _).mpr hgen] at hϕ
  rw [LinearEquiv.map_zero, Finsupp.zero_apply]
  exact (Submodule.eq_bot_iff _).mp (hϕ (Finsupp.lapply i ∘ₗ ↑b.repr) bot_le) _ ⟨x, hx, rfl⟩

theorem eq_bot_of_generator_maximal_submodule_image_eq_zero {N O : Submodule R M} (b : Basis ι R O) (hNO : N ≤ O)
    {ϕ : O →ₗ[R] R}
    (hϕ : ∀ ψ : O →ₗ[R] R, ϕ.submoduleImage N ≤ ψ.submoduleImage N → ψ.submoduleImage N = ϕ.submoduleImage N)
    [(ϕ.submoduleImage N).IsPrincipal] (hgen : generator (ϕ.submoduleImage N) = 0) : N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  refine' congr_arg coe (show (⟨x, hNO hx⟩ : O) = 0 from b.ext_elem fun i => _)
  rw [(eq_bot_iff_generator_eq_zero _).mpr hgen] at hϕ
  rw [LinearEquiv.map_zero, Finsupp.zero_apply]
  refine' (Submodule.eq_bot_iff _).mp (hϕ (Finsupp.lapply i ∘ₗ ↑b.repr) bot_le) _ _
  exact (LinearMap.mem_submodule_image_of_le hNO).mpr ⟨x, hx, rfl⟩

end Ringₓ

section IsDomain

variable {ι : Type _} {R : Type _} [CommRingₓ R] [IsDomain R]

variable {M : Type _} [AddCommGroupₓ M] [Module R M] {b : ι → M}

open Submodule.IsPrincipal Set Submodule

theorem dvd_generator_iff {I : Ideal R} [I.IsPrincipal] {x : R} (hx : x ∈ I) : x ∣ generator I ↔ I = Ideal.span {x} :=
  by
  conv_rhs => rw [← span_singleton_generator I]
  erw [Ideal.span_singleton_eq_span_singleton, ← dvd_dvd_iff_associated, ← mem_iff_generator_dvd]
  exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

end IsDomain

section PrincipalIdealDomain

open Submodule.IsPrincipal Set Submodule

variable {ι : Type _} {R : Type _} [CommRingₓ R] [IsDomain R] [IsPrincipalIdealRing R]

variable {M : Type _} [AddCommGroupₓ M] [Module R M] {b : ι → M}

open Submodule.IsPrincipal

theorem generator_maximal_submodule_image_dvd {N O : Submodule R M} (hNO : N ≤ O) {ϕ : O →ₗ[R] R}
    (hϕ : ∀ ψ : O →ₗ[R] R, ϕ.submoduleImage N ≤ ψ.submoduleImage N → ψ.submoduleImage N = ϕ.submoduleImage N)
    [(ϕ.submoduleImage N).IsPrincipal] (y : M) (yN : y ∈ N) (ϕy_eq : ϕ ⟨y, hNO yN⟩ = generator (ϕ.submoduleImage N))
    (ψ : O →ₗ[R] R) : generator (ϕ.submoduleImage N) ∣ ψ ⟨y, hNO yN⟩ := by
  let a : R := generator (ϕ.submodule_image N)
  let d : R := is_principal.generator (Submodule.span R {a, ψ ⟨y, hNO yN⟩})
  have d_dvd_left : d ∣ a := (mem_iff_generator_dvd _).mp (subset_span (mem_insert _ _))
  have d_dvd_right : d ∣ ψ ⟨y, hNO yN⟩ :=
    (mem_iff_generator_dvd _).mp (subset_span (mem_insert_of_mem _ (mem_singleton _)))
  refine' dvd_trans _ d_dvd_right
  rw [dvd_generator_iff, Ideal.span, ← span_singleton_generator (Submodule.span R {a, ψ ⟨y, hNO yN⟩})]
  obtain ⟨r₁, r₂, d_eq⟩ : ∃ r₁ r₂ : R, d = r₁ * a + r₂ * ψ ⟨y, hNO yN⟩ := by
    obtain ⟨r₁, r₂', hr₂', hr₁⟩ := mem_span_insert.mp (is_principal.generator_mem (Submodule.span R {a, ψ ⟨y, hNO yN⟩}))
    obtain ⟨r₂, rfl⟩ := mem_span_singleton.mp hr₂'
    exact ⟨r₁, r₂, hr₁⟩
  let ψ' : O →ₗ[R] R := r₁ • ϕ + r₂ • ψ
  have : span R {d} ≤ ψ'.submodule_image N := by
    rw [span_le, singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_submodule_image_of_le hNO]
    refine' ⟨y, yN, _⟩
    change r₁ * ϕ ⟨y, hNO yN⟩ + r₂ * ψ ⟨y, hNO yN⟩ = d
    rw [d_eq, ϕy_eq]
  refine' le_antisymmₓ (this.trans (le_of_eqₓ _)) (ideal.span_singleton_le_span_singleton.mpr d_dvd_left)
  rw [span_singleton_generator]
  refine' hϕ ψ' (le_transₓ _ this)
  rw [← span_singleton_generator (ϕ.submodule_image N)]
  exact ideal.span_singleton_le_span_singleton.mpr d_dvd_left
  · exact subset_span (mem_insert _ _)
    

/-- The induction hypothesis of `submodule.basis_of_pid` and `submodule.smith_normal_form`.

Basically, it says: let `N ≤ M` be a pair of submodules, then we can find a pair of
submodules `N' ≤ M'` of strictly smaller rank, whose basis we can extend to get a basis
of `N` and `M`. Moreover, if the basis for `M'` is up to scalars a basis for `N'`,
then the basis we find for `M` is up to scalars a basis for `N`.

For `basis_of_pid` we only need the first half and can fix `M = ⊤`,
for `smith_normal_form` we need the full statement,
but must also feed in a basis for `M` using `basis_of_pid` to keep the induction going.
-/
theorem Submodule.basis_of_pid_aux [Fintype ι] {O : Type _} [AddCommGroupₓ O] [Module R O] (M N : Submodule R O)
    (b'M : Basis ι R M) (N_bot : N ≠ ⊥) (N_le_M : N ≤ M) :
    ∃ y ∈ M,
      ∃ (a : R)(hay : a • y ∈ N),
        ∃ M' ≤ M,
          ∃ N' ≤ N,
            ∃ (N'_le_M' : N' ≤ M')(y_ortho_M' : ∀ (c : R) (z : O), z ∈ M' → c • y + z = 0 → c = 0)(ay_ortho_N' :
              ∀ (c : R) (z : O), z ∈ N' → c • a • y + z = 0 → c = 0),
              ∀ (n') (bN' : Basis (Finₓ n') R N'),
                ∃ bN : Basis (Finₓ (n' + 1)) R N,
                  ∀ (m') (hn'm' : n' ≤ m') (bM' : Basis (Finₓ m') R M'),
                    ∃ (hnm : n' + 1 ≤ m' + 1)(bM : Basis (Finₓ (m' + 1)) R M),
                      ∀ (as : Finₓ n' → R) (h : ∀ i : Finₓ n', (bN' i : O) = as i • (bM' (Finₓ.castLe hn'm' i) : O)),
                        ∃ as' : Finₓ (n' + 1) → R,
                          ∀ i : Finₓ (n' + 1), (bN i : O) = as' i • (bM (Finₓ.castLe hnm i) : O) :=
  by
  -- Let `ϕ` be a maximal projection of `M` onto `R`, in the sense that there is
  -- no `ψ` whose image of `N` is larger than `ϕ`'s image of `N`.
  have :
    ∃ ϕ : M →ₗ[R] R,
      ∀ ψ : M →ₗ[R] R, ϕ.submoduleImage N ≤ ψ.submoduleImage N → ψ.submoduleImage N = ϕ.submoduleImage N :=
    by
    obtain ⟨P, P_eq, P_max⟩ :=
      set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) _
        (show (Set.Range fun ψ : M →ₗ[R] R => ψ.submoduleImage N).Nonempty from ⟨_, set.mem_range.mpr ⟨0, rfl⟩⟩)
    obtain ⟨ϕ, rfl⟩ := set.mem_range.mp P_eq
    exact ⟨ϕ, fun ψ hψ => P_max _ ⟨_, rfl⟩ hψ⟩
  let ϕ := this.some
  have ϕ_max := this.some_spec
  -- Since `ϕ(N)` is a `R`-submodule of the PID `R`,
  -- it is principal and generated by some `a`.
  let a := generator (ϕ.submodule_image N)
  have a_mem : a ∈ ϕ.submodule_image N := generator_mem _
  -- If `a` is zero, then the submodule is trivial. So let's assume `a ≠ 0`, `N ≠ ⊥`.
  by_cases' a_zero : a = 0
  · have := eq_bot_of_generator_maximal_submodule_image_eq_zero b'M N_le_M ϕ_max a_zero
    contradiction
    
  -- We claim that `ϕ⁻¹ a = y` can be taken as basis element of `N`.
  obtain ⟨y, yN, ϕy_eq⟩ := (LinearMap.mem_submodule_image_of_le N_le_M).mp a_mem
  have ϕy_ne_zero : ϕ ⟨y, N_le_M yN⟩ ≠ 0 := fun h => a_zero (ϕy_eq.symm.trans h)
  -- Write `y` as `a • y'` for some `y'`.
  have hdvd : ∀ i, a ∣ b'M.coord i ⟨y, N_le_M yN⟩ := fun i =>
    generator_maximal_submodule_image_dvd N_le_M ϕ_max y yN ϕy_eq (b'M.coord i)
  choose c hc using hdvd
  let y' : O := ∑ i, c i • b'M i
  have y'M : y' ∈ M := M.sum_mem fun i _ => M.smul_mem (c i) (b'M i).2
  have mk_y' : (⟨y', y'M⟩ : M) = ∑ i, c i • b'M i :=
    Subtype.ext
      (show y' = M.subtype _ by
        simp only [← LinearMap.map_sum, ← LinearMap.map_smul]
        rfl)
  have a_smul_y' : a • y' = y := by
    refine' congr_arg coe (show (a • ⟨y', y'M⟩ : M) = ⟨y, N_le_M yN⟩ from _)
    rw [← b'M.sum_repr ⟨y, N_le_M yN⟩, mk_y', Finset.smul_sum]
    refine' Finset.sum_congr rfl fun i _ => _
    rw [← mul_smul, ← hc]
    rfl
  -- We found an `y` and an `a`!
  refine' ⟨y', y'M, a, a_smul_y'.symm ▸ yN, _⟩
  have ϕy'_eq : ϕ ⟨y', y'M⟩ = 1 :=
    mul_left_cancel₀ a_zero
      (calc
        a • ϕ ⟨y', y'M⟩ = ϕ ⟨a • y', _⟩ := (ϕ.map_smul a ⟨y', y'M⟩).symm
        _ = ϕ ⟨y, N_le_M yN⟩ := by
          simp only [← a_smul_y']
        _ = a := ϕy_eq
        _ = a * 1 := (mul_oneₓ a).symm
        )
  have ϕy'_ne_zero : ϕ ⟨y', y'M⟩ ≠ 0 := by
    simpa only [← ϕy'_eq] using one_ne_zero
  -- `M' := ker (ϕ : M → R)` is smaller than `M` and `N' := ker (ϕ : N → R)` is smaller than `N`.
  let M' : Submodule R O := ϕ.ker.map M.subtype
  let N' : Submodule R O := (ϕ.comp (of_le N_le_M)).ker.map N.subtype
  have M'_le_M : M' ≤ M := M.map_subtype_le ϕ.ker
  have N'_le_M' : N' ≤ M' := by
    intro x hx
    simp only [← mem_map, ← LinearMap.mem_ker] at hx⊢
    obtain ⟨⟨x, xN⟩, hx, rfl⟩ := hx
    exact ⟨⟨x, N_le_M xN⟩, hx, rfl⟩
  have N'_le_N : N' ≤ N := N.map_subtype_le (ϕ.comp (of_le N_le_M)).ker
  -- So fill in those results as well.
  refine' ⟨M', M'_le_M, N', N'_le_N, N'_le_M', _⟩
  -- Note that `y'` is orthogonal to `M'`.
  have y'_ortho_M' : ∀ (c : R), ∀ z ∈ M', ∀, c • y' + z = 0 → c = 0 := by
    intro c x xM' hc
    obtain ⟨⟨x, xM⟩, hx', rfl⟩ := submodule.mem_map.mp xM'
    rw [LinearMap.mem_ker] at hx'
    have hc' : (c • ⟨y', y'M⟩ + ⟨x, xM⟩ : M) = 0 := Subtype.coe_injective hc
    simpa only [← LinearMap.map_add, ← LinearMap.map_zero, ← LinearMap.map_smul, ← smul_eq_mul, ← add_zeroₓ, ←
      mul_eq_zero, ← ϕy'_ne_zero, ← hx', ← or_falseₓ] using congr_arg ϕ hc'
  -- And `a • y'` is orthogonal to `N'`.
  have ay'_ortho_N' : ∀ (c : R), ∀ z ∈ N', ∀, c • a • y' + z = 0 → c = 0 := by
    intro c z zN' hc
    refine' (mul_eq_zero.mp (y'_ortho_M' (a * c) z (N'_le_M' zN') _)).resolve_left a_zero
    rw [mul_comm, mul_smul, hc]
  -- So we can extend a basis for `N'` with `y`
  refine' ⟨y'_ortho_M', ay'_ortho_N', fun n' bN' => ⟨_, _⟩⟩
  · refine' Basis.mkFinConsOfLe y yN bN' N'_le_N _ _
    · intro c z zN' hc
      refine' ay'_ortho_N' c z zN' _
      rwa [← a_smul_y'] at hc
      
    · intro z zN
      obtain ⟨b, hb⟩ : _ ∣ ϕ ⟨z, N_le_M zN⟩ := generator_submodule_image_dvd_of_mem N_le_M ϕ zN
      refine' ⟨-b, submodule.mem_map.mpr ⟨⟨_, N.sub_mem zN (N.smul_mem b yN)⟩, _, _⟩⟩
      · refine' linear_map.mem_ker.mpr (show ϕ (⟨z, N_le_M zN⟩ - b • ⟨y, N_le_M yN⟩) = 0 from _)
        rw [LinearMap.map_sub, LinearMap.map_smul, hb, ϕy_eq, smul_eq_mul, mul_comm, sub_self]
        
      · simp only [← sub_eq_add_neg, ← neg_smul]
        rfl
        
      
    
  -- And extend a basis for `M'` with `y'`
  intro m' hn'm' bM'
  refine' ⟨Nat.succ_le_succₓ hn'm', _, _⟩
  · refine' Basis.mkFinConsOfLe y' y'M bM' M'_le_M y'_ortho_M' _
    intro z zM
    refine' ⟨-ϕ ⟨z, zM⟩, ⟨⟨z, zM⟩ - ϕ ⟨z, zM⟩ • ⟨y', y'M⟩, linear_map.mem_ker.mpr _, _⟩⟩
    · rw [LinearMap.map_sub, LinearMap.map_smul, ϕy'_eq, smul_eq_mul, mul_oneₓ, sub_self]
      
    · rw [LinearMap.map_sub, LinearMap.map_smul, sub_eq_add_neg, neg_smul]
      rfl
      
    
  -- It remains to show the extended bases are compatible with each other.
  intro as h
  refine' ⟨Finₓ.cons a as, _⟩
  intro i
  rw [Basis.coe_mk_fin_cons_of_le, Basis.coe_mk_fin_cons_of_le]
  refine' Finₓ.cases _ (fun i => _) i
  · simp only [← Finₓ.cons_zero, ← Finₓ.cast_le_zero]
    exact a_smul_y'.symm
    
  · rw [Finₓ.cast_le_succ]
    simp only [← Finₓ.cons_succ, ← coe_of_le, ← h i]
    

/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

This is a `lemma` to make the induction a bit easier. To actually access the basis,
see `submodule.basis_of_pid`.

See also the stronger version `submodule.smith_normal_form`.
-/
theorem Submodule.nonempty_basis_of_pid {ι : Type _} [Fintype ι] (b : Basis ι R M) (N : Submodule R M) :
    ∃ n : ℕ, Nonempty (Basis (Finₓ n) R N) := by
  have := Classical.decEq M
  refine' N.induction_on_rank b _ _
  intro N ih
  let b' := (b.reindex (Fintype.equivFin ι)).map (LinearEquiv.ofTop _ rfl).symm
  by_cases' N_bot : N = ⊥
  · subst N_bot
    exact ⟨0, ⟨Basis.empty _⟩⟩
    
  obtain ⟨y, -, a, hay, M', -, N', N'_le_N, -, -, ay_ortho, h'⟩ := Submodule.basis_of_pid_aux ⊤ N b' N_bot le_top
  obtain ⟨n', ⟨bN'⟩⟩ := ih N' N'_le_N _ hay ay_ortho
  obtain ⟨bN, hbN⟩ := h' n' bN'
  exact ⟨n' + 1, ⟨bN⟩⟩

/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

See also the stronger version `submodule.smith_normal_form`.
-/
noncomputable def Submodule.basisOfPid {ι : Type _} [Fintype ι] (b : Basis ι R M) (N : Submodule R M) :
    Σn : ℕ, Basis (Finₓ n) R N :=
  ⟨_, (N.nonempty_basis_of_pid b).some_spec.some⟩

theorem Submodule.basis_of_pid_bot {ι : Type _} [Fintype ι] (b : Basis ι R M) :
    Submodule.basisOfPid b ⊥ = ⟨0, Basis.empty _⟩ := by
  obtain ⟨n, b'⟩ := Submodule.basisOfPid b ⊥
  let e : Finₓ n ≃ Finₓ 0 := b'.index_equiv (Basis.empty _ : Basis (Finₓ 0) R (⊥ : Submodule R M))
  obtain rfl : n = 0 := by
    simpa using fintype.card_eq.mpr ⟨e⟩
  exact Sigma.eq rfl (Basis.eq_of_apply_eq <| finZeroElim)

/-- A submodule inside a free `R`-submodule of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

See also the stronger version `submodule.smith_normal_form_of_le`.
-/
noncomputable def Submodule.basisOfPidOfLe {ι : Type _} [Fintype ι] {N O : Submodule R M} (hNO : N ≤ O)
    (b : Basis ι R O) : Σn : ℕ, Basis (Finₓ n) R N :=
  let ⟨n, bN'⟩ := Submodule.basisOfPid b (N.comap O.Subtype)
  ⟨n, bN'.map (Submodule.comapSubtypeEquivOfLe hNO)⟩

/-- A submodule inside the span of a linear independent family is a free `R`-module of finite rank,
if `R` is a principal ideal domain. -/
noncomputable def Submodule.basisOfPidOfLeSpan {ι : Type _} [Fintype ι] {b : ι → M} (hb : LinearIndependent R b)
    {N : Submodule R M} (le : N ≤ Submodule.span R (Set.Range b)) : Σn : ℕ, Basis (Finₓ n) R N :=
  Submodule.basisOfPidOfLe le (Basis.span hb)

variable {M}

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i «expr ∉ » I)
/-- A finite type torsion free module over a PID is free. -/
noncomputable def Module.freeOfFiniteTypeTorsionFree [Fintype ι] {s : ι → M} (hs : span R (Range s) = ⊤)
    [NoZeroSmulDivisors R M] : Σn : ℕ, Basis (Finₓ n) R M := by
  classical
  -- We define `N` as the submodule spanned by a maximal linear independent subfamily of `s`
  have := exists_maximal_independent R s
  let I : Set ι := this.some
  obtain
    ⟨indepI : LinearIndependent R (s ∘ coe : I → M), hI :
      ∀ (i) (_ : i ∉ I), ∃ a : R, a ≠ 0 ∧ a • s i ∈ span R (s '' I)⟩ :=
    this.some_spec
  let N := span R (range <| (s ∘ coe : I → M))
  -- same as `span R (s '' I)` but more convenient
  let sI : I → N := fun i => ⟨s i.1, subset_span (mem_range_self i)⟩
  -- `s` restricted to `I`
  let sI_basis : Basis I R N
  -- `s` restricted to `I` is a basis of `N`
  exact Basis.span indepI
  -- Our first goal is to build `A ≠ 0` such that `A • M ⊆ N`
  have exists_a : ∀ i : ι, ∃ a : R, a ≠ 0 ∧ a • s i ∈ N := by
    intro i
    by_cases' hi : i ∈ I
    · use 1, zero_ne_one.symm
      rw [one_smul]
      exact subset_span (mem_range_self (⟨i, hi⟩ : I))
      
    · simpa [← image_eq_range s I] using hI i hi
      
  choose a ha ha' using exists_a
  let A := ∏ i, a i
  have hA : A ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    simpa using ha
  -- `M ≃ A • M` because `M` is torsion free and `A ≠ 0`
  let φ : M →ₗ[R] M := LinearMap.lsmul R M A
  have : φ.ker = ⊥ := LinearMap.ker_lsmul hA
  let ψ : M ≃ₗ[R] φ.range := LinearEquiv.ofInjective φ (linear_map.ker_eq_bot.mp this)
  have : φ.range ≤ N := by
    -- as announced, `A • M ⊆ N`
    suffices ∀ i, φ (s i) ∈ N by
      rw [LinearMap.range_eq_map, ← hs, φ.map_span_le]
      rintro _ ⟨i, rfl⟩
      apply this
    intro i
    calc (∏ j, a j) • s i = (∏ j in {i}ᶜ, a j) • a i • s i := by
        rw [Fintype.prod_eq_prod_compl_mul i, mul_smul]_ ∈ N := N.smul_mem _ (ha' i)
  -- Since a submodule of a free `R`-module is free, we get that `A • M` is free
  obtain ⟨n, b : Basis (Finₓ n) R φ.range⟩ := Submodule.basisOfPidOfLe this sI_basis
  -- hence `M` is free.
  exact ⟨n, b.map ψ.symm⟩

/-- A finite type torsion free module over a PID is free. -/
noncomputable def Module.freeOfFiniteTypeTorsionFree' [Module.Finite R M] [NoZeroSmulDivisors R M] :
    Σn : ℕ, Basis (Finₓ n) R M :=
  Module.freeOfFiniteTypeTorsionFree Module.Finite.exists_fin.some_spec.some_spec

section SmithNormal

/-- A Smith normal form basis for a submodule `N` of a module `M` consists of
bases for `M` and `N` such that the inclusion map `N → M` can be written as a
(rectangular) matrix with `a` along the diagonal: in Smith normal form. -/
@[nolint has_inhabited_instance]
structure Basis.SmithNormalForm (N : Submodule R M) (ι : Type _) (n : ℕ) where
  bM : Basis ι R M
  bN : Basis (Finₓ n) R N
  f : Finₓ n ↪ ι
  a : Finₓ n → R
  snf : ∀ i, (bN i : M) = a i • bM (f i)

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

See `submodule.smith_normal_form_of_le` for a version of this theorem that returns
a `basis.smith_normal_form`.

This is a strengthening of `submodule.basis_of_pid_of_le`.
-/
theorem Submodule.exists_smith_normal_form_of_le [Fintype ι] (b : Basis ι R M) (N O : Submodule R M) (N_le_O : N ≤ O) :
    ∃ (n o : ℕ)(hno : n ≤ o)(bO : Basis (Finₓ o) R O)(bN : Basis (Finₓ n) R N)(a : Finₓ n → R),
      ∀ i, (bN i : M) = a i • bO (Finₓ.castLe hno i) :=
  by
  revert N
  refine' induction_on_rank b _ _ O
  intro M ih N N_le_M
  obtain ⟨m, b'M⟩ := M.basis_of_pid b
  by_cases' N_bot : N = ⊥
  · subst N_bot
    exact ⟨0, m, Nat.zero_leₓ _, b'M, Basis.empty _, finZeroElim, finZeroElim⟩
    
  obtain ⟨y, hy, a, hay, M', M'_le_M, N', N'_le_N, N'_le_M', y_ortho, ay_ortho, h⟩ :=
    Submodule.basis_of_pid_aux M N b'M N_bot N_le_M
  obtain ⟨n', m', hn'm', bM', bN', as', has'⟩ := ih M' M'_le_M y hy y_ortho N' N'_le_M'
  obtain ⟨bN, h'⟩ := h n' bN'
  obtain ⟨hmn, bM, h''⟩ := h' m' hn'm' bM'
  obtain ⟨as, has⟩ := h'' as' has'
  exact ⟨_, _, hmn, bM, bN, as, has⟩

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

See `submodule.exists_smith_normal_form_of_le` for a version of this theorem that doesn't
need to map `N` into a submodule of `O`.

This is a strengthening of `submodule.basis_of_pid_of_le`.
-/
noncomputable def Submodule.smithNormalFormOfLe [Fintype ι] (b : Basis ι R M) (N O : Submodule R M) (N_le_O : N ≤ O) :
    Σo n : ℕ, Basis.SmithNormalForm (N.comap O.Subtype) (Finₓ o) n := by
  choose n o hno bO bN a snf using N.exists_smith_normal_form_of_le b O N_le_O
  refine' ⟨o, n, bO, bN.map (comap_subtype_equiv_of_le N_le_O).symm, (Finₓ.castLe hno).toEmbedding, a, fun i => _⟩
  ext
  simp only [← snf, ← Basis.map_apply, ← Submodule.comap_subtype_equiv_of_le_symm_apply_coe_coe, ←
    Submodule.coe_smul_of_tower, ← RelEmbedding.coe_fn_to_embedding]

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

This is a strengthening of `submodule.basis_of_pid`.

See also `ideal.smith_normal_form`, which moreover proves that the dimension of
an ideal is the same as the dimension of the whole ring.
-/
noncomputable def Submodule.smithNormalForm [Fintype ι] (b : Basis ι R M) (N : Submodule R M) :
    Σn : ℕ, Basis.SmithNormalForm N ι n :=
  let ⟨m, n, bM, bN, f, a, snf⟩ := N.smithNormalFormOfLe b ⊤ le_top
  let bM' := bM.map (LinearEquiv.ofTop _ rfl)
  let e := bM'.indexEquiv b
  ⟨n, bM'.reindex e, bN.map (comapSubtypeEquivOfLe le_top), f.trans e.toEmbedding, a, fun i => by
    simp only [← snf, ← Basis.map_apply, ← LinearEquiv.of_top_apply, ← Submodule.coe_smul_of_tower, ←
      Submodule.comap_subtype_equiv_of_le_apply_coe, ← coe_coe, ← Basis.reindex_apply, ← Equivₓ.to_embedding_apply, ←
      Function.Embedding.trans_apply, ← Equivₓ.symm_apply_apply]⟩

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.

See `ideal.exists_smith_normal_form` for a version of this theorem that doesn't
need to map `I` into a submodule of `R`.

This is a strengthening of `submodule.basis_of_pid`.
-/
noncomputable def Ideal.smithNormalForm [Fintype ι] {S : Type _} [CommRingₓ S] [IsDomain S] [Algebra R S]
    (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) : Basis.SmithNormalForm (I.restrictScalars R) ι (Fintype.card ι) :=
  let ⟨n, bS, bI, f, a, snf⟩ := (I.restrictScalars R).SmithNormalForm b
  have eq := Ideal.rank_eq bS hI (bI.map ((restrictScalarsEquiv R S S I).restrictScalars _))
  let e : Finₓ n ≃ Finₓ (Fintype.card ι) :=
    Fintype.equivOfCardEq
      (by
        rw [Eq, Fintype.card_fin])
  ⟨bS, bI.reindex e, e.symm.toEmbedding.trans f, a ∘ e.symm, fun i => by
    simp only [← snf, ← Basis.coe_reindex, ← Function.Embedding.trans_apply, ← Equivₓ.to_embedding_apply]⟩

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.

See also `ideal.smith_normal_form` for a version of this theorem that returns
a `basis.smith_normal_form`.
-/
theorem Ideal.exists_smith_normal_form [Fintype ι] {S : Type _} [CommRingₓ S] [IsDomain S] [Algebra R S]
    (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) :
    ∃ (b' : Basis ι R S)(a : ι → R)(ab' : Basis ι R I), ∀ i, (ab' i : S) = a i • b' i :=
  let ⟨bS, bI, f, a, snf⟩ := I.SmithNormalForm b hI
  let e : Finₓ (Fintype.card ι) ≃ ι :=
    Equivₓ.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨f.Injective, Fintype.card_fin _⟩)
  have fe : ∀ i, f (e.symm i) = i := e.apply_symm_apply
  ⟨bS, a ∘ e.symm, (bI.reindex e).map ((restrictScalarsEquiv _ _ _ _).restrictScalars R), fun i => by
    simp only [← snf, ← fe, ← Basis.map_apply, ← LinearEquiv.restrict_scalars_apply, ←
      Submodule.restrict_scalars_equiv_apply, ← Basis.coe_reindex]⟩

end SmithNormal

end PrincipalIdealDomain

/-- A set of linearly independent vectors in a module `M` over a semiring `S` is also linearly
independent over a subring `R` of `K`. -/
theorem LinearIndependent.restrict_scalars_algebras {R S M ι : Type _} [CommSemiringₓ R] [Semiringₓ S]
    [AddCommMonoidₓ M] [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]
    (hinj : Function.Injective (algebraMap R S)) {v : ι → M} (li : LinearIndependent S v) : LinearIndependent R v :=
  LinearIndependent.restrict_scalars
    (by
      rwa [Algebra.algebra_map_eq_smul_one'] at hinj)
    li


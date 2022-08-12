/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Algebra.Lie.Abelian
import Mathbin.Algebra.Lie.IdealOperations
import Mathbin.Algebra.Lie.Quotient

/-!
# The centralizer of a Lie submodule and the normalizer of a Lie subalgebra.

Given a Lie module `M` over a Lie subalgebra `L`, the centralizer of a Lie submodule `N ⊆ M` is
the Lie submodule with underlying set `{ m | ∀ (x : L), ⁅x, m⁆ ∈ N }`.

The lattice of Lie submodules thus has two natural operations, the centralizer: `N ↦ N.centralizer`
and the ideal operation: `N ↦ ⁅⊤, N⁆`; these are adjoint, i.e., they form a Galois connection. This
adjointness is the reason that we may define nilpotency in terms of either the upper or lower
central series.

Given a Lie subalgebra `H ⊆ L`, we may regard `H` as a Lie submodule of `L` over `H`, and thus
consider the centralizer. This turns out to be a Lie subalgebra and is known as the normalizer.

## Main definitions

  * `lie_submodule.centralizer`
  * `lie_subalgebra.normalizer`
  * `lie_submodule.gc_top_lie_centralizer`

## Tags

lie algebra, centralizer, normalizer
-/


variable {R L M M' : Type _}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroupₓ M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroupₓ M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

namespace LieSubmodule

variable (N : LieSubmodule R L M) {N₁ N₂ : LieSubmodule R L M}

/-- The centralizer of a Lie submodule. -/
def centralizer : LieSubmodule R L M where
  Carrier := { m | ∀ x : L, ⁅x,m⁆ ∈ N }
  add_mem' := fun m₁ m₂ hm₁ hm₂ x => by
    rw [lie_add]
    exact N.add_mem' (hm₁ x) (hm₂ x)
  zero_mem' := fun x => by
    simp
  smul_mem' := fun t m hm x => by
    rw [lie_smul]
    exact N.smul_mem' t (hm x)
  lie_mem := fun x m hm y => by
    rw [leibniz_lie]
    exact N.add_mem' (hm ⁅y,x⁆) (N.lie_mem (hm y))

@[simp]
theorem mem_centralizer (m : M) : m ∈ N.Centralizer ↔ ∀ x : L, ⁅x,m⁆ ∈ N :=
  Iff.rfl

theorem le_centralizer : N ≤ N.Centralizer := by
  intro m hm
  rw [mem_centralizer]
  exact fun x => N.lie_mem hm

theorem centralizer_inf : (N₁⊓N₂).Centralizer = N₁.Centralizer⊓N₂.Centralizer := by
  ext
  simp [forall_and_distrib]

@[mono]
theorem monotone_centalizer : Monotone (centralizer : LieSubmodule R L M → LieSubmodule R L M) := by
  intro N₁ N₂ h m hm
  rw [mem_centralizer] at hm⊢
  exact fun x => h (hm x)

@[simp]
theorem comap_centralizer (f : M' →ₗ⁅R,L⁆ M) : N.Centralizer.comap f = (N.comap f).Centralizer := by
  ext
  simp

theorem top_lie_le_iff_le_centralizer (N' : LieSubmodule R L M) : ⁅(⊤ : LieIdeal R L),N⁆ ≤ N' ↔ N ≤ N'.Centralizer := by
  rw [lie_le_iff]
  tauto

theorem gc_top_lie_centralizer : GaloisConnection (fun N : LieSubmodule R L M => ⁅(⊤ : LieIdeal R L),N⁆) centralizer :=
  top_lie_le_iff_le_centralizer

variable (R L M)

theorem centralizer_bot_eq_max_triv_submodule :
    (⊥ : LieSubmodule R L M).Centralizer = LieModule.maxTrivSubmodule R L M :=
  rfl

end LieSubmodule

namespace LieSubalgebra

variable (H : LieSubalgebra R L)

/-- Regarding a Lie subalgebra `H ⊆ L` as a module over itself, its centralizer is in fact a Lie
subalgebra. This is called the normalizer of the Lie subalgebra. -/
def normalizer : LieSubalgebra R L :=
  { H.toLieSubmodule.Centralizer with
    lie_mem' := fun y z hy hz x => by
      rw [coe_bracket_of_module, mem_to_lie_submodule, leibniz_lie, ← lie_skew y, ← sub_eq_add_neg]
      exact H.sub_mem (hz ⟨_, hy x⟩) (hy ⟨_, hz x⟩) }

theorem mem_normalizer_iff' (x : L) : x ∈ H.normalizer ↔ ∀ y : L, y ∈ H → ⁅y,x⁆ ∈ H := by
  rw [Subtype.forall']
  rfl

theorem mem_normalizer_iff (x : L) : x ∈ H.normalizer ↔ ∀ y : L, y ∈ H → ⁅x,y⁆ ∈ H := by
  rw [mem_normalizer_iff']
  refine' forall₂_congrₓ fun y hy => _
  rw [← lie_skew, neg_mem_iff]

theorem le_normalizer : H ≤ H.normalizer :=
  H.toLieSubmodule.le_centralizer

theorem coe_centralizer_eq_normalizer : (H.toLieSubmodule.Centralizer : Submodule R L) = H.normalizer :=
  rfl

variable {H}

theorem lie_mem_sup_of_mem_normalizer {x y z : L} (hx : x ∈ H.normalizer) (hy : y ∈ (R∙x)⊔↑H) (hz : z ∈ (R∙x)⊔↑H) :
    ⁅y,z⁆ ∈ (R∙x)⊔↑H := by
  rw [Submodule.mem_sup] at hy hz
  obtain ⟨u₁, hu₁, v, hv : v ∈ H, rfl⟩ := hy
  obtain ⟨u₂, hu₂, w, hw : w ∈ H, rfl⟩ := hz
  obtain ⟨t, rfl⟩ := submodule.mem_span_singleton.mp hu₁
  obtain ⟨s, rfl⟩ := submodule.mem_span_singleton.mp hu₂
  apply Submodule.mem_sup_right
  simp only [← LieSubalgebra.mem_coe_submodule, ← smul_lie, ← add_lie, ← zero_addₓ, ← lie_add, ← smul_zero, ← lie_smul,
    ← lie_self]
  refine' H.add_mem (H.smul_mem s _) (H.add_mem (H.smul_mem t _) (H.lie_mem hv hw))
  exacts[(H.mem_normalizer_iff' x).mp hx v hv, (H.mem_normalizer_iff x).mp hx w hw]

/-- A Lie subalgebra is an ideal of its normalizer. -/
theorem ideal_in_normalizer {x y : L} (hx : x ∈ H.normalizer) (hy : y ∈ H) : ⁅x,y⁆ ∈ H := by
  rw [← lie_skew, neg_mem_iff]
  exact hx ⟨y, hy⟩

/-- A Lie subalgebra `H` is an ideal of any Lie subalgebra `K` containing `H` and contained in the
normalizer of `H`. -/
theorem exists_nested_lie_ideal_of_le_normalizer {K : LieSubalgebra R L} (h₁ : H ≤ K) (h₂ : K ≤ H.normalizer) :
    ∃ I : LieIdeal R K, (I : LieSubalgebra R K) = ofLe h₁ := by
  rw [exists_nested_lie_ideal_coe_eq_iff]
  exact fun x y hx hy => ideal_in_normalizer (h₂ hx) hy

variable (H)

theorem normalizer_eq_self_iff : H.normalizer = H ↔ (LieModule.maxTrivSubmodule R H <| L ⧸ H.toLieSubmodule) = ⊥ := by
  rw [LieSubmodule.eq_bot_iff]
  refine' ⟨fun h => _, fun h => le_antisymmₓ (fun x hx => _) H.le_normalizer⟩
  · rintro ⟨x⟩ hx
    suffices x ∈ H by
      simpa
    rw [← h, H.mem_normalizer_iff']
    intro y hy
    replace hx : ⁅_,LieSubmodule.Quotient.mk' _ x⁆ = 0 := hx ⟨y, hy⟩
    rwa [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero] at hx
    
  · let y := LieSubmodule.Quotient.mk' H.to_lie_submodule x
    have hy : y ∈ LieModule.maxTrivSubmodule R H (L ⧸ H.to_lie_submodule) := by
      rintro ⟨z, hz⟩
      rw [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero, coe_bracket_of_module, Submodule.coe_mk,
        mem_to_lie_submodule]
      exact (H.mem_normalizer_iff' x).mp hx z hz
    simpa using h y hy
    

end LieSubalgebra


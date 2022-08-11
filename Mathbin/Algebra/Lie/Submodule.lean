/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Algebra.Lie.Subalgebra
import Mathbin.RingTheory.Noetherian

/-!
# Lie submodules of a Lie algebra

In this file we define Lie submodules and Lie ideals, we construct the lattice structure on Lie
submodules and we use it to define various important operations, notably the Lie span of a subset
of a Lie module.

## Main definitions

  * `lie_submodule`
  * `lie_submodule.well_founded_of_noetherian`
  * `lie_submodule.lie_span`
  * `lie_submodule.map`
  * `lie_submodule.comap`
  * `lie_ideal`
  * `lie_ideal.map`
  * `lie_ideal.comap`

## Tags

lie algebra, lie submodule, lie ideal, lattice structure
-/


universe u v w w₁ w₂

section LieSubmodule

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] [AddCommGroupₓ M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

/-- A Lie submodule of a Lie module is a submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie module. -/
structure LieSubmodule extends Submodule R M where
  lie_mem : ∀ {x : L} {m : M}, m ∈ carrier → ⁅x,m⁆ ∈ carrier

attribute [nolint doc_blame] LieSubmodule.toSubmodule

namespace LieSubmodule

variable {R L M} (N N' : LieSubmodule R L M)

instance : SetLike (LieSubmodule R L M) M where
  coe := Carrier
  coe_injective' := fun N O h => by
    cases N <;> cases O <;> congr

instance : AddSubgroupClass (LieSubmodule R L M) M where
  add_mem := fun N => N.add_mem'
  zero_mem := fun N => N.zero_mem'
  neg_mem := fun N x hx => show -x ∈ N.toSubmodule from neg_mem hx

/-- The zero module is a Lie submodule of any Lie module. -/
instance : Zero (LieSubmodule R L M) :=
  ⟨{ (0 : Submodule R M) with
      lie_mem := fun x m h => by
        rw [(Submodule.mem_bot R).1 h]
        apply lie_zero }⟩

instance : Inhabited (LieSubmodule R L M) :=
  ⟨0⟩

instance coeSubmodule : Coe (LieSubmodule R L M) (Submodule R M) :=
  ⟨toSubmodule⟩

@[simp]
theorem to_submodule_eq_coe : N.toSubmodule = N :=
  rfl

@[norm_cast]
theorem coe_to_submodule : ((N : Submodule R M) : Set M) = N :=
  rfl

@[simp]
theorem mem_carrier {x : M} : x ∈ N.Carrier ↔ x ∈ (N : Set M) :=
  Iff.rfl

@[simp]
theorem mem_mk_iff (S : Set M) (h₁ h₂ h₃ h₄) {x : M} : x ∈ (⟨S, h₁, h₂, h₃, h₄⟩ : LieSubmodule R L M) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem mem_coe_submodule {x : M} : x ∈ (N : Submodule R M) ↔ x ∈ N :=
  Iff.rfl

theorem mem_coe {x : M} : x ∈ (N : Set M) ↔ x ∈ N :=
  Iff.rfl

@[simp]
protected theorem zero_mem : (0 : M) ∈ N :=
  zero_mem N

@[simp]
theorem mk_eq_zero {x} (h : x ∈ N) : (⟨x, h⟩ : N) = 0 ↔ x = 0 :=
  Subtype.ext_iff_val

@[simp]
theorem coe_to_set_mk (S : Set M) (h₁ h₂ h₃ h₄) : ((⟨S, h₁, h₂, h₃, h₄⟩ : LieSubmodule R L M) : Set M) = S :=
  rfl

@[simp]
theorem coe_to_submodule_mk (p : Submodule R M) (h) :
    (({ p with lie_mem := h } : LieSubmodule R L M) : Submodule R M) = p := by
  cases p
  rfl

theorem coe_submodule_injective : Function.Injective (toSubmodule : LieSubmodule R L M → Submodule R M) := fun x y h =>
  by
  cases x
  cases y
  congr
  injection h

@[ext]
theorem ext (h : ∀ m, m ∈ N ↔ m ∈ N') : N = N' :=
  SetLike.ext h

@[simp]
theorem coe_to_submodule_eq_iff : (N : Submodule R M) = (N' : Submodule R M) ↔ N = N' :=
  coe_submodule_injective.eq_iff

/-- Copy of a lie_submodule with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (s : Set M) (hs : s = ↑N) : LieSubmodule R L M where
  Carrier := s
  zero_mem' := hs.symm ▸ N.zero_mem'
  add_mem' := hs.symm ▸ N.add_mem'
  smul_mem' := hs.symm ▸ N.smul_mem'
  lie_mem := hs.symm ▸ N.lie_mem

@[simp]
theorem coe_copy (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S) : (S.copy s hs : Set M) = s :=
  rfl

theorem copy_eq (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S) : S.copy s hs = S :=
  coe_submodule_injective (SetLike.coe_injective hs)

instance : LieRingModule L N where
  bracket := fun (x : L) (m : N) => ⟨⁅x,m.val⁆, N.lie_mem m.property⟩
  add_lie := by
    intro x y m
    apply SetCoe.ext
    apply add_lie
  lie_add := by
    intro x m n
    apply SetCoe.ext
    apply lie_add
  leibniz_lie := by
    intro x y m
    apply SetCoe.ext
    apply leibniz_lie

instance module' {S : Type _} [Semiringₓ S] [HasSmul S R] [Module S M] [IsScalarTower S R M] : Module S N :=
  N.toSubmodule.module'

instance : Module R N :=
  N.toSubmodule.Module

instance {S : Type _} [Semiringₓ S] [HasSmul S R] [HasSmul Sᵐᵒᵖ R] [Module S M] [Module Sᵐᵒᵖ M] [IsScalarTower S R M]
    [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] : IsCentralScalar S N :=
  N.toSubmodule.IsCentralScalar

instance : LieModule R L N where
  lie_smul := by
    intro t x y
    apply SetCoe.ext
    apply lie_smul
  smul_lie := by
    intro t x y
    apply SetCoe.ext
    apply smul_lie

@[simp, norm_cast]
theorem coe_zero : ((0 : N) : M) = (0 : M) :=
  rfl

@[simp, norm_cast]
theorem coe_add (m m' : N) : (↑(m + m') : M) = (m : M) + (m' : M) :=
  rfl

@[simp, norm_cast]
theorem coe_neg (m : N) : (↑(-m) : M) = -(m : M) :=
  rfl

@[simp, norm_cast]
theorem coe_sub (m m' : N) : (↑(m - m') : M) = (m : M) - (m' : M) :=
  rfl

@[simp, norm_cast]
theorem coe_smul (t : R) (m : N) : (↑(t • m) : M) = t • (m : M) :=
  rfl

@[simp, norm_cast]
theorem coe_bracket (x : L) (m : N) : (↑⁅x,m⁆ : M) = ⁅x,↑m⁆ :=
  rfl

end LieSubmodule

section LieIdeal

variable (L)

/-- An ideal of a Lie algebra is a Lie submodule of the Lie algebra as a Lie module over itself. -/
abbrev LieIdeal :=
  LieSubmodule R L L

theorem lie_mem_right (I : LieIdeal R L) (x y : L) (h : y ∈ I) : ⁅x,y⁆ ∈ I :=
  I.lie_mem h

theorem lie_mem_left (I : LieIdeal R L) (x y : L) (h : x ∈ I) : ⁅x,y⁆ ∈ I := by
  rw [← lie_skew, ← neg_lie]
  apply lie_mem_right
  assumption

/-- An ideal of a Lie algebra is a Lie subalgebra. -/
def lieIdealSubalgebra (I : LieIdeal R L) : LieSubalgebra R L :=
  { I.toSubmodule with
    lie_mem' := by
      intro x y hx hy
      apply lie_mem_right
      exact hy }

instance : Coe (LieIdeal R L) (LieSubalgebra R L) :=
  ⟨fun I => lieIdealSubalgebra R L I⟩

@[norm_cast]
theorem LieIdeal.coe_to_subalgebra (I : LieIdeal R L) : ((I : LieSubalgebra R L) : Set L) = I :=
  rfl

@[norm_cast]
theorem LieIdeal.coe_to_lie_subalgebra_to_submodule (I : LieIdeal R L) :
    ((I : LieSubalgebra R L) : Submodule R L) = I :=
  rfl

end LieIdeal

variable {R M}

theorem Submodule.exists_lie_submodule_coe_eq_iff (p : Submodule R M) :
    (∃ N : LieSubmodule R L M, ↑N = p) ↔ ∀ (x : L) (m : M), m ∈ p → ⁅x,m⁆ ∈ p := by
  constructor
  · rintro ⟨N, rfl⟩
    exact N.lie_mem
    
  · intro h
    use { p with lie_mem := h }
    exact LieSubmodule.coe_to_submodule_mk p _
    

namespace LieSubalgebra

variable {L} (K : LieSubalgebra R L)

/-- Given a Lie subalgebra `K ⊆ L`, if we view `L` as a `K`-module by restriction, it contains
a distinguished Lie submodule for the action of `K`, namely `K` itself. -/
def toLieSubmodule : LieSubmodule R K L :=
  { (K : Submodule R L) with lie_mem := fun x y hy => K.lie_mem x.property hy }

@[simp]
theorem coe_to_lie_submodule : (K.toLieSubmodule : Submodule R L) = K := by
  rcases K with ⟨⟨⟩⟩
  rfl

variable {K}

@[simp]
theorem mem_to_lie_submodule (x : L) : x ∈ K.toLieSubmodule ↔ x ∈ K :=
  Iff.rfl

theorem exists_lie_ideal_coe_eq_iff : (∃ I : LieIdeal R L, ↑I = K) ↔ ∀ x y : L, y ∈ K → ⁅x,y⁆ ∈ K := by
  simp only [coe_to_submodule_eq_iff, ← LieIdeal.coe_to_lie_subalgebra_to_submodule, ←
    Submodule.exists_lie_submodule_coe_eq_iff L]
  exact Iff.rfl

theorem exists_nested_lie_ideal_coe_eq_iff {K' : LieSubalgebra R L} (h : K ≤ K') :
    (∃ I : LieIdeal R K', ↑I = ofLe h) ↔ ∀ x y : L, x ∈ K' → y ∈ K → ⁅x,y⁆ ∈ K := by
  simp only [← exists_lie_ideal_coe_eq_iff, ← coe_bracket, ← mem_of_le]
  constructor
  · intro h' x y hx hy
    exact h' ⟨x, hx⟩ ⟨y, h hy⟩ hy
    
  · rintro h' ⟨x, hx⟩ ⟨y, hy⟩ hy'
    exact h' x y hx hy'
    

end LieSubalgebra

end LieSubmodule

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] [AddCommGroupₓ M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

variable (N N' : LieSubmodule R L M) (I J : LieIdeal R L)

section LatticeStructure

open Set

theorem coe_injective : Function.Injective (coe : LieSubmodule R L M → Set M) :=
  SetLike.coe_injective

@[simp, norm_cast]
theorem coe_submodule_le_coe_submodule : (N : Submodule R M) ≤ N' ↔ N ≤ N' :=
  Iff.rfl

instance : HasBot (LieSubmodule R L M) :=
  ⟨0⟩

@[simp]
theorem bot_coe : ((⊥ : LieSubmodule R L M) : Set M) = {0} :=
  rfl

@[simp]
theorem bot_coe_submodule : ((⊥ : LieSubmodule R L M) : Submodule R M) = ⊥ :=
  rfl

@[simp]
theorem mem_bot (x : M) : x ∈ (⊥ : LieSubmodule R L M) ↔ x = 0 :=
  mem_singleton_iff

instance : HasTop (LieSubmodule R L M) :=
  ⟨{ (⊤ : Submodule R M) with lie_mem := fun x m h => mem_univ ⁅x,m⁆ }⟩

@[simp]
theorem top_coe : ((⊤ : LieSubmodule R L M) : Set M) = univ :=
  rfl

@[simp]
theorem top_coe_submodule : ((⊤ : LieSubmodule R L M) : Submodule R M) = ⊤ :=
  rfl

@[simp]
theorem mem_top (x : M) : x ∈ (⊤ : LieSubmodule R L M) :=
  mem_univ x

instance : HasInf (LieSubmodule R L M) :=
  ⟨fun N N' => { (N⊓N' : Submodule R M) with lie_mem := fun x m h => mem_inter (N.lie_mem h.1) (N'.lie_mem h.2) }⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:1122:4: unsupported set replacement {((s : submodule R M)) | s «expr ∈ » S}
instance : HasInfₓ (LieSubmodule R L M) :=
  ⟨fun S =>
    { inf
        "./././Mathport/Syntax/Translate/Basic.lean:1122:4: unsupported set replacement {((s : submodule R M)) | s «expr ∈ » S}" with
      lie_mem := fun x m h => by
        simp only [← Submodule.mem_carrier, ← mem_Inter, ← Submodule.Inf_coe, ← mem_set_of_eq, ←
          forall_apply_eq_imp_iff₂, ← exists_imp_distrib] at *
        intro N hN
        apply N.lie_mem (h N hN) }⟩

@[simp]
theorem inf_coe : (↑(N⊓N') : Set M) = N ∩ N' :=
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:1122:4: unsupported set replacement {((s : submodule R M)) | s «expr ∈ » S}
@[simp]
theorem Inf_coe_to_submodule (S : Set (LieSubmodule R L M)) :
    (↑(inf S) : Submodule R M) =
      inf
        "./././Mathport/Syntax/Translate/Basic.lean:1122:4: unsupported set replacement {((s : submodule R M)) | s «expr ∈ » S}" :=
  rfl

@[simp]
theorem Inf_coe (S : Set (LieSubmodule R L M)) : (↑(inf S) : Set M) = ⋂ s ∈ S, (s : Set M) := by
  rw [← LieSubmodule.coe_to_submodule, Inf_coe_to_submodule, Submodule.Inf_coe]
  ext m
  simpa only [← mem_Inter, ← mem_set_of_eq, ← forall_apply_eq_imp_iff₂, ← exists_imp_distrib]

theorem Inf_glb (S : Set (LieSubmodule R L M)) : IsGlb S (inf S) := by
  have h : ∀ N N' : LieSubmodule R L M, (N : Set M) ≤ N' ↔ N ≤ N' := by
    intros
    rfl
  apply IsGlb.of_image h
  simp only [← Inf_coe]
  exact is_glb_binfi

/-- The set of Lie submodules of a Lie module form a complete lattice.

We provide explicit values for the fields `bot`, `top`, `inf` to get more convenient definitions
than we would otherwise obtain from `complete_lattice_of_Inf`.  -/
instance : CompleteLattice (LieSubmodule R L M) :=
  { SetLike.partialOrder, completeLatticeOfInf _ Inf_glb with le := (· ≤ ·), lt := (· < ·), bot := ⊥,
    bot_le := fun N _ h => by
      rw [mem_bot] at h
      rw [h]
      exact N.zero_mem',
    top := ⊤, le_top := fun _ _ _ => trivialₓ, inf := (·⊓·), le_inf := fun N₁ N₂ N₃ h₁₂ h₁₃ m hm => ⟨h₁₂ hm, h₁₃ hm⟩,
    inf_le_left := fun _ _ _ => And.left, inf_le_right := fun _ _ _ => And.right }

instance : AddCommMonoidₓ (LieSubmodule R L M) where
  add := (·⊔·)
  add_assoc := fun _ _ _ => sup_assoc
  zero := ⊥
  zero_add := fun _ => bot_sup_eq
  add_zero := fun _ => sup_bot_eq
  add_comm := fun _ _ => sup_comm

@[simp]
theorem add_eq_sup : N + N' = N⊔N' :=
  rfl

@[norm_cast, simp]
theorem sup_coe_to_submodule : (↑(N⊔N') : Submodule R M) = (N : Submodule R M)⊔(N' : Submodule R M) := by
  have aux : ∀ (x : L) (m), m ∈ (N⊔N' : Submodule R M) → ⁅x,m⁆ ∈ (N⊔N' : Submodule R M) := by
    simp only [← Submodule.mem_sup]
    rintro x m ⟨y, hy, z, hz, rfl⟩
    refine' ⟨⁅x,y⁆, N.lie_mem hy, ⁅x,z⁆, N'.lie_mem hz, (lie_add _ _ _).symm⟩
  refine' le_antisymmₓ (Inf_le ⟨{ (N⊔N' : Submodule R M) with lie_mem := aux }, _⟩) _
  · simp only [← exists_prop, ← and_trueₓ, ← mem_set_of_eq, ← eq_self_iff_true, ← coe_to_submodule_mk,
      coe_submodule_le_coe_submodule, ← and_selfₓ, ← le_sup_left, ← le_sup_right]
    
  · simp
    

@[norm_cast, simp]
theorem inf_coe_to_submodule : (↑(N⊓N') : Submodule R M) = (N : Submodule R M)⊓(N' : Submodule R M) :=
  rfl

@[simp]
theorem mem_inf (x : M) : x ∈ N⊓N' ↔ x ∈ N ∧ x ∈ N' := by
  rw [← mem_coe_submodule, ← mem_coe_submodule, ← mem_coe_submodule, inf_coe_to_submodule, Submodule.mem_inf]

theorem mem_sup (x : M) : x ∈ N⊔N' ↔ ∃ y ∈ N, ∃ z ∈ N', y + z = x := by
  rw [← mem_coe_submodule, sup_coe_to_submodule, Submodule.mem_sup]
  exact Iff.rfl

theorem eq_bot_iff : N = ⊥ ↔ ∀ m : M, m ∈ N → m = 0 := by
  rw [eq_bot_iff]
  exact Iff.rfl

-- TODO[gh-6025]: make this an instance once safe to do so
theorem subsingleton_of_bot : Subsingleton (LieSubmodule R L ↥(⊥ : LieSubmodule R L M)) := by
  apply subsingleton_of_bot_eq_top
  ext ⟨x, hx⟩
  change x ∈ ⊥ at hx
  rw [Submodule.mem_bot] at hx
  subst hx
  simp only [← true_iffₓ, ← eq_self_iff_true, ← Submodule.mk_eq_zero, ← LieSubmodule.mem_bot]

instance :
    IsModularLattice (LieSubmodule R L M) where sup_inf_le_assoc_of_le := fun N₁ N₂ N₃ => by
    simp only [coe_submodule_le_coe_submodule, ← sup_coe_to_submodule, ← inf_coe_to_submodule]
    exact IsModularLattice.sup_inf_le_assoc_of_le ↑N₂

variable (R L M)

theorem well_founded_of_noetherian [IsNoetherian R M] :
    WellFounded ((· > ·) : LieSubmodule R L M → LieSubmodule R L M → Prop) :=
  let f :
    ((· > ·) : LieSubmodule R L M → LieSubmodule R L M → Prop) →r ((· > ·) : Submodule R M → Submodule R M → Prop) :=
    { toFun := coe, map_rel' := fun N N' h => h }
  RelHomClass.well_founded f (is_noetherian_iff_well_founded.mp inferInstance)

@[simp]
theorem subsingleton_iff : Subsingleton (LieSubmodule R L M) ↔ Subsingleton M :=
  have h : Subsingleton (LieSubmodule R L M) ↔ Subsingleton (Submodule R M) := by
    rw [← subsingleton_iff_bot_eq_top, ← subsingleton_iff_bot_eq_top, ← coe_to_submodule_eq_iff, top_coe_submodule,
      bot_coe_submodule]
  h.trans <| Submodule.subsingleton_iff R

@[simp]
theorem nontrivial_iff : Nontrivial (LieSubmodule R L M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R L M).trans not_nontrivial_iff_subsingleton.symm)

instance [Nontrivial M] : Nontrivial (LieSubmodule R L M) :=
  (nontrivial_iff R L M).mpr ‹_›

theorem nontrivial_iff_ne_bot {N : LieSubmodule R L M} : Nontrivial N ↔ N ≠ ⊥ := by
  constructor <;> contrapose!
  · rintro rfl ⟨⟨m₁, h₁ : m₁ ∈ (⊥ : LieSubmodule R L M)⟩, ⟨m₂, h₂ : m₂ ∈ (⊥ : LieSubmodule R L M)⟩, h₁₂⟩
    simpa [← (LieSubmodule.mem_bot _).mp h₁, ← (LieSubmodule.mem_bot _).mp h₂] using h₁₂
    
  · rw [not_nontrivial_iff_subsingleton, LieSubmodule.eq_bot_iff]
    rintro ⟨h⟩ m hm
    simpa using h ⟨m, hm⟩ ⟨_, N.zero_mem⟩
    

variable {R L M}

section InclusionMaps

/-- The inclusion of a Lie submodule into its ambient space is a morphism of Lie modules. -/
def incl : N →ₗ⁅R,L⁆ M :=
  { Submodule.subtype (N : Submodule R M) with map_lie' := fun x m => rfl }

@[simp]
theorem incl_coe : (N.incl : N →ₗ[R] M) = (N : Submodule R M).Subtype :=
  rfl

@[simp]
theorem incl_apply (m : N) : N.incl m = m :=
  rfl

theorem incl_eq_val : (N.incl : N → M) = Subtype.val :=
  rfl

variable {N N'} (h : N ≤ N')

/-- Given two nested Lie submodules `N ⊆ N'`, the inclusion `N ↪ N'` is a morphism of Lie modules.-/
def homOfLe : N →ₗ⁅R,L⁆ N' :=
  { Submodule.ofLe (show N.toSubmodule ≤ N'.toSubmodule from h) with map_lie' := fun x m => rfl }

@[simp]
theorem coe_hom_of_le (m : N) : (homOfLe h m : M) = m :=
  rfl

theorem hom_of_le_apply (m : N) : homOfLe h m = ⟨m.1, h m.2⟩ :=
  rfl

theorem hom_of_le_injective : Function.Injective (homOfLe h) := fun x y => by
  simp only [← hom_of_le_apply, ← imp_self, ← Subtype.mk_eq_mk, ← SetLike.coe_eq_coe, ← Subtype.val_eq_coe]

end InclusionMaps

section LieSpan

variable (R L) (s : Set M)

/-- The `lie_span` of a set `s ⊆ M` is the smallest Lie submodule of `M` that contains `s`. -/
def lieSpan : LieSubmodule R L M :=
  inf { N | s ⊆ N }

variable {R L s}

theorem mem_lie_span {x : M} : x ∈ lieSpan R L s ↔ ∀ N : LieSubmodule R L M, s ⊆ N → x ∈ N := by
  change x ∈ (lie_span R L s : Set M) ↔ _
  erw [Inf_coe]
  exact mem_Inter₂

theorem subset_lie_span : s ⊆ lieSpan R L s := by
  intro m hm
  erw [mem_lie_span]
  intro N hN
  exact hN hm

theorem submodule_span_le_lie_span : Submodule.span R s ≤ lieSpan R L s := by
  rw [Submodule.span_le]
  apply subset_lie_span

theorem lie_span_le {N} : lieSpan R L s ≤ N ↔ s ⊆ N := by
  constructor
  · exact subset.trans subset_lie_span
    
  · intro hs m hm
    rw [mem_lie_span] at hm
    exact hm _ hs
    

theorem lie_span_mono {t : Set M} (h : s ⊆ t) : lieSpan R L s ≤ lieSpan R L t := by
  rw [lie_span_le]
  exact subset.trans h subset_lie_span

theorem lie_span_eq : lieSpan R L (N : Set M) = N :=
  le_antisymmₓ (lie_span_le.mpr rfl.Subset) subset_lie_span

theorem coe_lie_span_submodule_eq_iff {p : Submodule R M} :
    (lieSpan R L (p : Set M) : Submodule R M) = p ↔ ∃ N : LieSubmodule R L M, ↑N = p := by
  rw [p.exists_lie_submodule_coe_eq_iff L]
  constructor <;> intro h
  · intro x m hm
    rw [← h, mem_coe_submodule]
    exact lie_mem _ (subset_lie_span hm)
    
  · rw [← coe_to_submodule_mk p h, coe_to_submodule, coe_to_submodule_eq_iff, lie_span_eq]
    

variable (R L M)

/-- `lie_span` forms a Galois insertion with the coercion from `lie_submodule` to `set`. -/
protected def gi : GaloisInsertion (lieSpan R L : Set M → LieSubmodule R L M) coe where
  choice := fun s _ => lieSpan R L s
  gc := fun s t => lie_span_le
  le_l_u := fun s => subset_lie_span
  choice_eq := fun s h => rfl

@[simp]
theorem span_empty : lieSpan R L (∅ : Set M) = ⊥ :=
  (LieSubmodule.gi R L M).gc.l_bot

@[simp]
theorem span_univ : lieSpan R L (Set.Univ : Set M) = ⊤ :=
  eq_top_iff.2 <| SetLike.le_def.2 <| subset_lie_span

theorem lie_span_eq_bot_iff : lieSpan R L s = ⊥ ↔ ∀, ∀ m ∈ s, ∀, m = (0 : M) := by
  rw [_root_.eq_bot_iff, lie_span_le, bot_coe, subset_singleton_iff]

variable {M}

theorem span_union (s t : Set M) : lieSpan R L (s ∪ t) = lieSpan R L s⊔lieSpan R L t :=
  (LieSubmodule.gi R L M).gc.l_sup

theorem span_Union {ι} (s : ι → Set M) : lieSpan R L (⋃ i, s i) = ⨆ i, lieSpan R L (s i) :=
  (LieSubmodule.gi R L M).gc.l_supr

end LieSpan

end LatticeStructure

end LieSubmodule

section LieSubmoduleMapAndComap

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroupₓ M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroupₓ M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

namespace LieSubmodule

variable (f : M →ₗ⁅R,L⁆ M') (N N₂ : LieSubmodule R L M) (N' : LieSubmodule R L M')

/-- A morphism of Lie modules `f : M → M'` pushes forward Lie submodules of `M` to Lie submodules
of `M'`. -/
def map : LieSubmodule R L M' :=
  { (N : Submodule R M).map (f : M →ₗ[R] M') with
    lie_mem := fun x m' h => by
      rcases h with ⟨m, hm, hfm⟩
      use ⁅x,m⁆
      constructor
      · apply N.lie_mem hm
        
      · norm_cast  at hfm
        simp [← hfm]
         }

@[simp]
theorem coe_submodule_map : (N.map f : Submodule R M') = (N : Submodule R M).map (f : M →ₗ[R] M') :=
  rfl

/-- A morphism of Lie modules `f : M → M'` pulls back Lie submodules of `M'` to Lie submodules of
`M`. -/
def comap : LieSubmodule R L M :=
  { (N' : Submodule R M').comap (f : M →ₗ[R] M') with
    lie_mem := fun x m h => by
      suffices ⁅x,f m⁆ ∈ N' by
        simp [← this]
      apply N'.lie_mem h }

@[simp]
theorem coe_submodule_comap : (N'.comap f : Submodule R M) = (N' : Submodule R M').comap (f : M →ₗ[R] M') :=
  rfl

variable {f N N₂ N'}

theorem map_le_iff_le_comap : map f N ≤ N' ↔ N ≤ comap f N' :=
  Set.image_subset_iff

variable (f)

theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun N N' => map_le_iff_le_comap

variable {f}

@[simp]
theorem map_sup : (N⊔N₂).map f = N.map f⊔N₂.map f :=
  (gc_map_comap f).l_sup

theorem mem_map (m' : M') : m' ∈ N.map f ↔ ∃ m, m ∈ N ∧ f m = m' :=
  Submodule.mem_map

@[simp]
theorem mem_comap {m : M} : m ∈ comap f N' ↔ f m ∈ N' :=
  Iff.rfl

theorem comap_incl_eq_top : N₂.comap N.incl = ⊤ ↔ N ≤ N₂ := by
  simpa only [LieSubmodule.coe_to_submodule_eq_iff, ← LieSubmodule.coe_submodule_comap, ← LieSubmodule.incl_coe, ←
    LieSubmodule.top_coe_submodule, ← Submodule.comap_subtype_eq_top]

theorem comap_incl_eq_bot : N₂.comap N.incl = ⊥ ↔ N⊓N₂ = ⊥ := by
  simpa only [← _root_.eq_bot_iff, LieSubmodule.coe_to_submodule_eq_iff, ← LieSubmodule.coe_submodule_comap, ←
    LieSubmodule.incl_coe, ← LieSubmodule.bot_coe_submodule, Submodule.disjoint_iff_comap_eq_bot]

end LieSubmodule

namespace LieIdeal

variable (f : L →ₗ⁅R⁆ L') (I I₂ : LieIdeal R L) (J : LieIdeal R L')

@[simp]
theorem top_coe_lie_subalgebra : ((⊤ : LieIdeal R L) : LieSubalgebra R L) = ⊤ :=
  rfl

/-- A morphism of Lie algebras `f : L → L'` pushes forward Lie ideals of `L` to Lie ideals of `L'`.

Note that unlike `lie_submodule.map`, we must take the `lie_span` of the image. Mathematically
this is because although `f` makes `L'` into a Lie module over `L`, in general the `L` submodules of
`L'` are not the same as the ideals of `L'`. -/
def map : LieIdeal R L' :=
  LieSubmodule.lieSpan R L' <| (I : Submodule R L).map (f : L →ₗ[R] L')

/-- A morphism of Lie algebras `f : L → L'` pulls back Lie ideals of `L'` to Lie ideals of `L`.

Note that `f` makes `L'` into a Lie module over `L` (turning `f` into a morphism of Lie modules)
and so this is a special case of `lie_submodule.comap` but we do not exploit this fact. -/
def comap : LieIdeal R L :=
  { (J : Submodule R L').comap (f : L →ₗ[R] L') with
    lie_mem := fun x y h => by
      suffices ⁅f x,f y⁆ ∈ J by
        simp [← this]
      apply J.lie_mem h }

@[simp]
theorem map_coe_submodule (h : ↑(map f I) = f '' I) :
    (map f I : Submodule R L') = (I : Submodule R L).map (f : L →ₗ[R] L') := by
  rw [SetLike.ext'_iff, LieSubmodule.coe_to_submodule, h, Submodule.map_coe]
  rfl

@[simp]
theorem comap_coe_submodule : (comap f J : Submodule R L) = (J : Submodule R L').comap (f : L →ₗ[R] L') :=
  rfl

theorem map_le : map f I ≤ J ↔ f '' I ⊆ J :=
  LieSubmodule.lie_span_le

variable {f I I₂ J}

theorem mem_map {x : L} (hx : x ∈ I) : f x ∈ map f I := by
  apply LieSubmodule.subset_lie_span
  use x
  exact ⟨hx, rfl⟩

@[simp]
theorem mem_comap {x : L} : x ∈ comap f J ↔ f x ∈ J :=
  Iff.rfl

theorem map_le_iff_le_comap : map f I ≤ J ↔ I ≤ comap f J := by
  rw [map_le]
  exact Set.image_subset_iff

variable (f)

theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun I I' => map_le_iff_le_comap

variable {f}

@[simp]
theorem map_sup : (I⊔I₂).map f = I.map f⊔I₂.map f :=
  (gc_map_comap f).l_sup

theorem map_comap_le : map f (comap f J) ≤ J := by
  rw [map_le_iff_le_comap]
  exact le_rfl

/-- See also `lie_ideal.map_comap_eq`. -/
theorem comap_map_le : I ≤ comap f (map f I) := by
  rw [← map_le_iff_le_comap]
  exact le_rfl

@[mono]
theorem map_mono : Monotone (map f) := fun I₁ I₂ h => by
  rw [SetLike.le_def] at h
  apply LieSubmodule.lie_span_mono (Set.image_subset (⇑f) h)

@[mono]
theorem comap_mono : Monotone (comap f) := fun J₁ J₂ h => by
  rw [← SetLike.coe_subset_coe] at h⊢
  exact Set.preimage_mono h

theorem map_of_image (h : f '' I = J) : I.map f = J := by
  apply le_antisymmₓ
  · erw [LieSubmodule.lie_span_le, Submodule.map_coe, h]
    
  · rw [← SetLike.coe_subset_coe, ← h]
    exact LieSubmodule.subset_lie_span
    

/-- Note that this is not a special case of `lie_submodule.subsingleton_of_bot`. Indeed, given
`I : lie_ideal R L`, in general the two lattices `lie_ideal R I` and `lie_submodule R L I` are
different (though the latter does naturally inject into the former).

In other words, in general, ideals of `I`, regarded as a Lie algebra in its own right, are not the
same as ideals of `L` contained in `I`. -/
-- TODO[gh-6025]: make this an instance once safe to do so
theorem subsingleton_of_bot : Subsingleton (LieIdeal R ↥(⊥ : LieIdeal R L)) := by
  apply subsingleton_of_bot_eq_top
  ext ⟨x, hx⟩
  change x ∈ ⊥ at hx
  rw [Submodule.mem_bot] at hx
  subst hx
  simp only [← true_iffₓ, ← eq_self_iff_true, ← Submodule.mk_eq_zero, ← LieSubmodule.mem_bot]

end LieIdeal

namespace LieHom

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

/-- The kernel of a morphism of Lie algebras, as an ideal in the domain. -/
def ker : LieIdeal R L :=
  LieIdeal.comap f ⊥

/-- The range of a morphism of Lie algebras as an ideal in the codomain. -/
def idealRange : LieIdeal R L' :=
  LieSubmodule.lieSpan R L' f.range

theorem ideal_range_eq_lie_span_range : f.idealRange = LieSubmodule.lieSpan R L' f.range :=
  rfl

theorem ideal_range_eq_map : f.idealRange = LieIdeal.map f ⊤ := by
  ext
  simp only [← ideal_range, ← range_eq_map]
  rfl

/-- The condition that the image of a morphism of Lie algebras is an ideal. -/
def IsIdealMorphism : Prop :=
  (f.idealRange : LieSubalgebra R L') = f.range

@[simp]
theorem is_ideal_morphism_def : f.IsIdealMorphism ↔ (f.idealRange : LieSubalgebra R L') = f.range :=
  Iff.rfl

theorem is_ideal_morphism_iff : f.IsIdealMorphism ↔ ∀ (x : L') (y : L), ∃ z : L, ⁅x,f y⁆ = f z := by
  simp only [← is_ideal_morphism_def, ← ideal_range_eq_lie_span_range, LieSubalgebra.coe_to_submodule_eq_iff,
    f.range.coe_to_submodule, ← LieIdeal.coe_to_lie_subalgebra_to_submodule, ←
    LieSubmodule.coe_lie_span_submodule_eq_iff, ← LieSubalgebra.mem_coe_submodule, ← mem_range, ← exists_imp_distrib, ←
    Submodule.exists_lie_submodule_coe_eq_iff]
  constructor
  · intro h x y
    obtain ⟨z, hz⟩ := h x (f y) y rfl
    use z
    exact hz.symm
    
  · intro h x y z hz
    obtain ⟨w, hw⟩ := h x z
    use w
    rw [← hw, hz]
    

theorem range_subset_ideal_range : (f.range : Set L') ⊆ f.idealRange :=
  LieSubmodule.subset_lie_span

theorem map_le_ideal_range : I.map f ≤ f.idealRange := by
  rw [f.ideal_range_eq_map]
  exact LieIdeal.map_mono le_top

theorem ker_le_comap : f.ker ≤ J.comap f :=
  LieIdeal.comap_mono bot_le

@[simp]
theorem ker_coe_submodule : (ker f : Submodule R L) = (f : L →ₗ[R] L').ker :=
  rfl

@[simp]
theorem mem_ker {x : L} : x ∈ ker f ↔ f x = 0 :=
  show x ∈ (f.ker : Submodule R L) ↔ _ by
    simp only [← ker_coe_submodule, ← LinearMap.mem_ker, ← coe_to_linear_map]

theorem mem_ideal_range {x : L} : f x ∈ idealRange f := by
  rw [ideal_range_eq_map]
  exact LieIdeal.mem_map (LieSubmodule.mem_top x)

@[simp]
theorem mem_ideal_range_iff (h : IsIdealMorphism f) {y : L'} : y ∈ idealRange f ↔ ∃ x : L, f x = y := by
  rw [f.is_ideal_morphism_def] at h
  rw [← LieSubmodule.mem_coe, ← LieIdeal.coe_to_subalgebra, h, f.range_coe, Set.mem_range]

theorem le_ker_iff : I ≤ f.ker ↔ ∀ x, x ∈ I → f x = 0 := by
  constructor <;> intro h x hx
  · specialize h hx
    rw [mem_ker] at h
    exact h
    
  · rw [mem_ker]
    apply h x hx
    

theorem ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f := by
  rw [← LieSubmodule.coe_to_submodule_eq_iff, ker_coe_submodule, LieSubmodule.bot_coe_submodule, LinearMap.ker_eq_bot,
    coe_to_linear_map]

@[simp]
theorem range_coe_submodule : (f.range : Submodule R L') = (f : L →ₗ[R] L').range :=
  rfl

theorem range_eq_top : f.range = ⊤ ↔ Function.Surjective f := by
  rw [← LieSubalgebra.coe_to_submodule_eq_iff, range_coe_submodule, LieSubalgebra.top_coe_submodule]
  exact LinearMap.range_eq_top

@[simp]
theorem ideal_range_eq_top_of_surjective (h : Function.Surjective f) : f.idealRange = ⊤ := by
  rw [← f.range_eq_top] at h
  rw [ideal_range_eq_lie_span_range, h, ← LieSubalgebra.coe_to_submodule, ← LieSubmodule.coe_to_submodule_eq_iff,
    LieSubmodule.top_coe_submodule, LieSubalgebra.top_coe_submodule, LieSubmodule.coe_lie_span_submodule_eq_iff]
  use ⊤
  exact LieSubmodule.top_coe_submodule

theorem is_ideal_morphism_of_surjective (h : Function.Surjective f) : f.IsIdealMorphism := by
  rw [is_ideal_morphism_def, f.ideal_range_eq_top_of_surjective h, f.range_eq_top.mpr h,
    LieIdeal.top_coe_lie_subalgebra]

end LieHom

namespace LieIdeal

variable {f : L →ₗ⁅R⁆ L'} {I : LieIdeal R L} {J : LieIdeal R L'}

@[simp]
theorem map_eq_bot_iff : I.map f = ⊥ ↔ I ≤ f.ker := by
  rw [← le_bot_iff]
  exact LieIdeal.map_le_iff_le_comap

theorem coe_map_of_surjective (h : Function.Surjective f) :
    (I.map f : Submodule R L') = (I : Submodule R L).map (f : L →ₗ[R] L') := by
  let J : LieIdeal R L' :=
    { (I : Submodule R L).map (f : L →ₗ[R] L') with
      lie_mem := fun x y hy => by
        have hy' : ∃ x : L, x ∈ I ∧ f x = y := by
          simpa [← hy]
        obtain ⟨z₂, hz₂, rfl⟩ := hy'
        obtain ⟨z₁, rfl⟩ := h x
        simp only [← LieHom.coe_to_linear_map, ← SetLike.mem_coe, ← Set.mem_image, ← LieSubmodule.mem_coe_submodule, ←
          Submodule.mem_carrier, ← Submodule.map_coe]
        use ⁅z₁,z₂⁆
        exact ⟨I.lie_mem hz₂, f.map_lie z₁ z₂⟩ }
  erw [LieSubmodule.coe_lie_span_submodule_eq_iff]
  use J
  apply LieSubmodule.coe_to_submodule_mk

theorem mem_map_of_surjective {y : L'} (h₁ : Function.Surjective f) (h₂ : y ∈ I.map f) : ∃ x : I, f x = y := by
  rw [← LieSubmodule.mem_coe_submodule, coe_map_of_surjective h₁, Submodule.mem_map] at h₂
  obtain ⟨x, hx, rfl⟩ := h₂
  use ⟨x, hx⟩
  rfl

theorem bot_of_map_eq_bot {I : LieIdeal R L} (h₁ : Function.Injective f) (h₂ : I.map f = ⊥) : I = ⊥ := by
  rw [← f.ker_eq_bot] at h₁
  change comap f ⊥ = ⊥ at h₁
  rw [eq_bot_iff, map_le_iff_le_comap, h₁] at h₂
  rw [eq_bot_iff]
  exact h₂

/-- Given two nested Lie ideals `I₁ ⊆ I₂`, the inclusion `I₁ ↪ I₂` is a morphism of Lie algebras. -/
def homOfLe {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) : I₁ →ₗ⁅R⁆ I₂ :=
  { Submodule.ofLe (show I₁.toSubmodule ≤ I₂.toSubmodule from h) with map_lie' := fun x y => rfl }

@[simp]
theorem coe_hom_of_le {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) (x : I₁) : (homOfLe h x : L) = x :=
  rfl

theorem hom_of_le_apply {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) (x : I₁) : homOfLe h x = ⟨x.1, h x.2⟩ :=
  rfl

theorem hom_of_le_injective {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) : Function.Injective (homOfLe h) := fun x y => by
  simp only [← hom_of_le_apply, ← imp_self, ← Subtype.mk_eq_mk, ← SetLike.coe_eq_coe, ← Subtype.val_eq_coe]

@[simp]
theorem map_sup_ker_eq_map : LieIdeal.map f (I⊔f.ker) = LieIdeal.map f I := by
  suffices LieIdeal.map f (I⊔f.ker) ≤ LieIdeal.map f I by
    exact le_antisymmₓ this (LieIdeal.map_mono le_sup_left)
  apply LieSubmodule.lie_span_mono
  rintro x ⟨y, hy₁, hy₂⟩
  rw [← hy₂]
  erw [LieSubmodule.mem_sup] at hy₁
  obtain ⟨z₁, hz₁, z₂, hz₂, hy⟩ := hy₁
  rw [← hy]
  rw [f.coe_to_linear_map, f.map_add, f.mem_ker.mp hz₂, add_zeroₓ]
  exact ⟨z₁, hz₁, rfl⟩

@[simp]
theorem map_comap_eq (h : f.IsIdealMorphism) : map f (comap f J) = f.idealRange⊓J := by
  apply le_antisymmₓ
  · rw [le_inf_iff]
    exact ⟨f.map_le_ideal_range _, map_comap_le⟩
    
  · rw [f.is_ideal_morphism_def] at h
    rw [← SetLike.coe_subset_coe, LieSubmodule.inf_coe, ← coe_to_subalgebra, h]
    rintro y ⟨⟨x, h₁⟩, h₂⟩
    rw [← h₁] at h₂⊢
    exact mem_map h₂
    

@[simp]
theorem comap_map_eq (h : ↑(map f I) = f '' I) : comap f (map f I) = I⊔f.ker := by
  rw [← LieSubmodule.coe_to_submodule_eq_iff, comap_coe_submodule, I.map_coe_submodule f h,
    LieSubmodule.sup_coe_to_submodule, f.ker_coe_submodule, Submodule.comap_map_eq]

variable (f I J)

/-- Regarding an ideal `I` as a subalgebra, the inclusion map into its ambient space is a morphism
of Lie algebras. -/
def incl : I →ₗ⁅R⁆ L :=
  (I : LieSubalgebra R L).incl

@[simp]
theorem incl_range : I.incl.range = I :=
  (I : LieSubalgebra R L).incl_range

@[simp]
theorem incl_apply (x : I) : I.incl x = x :=
  rfl

@[simp]
theorem incl_coe : (I.incl : I →ₗ[R] L) = (I : Submodule R L).Subtype :=
  rfl

@[simp]
theorem comap_incl_self : comap I.incl I = ⊤ := by
  rw [← LieSubmodule.coe_to_submodule_eq_iff]
  exact Submodule.comap_subtype_self _

@[simp]
theorem ker_incl : I.incl.ker = ⊥ := by
  rw [← LieSubmodule.coe_to_submodule_eq_iff, I.incl.ker_coe_submodule, LieSubmodule.bot_coe_submodule, incl_coe,
    Submodule.ker_subtype]

@[simp]
theorem incl_ideal_range : I.incl.idealRange = I := by
  rw [LieHom.ideal_range_eq_lie_span_range, ← LieSubalgebra.coe_to_submodule, ← LieSubmodule.coe_to_submodule_eq_iff,
    incl_range, coe_to_lie_subalgebra_to_submodule, LieSubmodule.coe_lie_span_submodule_eq_iff]
  use I

theorem incl_is_ideal_morphism : I.incl.IsIdealMorphism := by
  rw [I.incl.is_ideal_morphism_def, incl_ideal_range]
  exact (I : LieSubalgebra R L).incl_range.symm

end LieIdeal

end LieSubmoduleMapAndComap

namespace LieModuleHom

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroupₓ M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroupₓ N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable (f : M →ₗ⁅R,L⁆ N)

/-- The kernel of a morphism of Lie algebras, as an ideal in the domain. -/
def ker : LieSubmodule R L M :=
  LieSubmodule.comap f ⊥

@[simp]
theorem ker_coe_submodule : (f.ker : Submodule R M) = (f : M →ₗ[R] N).ker :=
  rfl

theorem ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f := by
  rw [← LieSubmodule.coe_to_submodule_eq_iff, ker_coe_submodule, LieSubmodule.bot_coe_submodule, LinearMap.ker_eq_bot,
    coe_to_linear_map]

variable {f}

@[simp]
theorem mem_ker (m : M) : m ∈ f.ker ↔ f m = 0 :=
  Iff.rfl

@[simp]
theorem ker_id : (LieModuleHom.id : M →ₗ⁅R,L⁆ M).ker = ⊥ :=
  rfl

@[simp]
theorem comp_ker_incl : f.comp f.ker.incl = 0 := by
  ext ⟨m, hm⟩
  exact (mem_ker m).mp hm

theorem le_ker_iff_map (M' : LieSubmodule R L M) : M' ≤ f.ker ↔ LieSubmodule.map f M' = ⊥ := by
  rw [ker, eq_bot_iff, LieSubmodule.map_le_iff_le_comap]

variable (f)

/-- The range of a morphism of Lie modules `f : M → N` is a Lie submodule of `N`.
See Note [range copy pattern]. -/
def range : LieSubmodule R L N :=
  (LieSubmodule.map f ⊤).copy (Set.Range f) Set.image_univ.symm

@[simp]
theorem coe_range : (f.range : Set N) = Set.Range f :=
  rfl

@[simp]
theorem coe_submodule_range : (f.range : Submodule R N) = (f : M →ₗ[R] N).range :=
  rfl

@[simp]
theorem mem_range (n : N) : n ∈ f.range ↔ ∃ m, f m = n :=
  Iff.rfl

theorem map_top : LieSubmodule.map f ⊤ = f.range := by
  ext
  simp [← LieSubmodule.mem_map]

end LieModuleHom

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroupₓ M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (N : LieSubmodule R L M)

@[simp]
theorem ker_incl : N.incl.ker = ⊥ := by
  simp [LieSubmodule.coe_to_submodule_eq_iff]

@[simp]
theorem range_incl : N.incl.range = N := by
  simp [LieSubmodule.coe_to_submodule_eq_iff]

@[simp]
theorem comap_incl_self : comap N.incl N = ⊤ := by
  simp [LieSubmodule.coe_to_submodule_eq_iff]

end LieSubmodule

section TopEquiv

variable {R : Type u} {L : Type v}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L]

/-- The natural equivalence between the 'top' Lie subalgebra and the enclosing Lie algebra.

This is the Lie subalgebra version of `submodule.top_equiv`. -/
def LieSubalgebra.topEquiv : (⊤ : LieSubalgebra R L) ≃ₗ⁅R⁆ L :=
  { (⊤ : LieSubalgebra R L).incl with invFun := fun x => ⟨x, Set.mem_univ x⟩,
    left_inv := fun x => by
      ext
      rfl,
    right_inv := fun x => rfl }

@[simp]
theorem LieSubalgebra.top_equiv_apply (x : (⊤ : LieSubalgebra R L)) : LieSubalgebra.topEquiv x = x :=
  rfl

/-- The natural equivalence between the 'top' Lie ideal and the enclosing Lie algebra.

This is the Lie ideal version of `submodule.top_equiv`. -/
def LieIdeal.topEquiv : (⊤ : LieIdeal R L) ≃ₗ⁅R⁆ L :=
  LieSubalgebra.topEquiv

@[simp]
theorem LieIdeal.top_equiv_apply (x : (⊤ : LieIdeal R L)) : LieIdeal.topEquiv x = x :=
  rfl

end TopEquiv


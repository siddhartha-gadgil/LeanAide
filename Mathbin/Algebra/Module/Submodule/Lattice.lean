/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import Mathbin.Algebra.Module.Submodule.Basic
import Mathbin.Algebra.PunitInstances

/-!
# The lattice structure on `submodule`s

This file defines the lattice structure on submodules, `submodule.complete_lattice`, with `⊥`
defined as `{0}` and `⊓` defined as intersection of the underlying carrier.
If `p` and `q` are submodules of a module, `p ≤ q` means that `p ⊆ q`.

Many results about operations on this lattice structure are defined in `linear_algebra/basic.lean`,
most notably those which use `span`.

## Implementation notes

This structure should match the `add_submonoid.complete_lattice` structure, and we should try
to unify the APIs where possible.

-/


variable {R S M : Type _}

section AddCommMonoidₓ

variable [Semiringₓ R] [Semiringₓ S] [AddCommMonoidₓ M] [Module R M] [Module S M]

variable [HasSmul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

namespace Submodule

/-- The set `{0}` is the bottom element of the lattice of submodules. -/
instance : HasBot (Submodule R M) :=
  ⟨{ (⊥ : AddSubmonoid M) with Carrier := {0},
      smul_mem' := by
        simp (config := { contextual := true }) }⟩

instance inhabited' : Inhabited (Submodule R M) :=
  ⟨⊥⟩

@[simp]
theorem bot_coe : ((⊥ : Submodule R M) : Set M) = {0} :=
  rfl

@[simp]
theorem bot_to_add_submonoid : (⊥ : Submodule R M).toAddSubmonoid = ⊥ :=
  rfl

section

variable (R)

@[simp]
theorem restrict_scalars_bot : restrictScalars S (⊥ : Submodule R M) = ⊥ :=
  rfl

@[simp]
theorem mem_bot {x : M} : x ∈ (⊥ : Submodule R M) ↔ x = 0 :=
  Set.mem_singleton_iff

end

@[simp]
theorem restrict_scalars_eq_bot_iff {p : Submodule R M} : restrictScalars S p = ⊥ ↔ p = ⊥ := by
  simp [← SetLike.ext_iff]

instance uniqueBot : Unique (⊥ : Submodule R M) :=
  ⟨inferInstance, fun x => Subtype.ext <| (mem_bot R).1 x.Mem⟩

instance : OrderBot (Submodule R M) where
  bot := ⊥
  bot_le := fun p x => by
    simp (config := { contextual := true })[← zero_mem]

protected theorem eq_bot_iff (p : Submodule R M) : p = ⊥ ↔ ∀, ∀ x ∈ p, ∀, x = (0 : M) :=
  ⟨fun h => h.symm ▸ fun x hx => (mem_bot R).mp hx, fun h => eq_bot_iff.mpr fun x hx => (mem_bot R).mpr (h x hx)⟩

@[ext]
protected theorem bot_ext (x y : (⊥ : Submodule R M)) : x = y := by
  rcases x with ⟨x, xm⟩
  rcases y with ⟨y, ym⟩
  congr
  rw [(Submodule.eq_bot_iff _).mp rfl x xm]
  rw [(Submodule.eq_bot_iff _).mp rfl y ym]

protected theorem ne_bot_iff (p : Submodule R M) : p ≠ ⊥ ↔ ∃ x ∈ p, x ≠ (0 : M) := by
  have := Classical.propDecidable
  simp_rw [Ne.def, p.eq_bot_iff, not_forall]

theorem nonzero_mem_of_bot_lt {p : Submodule R M} (bot_lt : ⊥ < p) : ∃ a : p, a ≠ 0 :=
  let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp bot_lt.ne'
  ⟨⟨b, hb₁⟩, hb₂ ∘ congr_arg coe⟩

theorem exists_mem_ne_zero_of_ne_bot {p : Submodule R M} (h : p ≠ ⊥) : ∃ b : M, b ∈ p ∧ b ≠ 0 :=
  let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp h
  ⟨b, hb₁, hb₂⟩

/-- The bottom submodule is linearly equivalent to punit as an `R`-module. -/
@[simps]
def botEquivPunit : (⊥ : Submodule R M) ≃ₗ[R] PUnit where
  toFun := fun x => PUnit.unit
  invFun := fun x => 0
  map_add' := by
    intros
    ext
  map_smul' := by
    intros
    ext
  left_inv := by
    intro x
    ext
  right_inv := by
    intro x
    ext

theorem eq_bot_of_subsingleton (p : Submodule R M) [Subsingleton p] : p = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  exact congr_arg coe (Subsingleton.elimₓ (⟨v, hv⟩ : p) 0)

/-- The universal set is the top element of the lattice of submodules. -/
instance : HasTop (Submodule R M) :=
  ⟨{ (⊤ : AddSubmonoid M) with Carrier := Set.Univ, smul_mem' := fun _ _ _ => trivialₓ }⟩

@[simp]
theorem top_coe : ((⊤ : Submodule R M) : Set M) = Set.Univ :=
  rfl

@[simp]
theorem top_to_add_submonoid : (⊤ : Submodule R M).toAddSubmonoid = ⊤ :=
  rfl

@[simp]
theorem mem_top {x : M} : x ∈ (⊤ : Submodule R M) :=
  trivialₓ

section

variable (R)

@[simp]
theorem restrict_scalars_top : restrictScalars S (⊤ : Submodule R M) = ⊤ :=
  rfl

end

@[simp]
theorem restrict_scalars_eq_top_iff {p : Submodule R M} : restrictScalars S p = ⊤ ↔ p = ⊤ := by
  simp [← SetLike.ext_iff]

instance : OrderTop (Submodule R M) where
  top := ⊤
  le_top := fun p x _ => trivialₓ

theorem eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ ∀ x, x ∈ p :=
  eq_top_iff.trans ⟨fun h x => h trivialₓ, fun h x _ => h x⟩

/-- The top submodule is linearly equivalent to the module.

This is the module version of `add_submonoid.top_equiv`. -/
@[simps]
def topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M where
  toFun := fun x => x
  invFun := fun x =>
    ⟨x, by
      simp ⟩
  map_add' := by
    intros
    rfl
  map_smul' := by
    intros
    rfl
  left_inv := by
    intro x
    ext
    rfl
  right_inv := by
    intro x
    rfl

instance : HasInfₓ (Submodule R M) :=
  ⟨fun S =>
    { Carrier := ⋂ s ∈ S, (s : Set M),
      zero_mem' := by
        simp [← zero_mem],
      add_mem' := by
        simp (config := { contextual := true })[← add_mem],
      smul_mem' := by
        simp (config := { contextual := true })[← smul_mem] }⟩

private theorem Inf_le' {S : Set (Submodule R M)} {p} : p ∈ S → inf S ≤ p :=
  Set.bInter_subset_of_mem

private theorem le_Inf' {S : Set (Submodule R M)} {p} : (∀, ∀ q ∈ S, ∀, p ≤ q) → p ≤ inf S :=
  Set.subset_Inter₂

instance : HasInf (Submodule R M) :=
  ⟨fun p q =>
    { Carrier := p ∩ q,
      zero_mem' := by
        simp [← zero_mem],
      add_mem' := by
        simp (config := { contextual := true })[← add_mem],
      smul_mem' := by
        simp (config := { contextual := true })[← smul_mem] }⟩

instance : CompleteLattice (Submodule R M) :=
  { Submodule.orderTop, Submodule.orderBot, SetLike.partialOrder with sup := fun a b => inf { x | a ≤ x ∧ b ≤ x },
    le_sup_left := fun a b => le_Inf' fun x ⟨ha, hb⟩ => ha, le_sup_right := fun a b => le_Inf' fun x ⟨ha, hb⟩ => hb,
    sup_le := fun a b c h₁ h₂ => Inf_le' ⟨h₁, h₂⟩, inf := (·⊓·), le_inf := fun a b c => Set.subset_inter,
    inf_le_left := fun a b => Set.inter_subset_left _ _, inf_le_right := fun a b => Set.inter_subset_right _ _,
    sup := fun tt => inf { t | ∀, ∀ t' ∈ tt, ∀, t' ≤ t }, le_Sup := fun s p hs => le_Inf' fun q hq => hq _ hs,
    Sup_le := fun s p hs => Inf_le' hs, inf := inf, le_Inf := fun s a => le_Inf', Inf_le := fun s a => Inf_le' }

@[simp]
theorem inf_coe : ↑(p⊓q) = (p ∩ q : Set M) :=
  rfl

@[simp]
theorem mem_inf {p q : Submodule R M} {x : M} : x ∈ p⊓q ↔ x ∈ p ∧ x ∈ q :=
  Iff.rfl

@[simp]
theorem Inf_coe (P : Set (Submodule R M)) : (↑(inf P) : Set M) = ⋂ p ∈ P, ↑p :=
  rfl

@[simp]
theorem finset_inf_coe {ι} (s : Finset ι) (p : ι → Submodule R M) : (↑(s.inf p) : Set M) = ⋂ i ∈ s, ↑(p i) := by
  let this := Classical.decEq ι
  refine' s.induction_on _ fun i s hi ih => _
  · simp
    
  · rw [Finset.inf_insert, inf_coe, ih]
    simp
    

@[simp]
theorem infi_coe {ι} (p : ι → Submodule R M) : (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i) := by
  rw [infi, Inf_coe] <;> ext a <;> simp <;> exact ⟨fun h i => h _ i rfl, fun h i x e => e ▸ h _⟩

@[simp]
theorem mem_Inf {S : Set (Submodule R M)} {x : M} : x ∈ inf S ↔ ∀, ∀ p ∈ S, ∀, x ∈ p :=
  Set.mem_Inter₂

@[simp]
theorem mem_infi {ι} (p : ι → Submodule R M) {x} : (x ∈ ⨅ i, p i) ↔ ∀ i, x ∈ p i := by
  rw [← SetLike.mem_coe, infi_coe, Set.mem_Inter] <;> rfl

@[simp]
theorem mem_finset_inf {ι} {s : Finset ι} {p : ι → Submodule R M} {x : M} : x ∈ s.inf p ↔ ∀, ∀ i ∈ s, ∀, x ∈ p i := by
  simp only [SetLike.mem_coe, ← finset_inf_coe, ← Set.mem_Inter]

theorem mem_sup_left {S T : Submodule R M} : ∀ {x : M}, x ∈ S → x ∈ S⊔T :=
  show S ≤ S⊔T from le_sup_left

theorem mem_sup_right {S T : Submodule R M} : ∀ {x : M}, x ∈ T → x ∈ S⊔T :=
  show T ≤ S⊔T from le_sup_right

theorem add_mem_sup {S T : Submodule R M} {s t : M} (hs : s ∈ S) (ht : t ∈ T) : s + t ∈ S⊔T :=
  add_mem (mem_sup_left hs) (mem_sup_right ht)

theorem mem_supr_of_mem {ι : Sort _} {b : M} {p : ι → Submodule R M} (i : ι) (h : b ∈ p i) : b ∈ ⨆ i, p i :=
  have : p i ≤ ⨆ i, p i := le_supr p i
  @this b h

open BigOperators

theorem sum_mem_supr {ι : Type _} [Fintype ι] {f : ι → M} {p : ι → Submodule R M} (h : ∀ i, f i ∈ p i) :
    (∑ i, f i) ∈ ⨆ i, p i :=
  sum_mem fun i hi => mem_supr_of_mem i (h i)

theorem sum_mem_bsupr {ι : Type _} {s : Finset ι} {f : ι → M} {p : ι → Submodule R M} (h : ∀, ∀ i ∈ s, ∀, f i ∈ p i) :
    (∑ i in s, f i) ∈ ⨆ i ∈ s, p i :=
  sum_mem fun i hi => mem_supr_of_mem i <| mem_supr_of_mem hi (h i hi)

/-! Note that `submodule.mem_supr` is provided in `linear_algebra/basic.lean`. -/


theorem mem_Sup_of_mem {S : Set (Submodule R M)} {s : Submodule R M} (hs : s ∈ S) : ∀ {x : M}, x ∈ s → x ∈ sup S :=
  show s ≤ sup S from le_Sup hs

theorem disjoint_def {p p' : Submodule R M} : Disjoint p p' ↔ ∀, ∀ x ∈ p, ∀, x ∈ p' → x = (0 : M) :=
  show (∀ x, x ∈ p ∧ x ∈ p' → x ∈ ({0} : Set M)) ↔ _ by
    simp

theorem disjoint_def' {p p' : Submodule R M} : Disjoint p p' ↔ ∀, ∀ x ∈ p, ∀, ∀ y ∈ p', ∀, x = y → x = (0 : M) :=
  disjoint_def.trans ⟨fun h x hx y hy hxy => h x hx <| hxy.symm ▸ hy, fun h x hx hx' => h _ hx x hx' rfl⟩

theorem eq_zero_of_coe_mem_of_disjoint (hpq : Disjoint p q) {a : p} (ha : (a : M) ∈ q) : a = 0 := by
  exact_mod_cast disjoint_def.mp hpq a (coe_mem a) ha

end Submodule

section NatSubmodule

/-- An additive submonoid is equivalent to a ℕ-submodule. -/
def AddSubmonoid.toNatSubmodule : AddSubmonoid M ≃o Submodule ℕ M where
  toFun := fun S => { S with smul_mem' := fun r s hs => show r • s ∈ S from nsmul_mem hs _ }
  invFun := Submodule.toAddSubmonoid
  left_inv := fun ⟨S, _, _⟩ => rfl
  right_inv := fun ⟨S, _, _, _⟩ => rfl
  map_rel_iff' := fun a b => Iff.rfl

@[simp]
theorem AddSubmonoid.to_nat_submodule_symm :
    ⇑(AddSubmonoid.toNatSubmodule.symm : _ ≃o AddSubmonoid M) = Submodule.toAddSubmonoid :=
  rfl

@[simp]
theorem AddSubmonoid.coe_to_nat_submodule (S : AddSubmonoid M) : (S.toNatSubmodule : Set M) = S :=
  rfl

@[simp]
theorem AddSubmonoid.to_nat_submodule_to_add_submonoid (S : AddSubmonoid M) : S.toNatSubmodule.toAddSubmonoid = S :=
  AddSubmonoid.toNatSubmodule.symm_apply_apply S

@[simp]
theorem Submodule.to_add_submonoid_to_nat_submodule (S : Submodule ℕ M) : S.toAddSubmonoid.toNatSubmodule = S :=
  AddSubmonoid.toNatSubmodule.apply_symm_apply S

end NatSubmodule

end AddCommMonoidₓ

section IntSubmodule

variable [AddCommGroupₓ M]

/-- An additive subgroup is equivalent to a ℤ-submodule. -/
def AddSubgroup.toIntSubmodule : AddSubgroup M ≃o Submodule ℤ M where
  toFun := fun S => { S with smul_mem' := fun r s hs => S.zsmul_mem hs _ }
  invFun := Submodule.toAddSubgroup
  left_inv := fun ⟨S, _, _, _⟩ => rfl
  right_inv := fun ⟨S, _, _, _⟩ => rfl
  map_rel_iff' := fun a b => Iff.rfl

@[simp]
theorem AddSubgroup.to_int_submodule_symm :
    ⇑(AddSubgroup.toIntSubmodule.symm : _ ≃o AddSubgroup M) = Submodule.toAddSubgroup :=
  rfl

@[simp]
theorem AddSubgroup.coe_to_int_submodule (S : AddSubgroup M) : (S.toIntSubmodule : Set M) = S :=
  rfl

@[simp]
theorem AddSubgroup.to_int_submodule_to_add_subgroup (S : AddSubgroup M) : S.toIntSubmodule.toAddSubgroup = S :=
  AddSubgroup.toIntSubmodule.symm_apply_apply S

@[simp]
theorem Submodule.to_add_subgroup_to_int_submodule (S : Submodule ℤ M) : S.toAddSubgroup.toIntSubmodule = S :=
  AddSubgroup.toIntSubmodule.apply_symm_apply S

end IntSubmodule


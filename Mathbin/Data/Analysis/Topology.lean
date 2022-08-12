/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Computational realization of topological spaces (experimental).
-/
import Mathbin.Topology.Bases
import Mathbin.Data.Analysis.Filter

open Set

open Filter hiding Realizer

open TopologicalSpace

/-- A `ctop α σ` is a realization of a topology (basis) on `α`,
  represented by a type `σ` together with operations for the top element and
  the intersection operation. -/
structure Ctop (α σ : Type _) where
  f : σ → Set α
  top : α → σ
  top_mem : ∀ x : α, x ∈ f (top x)
  inter : ∀ (a b) (x : α), x ∈ f a ∩ f b → σ
  inter_mem : ∀ a b x h, x ∈ f (inter a b x h)
  inter_sub : ∀ a b x h, f (inter a b x h) ⊆ f a ∩ f b

variable {α : Type _} {β : Type _} {σ : Type _} {τ : Type _}

namespace Ctop

section

variable (F : Ctop α σ)

instance : CoeFun (Ctop α σ) fun _ => σ → Set α :=
  ⟨Ctop.F⟩

@[simp]
theorem coe_mk (f T h₁ I h₂ h₃ a) : (@Ctop.mk α σ f T h₁ I h₂ h₃) a = f a :=
  rfl

/-- Map a ctop to an equivalent representation type. -/
def ofEquiv (E : σ ≃ τ) : Ctop α σ → Ctop α τ
  | ⟨f, T, h₁, I, h₂, h₃⟩ =>
    { f := fun a => f (E.symm a), top := fun x => E (T x),
      top_mem := fun x => by
        simpa using h₁ x,
      inter := fun a b x h => E (I (E.symm a) (E.symm b) x h),
      inter_mem := fun a b x h => by
        simpa using h₂ (E.symm a) (E.symm b) x h,
      inter_sub := fun a b x h => by
        simpa using h₃ (E.symm a) (E.symm b) x h }

@[simp]
theorem of_equiv_val (E : σ ≃ τ) (F : Ctop α σ) (a : τ) : F.ofEquiv E a = F (E.symm a) := by
  cases F <;> rfl

end

/-- Every `ctop` is a topological space. -/
def toTopsp (F : Ctop α σ) : TopologicalSpace α :=
  TopologicalSpace.generateFrom (Set.Range F.f)

theorem to_topsp_is_topological_basis (F : Ctop α σ) :
    @TopologicalSpace.IsTopologicalBasis _ F.toTopsp (Set.Range F.f) := by
  let this := F.to_topsp <;>
    exact
      ⟨fun u ⟨a, e₁⟩ v ⟨b, e₂⟩ => e₁ ▸ e₂ ▸ fun x h => ⟨_, ⟨_, rfl⟩, F.inter_mem a b x h, F.inter_sub a b x h⟩,
        eq_univ_iff_forall.2 fun x => ⟨_, ⟨_, rfl⟩, F.top_mem x⟩, rfl⟩

@[simp]
theorem mem_nhds_to_topsp (F : Ctop α σ) {s : Set α} {a : α} : s ∈ @nhds _ F.toTopsp a ↔ ∃ b, a ∈ F b ∧ F b ⊆ s :=
  (@TopologicalSpace.IsTopologicalBasis.mem_nhds_iff _ F.toTopsp _ _ _ F.to_topsp_is_topological_basis).trans <|
    ⟨fun ⟨_, ⟨x, rfl⟩, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨_, ⟨x, rfl⟩, h⟩⟩

end Ctop

/-- A `ctop` realizer for the topological space `T` is a `ctop`
  which generates `T`. -/
structure Ctop.Realizer (α) [T : TopologicalSpace α] where
  σ : Type _
  f : Ctop α σ
  Eq : F.toTopsp = T

open Ctop

protected def Ctop.toRealizer (F : Ctop α σ) : @Ctop.Realizer _ F.toTopsp :=
  @Ctop.Realizer.mk _ F.toTopsp σ F rfl

namespace Ctop.Realizer

protected theorem is_basis [T : TopologicalSpace α] (F : Realizer α) :
    TopologicalSpace.IsTopologicalBasis (Set.Range F.f.f) := by
  have := to_topsp_is_topological_basis F.F <;> rwa [F.eq] at this

protected theorem mem_nhds [T : TopologicalSpace α] (F : Realizer α) {s : Set α} {a : α} :
    s ∈ 𝓝 a ↔ ∃ b, a ∈ F.f b ∧ F.f b ⊆ s := by
  have := mem_nhds_to_topsp F.F <;> rwa [F.eq] at this

theorem is_open_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} :
    IsOpen s ↔ ∀, ∀ a ∈ s, ∀, ∃ b, a ∈ F.f b ∧ F.f b ⊆ s :=
  is_open_iff_mem_nhds.trans <| ball_congr fun a h => F.mem_nhds

theorem is_closed_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} :
    IsClosed s ↔ ∀ a, (∀ b, a ∈ F.f b → ∃ z, z ∈ F.f b ∩ s) → a ∈ s :=
  is_open_compl_iff.symm.trans <|
    F.is_open_iff.trans <|
      forall_congrₓ fun a =>
        show (a ∉ s → ∃ b : F.σ, a ∈ F.f b ∧ ∀, ∀ z ∈ F.f b, ∀, z ∉ s) ↔ _ by
          have := Classical.propDecidable <;>
            rw [not_imp_comm] <;> simp [← not_exists, ← not_and, ← not_forall, ← and_comm]

theorem mem_interior_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} {a : α} :
    a ∈ Interior s ↔ ∃ b, a ∈ F.f b ∧ F.f b ⊆ s :=
  mem_interior_iff_mem_nhds.trans F.mem_nhds

protected theorem is_open [TopologicalSpace α] (F : Realizer α) (s : F.σ) : IsOpen (F.f s) :=
  is_open_iff_nhds.2 fun a m => by
    simpa using F.mem_nhds.2 ⟨s, m, subset.refl _⟩

theorem ext' [T : TopologicalSpace α] {σ : Type _} {F : Ctop α σ} (H : ∀ a s, s ∈ 𝓝 a ↔ ∃ b, a ∈ F b ∧ F b ⊆ s) :
    F.toTopsp = T := by
  refine' eq_of_nhds_eq_nhds fun x => _
  ext s
  rw [mem_nhds_to_topsp, H]

theorem ext [T : TopologicalSpace α] {σ : Type _} {F : Ctop α σ} (H₁ : ∀ a, IsOpen (F a))
    (H₂ : ∀ a s, s ∈ 𝓝 a → ∃ b, a ∈ F b ∧ F b ⊆ s) : F.toTopsp = T :=
  ext' fun a s => ⟨H₂ a s, fun ⟨b, h₁, h₂⟩ => mem_nhds_iff.2 ⟨_, h₂, H₁ _, h₁⟩⟩

variable [TopologicalSpace α]

protected def id : Realizer α :=
  ⟨{ x : Set α // IsOpen x },
    { f := Subtype.val, top := fun _ => ⟨Univ, is_open_univ⟩, top_mem := mem_univ,
      inter := fun ⟨x, h₁⟩ ⟨y, h₂⟩ a h₃ => ⟨_, h₁.inter h₂⟩, inter_mem := fun ⟨x, h₁⟩ ⟨y, h₂⟩ a => id,
      inter_sub := fun ⟨x, h₁⟩ ⟨y, h₂⟩ a h₃ => Subset.refl _ },
    (ext Subtype.property) fun x s h =>
      let ⟨t, h, o, m⟩ := mem_nhds_iff.1 h
      ⟨⟨t, o⟩, m, h⟩⟩

def ofEquiv (F : Realizer α) (E : F.σ ≃ τ) : Realizer α :=
  ⟨τ, F.f.ofEquiv E,
    ext' fun a s =>
      F.mem_nhds.trans <|
        ⟨fun ⟨s, h⟩ =>
          ⟨E s, by
            simpa using h⟩,
          fun ⟨t, h⟩ =>
          ⟨E.symm t, by
            simpa using h⟩⟩⟩

@[simp]
theorem of_equiv_σ (F : Realizer α) (E : F.σ ≃ τ) : (F.ofEquiv E).σ = τ :=
  rfl

@[simp]
theorem of_equiv_F (F : Realizer α) (E : F.σ ≃ τ) (s : τ) : (F.ofEquiv E).f s = F.f (E.symm s) := by
  delta' of_equiv <;> simp

protected def nhds (F : Realizer α) (a : α) : (𝓝 a).Realizer :=
  ⟨{ s : F.σ // a ∈ F.f s },
    { f := fun s => F.f s.1, pt := ⟨_, F.f.top_mem a⟩, inf := fun ⟨x, h₁⟩ ⟨y, h₂⟩ => ⟨_, F.f.inter_mem x y a ⟨h₁, h₂⟩⟩,
      inf_le_left := fun ⟨x, h₁⟩ ⟨y, h₂⟩ z h => (F.f.inter_sub x y a ⟨h₁, h₂⟩ h).1,
      inf_le_right := fun ⟨x, h₁⟩ ⟨y, h₂⟩ z h => (F.f.inter_sub x y a ⟨h₁, h₂⟩ h).2 },
    filter_eq <|
      Set.ext fun x =>
        ⟨fun ⟨⟨s, as⟩, h⟩ => mem_nhds_iff.2 ⟨_, h, F.IsOpen _, as⟩, fun h =>
          let ⟨s, h, as⟩ := F.mem_nhds.1 h
          ⟨⟨s, h⟩, as⟩⟩⟩

@[simp]
theorem nhds_σ (m : α → β) (F : Realizer α) (a : α) : (F.nhds a).σ = { s : F.σ // a ∈ F.f s } :=
  rfl

@[simp]
theorem nhds_F (m : α → β) (F : Realizer α) (a : α) (s) : (F.nhds a).f s = F.f s.1 :=
  rfl

theorem tendsto_nhds_iff {m : β → α} {f : Filter β} (F : f.Realizer) (R : Realizer α) {a : α} :
    Tendsto m f (𝓝 a) ↔ ∀ t, a ∈ R.f t → ∃ s, ∀, ∀ x ∈ F.f s, ∀, m x ∈ R.f t :=
  (F.tendsto_iff _ (R.nhds a)).trans Subtype.forall

end Ctop.Realizer

structure LocallyFinite.Realizer [TopologicalSpace α] (F : Realizer α) (f : β → Set α) where
  bas : ∀ a, { s // a ∈ F.f s }
  Sets : ∀ x : α, Fintype { i | (f i ∩ F.f (bas x)).Nonempty }

theorem LocallyFinite.Realizer.to_locally_finite [TopologicalSpace α] {F : Realizer α} {f : β → Set α}
    (R : LocallyFinite.Realizer F f) : LocallyFinite f := fun a =>
  ⟨_, F.mem_nhds.2 ⟨(R.bas a).1, (R.bas a).2, Subset.refl _⟩, ⟨R.Sets a⟩⟩

theorem locally_finite_iff_exists_realizer [TopologicalSpace α] (F : Realizer α) {f : β → Set α} :
    LocallyFinite f ↔ Nonempty (LocallyFinite.Realizer F f) :=
  ⟨fun h =>
    let ⟨g, h₁⟩ := Classical.axiom_of_choice h
    let ⟨g₂, h₂⟩ :=
      Classical.axiom_of_choice fun x =>
        show ∃ b : F.σ, x ∈ F.f b ∧ F.f b ⊆ g x from
          let ⟨h, h'⟩ := h₁ x
          F.mem_nhds.1 h
    ⟨⟨fun x => ⟨g₂ x, (h₂ x).1⟩, fun x =>
        finite.fintype <|
          let ⟨h, h'⟩ := h₁ x
          h'.Subset fun i hi => hi.mono (inter_subset_inter_right _ (h₂ x).2)⟩⟩,
    fun ⟨R⟩ => R.to_locally_finite⟩

def Compact.Realizer [TopologicalSpace α] (R : Realizer α) (s : Set α) :=
  ∀ {f : Filter α} (F : f.Realizer) (x : F.σ), f ≠ ⊥ → F.f x ⊆ s → { a // a ∈ s ∧ 𝓝 a⊓f ≠ ⊥ }


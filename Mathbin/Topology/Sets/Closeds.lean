/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import Mathbin.Topology.Sets.Opens

/-!
# Closed sets

We define a few types of closed sets in a topological space.

## Main Definitions

For a topological space `α`,
* `closeds α`: The type of closed sets.
* `clopens α`: The type of clopen sets.
-/


open Order OrderDual Set

variable {ι α β : Type _} [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-! ### Closed sets -/


/-- The type of closed subsets of a topological space. -/
structure Closeds (α : Type _) [TopologicalSpace α] where
  Carrier : Set α
  closed' : IsClosed carrier

namespace Closeds

variable {α}

instance : SetLike (Closeds α) α where
  coe := Closeds.Carrier
  coe_injective' := fun s t h => by
    cases s
    cases t
    congr

theorem closed (s : Closeds α) : IsClosed (s : Set α) :=
  s.closed'

@[ext]
protected theorem ext {s t : Closeds α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl

/-- The closure of a set, as an element of `closeds`. -/
protected def closure (s : Set α) : Closeds α :=
  ⟨Closure s, is_closed_closure⟩

theorem gc : GaloisConnection Closeds.closure (coe : Closeds α → Set α) := fun s U =>
  ⟨subset_closure.trans, fun h => closure_minimal h U.closed⟩

/-- The galois coinsertion between sets and opens. -/
def gi : GaloisInsertion (@Closeds.closure α _) coe where
  choice := fun s hs => ⟨s, closure_eq_iff_is_closed.1 <| hs.antisymm subset_closure⟩
  gc := gc
  le_l_u := fun _ => subset_closure
  choice_eq := fun s hs => SetLike.coe_injective <| subset_closure.antisymm hs

instance : CompleteLattice (Closeds α) :=
  CompleteLattice.copy
    (GaloisInsertion.liftCompleteLattice gi)-- le
    _
    rfl-- top
    ⟨Univ, is_closed_univ⟩
    rfl-- bot
    ⟨∅, is_closed_empty⟩
    (SetLike.coe_injective closure_empty.symm)
    (-- sup
    fun s t => ⟨s ∪ t, s.2.union t.2⟩)
    (funext fun s => funext fun t => SetLike.coe_injective (s.2.union t.2).closure_eq.symm)
    (-- inf
    fun s t => ⟨s ∩ t, s.2.inter t.2⟩)
    rfl-- Sup
    _
    rfl
    (-- Inf
    fun S => ⟨⋂ s ∈ S, ↑s, is_closed_bInter fun s _ => s.2⟩)
    (funext fun S => SetLike.coe_injective Inf_image.symm)

/-- The type of closed sets is inhabited, with default element the empty set. -/
instance : Inhabited (Closeds α) :=
  ⟨⊥⟩

@[simp, norm_cast]
theorem coe_sup (s t : Closeds α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp, norm_cast]
theorem coe_inf (s t : Closeds α) : (↑(s⊓t) : Set α) = s ∩ t :=
  rfl

@[simp, norm_cast]
theorem coe_top : (↑(⊤ : Closeds α) : Set α) = univ :=
  rfl

@[simp, norm_cast]
theorem coe_bot : (↑(⊥ : Closeds α) : Set α) = ∅ :=
  rfl

@[simp, norm_cast]
theorem coe_Inf {S : Set (Closeds α)} : (↑(inf S) : Set α) = ⋂ i ∈ S, ↑i :=
  rfl

@[simp, norm_cast]
theorem coe_finset_sup (f : ι → Closeds α) (s : Finset ι) : (↑(s.sup f) : Set α) = s.sup (coe ∘ f) :=
  map_finset_sup (⟨⟨coe, coe_sup⟩, coe_bot⟩ : SupBotHom (Closeds α) (Set α)) _ _

@[simp, norm_cast]
theorem coe_finset_inf (f : ι → Closeds α) (s : Finset ι) : (↑(s.inf f) : Set α) = s.inf (coe ∘ f) :=
  map_finset_inf (⟨⟨coe, coe_inf⟩, coe_top⟩ : InfTopHom (Closeds α) (Set α)) _ _

theorem infi_def {ι} (s : ι → Closeds α) : (⨅ i, s i) = ⟨⋂ i, s i, is_closed_Inter fun i => (s i).2⟩ := by
  ext
  simp only [← infi, ← coe_Inf, ← bInter_range]
  rfl

@[simp]
theorem infi_mk {ι} (s : ι → Set α) (h : ∀ i, IsClosed (s i)) :
    (⨅ i, ⟨s i, h i⟩ : Closeds α) = ⟨⋂ i, s i, is_closed_Inter h⟩ := by
  simp [← infi_def]

@[simp, norm_cast]
theorem coe_infi {ι} (s : ι → Closeds α) : ((⨅ i, s i : Closeds α) : Set α) = ⋂ i, s i := by
  simp [← infi_def]

@[simp]
theorem mem_infi {ι} {x : α} {s : ι → Closeds α} : x ∈ infi s ↔ ∀ i, x ∈ s i := by
  simp [SetLike.mem_coe]

@[simp]
theorem mem_Inf {S : Set (Closeds α)} {x : α} : x ∈ inf S ↔ ∀, ∀ s ∈ S, ∀, x ∈ s := by
  simp_rw [Inf_eq_infi, mem_infi]

instance : Coframe (Closeds α) :=
  { Closeds.completeLattice with inf := inf,
    infi_sup_le_sup_Inf := fun a s =>
      (SetLike.coe_injective <| by
          simp only [← coe_sup, ← coe_infi, ← coe_Inf, ← Set.union_Inter₂]).le }

end Closeds

/-- The complement of a closed set as an open set. -/
@[simps]
def Closeds.compl (s : Closeds α) : Opens α :=
  ⟨sᶜ, s.2.is_open_compl⟩

/-- The complement of an open set as a closed set. -/
@[simps]
def Opens.compl (s : Opens α) : Closeds α :=
  ⟨sᶜ, s.2.is_closed_compl⟩

theorem Closeds.compl_compl (s : Closeds α) : s.compl.compl = s :=
  Closeds.ext (compl_compl s)

theorem Opens.compl_compl (s : Opens α) : s.compl.compl = s :=
  Opens.ext (compl_compl s)

theorem Closeds.compl_bijective : Function.Bijective (@Closeds.compl α _) :=
  Function.bijective_iff_has_inverse.mpr ⟨Opens.compl, Closeds.compl_compl, Opens.compl_compl⟩

theorem Opens.compl_bijective : Function.Bijective (@Opens.compl α _) :=
  Function.bijective_iff_has_inverse.mpr ⟨Closeds.compl, Opens.compl_compl, Closeds.compl_compl⟩

/-! ### Clopen sets -/


/-- The type of clopen sets of a topological space. -/
structure Clopens (α : Type _) [TopologicalSpace α] where
  Carrier : Set α
  clopen' : IsClopen carrier

namespace Clopens

instance : SetLike (Clopens α) α where
  coe := fun s => s.Carrier
  coe_injective' := fun s t h => by
    cases s
    cases t
    congr

theorem clopen (s : Clopens α) : IsClopen (s : Set α) :=
  s.clopen'

/-- Reinterpret a compact open as an open. -/
@[simps]
def toOpens (s : Clopens α) : Opens α :=
  ⟨s, s.clopen.IsOpen⟩

@[ext]
protected theorem ext {s t : Clopens α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl

instance : HasSup (Clopens α) :=
  ⟨fun s t => ⟨s ∪ t, s.clopen.union t.clopen⟩⟩

instance : HasInf (Clopens α) :=
  ⟨fun s t => ⟨s ∩ t, s.clopen.inter t.clopen⟩⟩

instance : HasTop (Clopens α) :=
  ⟨⟨⊤, is_clopen_univ⟩⟩

instance : HasBot (Clopens α) :=
  ⟨⟨⊥, is_clopen_empty⟩⟩

instance : HasSdiff (Clopens α) :=
  ⟨fun s t => ⟨s \ t, s.clopen.diff t.clopen⟩⟩

instance : HasCompl (Clopens α) :=
  ⟨fun s => ⟨sᶜ, s.clopen.compl⟩⟩

instance : BooleanAlgebra (Clopens α) :=
  SetLike.coe_injective.BooleanAlgebra _ (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (fun _ => rfl) fun _ _ => rfl

@[simp]
theorem coe_sup (s t : Clopens α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_inf (s t : Clopens α) : (↑(s⊓t) : Set α) = s ∩ t :=
  rfl

@[simp]
theorem coe_top : (↑(⊤ : Clopens α) : Set α) = univ :=
  rfl

@[simp]
theorem coe_bot : (↑(⊥ : Clopens α) : Set α) = ∅ :=
  rfl

@[simp]
theorem coe_sdiff (s t : Clopens α) : (↑(s \ t) : Set α) = s \ t :=
  rfl

@[simp]
theorem coe_compl (s : Clopens α) : (↑(sᶜ) : Set α) = sᶜ :=
  rfl

instance : Inhabited (Clopens α) :=
  ⟨⊥⟩

end Clopens

end TopologicalSpace


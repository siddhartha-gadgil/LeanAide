/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import Mathbin.Topology.Sets.Closeds

/-!
# Compact sets

We define a few types of compact sets in a topological space.

## Main Definitions

For a topological space `α`,
* `compacts α`: The type of compact sets.
* `nonempty_compacts α`: The type of non-empty compact sets.
* `positive_compacts α`: The type of compact sets with non-empty interior.
* `compact_opens α`: The type of compact open sets. This is a central object in the study of
  spectral spaces.
-/


open Set

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-! ### Compact sets -/


/-- The type of compact sets of a topological space. -/
structure Compacts (α : Type _) [TopologicalSpace α] where
  Carrier : Set α
  compact' : IsCompact carrier

namespace Compacts

variable {α}

instance : SetLike (Compacts α) α where
  coe := Compacts.Carrier
  coe_injective' := fun s t h => by
    cases s
    cases t
    congr

theorem compact (s : Compacts α) : IsCompact (s : Set α) :=
  s.compact'

instance (K : Compacts α) : CompactSpace K :=
  is_compact_iff_compact_space.1 K.compact

instance : CanLift (Set α) (Compacts α) where
  coe := coe
  cond := IsCompact
  prf := fun K hK => ⟨⟨K, hK⟩, rfl⟩

@[ext]
protected theorem ext {s t : Compacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl

@[simp]
theorem carrier_eq_coe (s : Compacts α) : s.Carrier = s :=
  rfl

instance : HasSup (Compacts α) :=
  ⟨fun s t => ⟨s ∪ t, s.compact.union t.compact⟩⟩

instance [T2Space α] : HasInf (Compacts α) :=
  ⟨fun s t => ⟨s ∩ t, s.compact.inter t.compact⟩⟩

instance [CompactSpace α] : HasTop (Compacts α) :=
  ⟨⟨Univ, compact_univ⟩⟩

instance : HasBot (Compacts α) :=
  ⟨⟨∅, is_compact_empty⟩⟩

instance : SemilatticeSup (Compacts α) :=
  SetLike.coe_injective.SemilatticeSup _ fun _ _ => rfl

instance [T2Space α] : DistribLattice (Compacts α) :=
  SetLike.coe_injective.DistribLattice _ (fun _ _ => rfl) fun _ _ => rfl

instance : OrderBot (Compacts α) :=
  OrderBot.lift (coe : _ → Set α) (fun _ _ => id) rfl

instance [CompactSpace α] : BoundedOrder (Compacts α) :=
  BoundedOrder.lift (coe : _ → Set α) (fun _ _ => id) rfl rfl

/-- The type of compact sets is inhabited, with default element the empty set. -/
instance : Inhabited (Compacts α) :=
  ⟨⊥⟩

@[simp]
theorem coe_sup (s t : Compacts α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_inf [T2Space α] (s t : Compacts α) : (↑(s⊓t) : Set α) = s ∩ t :=
  rfl

@[simp]
theorem coe_top [CompactSpace α] : (↑(⊤ : Compacts α) : Set α) = univ :=
  rfl

@[simp]
theorem coe_bot : (↑(⊥ : Compacts α) : Set α) = ∅ :=
  rfl

@[simp]
theorem coe_finset_sup {ι : Type _} {s : Finset ι} {f : ι → Compacts α} : (↑(s.sup f) : Set α) = s.sup fun i => f i :=
  by
  classical
  refine' Finset.induction_on s rfl fun a s _ h => _
  simp_rw [Finset.sup_insert, coe_sup, sup_eq_union]
  congr

/-- The image of a compact set under a continuous function. -/
protected def map (f : α → β) (hf : Continuous f) (K : Compacts α) : Compacts β :=
  ⟨f '' K.1, K.2.Image hf⟩

@[simp]
theorem coe_map {f : α → β} (hf : Continuous f) (s : Compacts α) : (s.map f hf : Set β) = f '' s :=
  rfl

/-- A homeomorphism induces an equivalence on compact sets, by taking the image. -/
@[simp]
protected def equiv (f : α ≃ₜ β) : Compacts α ≃ Compacts β where
  toFun := Compacts.map f f.Continuous
  invFun := Compacts.map _ f.symm.Continuous
  left_inv := fun s => by
    ext1
    simp only [← coe_map, image_comp, ← f.symm_comp_self, ← image_id]
  right_inv := fun s => by
    ext1
    simp only [← coe_map, image_comp, ← f.self_comp_symm, ← image_id]

/-- The image of a compact set under a homeomorphism can also be expressed as a preimage. -/
theorem equiv_to_fun_val (f : α ≃ₜ β) (K : Compacts α) : (Compacts.equiv f K).1 = f.symm ⁻¹' K.1 :=
  congr_fun (image_eq_preimage_of_inverse f.left_inv f.right_inv) K.1

/-- The product of two `compacts`, as a `compacts` in the product space. -/
protected def prod (K : Compacts α) (L : Compacts β) : Compacts (α × β) where
  Carrier := (K : Set α) ×ˢ (L : Set β)
  compact' := IsCompact.prod K.2 L.2

@[simp]
theorem coe_prod (K : Compacts α) (L : Compacts β) : (K.Prod L : Set (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

end Compacts

/-! ### Nonempty compact sets -/


/-- The type of nonempty compact sets of a topological space. -/
structure NonemptyCompacts (α : Type _) [TopologicalSpace α] extends Compacts α where
  nonempty' : carrier.Nonempty

namespace NonemptyCompacts

instance : SetLike (NonemptyCompacts α) α where
  coe := fun s => s.Carrier
  coe_injective' := fun s t h => by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

theorem compact (s : NonemptyCompacts α) : IsCompact (s : Set α) :=
  s.compact'

protected theorem nonempty (s : NonemptyCompacts α) : (s : Set α).Nonempty :=
  s.nonempty'

/-- Reinterpret a nonempty compact as a closed set. -/
def toCloseds [T2Space α] (s : NonemptyCompacts α) : Closeds α :=
  ⟨s, s.compact.IsClosed⟩

@[ext]
protected theorem ext {s t : NonemptyCompacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl

@[simp]
theorem carrier_eq_coe (s : NonemptyCompacts α) : s.Carrier = s :=
  rfl

instance : HasSup (NonemptyCompacts α) :=
  ⟨fun s t => ⟨s.toCompacts⊔t.toCompacts, s.Nonempty.mono <| subset_union_left _ _⟩⟩

instance [CompactSpace α] [Nonempty α] : HasTop (NonemptyCompacts α) :=
  ⟨⟨⊤, univ_nonempty⟩⟩

instance : SemilatticeSup (NonemptyCompacts α) :=
  SetLike.coe_injective.SemilatticeSup _ fun _ _ => rfl

instance [CompactSpace α] [Nonempty α] : OrderTop (NonemptyCompacts α) :=
  OrderTop.lift (coe : _ → Set α) (fun _ _ => id) rfl

@[simp]
theorem coe_sup (s t : NonemptyCompacts α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : NonemptyCompacts α) : Set α) = univ :=
  rfl

/-- In an inhabited space, the type of nonempty compact subsets is also inhabited, with
default element the singleton set containing the default element. -/
instance [Inhabited α] : Inhabited (NonemptyCompacts α) :=
  ⟨{ Carrier := {default}, compact' := is_compact_singleton, nonempty' := singleton_nonempty _ }⟩

instance to_compact_space {s : NonemptyCompacts α} : CompactSpace s :=
  is_compact_iff_compact_space.1 s.compact

instance to_nonempty {s : NonemptyCompacts α} : Nonempty s :=
  s.Nonempty.to_subtype

/-- The product of two `nonempty_compacts`, as a `nonempty_compacts` in the product space. -/
protected def prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) : NonemptyCompacts (α × β) :=
  { K.toCompacts.Prod L.toCompacts with nonempty' := K.Nonempty.Prod L.Nonempty }

@[simp]
theorem coe_prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) :
    (K.Prod L : Set (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

end NonemptyCompacts

/-! ### Positive compact sets -/


/-- The type of compact sets nonempty interior of a topological space. See also `compacts` and
`nonempty_compacts` -/
structure PositiveCompacts (α : Type _) [TopologicalSpace α] extends Compacts α where
  interior_nonempty' : (Interior carrier).Nonempty

namespace PositiveCompacts

instance : SetLike (PositiveCompacts α) α where
  coe := fun s => s.Carrier
  coe_injective' := fun s t h => by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

theorem compact (s : PositiveCompacts α) : IsCompact (s : Set α) :=
  s.compact'

theorem interior_nonempty (s : PositiveCompacts α) : (Interior (s : Set α)).Nonempty :=
  s.interior_nonempty'

protected theorem nonempty (s : PositiveCompacts α) : (s : Set α).Nonempty :=
  s.interior_nonempty.mono interior_subset

/-- Reinterpret a positive compact as a nonempty compact. -/
def toNonemptyCompacts (s : PositiveCompacts α) : NonemptyCompacts α :=
  ⟨s.toCompacts, s.Nonempty⟩

@[ext]
protected theorem ext {s t : PositiveCompacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl

@[simp]
theorem carrier_eq_coe (s : PositiveCompacts α) : s.Carrier = s :=
  rfl

instance : HasSup (PositiveCompacts α) :=
  ⟨fun s t => ⟨s.toCompacts⊔t.toCompacts, s.interior_nonempty.mono <| interior_mono <| subset_union_left _ _⟩⟩

instance [CompactSpace α] [Nonempty α] : HasTop (PositiveCompacts α) :=
  ⟨⟨⊤, interior_univ.symm.subst univ_nonempty⟩⟩

instance : SemilatticeSup (PositiveCompacts α) :=
  SetLike.coe_injective.SemilatticeSup _ fun _ _ => rfl

instance [CompactSpace α] [Nonempty α] : OrderTop (PositiveCompacts α) :=
  OrderTop.lift (coe : _ → Set α) (fun _ _ => id) rfl

@[simp]
theorem coe_sup (s t : PositiveCompacts α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : PositiveCompacts α) : Set α) = univ :=
  rfl

theorem _root_.exists_positive_compacts_subset [LocallyCompactSpace α] {U : Set α} (ho : IsOpen U) (hn : U.Nonempty) :
    ∃ K : PositiveCompacts α, ↑K ⊆ U :=
  let ⟨x, hx⟩ := hn
  let ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset ho hx
  ⟨⟨⟨K, hKc⟩, ⟨x, hxK⟩⟩, hKU⟩

instance [CompactSpace α] [Nonempty α] : Inhabited (PositiveCompacts α) :=
  ⟨⊤⟩

/-- In a nonempty locally compact space, there exists a compact set with nonempty interior. -/
instance nonempty' [LocallyCompactSpace α] [Nonempty α] : Nonempty (PositiveCompacts α) :=
  nonempty_of_exists <| exists_positive_compacts_subset is_open_univ univ_nonempty

/-- The product of two `positive_compacts`, as a `positive_compacts` in the product space. -/
protected def prod (K : PositiveCompacts α) (L : PositiveCompacts β) : PositiveCompacts (α × β) :=
  { K.toCompacts.Prod L.toCompacts with
    interior_nonempty' := by
      simp only [← compacts.carrier_eq_coe, ← compacts.coe_prod, ← interior_prod_eq]
      exact K.interior_nonempty.prod L.interior_nonempty }

@[simp]
theorem coe_prod (K : PositiveCompacts α) (L : PositiveCompacts β) :
    (K.Prod L : Set (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

end PositiveCompacts

/-! ### Compact open sets -/


/-- The type of compact open sets of a topological space. This is useful in non Hausdorff contexts,
in particular spectral spaces. -/
structure CompactOpens (α : Type _) [TopologicalSpace α] extends Compacts α where
  open' : IsOpen carrier

namespace CompactOpens

instance : SetLike (CompactOpens α) α where
  coe := fun s => s.Carrier
  coe_injective' := fun s t h => by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

theorem compact (s : CompactOpens α) : IsCompact (s : Set α) :=
  s.compact'

theorem open (s : CompactOpens α) : IsOpen (s : Set α) :=
  s.open'

/-- Reinterpret a compact open as an open. -/
@[simps]
def toOpens (s : CompactOpens α) : Opens α :=
  ⟨s, s.open⟩

/-- Reinterpret a compact open as a clopen. -/
@[simps]
def toClopens [T2Space α] (s : CompactOpens α) : Clopens α :=
  ⟨s, s.open, s.compact.IsClosed⟩

@[ext]
protected theorem ext {s t : CompactOpens α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl

instance : HasSup (CompactOpens α) :=
  ⟨fun s t => ⟨s.toCompacts⊔t.toCompacts, s.open.union t.open⟩⟩

instance [T2Space α] : HasInf (CompactOpens α) :=
  ⟨fun s t => ⟨s.toCompacts⊓t.toCompacts, s.open.inter t.open⟩⟩

instance [CompactSpace α] : HasTop (CompactOpens α) :=
  ⟨⟨⊤, is_open_univ⟩⟩

instance : HasBot (CompactOpens α) :=
  ⟨⟨⊥, is_open_empty⟩⟩

instance [T2Space α] : HasSdiff (CompactOpens α) :=
  ⟨fun s t => ⟨⟨s \ t, s.compact.diff t.open⟩, s.open.sdiff t.compact.IsClosed⟩⟩

instance [T2Space α] [CompactSpace α] : HasCompl (CompactOpens α) :=
  ⟨fun s => ⟨⟨sᶜ, s.open.is_closed_compl.IsCompact⟩, s.compact.IsClosed.is_open_compl⟩⟩

instance : SemilatticeSup (CompactOpens α) :=
  SetLike.coe_injective.SemilatticeSup _ fun _ _ => rfl

instance : OrderBot (CompactOpens α) :=
  OrderBot.lift (coe : _ → Set α) (fun _ _ => id) rfl

instance [T2Space α] : GeneralizedBooleanAlgebra (CompactOpens α) :=
  SetLike.coe_injective.GeneralizedBooleanAlgebra _ (fun _ _ => rfl) (fun _ _ => rfl) rfl fun _ _ => rfl

instance [CompactSpace α] : BoundedOrder (CompactOpens α) :=
  BoundedOrder.lift (coe : _ → Set α) (fun _ _ => id) rfl rfl

instance [T2Space α] [CompactSpace α] : BooleanAlgebra (CompactOpens α) :=
  SetLike.coe_injective.BooleanAlgebra _ (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (fun _ => rfl) fun _ _ => rfl

@[simp]
theorem coe_sup (s t : CompactOpens α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_inf [T2Space α] (s t : CompactOpens α) : (↑(s⊓t) : Set α) = s ∩ t :=
  rfl

@[simp]
theorem coe_top [CompactSpace α] : (↑(⊤ : CompactOpens α) : Set α) = univ :=
  rfl

@[simp]
theorem coe_bot : (↑(⊥ : CompactOpens α) : Set α) = ∅ :=
  rfl

@[simp]
theorem coe_sdiff [T2Space α] (s t : CompactOpens α) : (↑(s \ t) : Set α) = s \ t :=
  rfl

@[simp]
theorem coe_compl [T2Space α] [CompactSpace α] (s : CompactOpens α) : (↑(sᶜ) : Set α) = sᶜ :=
  rfl

instance : Inhabited (CompactOpens α) :=
  ⟨⊥⟩

/-- The image of a compact open under a continuous open map. -/
@[simps]
def map (f : α → β) (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α) : CompactOpens β :=
  ⟨s.toCompacts.map f hf, hf' _ s.open⟩

@[simp]
theorem coe_map {f : α → β} (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α) :
    (s.map f hf hf' : Set β) = f '' s :=
  rfl

/-- The product of two `compact_opens`, as a `compact_opens` in the product space. -/
protected def prod (K : CompactOpens α) (L : CompactOpens β) : CompactOpens (α × β) :=
  { K.toCompacts.Prod L.toCompacts with open' := K.open.Prod L.open }

@[simp]
theorem coe_prod (K : CompactOpens α) (L : CompactOpens β) : (K.Prod L : Set (α × β)) = (K : Set α) ×ˢ (L : Set β) :=
  rfl

end CompactOpens

end TopologicalSpace


/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
import Mathbin.Order.CompleteLattice
import Mathbin.Order.Directed

/-!
# Frames, completely distributive lattices and Boolean algebras

In this file we define and provide API for frames, completely distributive lattices and completely
distributive Boolean algebras.

## Typeclasses

* `order.frame`: Frame: A complete lattice whose `⊓` distributes over `⨆`.
* `order.coframe`: Coframe: A complete lattice whose `⊔` distributes over `⨅`.
* `complete_distrib_lattice`: Completely distributive lattices: A complete lattice whose `⊓` and `⊔`
  distribute over `⨆` and `⨅` respectively.
* `complete_boolean_algebra`: Completely distributive Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.

A set of opens gives rise to a topological space precisely if it forms a frame. Such a frame is also
completely distributive, but not all frames are. `filter` is a coframe but not a completely
distributive lattice.

## TODO

Add instances for `prod`

## References

* [Wikipedia, *Complete Heyting algebra*](https://en.wikipedia.org/wiki/Complete_Heyting_algebra)
* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/


open Function Set

universe u v w

variable {α : Type u} {β : Type v} {ι : Sort w} {κ : ι → Sort _}

/-- A frame, aka complete Heyting algebra, is a complete lattice whose `⊓` distributes over `⨆`. -/
class Order.Frame (α : Type _) extends CompleteLattice α where
  inf_Sup_le_supr_inf (a : α) (s : Set α) : a⊓Sup s ≤ ⨆ b ∈ s, a⊓b

/-- A coframe, aka complete Brouwer algebra or complete co-Heyting algebra, is a complete lattice
whose `⊔` distributes over `⨅`. -/
class Order.Coframe (α : Type _) extends CompleteLattice α where
  infi_sup_le_sup_Inf (a : α) (s : Set α) : (⨅ b ∈ s, a⊔b) ≤ a⊔Inf s

open Order

/-- A completely distributive lattice is a complete lattice whose `⊔` and `⊓` respectively
distribute over `⨅` and `⨆`. -/
class CompleteDistribLattice (α : Type _) extends Frame α where
  infi_sup_le_sup_Inf : ∀ a s, (⨅ b ∈ s, a⊔b) ≤ a⊔Inf s

-- See note [lower instance priority]
instance (priority := 100) CompleteDistribLattice.toCoframe [CompleteDistribLattice α] : Coframe α :=
  { ‹CompleteDistribLattice α› with }

section Frame

variable [Frame α] {s t : Set α} {a b : α}

instance OrderDual.coframe : Coframe αᵒᵈ :=
  { OrderDual.completeLattice α with infi_sup_le_sup_Inf := Frame.inf_Sup_le_supr_inf }

theorem inf_Sup_eq : a⊓sup s = ⨆ b ∈ s, a⊓b :=
  (Frame.inf_Sup_le_supr_inf _ _).antisymm supr_inf_le_inf_Sup

theorem Sup_inf_eq : sup s⊓b = ⨆ a ∈ s, a⊓b := by
  simpa only [← inf_comm] using @inf_Sup_eq α _ s b

theorem supr_inf_eq (f : ι → α) (a : α) : (⨆ i, f i)⊓a = ⨆ i, f i⊓a := by
  rw [supr, Sup_inf_eq, supr_range]

theorem inf_supr_eq (a : α) (f : ι → α) : (a⊓⨆ i, f i) = ⨆ i, a⊓f i := by
  simpa only [← inf_comm] using supr_inf_eq f a

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem bsupr_inf_eq {f : ∀ i, κ i → α} (a : α) : (⨆ (i) (j), f i j)⊓a = ⨆ (i) (j), f i j⊓a := by
  simp only [← supr_inf_eq]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem inf_bsupr_eq {f : ∀ i, κ i → α} (a : α) : (a⊓⨆ (i) (j), f i j) = ⨆ (i) (j), a⊓f i j := by
  simp only [← inf_supr_eq]

theorem supr_inf_supr {ι ι' : Type _} {f : ι → α} {g : ι' → α} : ((⨆ i, f i)⊓⨆ j, g j) = ⨆ i : ι × ι', f i.1⊓g i.2 := by
  simp only [← inf_supr_eq, ← supr_inf_eq, ← supr_prod]

theorem bsupr_inf_bsupr {ι ι' : Type _} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨆ i ∈ s, f i)⊓⨆ j ∈ t, g j) = ⨆ p ∈ s ×ˢ t, f (p : ι × ι').1⊓g p.2 := by
  simp only [← supr_subtype', ← supr_inf_supr]
  exact (Equivₓ.surjective _).supr_congr (Equivₓ.Set.prod s t).symm fun x => rfl

theorem Sup_inf_Sup : sup s⊓sup t = ⨆ p ∈ s ×ˢ t, (p : α × α).1⊓p.2 := by
  simp only [← Sup_eq_supr, ← bsupr_inf_bsupr]

theorem supr_disjoint_iff {f : ι → α} : Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp only [← disjoint_iff, ← supr_inf_eq, ← supr_eq_bot]

theorem disjoint_supr_iff {f : ι → α} : Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simpa only [← Disjoint.comm] using supr_disjoint_iff

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem supr₂_disjoint_iff {f : ∀ i, κ i → α} : Disjoint (⨆ (i) (j), f i j) a ↔ ∀ i j, Disjoint (f i j) a := by
  simp_rw [supr_disjoint_iff]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem disjoint_supr₂_iff {f : ∀ i, κ i → α} : Disjoint a (⨆ (i) (j), f i j) ↔ ∀ i j, Disjoint a (f i j) := by
  simp_rw [disjoint_supr_iff]

theorem Sup_disjoint_iff {s : Set α} : Disjoint (sup s) a ↔ ∀, ∀ b ∈ s, ∀, Disjoint b a := by
  simp only [← disjoint_iff, ← Sup_inf_eq, ← supr_eq_bot]

theorem disjoint_Sup_iff {s : Set α} : Disjoint a (sup s) ↔ ∀, ∀ b ∈ s, ∀, Disjoint a b := by
  simpa only [← Disjoint.comm] using Sup_disjoint_iff

theorem supr_inf_of_monotone {ι : Type _} [Preorderₓ ι] [IsDirected ι (· ≤ ·)] {f g : ι → α} (hf : Monotone f)
    (hg : Monotone g) : (⨆ i, f i⊓g i) = (⨆ i, f i)⊓⨆ i, g i := by
  refine' (le_supr_inf_supr f g).antisymm _
  rw [supr_inf_supr]
  refine' supr_mono' fun i => _
  rcases directed_of (· ≤ ·) i.1 i.2 with ⟨j, h₁, h₂⟩
  exact ⟨j, inf_le_inf (hf h₁) (hg h₂)⟩

theorem supr_inf_of_antitone {ι : Type _} [Preorderₓ ι] [IsDirected ι (swap (· ≤ ·))] {f g : ι → α} (hf : Antitone f)
    (hg : Antitone g) : (⨆ i, f i⊓g i) = (⨆ i, f i)⊓⨆ i, g i :=
  @supr_inf_of_monotone α _ ιᵒᵈ _ _ f g hf.dual_left hg.dual_left

instance Pi.frame {ι : Type _} {π : ι → Type _} [∀ i, Frame (π i)] : Frame (∀ i, π i) :=
  { Pi.completeLattice with
    inf_Sup_le_supr_inf := fun a s i => by
      simp only [← CompleteLattice.supₓ, ← Sup_apply, ← supr_apply, ← Pi.inf_apply, ← inf_supr_eq, supr_subtype''] }

-- see Note [lower instance priority]
instance (priority := 100) Frame.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    rw [← Sup_pair, ← Sup_pair, inf_Sup_eq, ← Sup_image, image_pair]

end Frame

section Coframe

variable [Coframe α] {s t : Set α} {a b : α}

instance OrderDual.frame : Frame αᵒᵈ :=
  { OrderDual.completeLattice α with inf_Sup_le_supr_inf := Coframe.infi_sup_le_sup_Inf }

theorem sup_Inf_eq : a⊔inf s = ⨅ b ∈ s, a⊔b :=
  @inf_Sup_eq αᵒᵈ _ _ _

theorem Inf_sup_eq : inf s⊔b = ⨅ a ∈ s, a⊔b :=
  @Sup_inf_eq αᵒᵈ _ _ _

theorem infi_sup_eq (f : ι → α) (a : α) : (⨅ i, f i)⊔a = ⨅ i, f i⊔a :=
  @supr_inf_eq αᵒᵈ _ _ _ _

theorem sup_infi_eq (a : α) (f : ι → α) : (a⊔⨅ i, f i) = ⨅ i, a⊔f i :=
  @inf_supr_eq αᵒᵈ _ _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem binfi_sup_eq {f : ∀ i, κ i → α} (a : α) : (⨅ (i) (j), f i j)⊔a = ⨅ (i) (j), f i j⊔a :=
  @bsupr_inf_eq αᵒᵈ _ _ _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem sup_binfi_eq {f : ∀ i, κ i → α} (a : α) : (a⊔⨅ (i) (j), f i j) = ⨅ (i) (j), a⊔f i j :=
  @inf_bsupr_eq αᵒᵈ _ _ _ _ _

theorem infi_sup_infi {ι ι' : Type _} {f : ι → α} {g : ι' → α} : ((⨅ i, f i)⊔⨅ i, g i) = ⨅ i : ι × ι', f i.1⊔g i.2 :=
  @supr_inf_supr αᵒᵈ _ _ _ _ _

theorem binfi_sup_binfi {ι ι' : Type _} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨅ i ∈ s, f i)⊔⨅ j ∈ t, g j) = ⨅ p ∈ s ×ˢ t, f (p : ι × ι').1⊔g p.2 :=
  @bsupr_inf_bsupr αᵒᵈ _ _ _ _ _ _ _

theorem Inf_sup_Inf : inf s⊔inf t = ⨅ p ∈ s ×ˢ t, (p : α × α).1⊔p.2 :=
  @Sup_inf_Sup αᵒᵈ _ _ _

theorem infi_sup_of_monotone {ι : Type _} [Preorderₓ ι] [IsDirected ι (swap (· ≤ ·))] {f g : ι → α} (hf : Monotone f)
    (hg : Monotone g) : (⨅ i, f i⊔g i) = (⨅ i, f i)⊔⨅ i, g i :=
  supr_inf_of_antitone hf.dual_right hg.dual_right

theorem infi_sup_of_antitone {ι : Type _} [Preorderₓ ι] [IsDirected ι (· ≤ ·)] {f g : ι → α} (hf : Antitone f)
    (hg : Antitone g) : (⨅ i, f i⊔g i) = (⨅ i, f i)⊔⨅ i, g i :=
  supr_inf_of_monotone hf.dual_right hg.dual_right

instance Pi.coframe {ι : Type _} {π : ι → Type _} [∀ i, Coframe (π i)] : Coframe (∀ i, π i) :=
  { Pi.completeLattice with inf := inf,
    infi_sup_le_sup_Inf := fun a s i => by
      simp only [sup_infi_eq, ← Inf_apply, infi_subtype'', ← infi_apply, ← Pi.sup_apply] }

-- see Note [lower instance priority]
instance (priority := 100) Coframe.toDistribLattice : DistribLattice α :=
  { ‹Coframe α› with
    le_sup_inf := fun a b c => by
      rw [← Inf_pair, ← Inf_pair, sup_Inf_eq, ← Inf_image, image_pair] }

end Coframe

section CompleteDistribLattice

variable [CompleteDistribLattice α] {a b : α} {s t : Set α}

instance : CompleteDistribLattice αᵒᵈ :=
  { OrderDual.frame, OrderDual.coframe with }

instance Pi.completeDistribLattice {ι : Type _} {π : ι → Type _} [∀ i, CompleteDistribLattice (π i)] :
    CompleteDistribLattice (∀ i, π i) :=
  { Pi.frame, Pi.coframe with }

end CompleteDistribLattice

/-- A complete Boolean algebra is a completely distributive Boolean algebra. -/
class CompleteBooleanAlgebra (α) extends BooleanAlgebra α, CompleteDistribLattice α

instance Pi.completeBooleanAlgebra {ι : Type _} {π : ι → Type _} [∀ i, CompleteBooleanAlgebra (π i)] :
    CompleteBooleanAlgebra (∀ i, π i) :=
  { Pi.booleanAlgebra, Pi.completeDistribLattice with }

instance Prop.completeBooleanAlgebra : CompleteBooleanAlgebra Prop :=
  { Prop.booleanAlgebra, Prop.completeLattice with
    infi_sup_le_sup_Inf := fun p s =>
      Iff.mp <| by
        simp only [← forall_or_distrib_left, ← CompleteLattice.infₓ, ← infi_Prop_eq, ← sup_Prop_eq],
    inf_Sup_le_supr_inf := fun p s =>
      Iff.mp <| by
        simp only [← CompleteLattice.supₓ, ← exists_and_distrib_left, ← inf_Prop_eq, ← supr_Prop_eq] }

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] {a b : α} {s : Set α} {f : ι → α}

theorem compl_infi : infi fᶜ = ⨆ i, f iᶜ :=
  le_antisymmₓ (compl_le_of_compl_le <| le_infi fun i => compl_le_of_compl_le <| le_supr (compl ∘ f) i)
    (supr_le fun i => compl_le_compl <| infi_le _ _)

theorem compl_supr : supr fᶜ = ⨅ i, f iᶜ :=
  compl_injective
    (by
      simp [← compl_infi])

theorem compl_Inf : inf sᶜ = ⨆ i ∈ s, iᶜ := by
  simp only [← Inf_eq_infi, ← compl_infi]

theorem compl_Sup : sup sᶜ = ⨅ i ∈ s, iᶜ := by
  simp only [← Sup_eq_supr, ← compl_supr]

theorem compl_Inf' : inf sᶜ = sup (compl '' s) :=
  compl_Inf.trans Sup_image.symm

theorem compl_Sup' : sup sᶜ = inf (compl '' s) :=
  compl_Sup.trans Inf_image.symm

end CompleteBooleanAlgebra

section lift

/-- Pullback an `order.frame` along an injection. -/
-- See note [reducible non-instances]
@[reducible]
protected def Function.Injective.frame [HasSup α] [HasInf α] [HasSupₓ α] [HasInfₓ α] [HasTop α] [HasBot α] [Frame β]
    (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a⊔b) = f a⊔f b) (map_inf : ∀ a b, f (a⊓b) = f a⊓f b)
    (map_Sup : ∀ s, f (sup s) = ⨆ a ∈ s, f a) (map_Inf : ∀ s, f (inf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤)
    (map_bot : f ⊥ = ⊥) : Frame α :=
  { hf.CompleteLattice f map_sup map_inf map_Sup map_Inf map_top map_bot with
    inf_Sup_le_supr_inf := fun a s => by
      change f (a⊓Sup s) ≤ f _
      rw [← Sup_image, map_inf, map_Sup s, inf_bsupr_eq]
      simp_rw [← map_inf]
      exact ((map_Sup _).trans supr_image).Ge }

/-- Pullback an `order.coframe` along an injection. -/
-- See note [reducible non-instances]
@[reducible]
protected def Function.Injective.coframe [HasSup α] [HasInf α] [HasSupₓ α] [HasInfₓ α] [HasTop α] [HasBot α] [Coframe β]
    (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a⊔b) = f a⊔f b) (map_inf : ∀ a b, f (a⊓b) = f a⊓f b)
    (map_Sup : ∀ s, f (sup s) = ⨆ a ∈ s, f a) (map_Inf : ∀ s, f (inf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤)
    (map_bot : f ⊥ = ⊥) : Coframe α :=
  { hf.CompleteLattice f map_sup map_inf map_Sup map_Inf map_top map_bot with
    infi_sup_le_sup_Inf := fun a s => by
      change f _ ≤ f (a⊔Inf s)
      rw [← Inf_image, map_sup, map_Inf s, sup_binfi_eq]
      simp_rw [← map_sup]
      exact ((map_Inf _).trans infi_image).le }

/-- Pullback a `complete_distrib_lattice` along an injection. -/
-- See note [reducible non-instances]
@[reducible]
protected def Function.Injective.completeDistribLattice [HasSup α] [HasInf α] [HasSupₓ α] [HasInfₓ α] [HasTop α]
    [HasBot α] [CompleteDistribLattice β] (f : α → β) (hf : Function.Injective f) (map_sup : ∀ a b, f (a⊔b) = f a⊔f b)
    (map_inf : ∀ a b, f (a⊓b) = f a⊓f b) (map_Sup : ∀ s, f (sup s) = ⨆ a ∈ s, f a)
    (map_Inf : ∀ s, f (inf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteDistribLattice α :=
  { hf.Frame f map_sup map_inf map_Sup map_Inf map_top map_bot,
    hf.Coframe f map_sup map_inf map_Sup map_Inf map_top map_bot with }

/-- Pullback a `complete_boolean_algebra` along an injection. -/
-- See note [reducible non-instances]
@[reducible]
protected def Function.Injective.completeBooleanAlgebra [HasSup α] [HasInf α] [HasSupₓ α] [HasInfₓ α] [HasTop α]
    [HasBot α] [HasCompl α] [HasSdiff α] [CompleteBooleanAlgebra β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a⊔b) = f a⊔f b) (map_inf : ∀ a b, f (a⊓b) = f a⊓f b) (map_Sup : ∀ s, f (sup s) = ⨆ a ∈ s, f a)
    (map_Inf : ∀ s, f (inf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f (aᶜ) = f aᶜ)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) : CompleteBooleanAlgebra α :=
  { hf.CompleteDistribLattice f map_sup map_inf map_Sup map_Inf map_top map_bot,
    hf.BooleanAlgebra f map_sup map_inf map_top map_bot map_compl map_sdiff with }

end lift


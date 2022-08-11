/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Order.CompleteBooleanAlgebra
import Mathbin.Order.Cover
import Mathbin.Order.ModularLattice
import Mathbin.Data.Fintype.Basic

/-!
# Atoms, Coatoms, and Simple Lattices

This module defines atoms, which are minimal non-`⊥` elements in bounded lattices, simple lattices,
which are lattices with only two elements, and related ideas.

## Main definitions

### Atoms and Coatoms
  * `is_atom a` indicates that the only element below `a` is `⊥`.
  * `is_coatom a` indicates that the only element above `a` is `⊤`.

### Atomic and Atomistic Lattices
  * `is_atomic` indicates that every element other than `⊥` is above an atom.
  * `is_coatomic` indicates that every element other than `⊤` is below a coatom.
  * `is_atomistic` indicates that every element is the `Sup` of a set of atoms.
  * `is_coatomistic` indicates that every element is the `Inf` of a set of coatoms.

### Simple Lattices
  * `is_simple_order` indicates that an order has only two unique elements, `⊥` and `⊤`.
  * `is_simple_order.bounded_order`
  * `is_simple_order.distrib_lattice`
  * Given an instance of `is_simple_order`, we provide the following definitions. These are not
    made global instances as they contain data :
    * `is_simple_order.boolean_algebra`
    * `is_simple_order.complete_lattice`
    * `is_simple_order.complete_boolean_algebra`

## Main results
  * `is_atom_dual_iff_is_coatom` and `is_coatom_dual_iff_is_atom` express the (definitional) duality
   of `is_atom` and `is_coatom`.
  * `is_simple_order_iff_is_atom_top` and `is_simple_order_iff_is_coatom_bot` express the
  connection between atoms, coatoms, and simple lattices
  * `is_compl.is_atom_iff_is_coatom` and `is_compl.is_coatom_if_is_atom`: In a modular
  bounded lattice, a complement of an atom is a coatom and vice versa.
  * `is_atomic_iff_is_coatomic`: A modular complemented lattice is atomic iff it is coatomic.
  * `fintype.to_is_atomic`, `fintype.to_is_coatomic`: Finite partial orders with bottom resp. top
    are atomic resp. coatomic.

-/


variable {α : Type _}

section Atoms

section IsAtom

section Preorderₓ

variable [Preorderₓ α] [OrderBot α] {a b x : α}

/-- An atom of an `order_bot` is an element with no other element between it and `⊥`,
  which is not `⊥`. -/
def IsAtom (a : α) : Prop :=
  a ≠ ⊥ ∧ ∀ b, b < a → b = ⊥

theorem IsAtom.Iic (ha : IsAtom a) (hax : a ≤ x) : IsAtom (⟨a, hax⟩ : Set.Iic x) :=
  ⟨fun con => ha.1 (Subtype.mk_eq_mk.1 con), fun ⟨b, hb⟩ hba => Subtype.mk_eq_mk.2 (ha.2 b hba)⟩

theorem IsAtom.of_is_atom_coe_Iic {a : Set.Iic x} (ha : IsAtom a) : IsAtom (a : α) :=
  ⟨fun con => ha.1 (Subtype.ext con), fun b hba => Subtype.mk_eq_mk.1 (ha.2 ⟨b, hba.le.trans a.Prop⟩ hba)⟩

end Preorderₓ

variable [PartialOrderₓ α] [OrderBot α] {a b x : α}

theorem IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥ :=
  ⟨h.2 x, fun hx => hx.symm ▸ h.1.bot_lt⟩

theorem IsAtom.le_iff (h : IsAtom a) : x ≤ a ↔ x = ⊥ ∨ x = a := by
  rw [le_iff_lt_or_eqₓ, h.lt_iff]

theorem IsAtom.Iic_eq (h : IsAtom a) : Set.Iic a = {⊥, a} :=
  Set.ext fun x => h.le_iff

@[simp]
theorem bot_covby_iff : ⊥ ⋖ a ↔ IsAtom a := by
  simp only [← Covby, ← bot_lt_iff_ne_bot, ← IsAtom, ← not_imp_not]

alias bot_covby_iff ↔ Covby.is_atom IsAtom.bot_covby

end IsAtom

section IsCoatom

section Preorderₓ

variable [Preorderₓ α]

/-- A coatom of an `order_top` is an element with no other element between it and `⊤`,
  which is not `⊤`. -/
def IsCoatom [OrderTop α] (a : α) : Prop :=
  a ≠ ⊤ ∧ ∀ b, a < b → b = ⊤

@[simp]
theorem is_coatom_dual_iff_is_atom [OrderBot α] {a : α} : IsCoatom (OrderDual.toDual a) ↔ IsAtom a :=
  Iff.rfl

@[simp]
theorem is_atom_dual_iff_is_coatom [OrderTop α] {a : α} : IsAtom (OrderDual.toDual a) ↔ IsCoatom a :=
  Iff.rfl

alias is_coatom_dual_iff_is_atom ↔ _ IsAtom.dual

alias is_atom_dual_iff_is_coatom ↔ _ IsCoatom.dual

variable [OrderTop α] {a x : α}

theorem IsCoatom.Ici (ha : IsCoatom a) (hax : x ≤ a) : IsCoatom (⟨a, hax⟩ : Set.Ici x) :=
  ha.dual.Iic hax

theorem IsCoatom.of_is_coatom_coe_Ici {a : Set.Ici x} (ha : IsCoatom a) : IsCoatom (a : α) :=
  @IsAtom.of_is_atom_coe_Iic αᵒᵈ _ _ x a ha

end Preorderₓ

variable [PartialOrderₓ α] [OrderTop α] {a b x : α}

theorem IsCoatom.lt_iff (h : IsCoatom a) : a < x ↔ x = ⊤ :=
  h.dual.lt_iff

theorem IsCoatom.le_iff (h : IsCoatom a) : a ≤ x ↔ x = ⊤ ∨ x = a :=
  h.dual.le_iff

theorem IsCoatom.Ici_eq (h : IsCoatom a) : Set.Ici a = {⊤, a} :=
  h.dual.Iic_eq

@[simp]
theorem covby_top_iff : a ⋖ ⊤ ↔ IsCoatom a :=
  to_dual_covby_to_dual_iff.symm.trans bot_covby_iff

alias covby_top_iff ↔ Covby.is_coatom IsCoatom.covby_top

end IsCoatom

section Pairwise

theorem IsAtom.inf_eq_bot_of_ne [SemilatticeInf α] [OrderBot α] {a b : α} (ha : IsAtom a) (hb : IsAtom b)
    (hab : a ≠ b) : a⊓b = ⊥ :=
  hab.not_le_or_not_le.elim (ha.lt_iff.1 ∘ inf_lt_left.2) (hb.lt_iff.1 ∘ inf_lt_right.2)

theorem IsAtom.disjoint_of_ne [SemilatticeInf α] [OrderBot α] {a b : α} (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    Disjoint a b :=
  disjoint_iff.mpr (IsAtom.inf_eq_bot_of_ne ha hb hab)

theorem IsCoatom.sup_eq_top_of_ne [SemilatticeSup α] [OrderTop α] {a b : α} (ha : IsCoatom a) (hb : IsCoatom b)
    (hab : a ≠ b) : a⊔b = ⊤ :=
  ha.dual.inf_eq_bot_of_ne hb.dual hab

end Pairwise

end Atoms

section Atomic

variable [PartialOrderₓ α] (α)

/-- A lattice is atomic iff every element other than `⊥` has an atom below it. -/
class IsAtomic [OrderBot α] : Prop where
  eq_bot_or_exists_atom_le : ∀ b : α, b = ⊥ ∨ ∃ a : α, IsAtom a ∧ a ≤ b

/-- A lattice is coatomic iff every element other than `⊤` has a coatom above it. -/
class IsCoatomic [OrderTop α] : Prop where
  eq_top_or_exists_le_coatom : ∀ b : α, b = ⊤ ∨ ∃ a : α, IsCoatom a ∧ b ≤ a

export IsAtomic (eq_bot_or_exists_atom_le)

export IsCoatomic (eq_top_or_exists_le_coatom)

variable {α}

@[simp]
theorem is_coatomic_dual_iff_is_atomic [OrderBot α] : IsCoatomic αᵒᵈ ↔ IsAtomic α :=
  ⟨fun h =>
    ⟨fun b => by
      apply h.eq_top_or_exists_le_coatom⟩,
    fun h =>
    ⟨fun b => by
      apply h.eq_bot_or_exists_atom_le⟩⟩

@[simp]
theorem is_atomic_dual_iff_is_coatomic [OrderTop α] : IsAtomic αᵒᵈ ↔ IsCoatomic α :=
  ⟨fun h =>
    ⟨fun b => by
      apply h.eq_bot_or_exists_atom_le⟩,
    fun h =>
    ⟨fun b => by
      apply h.eq_top_or_exists_le_coatom⟩⟩

namespace IsAtomic

variable [OrderBot α] [IsAtomic α]

instance is_coatomic_dual : IsCoatomic αᵒᵈ :=
  is_coatomic_dual_iff_is_atomic.2 ‹IsAtomic α›

instance {x : α} : IsAtomic (Set.Iic x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_bot_or_exists_atom_le y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, hay.trans hy⟩, ha.Iic (hay.trans hy), hay⟩⟩

end IsAtomic

namespace IsCoatomic

variable [OrderTop α] [IsCoatomic α]

instance is_coatomic : IsAtomic αᵒᵈ :=
  is_atomic_dual_iff_is_coatomic.2 ‹IsCoatomic α›

instance {x : α} : IsCoatomic (Set.Ici x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_top_or_exists_le_coatom y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, le_transₓ hy hay⟩, ha.Ici (le_transₓ hy hay), hay⟩⟩

end IsCoatomic

theorem is_atomic_iff_forall_is_atomic_Iic [OrderBot α] : IsAtomic α ↔ ∀ x : α, IsAtomic (Set.Iic x) :=
  ⟨@IsAtomic.Set.Iic.is_atomic _ _ _, fun h =>
    ⟨fun x =>
      ((@eq_bot_or_exists_atom_le _ _ _ (h x)) (⊤ : Set.Iic x)).imp Subtype.mk_eq_mk.1
        (exists_imp_exists' coe fun ⟨a, ha⟩ => And.imp_left IsAtom.of_is_atom_coe_Iic)⟩⟩

theorem is_coatomic_iff_forall_is_coatomic_Ici [OrderTop α] : IsCoatomic α ↔ ∀ x : α, IsCoatomic (Set.Ici x) :=
  is_atomic_dual_iff_is_coatomic.symm.trans <|
    is_atomic_iff_forall_is_atomic_Iic.trans <| forall_congrₓ fun x => is_coatomic_dual_iff_is_atomic.symm.trans Iff.rfl

section WellFounded

theorem is_atomic_of_order_bot_well_founded_lt [OrderBot α] (h : WellFounded ((· < ·) : α → α → Prop)) : IsAtomic α :=
  ⟨fun a =>
    or_iff_not_imp_left.2 fun ha =>
      let ⟨b, hb, hm⟩ := h.has_min { b | b ≠ ⊥ ∧ b ≤ a } ⟨a, ha, le_rfl⟩
      ⟨b, ⟨hb.1, fun c => not_imp_not.1 fun hc hl => hm c ⟨hc, hl.le.trans hb.2⟩ hl⟩, hb.2⟩⟩

theorem is_coatomic_of_order_top_gt_well_founded [OrderTop α] (h : WellFounded ((· > ·) : α → α → Prop)) :
    IsCoatomic α :=
  is_atomic_dual_iff_is_coatomic.1 (@is_atomic_of_order_bot_well_founded_lt αᵒᵈ _ _ h)

end WellFounded

end Atomic

section Atomistic

variable (α) [CompleteLattice α]

/-- A lattice is atomistic iff every element is a `Sup` of a set of atoms. -/
class IsAtomistic : Prop where
  eq_Sup_atoms : ∀ b : α, ∃ s : Set α, b = sup s ∧ ∀ a, a ∈ s → IsAtom a

/-- A lattice is coatomistic iff every element is an `Inf` of a set of coatoms. -/
class IsCoatomistic : Prop where
  eq_Inf_coatoms : ∀ b : α, ∃ s : Set α, b = inf s ∧ ∀ a, a ∈ s → IsCoatom a

export IsAtomistic (eq_Sup_atoms)

export IsCoatomistic (eq_Inf_coatoms)

variable {α}

@[simp]
theorem is_coatomistic_dual_iff_is_atomistic : IsCoatomistic αᵒᵈ ↔ IsAtomistic α :=
  ⟨fun h =>
    ⟨fun b => by
      apply h.eq_Inf_coatoms⟩,
    fun h =>
    ⟨fun b => by
      apply h.eq_Sup_atoms⟩⟩

@[simp]
theorem is_atomistic_dual_iff_is_coatomistic : IsAtomistic αᵒᵈ ↔ IsCoatomistic α :=
  ⟨fun h =>
    ⟨fun b => by
      apply h.eq_Sup_atoms⟩,
    fun h =>
    ⟨fun b => by
      apply h.eq_Inf_coatoms⟩⟩

namespace IsAtomistic

instance is_coatomistic_dual [h : IsAtomistic α] : IsCoatomistic αᵒᵈ :=
  is_coatomistic_dual_iff_is_atomistic.2 h

variable [IsAtomistic α]

instance (priority := 100) : IsAtomic α :=
  ⟨fun b => by
    rcases eq_Sup_atoms b with ⟨s, rfl, hs⟩
    cases' s.eq_empty_or_nonempty with h h
    · simp [← h]
      
    · exact Or.intro_rightₓ _ ⟨h.some, hs _ h.some_spec, le_Sup h.some_spec⟩
      ⟩

end IsAtomistic

section IsAtomistic

variable [IsAtomistic α]

@[simp]
theorem Sup_atoms_le_eq (b : α) : sup { a : α | IsAtom a ∧ a ≤ b } = b := by
  rcases eq_Sup_atoms b with ⟨s, rfl, hs⟩
  exact le_antisymmₓ (Sup_le fun _ => And.right) (Sup_le_Sup fun a ha => ⟨hs a ha, le_Sup ha⟩)

@[simp]
theorem Sup_atoms_eq_top : sup { a : α | IsAtom a } = ⊤ := by
  refine' Eq.trans (congr rfl (Set.ext fun x => _)) (Sup_atoms_le_eq ⊤)
  exact (and_iff_left le_top).symm

theorem le_iff_atom_le_imp {a b : α} : a ≤ b ↔ ∀ c : α, IsAtom c → c ≤ a → c ≤ b :=
  ⟨fun ab c hc ca => le_transₓ ca ab, fun h => by
    rw [← Sup_atoms_le_eq a, ← Sup_atoms_le_eq b]
    exact Sup_le_Sup fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩

end IsAtomistic

namespace IsCoatomistic

instance is_atomistic_dual [h : IsCoatomistic α] : IsAtomistic αᵒᵈ :=
  is_atomistic_dual_iff_is_coatomistic.2 h

variable [IsCoatomistic α]

instance (priority := 100) : IsCoatomic α :=
  ⟨fun b => by
    rcases eq_Inf_coatoms b with ⟨s, rfl, hs⟩
    cases' s.eq_empty_or_nonempty with h h
    · simp [← h]
      
    · exact Or.intro_rightₓ _ ⟨h.some, hs _ h.some_spec, Inf_le h.some_spec⟩
      ⟩

end IsCoatomistic

end Atomistic

/-- An order is simple iff it has exactly two elements, `⊥` and `⊤`. -/
class IsSimpleOrder (α : Type _) [LE α] [BoundedOrder α] extends Nontrivial α : Prop where
  eq_bot_or_eq_top : ∀ a : α, a = ⊥ ∨ a = ⊤

export IsSimpleOrder (eq_bot_or_eq_top)

theorem is_simple_order_iff_is_simple_order_order_dual [LE α] [BoundedOrder α] : IsSimpleOrder α ↔ IsSimpleOrder αᵒᵈ :=
  by
  constructor <;> intro i <;> have := i
  · exact
      { exists_pair_ne := @exists_pair_ne α _,
        eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.ofDual a) : _ ∨ _) }
    
  · exact
      { exists_pair_ne := @exists_pair_ne αᵒᵈ _,
        eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.toDual a)) }
    

theorem IsSimpleOrder.bot_ne_top [LE α] [BoundedOrder α] [IsSimpleOrder α] : (⊥ : α) ≠ (⊤ : α) := by
  obtain ⟨a, b, h⟩ := exists_pair_ne α
  rcases eq_bot_or_eq_top a with (rfl | rfl) <;>
    rcases eq_bot_or_eq_top b with (rfl | rfl) <;>
      first |
        simpa|
        simpa using h.symm

section IsSimpleOrder

variable [PartialOrderₓ α] [BoundedOrder α] [IsSimpleOrder α]

instance {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] : IsSimpleOrder αᵒᵈ :=
  is_simple_order_iff_is_simple_order_order_dual.1
    (by
      infer_instance)

/-- A simple `bounded_order` induces a preorder. This is not an instance to prevent loops. -/
protected def IsSimpleOrder.preorder {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] : Preorderₓ α where
  le := (· ≤ ·)
  le_refl := fun a => by
    rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
  le_trans := fun a b c => by
    rcases eq_bot_or_eq_top a with (rfl | rfl)
    · simp
      
    · rcases eq_bot_or_eq_top b with (rfl | rfl)
      · rcases eq_bot_or_eq_top c with (rfl | rfl) <;> simp
        
      · simp
        
      

/-- A simple partial ordered `bounded_order` induces a linear order.
This is not an instance to prevent loops. -/
protected def IsSimpleOrder.linearOrder [DecidableEq α] : LinearOrderₓ α :=
  { (inferInstance : PartialOrderₓ α) with
    le_total := fun a b => by
      rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp ,
    decidableLe := fun a b =>
      if ha : a = ⊥ then isTrue (ha.le.trans bot_le)
      else
        if hb : b = ⊤ then isTrue (le_top.trans hb.Ge)
        else isFalse fun H => hb (top_unique (le_transₓ (top_le_iff.mpr (Or.resolve_left (eq_bot_or_eq_top a) ha)) H)),
    DecidableEq := by
      assumption }

@[simp]
theorem is_atom_top : IsAtom (⊤ : α) :=
  ⟨top_ne_bot, fun a ha => Or.resolve_right (eq_bot_or_eq_top a) (ne_of_ltₓ ha)⟩

@[simp]
theorem is_coatom_bot : IsCoatom (⊥ : α) :=
  is_atom_dual_iff_is_coatom.1 is_atom_top

theorem bot_covby_top : (⊥ : α) ⋖ ⊤ :=
  is_atom_top.bot_covby

end IsSimpleOrder

namespace IsSimpleOrder

section Preorderₓ

variable [Preorderₓ α] [BoundedOrder α] [IsSimpleOrder α] {a b : α} (h : a < b)

theorem eq_bot_of_lt : a = ⊥ :=
  (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right h.ne_top

theorem eq_top_of_lt : b = ⊤ :=
  (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left h.ne_bot

alias eq_bot_of_lt ← has_lt.lt.eq_bot

alias eq_top_of_lt ← has_lt.lt.eq_top

end Preorderₓ

section BoundedOrder

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

/-- A simple partial ordered `bounded_order` induces a lattice.
This is not an instance to prevent loops -/
protected def lattice {α} [DecidableEq α] [PartialOrderₓ α] [BoundedOrder α] [IsSimpleOrder α] : Lattice α :=
  @LinearOrderₓ.toLattice α IsSimpleOrder.linearOrder

/-- A lattice that is a `bounded_order` is a distributive lattice.
This is not an instance to prevent loops -/
protected def distribLattice : DistribLattice α :=
  { (inferInstance : Lattice α) with
    le_sup_inf := fun x y z => by
      rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }

-- see Note [lower instance priority]
instance (priority := 100) : IsAtomic α :=
  ⟨fun b => (eq_bot_or_eq_top b).imp_right fun h => ⟨⊤, ⟨is_atom_top, ge_of_eq h⟩⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) : IsCoatomic α :=
  is_atomic_dual_iff_is_coatomic.1 IsSimpleOrder.is_atomic

end BoundedOrder

-- It is important that in this section `is_simple_order` is the last type-class argument.
section DecidableEq

variable [DecidableEq α] [PartialOrderₓ α] [BoundedOrder α] [IsSimpleOrder α]

/-- Every simple lattice is isomorphic to `bool`, regardless of order. -/
@[simps]
def equivBool {α} [DecidableEq α] [LE α] [BoundedOrder α] [IsSimpleOrder α] : α ≃ Bool where
  toFun := fun x => x = ⊤
  invFun := fun x => cond x ⊤ ⊥
  left_inv := fun x => by
    rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [← bot_ne_top]
  right_inv := fun x => by
    cases x <;> simp [← bot_ne_top]

/-- Every simple lattice over a partial order is order-isomorphic to `bool`. -/
def orderIsoBool : α ≃o Bool :=
  { equivBool with
    map_rel_iff' := fun a b => by
      rcases eq_bot_or_eq_top a with (rfl | rfl)
      · simp [← bot_ne_top]
        
      · rcases eq_bot_or_eq_top b with (rfl | rfl)
        · simp [← bot_ne_top.symm, ← bot_ne_top, ← Bool.ff_lt_tt]
          
        · simp [← bot_ne_top]
          
         }

/- It is important that `is_simple_order` is the last type-class argument of this instance,
so that type-class inference fails quickly if it doesn't apply. -/
instance (priority := 200) {α} [DecidableEq α] [LE α] [BoundedOrder α] [IsSimpleOrder α] : Fintype α :=
  Fintype.ofEquiv Bool equivBool.symm

/-- A simple `bounded_order` is also a `boolean_algebra`. -/
protected def booleanAlgebra {α} [DecidableEq α] [Lattice α] [BoundedOrder α] [IsSimpleOrder α] : BooleanAlgebra α :=
  { show BoundedOrder α by
      infer_instance,
    IsSimpleOrder.distribLattice with compl := fun x => if x = ⊥ then ⊤ else ⊥,
    sdiff := fun x y => if x = ⊤ ∧ y = ⊥ then ⊤ else ⊥,
    sdiff_eq := fun x y => by
      rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [← bot_ne_top, ← HasSdiff.sdiff, ← compl],
    inf_compl_le_bot := fun x => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp
        
      · simp only [← top_inf_eq]
        split_ifs with h h <;> simp [← h]
        ,
    top_le_sup_compl := fun x => by
      rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp ,
    sup_inf_sdiff := fun x y => by
      rcases eq_bot_or_eq_top x with (rfl | rfl) <;> rcases eq_bot_or_eq_top y with (rfl | rfl) <;> simp [← bot_ne_top],
    inf_inf_sdiff := fun x y => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simpa
        
      rcases eq_bot_or_eq_top y with (rfl | rfl)
      · simpa
        
      · simp only [← true_andₓ, ← top_inf_eq, ← eq_self_iff_true]
        split_ifs with h h <;> simpa [← h]
         }

end DecidableEq

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

open Classical

/-- A simple `bounded_order` is also complete. -/
protected noncomputable def completeLattice : CompleteLattice α :=
  { (inferInstance : Lattice α), (inferInstance : BoundedOrder α) with sup := fun s => if ⊤ ∈ s then ⊤ else ⊥,
    inf := fun s => if ⊥ ∈ s then ⊥ else ⊤,
    le_Sup := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · exact bot_le
        
      · rw [if_pos h]
        ,
    Sup_le := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · rw [if_neg]
        intro con
        exact bot_ne_top (eq_top_iff.2 (h ⊤ con))
        
      · exact le_top
        ,
    Inf_le := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · rw [if_pos h]
        
      · exact le_top
        ,
    le_Inf := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · exact bot_le
        
      · rw [if_neg]
        intro con
        exact top_ne_bot (eq_bot_iff.2 (h ⊥ con))
         }

/-- A simple `bounded_order` is also a `complete_boolean_algebra`. -/
protected noncomputable def completeBooleanAlgebra : CompleteBooleanAlgebra α :=
  { IsSimpleOrder.completeLattice, IsSimpleOrder.booleanAlgebra with
    infi_sup_le_sup_Inf := fun x s => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp only [← bot_sup_eq, Inf_eq_infi]
        exact le_rfl
        
      · simp only [← top_sup_eq, ← le_top]
        ,
    inf_Sup_le_supr_inf := fun x s => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp only [← bot_inf_eq, ← bot_le]
        
      · simp only [← top_inf_eq, Sup_eq_supr]
        exact le_rfl
         }

end IsSimpleOrder

namespace IsSimpleOrder

variable [CompleteLattice α] [IsSimpleOrder α]

-- ./././Mathport/Syntax/Translate/Basic.lean:304:40: warning: unsupported option default_priority
set_option default_priority 100

instance : IsAtomistic α :=
  ⟨fun b =>
    (eq_bot_or_eq_top b).elim (fun h => ⟨∅, ⟨h.trans Sup_empty.symm, fun a ha => False.elim (Set.not_mem_empty _ ha)⟩⟩)
      fun h => ⟨{⊤}, h.trans Sup_singleton.symm, fun a ha => (Set.mem_singleton_iff.1 ha).symm ▸ is_atom_top⟩⟩

instance : IsCoatomistic α :=
  is_atomistic_dual_iff_is_coatomistic.1 IsSimpleOrder.is_atomistic

end IsSimpleOrder

namespace Fintype

namespace IsSimpleOrder

variable [PartialOrderₓ α] [BoundedOrder α] [IsSimpleOrder α] [DecidableEq α]

theorem univ : (Finset.univ : Finset α) = {⊤, ⊥} := by
  change Finset.map _ (Finset.univ : Finset Bool) = _
  rw [Fintype.univ_bool]
  simp only [← Finset.map_insert, ← Function.Embedding.coe_fn_mk, ← Finset.map_singleton]
  rfl

theorem card : Fintype.card α = 2 :=
  (Fintype.of_equiv_card _).trans Fintype.card_bool

end IsSimpleOrder

end Fintype

namespace Bool

instance : IsSimpleOrder Bool :=
  ⟨fun a => by
    rw [← Finset.mem_singleton, Or.comm, ← Finset.mem_insert, top_eq_tt, bot_eq_ff, ← Fintype.univ_bool]
    apply Finset.mem_univ⟩

end Bool

theorem is_simple_order_iff_is_atom_top [PartialOrderₓ α] [BoundedOrder α] : IsSimpleOrder α ↔ IsAtom (⊤ : α) :=
  ⟨fun h => @is_atom_top _ _ _ h, fun h =>
    { exists_pair_ne := ⟨⊤, ⊥, h.1⟩, eq_bot_or_eq_top := fun a => ((eq_or_lt_of_le le_top).imp_right (h.2 a)).symm }⟩

theorem is_simple_order_iff_is_coatom_bot [PartialOrderₓ α] [BoundedOrder α] : IsSimpleOrder α ↔ IsCoatom (⊥ : α) :=
  is_simple_order_iff_is_simple_order_order_dual.trans is_simple_order_iff_is_atom_top

namespace Set

theorem is_simple_order_Iic_iff_is_atom [PartialOrderₓ α] [OrderBot α] {a : α} : IsSimpleOrder (Iic a) ↔ IsAtom a :=
  is_simple_order_iff_is_atom_top.trans <|
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_ltₓ ab⟩ ab), fun h ⟨b, hab⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩

theorem is_simple_order_Ici_iff_is_coatom [PartialOrderₓ α] [OrderTop α] {a : α} : IsSimpleOrder (Ici a) ↔ IsCoatom a :=
  is_simple_order_iff_is_coatom_bot.trans <|
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_ltₓ ab⟩ ab), fun h ⟨b, hab⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩

end Set

namespace OrderIso

variable {β : Type _}

@[simp]
theorem is_atom_iff [PartialOrderₓ α] [OrderBot α] [PartialOrderₓ β] [OrderBot β] (f : α ≃o β) (a : α) :
    IsAtom (f a) ↔ IsAtom a :=
  and_congr (not_congr ⟨fun h => f.Injective (f.map_bot.symm ▸ h), fun h => f.map_bot ▸ congr rfl h⟩)
    ⟨fun h b hb => f.Injective ((h (f b) ((f : α ↪o β).lt_iff_lt.2 hb)).trans f.map_bot.symm), fun h b hb =>
      f.symm.Injective
        (by
          rw [f.symm.map_bot]
          apply h
          rw [← f.symm_apply_apply a]
          exact (f.symm : β ↪o α).lt_iff_lt.2 hb)⟩

@[simp]
theorem is_coatom_iff [PartialOrderₓ α] [OrderTop α] [PartialOrderₓ β] [OrderTop β] (f : α ≃o β) (a : α) :
    IsCoatom (f a) ↔ IsCoatom a :=
  f.dual.is_atom_iff a

theorem is_simple_order_iff [PartialOrderₓ α] [BoundedOrder α] [PartialOrderₓ β] [BoundedOrder β] (f : α ≃o β) :
    IsSimpleOrder α ↔ IsSimpleOrder β := by
  rw [is_simple_order_iff_is_atom_top, is_simple_order_iff_is_atom_top, ← f.is_atom_iff ⊤, f.map_top]

theorem is_simple_order [PartialOrderₓ α] [BoundedOrder α] [PartialOrderₓ β] [BoundedOrder β] [h : IsSimpleOrder β]
    (f : α ≃o β) : IsSimpleOrder α :=
  f.is_simple_order_iff.mpr h

theorem is_atomic_iff [PartialOrderₓ α] [OrderBot α] [PartialOrderₓ β] [OrderBot β] (f : α ≃o β) :
    IsAtomic α ↔ IsAtomic β := by
  suffices : (∀ b : α, b = ⊥ ∨ ∃ a : α, IsAtom a ∧ a ≤ b) ↔ ∀ b : β, b = ⊥ ∨ ∃ a : β, IsAtom a ∧ a ≤ b
  exact ⟨fun ⟨p⟩ => ⟨this.mp p⟩, fun ⟨p⟩ => ⟨this.mpr p⟩⟩
  apply f.to_equiv.forall_congr
  simp_rw [RelIso.coe_fn_to_equiv]
  intro b
  apply or_congr
  · rw [f.apply_eq_iff_eq_symm_apply, map_bot]
    
  · constructor
    · exact fun ⟨a, ha⟩ => ⟨f a, ⟨(f.is_atom_iff a).mpr ha.1, f.le_iff_le.mpr ha.2⟩⟩
      
    · rintro ⟨b, ⟨hb1, hb2⟩⟩
      refine' ⟨f.symm b, ⟨(f.symm.is_atom_iff b).mpr hb1, _⟩⟩
      rwa [← f.le_iff_le, f.apply_symm_apply]
      
    

theorem is_coatomic_iff [PartialOrderₓ α] [OrderTop α] [PartialOrderₓ β] [OrderTop β] (f : α ≃o β) :
    IsCoatomic α ↔ IsCoatomic β := by
  rw [← is_atomic_dual_iff_is_coatomic, ← is_atomic_dual_iff_is_coatomic]
  exact f.dual.is_atomic_iff

end OrderIso

section IsModularLattice

variable [Lattice α] [BoundedOrder α] [IsModularLattice α]

namespace IsCompl

variable {a b : α} (hc : IsCompl a b)

include hc

theorem is_atom_iff_is_coatom : IsAtom a ↔ IsCoatom b :=
  Set.is_simple_order_Iic_iff_is_atom.symm.trans <|
    hc.iicOrderIsoIci.is_simple_order_iff.trans Set.is_simple_order_Ici_iff_is_coatom

theorem is_coatom_iff_is_atom : IsCoatom a ↔ IsAtom b :=
  hc.symm.is_atom_iff_is_coatom.symm

end IsCompl

variable [IsComplemented α]

theorem is_coatomic_of_is_atomic_of_is_complemented_of_is_modular [IsAtomic α] : IsCoatomic α :=
  ⟨fun x => by
    rcases exists_is_compl x with ⟨y, xy⟩
    apply (eq_bot_or_exists_atom_le y).imp _ _
    · rintro rfl
      exact eq_top_of_is_compl_bot xy
      
    · rintro ⟨a, ha, ay⟩
      rcases exists_is_compl (xy.symm.Iic_order_iso_Ici ⟨a, ay⟩) with ⟨⟨b, xb⟩, hb⟩
      refine' ⟨↑(⟨b, xb⟩ : Set.Ici x), IsCoatom.of_is_coatom_coe_Ici _, xb⟩
      rw [← hb.is_atom_iff_is_coatom, OrderIso.is_atom_iff]
      apply ha.Iic
      ⟩

theorem is_atomic_of_is_coatomic_of_is_complemented_of_is_modular [IsCoatomic α] : IsAtomic α :=
  is_coatomic_dual_iff_is_atomic.1 is_coatomic_of_is_atomic_of_is_complemented_of_is_modular

theorem is_atomic_iff_is_coatomic : IsAtomic α ↔ IsCoatomic α :=
  ⟨fun h => @is_coatomic_of_is_atomic_of_is_complemented_of_is_modular _ _ _ _ _ h, fun h =>
    @is_atomic_of_is_coatomic_of_is_complemented_of_is_modular _ _ _ _ _ h⟩

end IsModularLattice

section Fintype

open Finset

-- see Note [lower instance priority]
instance (priority := 100) Fintype.to_is_coatomic [PartialOrderₓ α] [OrderTop α] [Fintype α] : IsCoatomic α := by
  refine' IsCoatomic.mk fun b => or_iff_not_imp_left.2 fun ht => _
  obtain ⟨c, hc, hmax⟩ := Set.Finite.exists_maximal_wrt id { x : α | b ≤ x ∧ x ≠ ⊤ } (Set.to_finite _) ⟨b, le_rfl, ht⟩
  refine' ⟨c, ⟨hc.2, fun y hcy => _⟩, hc.1⟩
  by_contra hyt
  obtain rfl : c = y := hmax y ⟨hc.1.trans hcy.le, hyt⟩ hcy.le
  exact (lt_self_iff_false _).mp hcy

-- see Note [lower instance priority]
instance (priority := 100) Fintype.to_is_atomic [PartialOrderₓ α] [OrderBot α] [Fintype α] : IsAtomic α :=
  is_coatomic_dual_iff_is_atomic.mp Fintype.to_is_coatomic

end Fintype


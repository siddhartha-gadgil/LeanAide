/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.ModelTheory.ElementaryMaps
import Mathbin.CategoryTheory.ConcreteCategory.Bundled

/-!
# Bundled First-Order Structures
This file bundles types together with their first-order structure.

## Main Definitions
* `first_order.language.Theory.Model` is the type of nonempty models of a particular theory.
* `first_order.language.equiv_setoid` is the isomorphism equivalence relation on bundled structures.

## TODO
* Define category structures on bundled structures and models.

-/


universe u v w w'

variable {L : FirstOrder.Language.{u, v}}

@[protected]
instance CategoryTheory.Bundled.structure {L : FirstOrder.Language.{u, v}}
    (M : CategoryTheory.Bundled.{w} L.Structure) : L.Structure M :=
  M.str

open FirstOrder Cardinal

namespace Equivₓ

variable (L) {M : Type w} [L.Structure M] {N : Type w'} (g : M ≃ N)

/-- A type bundled with the structure induced by an equivalence. -/
@[simps]
def bundledInduced : CategoryTheory.Bundled.{w'} L.Structure :=
  ⟨N, g.inducedStructure⟩

/-- An equivalence of types as a first-order equivalence to the bundled structure on the codomain.
-/
@[simp]
def bundledInducedEquiv : M ≃[L] g.bundledInduced L :=
  g.inducedStructureEquiv

end Equivₓ

namespace FirstOrder

namespace Language

/-- The equivalence relation on bundled `L.Structure`s indicating that they are isomorphic. -/
instance equivSetoid : Setoidₓ (CategoryTheory.Bundled L.Structure) where
  R := fun M N => Nonempty (M ≃[L] N)
  iseqv :=
    ⟨fun M => ⟨Equiv.refl L M⟩, fun M N => Nonempty.map Equiv.symm, fun M N P => Nonempty.map2 fun MN NP => NP.comp MN⟩

variable (T : L.Theory)

namespace Theory

/-- The type of nonempty models of a first-order theory. -/
structure ModelCat where
  Carrier : Type w
  [struc : L.Structure carrier]
  [is_model : T.Model carrier]
  [nonempty' : Nonempty carrier]

attribute [instance] Model.struc Model.is_model Model.nonempty'

namespace Model

instance : CoeSort T.Model (Type w) :=
  ⟨ModelCat.Carrier⟩

@[simp]
theorem carrier_eq_coe (M : T.Model) : M.Carrier = M :=
  rfl

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
def of (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M] : T.Model :=
  ⟨M⟩

@[simp]
theorem coe_of (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M] : (of T M : Type w) = M :=
  rfl

instance (M : T.Model) : Nonempty M :=
  inferInstance

section Inhabited

attribute [local instance] trivial_unit_structure

instance : Inhabited (ModelCat (∅ : L.Theory)) :=
  ⟨ModelCat.of _ Unit⟩

end Inhabited

variable {T}

/-- Maps a bundled model along a bijection. -/
def equivInduced {M : ModelCat.{u, v, w} T} {N : Type w'} (e : M ≃ N) : ModelCat.{u, v, w'} T where
  Carrier := N
  struc := e.inducedStructure
  is_model := @Equiv.Theory_model L M N _ e.inducedStructure T e.inducedStructureEquiv _
  nonempty' := e.symm.Nonempty

instance of_small (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T] [h : Small.{w'} M] : Small.{w'} (ModelCat.of T M) :=
  h

/-- Shrinks a small model to a particular universe. -/
noncomputable def shrink (M : ModelCat.{u, v, w} T) [Small.{w'} M] : ModelCat.{u, v, w'} T :=
  equivInduced (equivShrink M)

/-- Lifts a model to a particular universe. -/
def ulift (M : ModelCat.{u, v, w} T) : ModelCat.{u, v, max w w'} T :=
  equivInduced (Equivₓ.ulift.symm : M ≃ _)

/-- The reduct of any model of `φ.on_Theory T` is a model of `T`. -/
@[simps]
def reduct {L' : Language} (φ : L →ᴸ L') (M : (φ.OnTheory T).Model) : T.Model where
  Carrier := M
  struc := φ.reduct M
  nonempty' := M.nonempty'
  is_model := (@Lhom.on_Theory_model L L' M (φ.reduct M) _ φ _ T).1 M.is_model

instance leftStructure {L' : Language} {T : (L.Sum L').Theory} (M : T.Model) : L.Structure M :=
  (Lhom.sumInl : L →ᴸ L.Sum L').reduct M

instance rightStructure {L' : Language} {T : (L.Sum L').Theory} (M : T.Model) : L'.Structure M :=
  (Lhom.sumInr : L' →ᴸ L.Sum L').reduct M

end Model

variable {T}

/-- Bundles `M ⊨ T` as a `T.Model`. -/
def Model.bundled {M : Type w} [LM : L.Structure M] [ne : Nonempty M] (h : M ⊨ T) : T.Model :=
  @ModelCat.of L T M LM h Ne

@[simp]
theorem coe_of {M : Type w} [L.Structure M] [Nonempty M] (h : M ⊨ T) : (h.Bundled : Type w) = M :=
  rfl

end Theory

/-- A structure that is elementarily equivalent to a model, bundled as a model. -/
def ElementarilyEquivalent.toModel {M : T.Model} {N : Type _} [LN : L.Structure N] (h : M ≅[L] N) : T.Model where
  Carrier := N
  struc := LN
  nonempty' := h.Nonempty
  is_model := h.Theory_model

/-- An elementary substructure of a bundled model as a bundled model. -/
def ElementarySubstructure.toModel {M : T.Model} (S : L.ElementarySubstructure M) : T.Model :=
  S.ElementarilyEquivalent.symm.toModel T

instance {M : T.Model} (S : L.ElementarySubstructure M) [h : Small S] : Small (S.toModel T) :=
  h

end Language

end FirstOrder


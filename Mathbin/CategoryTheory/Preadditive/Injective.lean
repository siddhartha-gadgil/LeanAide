/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kevin Buzzard
-/
import Mathbin.Algebra.Homology.Exact
import Mathbin.CategoryTheory.Types
import Mathbin.CategoryTheory.Preadditive.Projective
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Injective objects and categories with enough injectives

An object `J` is injective iff every morphism into `J` can be obtained by extending a monomorphism.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- An object `J` is injective iff every morphism into `J` can be obtained by extending a monomorphism.
-/
class Injective (J : C) : Prop where
  Factors : ∀ {X Y : C} (g : X ⟶ J) (f : X ⟶ Y) [Mono f], ∃ h : Y ⟶ J, f ≫ h = g

section

/-- An injective presentation of an object `X` consists of a monomorphism `f : X ⟶ J`
to some injective object `J`.
-/
@[nolint has_inhabited_instance]
structure InjectivePresentation (X : C) where
  j : C
  Injective : Injective J := by
    run_tac
      tactic.apply_instance
  f : X ⟶ J
  mono : Mono f := by
    run_tac
      tactic.apply_instance

variable (C)

/-- A category "has enough injectives" if every object has an injective presentation,
i.e. if for every object `X` there is an injective object `J` and a monomorphism `X ↪ J`. -/
class EnoughInjectives : Prop where
  presentation : ∀ X : C, Nonempty (InjectivePresentation X)

end

namespace Injective

/-- Let `J` be injective and `g` a morphism into `J`, then `g` can be factored through any monomorphism.
-/
def factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : Y ⟶ J :=
  (Injective.factors g f).some

@[simp]
theorem comp_factor_thru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : f ≫ factorThru g f = g :=
  (Injective.factors g f).some_spec

section

open ZeroObject

instance zero_injective [HasZeroObject C] [HasZeroMorphisms C] :
    Injective (0 : C) where Factors := fun X Y g f mono =>
    ⟨0, by
      ext⟩

end

theorem of_iso {P Q : C} (i : P ≅ Q) (hP : Injective P) : Injective Q :=
  { Factors := fun X Y g f mono => by
      obtain ⟨h, h_eq⟩ := @injective.factors C _ P _ _ _ (g ≫ i.inv) f mono
      refine' ⟨h ≫ i.hom, _⟩
      rw [← category.assoc, h_eq, category.assoc, iso.inv_hom_id, category.comp_id] }

theorem iso_iff {P Q : C} (i : P ≅ Q) : Injective P ↔ Injective Q :=
  ⟨of_iso i, of_iso i.symm⟩

/-- The axiom of choice says that every nonempty type is an injective object in `Type`. -/
instance (X : Type u) [Nonempty X] :
    Injective X where Factors := fun Y Z g f mono =>
    ⟨fun z => by
      classical <;> exact if h : z ∈ Set.Range f then g (Classical.some h) else Nonempty.some inferInstance, by
      ext y
      change dite _ _ _ = _
      split_ifs
      · rw [mono_iff_injective] at mono
        rw [mono (Classical.some_spec h)]
        
      · exact False.elim (h ⟨y, rfl⟩)
        ⟩

instance Type.enough_injectives :
    EnoughInjectives
      (Type
        u) where presentation := fun X =>
    Nonempty.intro
      { j := WithBot X, Injective := inferInstance, f := Option.some,
        mono := by
          rw [mono_iff_injective]
          exact Option.some_injective X }

instance {P Q : C} [HasBinaryProduct P Q] [Injective P] [Injective Q] :
    Injective (P ⨯ Q) where Factors := fun X Y g f mono => by
    skip
    use limits.prod.lift (factor_thru (g ≫ limits.prod.fst) f) (factor_thru (g ≫ limits.prod.snd) f)
    simp only [← prod.comp_lift, ← comp_factor_thru]
    ext
    · simp only [← prod.lift_fst]
      
    · simp only [← prod.lift_snd]
      

instance {β : Type v} (c : β → C) [HasProduct c] [∀ b, Injective (c b)] :
    Injective (∏ c) where Factors := fun X Y g f mono => by
    skip
    refine' ⟨pi.lift fun b => factor_thru (g ≫ pi.π c _) f, _⟩
    ext ⟨j⟩
    simp only [← category.assoc, ← limit.lift_π, ← fan.mk_π_app, ← comp_factor_thru]

instance {P Q : C} [HasZeroMorphisms C] [HasBinaryBiproduct P Q] [Injective P] [Injective Q] :
    Injective (P ⊞ Q) where Factors := fun X Y g f mono => by
    skip
    refine' ⟨biprod.lift (factor_thru (g ≫ biprod.fst) f) (factor_thru (g ≫ biprod.snd) f), _⟩
    ext
    · simp only [← category.assoc, ← biprod.lift_fst, ← comp_factor_thru]
      
    · simp only [← category.assoc, ← biprod.lift_snd, ← comp_factor_thru]
      

instance {β : Type v} (c : β → C) [HasZeroMorphisms C] [HasBiproduct c] [∀ b, Injective (c b)] :
    Injective (⨁ c) where Factors := fun X Y g f mono => by
    skip
    refine' ⟨biproduct.lift fun b => factor_thru (g ≫ biproduct.π _ _) f, _⟩
    ext
    simp only [← category.assoc, ← biproduct.lift_π, ← comp_factor_thru]

instance {P : Cᵒᵖ} [Projective P] :
    Injective
      (unop
        P) where Factors := fun X Y g f mono =>
    ⟨(@projective.factor_thru Cᵒᵖ _ P _ _ _ g.op f.op _).unop,
      Quiver.Hom.op_inj
        (by
          simp )⟩

instance {J : Cᵒᵖ} [Injective J] :
    Projective
      (unop J) where Factors := fun E X f e he =>
    ⟨(@factor_thru Cᵒᵖ _ J _ _ _ f.op e.op _).unop,
      Quiver.Hom.op_inj
        (by
          simp )⟩

instance {J : C} [Injective J] :
    Projective
      (op J) where Factors := fun E X f e epi =>
    ⟨(@factor_thru C _ J _ _ _ f.unop e.unop _).op,
      Quiver.Hom.unop_inj
        (by
          simp )⟩

instance {P : C} [Projective P] :
    Injective
      (op
        P) where Factors := fun X Y g f mono =>
    ⟨(@projective.factor_thru C _ P _ _ _ g.unop f.unop _).op,
      Quiver.Hom.unop_inj
        (by
          simp )⟩

theorem injective_iff_projective_op {J : C} : Injective J ↔ Projective (op J) :=
  ⟨fun h => inferInstance, fun h => show Injective (unop (op J)) from inferInstance⟩

theorem projective_iff_injective_op {P : C} : Projective P ↔ Injective (op P) :=
  ⟨fun h => inferInstance, fun h => show Projective (unop (op P)) from inferInstance⟩

theorem injective_iff_preserves_epimorphisms_yoneda_obj (J : C) : Injective J ↔ (yoneda.obj J).PreservesEpimorphisms :=
  by
  rw [injective_iff_projective_op, projective.projective_iff_preserves_epimorphisms_coyoneda_obj]
  exact functor.preserves_epimorphisms.iso_iff (coyoneda.obj_op_op _)

section EnoughInjectives

variable [EnoughInjectives C]

/-- `injective.under X` provides an arbitrarily chosen injective object equipped with
an monomorphism `injective.ι : X ⟶ injective.under X`.
-/
def under (X : C) : C :=
  (EnoughInjectives.presentation X).some.j

instance injective_under (X : C) : Injective (under X) :=
  (EnoughInjectives.presentation X).some.Injective

/-- The monomorphism `injective.ι : X ⟶ injective.under X`
from the arbitrarily chosen injective object under `X`.
-/
def ι (X : C) : X ⟶ under X :=
  (EnoughInjectives.presentation X).some.f

instance ι_mono (X : C) : Mono (ι X) :=
  (EnoughInjectives.presentation X).some.mono

section

variable [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasCokernel f]

/-- When `C` has enough injectives, the object `injective.syzygies f` is
an arbitrarily chosen injective object under `cokernel f`.
-/
def syzygies : C :=
  under (cokernel f)deriving Injective

/-- When `C` has enough injective,
`injective.d f : Y ⟶ syzygies f` is the composition
`cokernel.π f ≫ ι (cokernel f)`.

(When `C` is abelian, we have `exact f (injective.d f)`.)
-/
abbrev d : Y ⟶ syzygies f :=
  cokernel.π f ≫ ι (cokernel f)

end

end EnoughInjectives

instance [EnoughInjectives C] : EnoughProjectives Cᵒᵖ :=
  ⟨fun X => ⟨⟨_, inferInstance, (Injective.ι (unop X)).op, inferInstance⟩⟩⟩

instance [EnoughProjectives C] : EnoughInjectives Cᵒᵖ :=
  ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (unop X)).op, inferInstance⟩⟩⟩

theorem enough_projectives_of_enough_injectives_op [EnoughInjectives Cᵒᵖ] : EnoughProjectives C :=
  ⟨fun X => ⟨⟨_, inferInstance, (Injective.ι (op X)).unop, inferInstance⟩⟩⟩

theorem enough_injectives_of_enough_projectives_op [EnoughProjectives Cᵒᵖ] : EnoughInjectives C :=
  ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (op X)).unop, inferInstance⟩⟩⟩

open Injective

section

variable [HasZeroMorphisms C] [HasImages Cᵒᵖ] [HasEqualizers Cᵒᵖ]

/-- Given a pair of exact morphism `f : Q ⟶ R` and `g : R ⟶ S` and a map `h : R ⟶ J` to an injective
object `J` such that `f ≫ h = 0`, then `g` descents to a map `S ⟶ J`. See below:

```
Q --- f --> R --- g --> S
            |
            | h
            v
            J
```
-/
def Exact.desc {J Q R S : C} [Injective J] (h : R ⟶ J) (f : Q ⟶ R) (g : R ⟶ S) (hgf : Exact g.op f.op) (w : f ≫ h = 0) :
    S ⟶ J :=
  (Exact.lift h.op g.op f.op hgf (congr_arg Quiver.Hom.op w)).unop

@[simp]
theorem Exact.comp_desc {J Q R S : C} [Injective J] (h : R ⟶ J) (f : Q ⟶ R) (g : R ⟶ S) (hgf : Exact g.op f.op)
    (w : f ≫ h = 0) : g ≫ Exact.desc h f g hgf w = h := by
  convert congr_arg Quiver.Hom.unop (exact.lift_comp h.op g.op f.op hgf (congr_arg Quiver.Hom.op w))

end

end Injective

end CategoryTheory


/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathbin.CategoryTheory.Bicategory.Coherence

/-!
# A `coherence` tactic for bicategories, and `⊗≫` (composition up to associators)

We provide a `coherence` tactic,
which proves that any two 2-morphisms (with the same source and target)
in a bicategory which are built out of associators and unitors
are equal.

We also provide `f ⊗≫ g`, the `bicategorical_comp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.

This file mainly deals with the type class setup for the coherence tactic. The actual front end
tactic is given in `category_theory/monooidal/coherence.lean` at the same time as the coherence
tactic for monoidal categories.
-/


noncomputable section

universe w v u

open CategoryTheory

open CategoryTheory.FreeBicategory

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B] {a b c d e : B}

namespace CategoryTheory.Bicategory

/-- A typeclass carrying a choice of lift of a 1-morphism from `B` to `free_bicategory B`. -/
class LiftHom {a b : B} (f : a ⟶ b) where
  lift : of.obj a ⟶ of.obj b

instance liftHomId : LiftHom (𝟙 a) where lift := 𝟙 (of.obj a)

instance liftHomComp (f : a ⟶ b) (g : b ⟶ c) [LiftHom f] [LiftHom g] :
    LiftHom (f ≫ g) where lift := LiftHom.lift f ≫ LiftHom.lift g

instance (priority := 100) liftHomOf (f : a ⟶ b) : LiftHom f where lift := of.map f

/-- A typeclass carrying a choice of lift of a 2-morphism from `B` to `free_bicategory B`. -/
class LiftHom₂ {f g : a ⟶ b} [LiftHom f] [LiftHom g] (η : f ⟶ g) where
  lift : LiftHom.lift f ⟶ LiftHom.lift g

instance liftHom₂Id (f : a ⟶ b) [LiftHom f] : LiftHom₂ (𝟙 f) where lift := 𝟙 _

instance liftHom₂LeftUnitorHom (f : a ⟶ b) [LiftHom f] : LiftHom₂ (λ_ f).Hom where lift := (λ_ (LiftHom.lift f)).Hom

instance liftHom₂LeftUnitorInv (f : a ⟶ b) [LiftHom f] : LiftHom₂ (λ_ f).inv where lift := (λ_ (LiftHom.lift f)).inv

instance liftHom₂RightUnitorHom (f : a ⟶ b) [LiftHom f] : LiftHom₂ (ρ_ f).Hom where lift := (ρ_ (LiftHom.lift f)).Hom

instance liftHom₂RightUnitorInv (f : a ⟶ b) [LiftHom f] : LiftHom₂ (ρ_ f).inv where lift := (ρ_ (LiftHom.lift f)).inv

instance liftHom₂AssociatorHom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) [LiftHom f] [LiftHom g] [LiftHom h] :
    LiftHom₂ (α_ f g h).Hom where lift := (α_ (LiftHom.lift f) (LiftHom.lift g) (LiftHom.lift h)).Hom

instance liftHom₂AssociatorInv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) [LiftHom f] [LiftHom g] [LiftHom h] :
    LiftHom₂ (α_ f g h).inv where lift := (α_ (LiftHom.lift f) (LiftHom.lift g) (LiftHom.lift h)).inv

instance liftHom₂Comp {f g h : a ⟶ b} [LiftHom f] [LiftHom g] [LiftHom h] (η : f ⟶ g) (θ : g ⟶ h) [LiftHom₂ η]
    [LiftHom₂ θ] : LiftHom₂ (η ≫ θ) where lift := LiftHom₂.lift η ≫ LiftHom₂.lift θ

instance liftHom₂WhiskerLeft (f : a ⟶ b) [LiftHom f] {g h : b ⟶ c} (η : g ⟶ h) [LiftHom g] [LiftHom h] [LiftHom₂ η] :
    LiftHom₂ (f ◁ η) where lift := LiftHom.lift f ◁ LiftHom₂.lift η

instance liftHom₂WhiskerRight {f g : a ⟶ b} (η : f ⟶ g) [LiftHom f] [LiftHom g] [LiftHom₂ η] {h : b ⟶ c} [LiftHom h] :
    LiftHom₂ (η ▷ h) where lift := LiftHom₂.lift η ▷ LiftHom.lift h

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`Hom] []
/-- A typeclass carrying a choice of bicategorical structural isomorphism between two objects.
Used by the `⊗≫` bicategorical composition operator, and the `coherence` tactic.
-/
class BicategoricalCoherence (f g : a ⟶ b) [LiftHom f] [LiftHom g] where
  Hom : f ⟶ g
  [IsIso : IsIso hom]

attribute [instance] bicategorical_coherence.is_iso

namespace BicategoricalCoherence

@[simps]
instance refl (f : a ⟶ b) [LiftHom f] : BicategoricalCoherence f f :=
  ⟨𝟙 _⟩

@[simps]
instance whiskerLeft (f : a ⟶ b) (g h : b ⟶ c) [LiftHom f] [LiftHom g] [LiftHom h] [BicategoricalCoherence g h] :
    BicategoricalCoherence (f ≫ g) (f ≫ h) :=
  ⟨f ◁ BicategoricalCoherence.hom g h⟩

@[simps]
instance whiskerRight (f g : a ⟶ b) (h : b ⟶ c) [LiftHom f] [LiftHom g] [LiftHom h] [BicategoricalCoherence f g] :
    BicategoricalCoherence (f ≫ h) (g ≫ h) :=
  ⟨BicategoricalCoherence.hom f g ▷ h⟩

@[simps]
instance tensorRight (f : a ⟶ b) (g : b ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence (𝟙 b) g] :
    BicategoricalCoherence f (f ≫ g) :=
  ⟨(ρ_ f).inv ≫ f ◁ BicategoricalCoherence.hom (𝟙 b) g⟩

@[simps]
instance tensorRight' (f : a ⟶ b) (g : b ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence g (𝟙 b)] :
    BicategoricalCoherence (f ≫ g) f :=
  ⟨f ◁ BicategoricalCoherence.hom g (𝟙 b) ≫ (ρ_ f).Hom⟩

@[simps]
instance left (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] : BicategoricalCoherence (𝟙 a ≫ f) g :=
  ⟨(λ_ f).Hom ≫ BicategoricalCoherence.hom f g⟩

@[simps]
instance left' (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] :
    BicategoricalCoherence f (𝟙 a ≫ g) :=
  ⟨BicategoricalCoherence.hom f g ≫ (λ_ g).inv⟩

@[simps]
instance right (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] :
    BicategoricalCoherence (f ≫ 𝟙 b) g :=
  ⟨(ρ_ f).Hom ≫ BicategoricalCoherence.hom f g⟩

@[simps]
instance right' (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] :
    BicategoricalCoherence f (g ≫ 𝟙 b) :=
  ⟨BicategoricalCoherence.hom f g ≫ (ρ_ g).inv⟩

@[simps]
instance assoc (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d) [LiftHom f] [LiftHom g] [LiftHom h] [LiftHom i]
    [BicategoricalCoherence (f ≫ g ≫ h) i] : BicategoricalCoherence ((f ≫ g) ≫ h) i :=
  ⟨(α_ f g h).Hom ≫ BicategoricalCoherence.hom (f ≫ g ≫ h) i⟩

@[simps]
instance assoc' (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d) [LiftHom f] [LiftHom g] [LiftHom h] [LiftHom i]
    [BicategoricalCoherence i (f ≫ g ≫ h)] : BicategoricalCoherence i ((f ≫ g) ≫ h) :=
  ⟨BicategoricalCoherence.hom i (f ≫ g ≫ h) ≫ (α_ f g h).inv⟩

end BicategoricalCoherence

/-- Construct an isomorphism between two objects in a bicategorical category
out of unitors and associators. -/
def bicategoricalIso (f g : a ⟶ b) [LiftHom f] [LiftHom g] [BicategoricalCoherence f g] : f ≅ g :=
  asIso (BicategoricalCoherence.hom f g)

/-- Compose two morphisms in a bicategorical category,
inserting unitors and associators between as necessary. -/
def bicategoricalComp {f g h i : a ⟶ b} [LiftHom g] [LiftHom h] [BicategoricalCoherence g h] (η : f ⟶ g) (θ : h ⟶ i) :
    f ⟶ i :=
  η ≫ BicategoricalCoherence.hom g h ≫ θ

-- mathport name: «expr ⊗≫ »
localized [Bicategory] infixr:80 " ⊗≫ " => CategoryTheory.Bicategory.bicategoricalComp

/-- Compose two isomorphisms in a bicategorical category,
inserting unitors and associators between as necessary. -/
-- type as \ot \gg
def bicategoricalIsoComp {f g h i : a ⟶ b} [LiftHom g] [LiftHom h] [BicategoricalCoherence g h] (η : f ≅ g)
    (θ : h ≅ i) : f ≅ i :=
  η ≪≫ asIso (BicategoricalCoherence.hom g h) ≪≫ θ

-- mathport name: «expr ≪⊗≫ »
localized [Bicategory] infixr:80 " ≪⊗≫ " => CategoryTheory.Bicategory.bicategoricalIsoComp

-- type as \ot \gg
example {f' : a ⟶ d} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {h' : a ⟶ d} (η : f' ⟶ f ≫ g ≫ h) (θ : (f ≫ g) ≫ h ⟶ h') :
    f' ⟶ h' :=
  η ⊗≫ θ

-- To automatically insert unitors/associators at the beginning or end,
-- you can use `η ⊗≫ 𝟙 _`
example {f' : a ⟶ d} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} (η : f' ⟶ (f ≫ g) ≫ h) : f' ⟶ f ≫ g ≫ h :=
  η ⊗≫ 𝟙 _

@[simp]
theorem bicategorical_comp_refl {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) : η ⊗≫ θ = η ≫ θ := by
  dsimp' [← bicategorical_comp]
  simp

end CategoryTheory.Bicategory

open CategoryTheory.Bicategory

namespace Tactic

setup_tactic_parser

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- Coherence tactic for bicategories. -/
unsafe def bicategorical_coherence : tactic Unit :=
  focus1 <| do
    let o ← get_options
    set_options <| o `class.instance_max_depth 128
    try sorry
    let quote.1 ((%%ₓlhs) = %%ₓrhs) ← target
    to_expr
          (pquote.1
            ((FreeBicategory.lift (Prefunctor.id _)).map₂ (LiftHom₂.lift (%%ₓlhs)) =
              (FreeBicategory.lift (Prefunctor.id _)).map₂ (LiftHom₂.lift (%%ₓrhs)))) >>=
        tactic.change
    congr

namespace Bicategory

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- Simp lemmas for rewriting a 2-morphism into a normal form. -/
unsafe def whisker_simps : tactic Unit :=
  sorry

namespace Coherence

/-- Auxiliary simp lemma for the `coherence` tactic:
this move brackets to the left in order to expose a maximal prefix
built out of unitors and associators.
-/
-- We have unused typeclass arguments here.
-- They are intentional, to ensure that `simp only [assoc_lift_hom₂]` only left associates
-- bicategorical structural morphisms.
@[nolint unused_arguments]
theorem assoc_lift_hom₂ {f g h i : a ⟶ b} [LiftHom f] [LiftHom g] [LiftHom h] (η : f ⟶ g) (θ : g ⟶ h) (ι : h ⟶ i)
    [LiftHom₂ η] [LiftHom₂ θ] : η ≫ θ ≫ ι = (η ≫ θ) ≫ ι :=
  (Category.assoc _ _ _).symm

end Coherence

end Bicategory

end Tactic


/-
Copyright (c) 2022. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yuma Mizuno, Oleksandr Manzyuk
-/
import Mathbin.CategoryTheory.Monoidal.Free.Coherence
import Mathbin.CategoryTheory.Bicategory.CoherenceTactic

/-!
# A `coherence` tactic for monoidal categories, and `⊗≫` (composition up to associators)

We provide a `coherence` tactic,
which proves equations where the two sides differ by replacing
strings of monoidal structural morphisms with other such strings.
(The replacements are always equalities by the monoidal coherence theorem.)

A simpler version of this tactic is `pure_coherence`,
which proves that any two morphisms (with the same source and target)
in a monoidal category which are built out of associators and unitors
are equal.

We also provide `f ⊗≫ g`, the `monoidal_comp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.
-/


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.FreeMonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace CategoryTheory.MonoidalCategory

/-- A typeclass carrying a choice of lift of an object from `C` to `free_monoidal_category C`. -/
class LiftObj (X : C) where
  lift : FreeMonoidalCategory C

instance liftObjUnit : LiftObj (𝟙_ C) where lift := Unit

instance liftObjTensor (X Y : C) [LiftObj X] [LiftObj Y] : LiftObj (X ⊗ Y) where lift := LiftObj.lift X ⊗ LiftObj.lift Y

instance (priority := 100) liftObjOf (X : C) : LiftObj X where lift := of X

/-- A typeclass carrying a choice of lift of a morphism from `C` to `free_monoidal_category C`. -/
class LiftHom {X Y : C} [LiftObj X] [LiftObj Y] (f : X ⟶ Y) where
  lift : LiftObj.lift X ⟶ LiftObj.lift Y

instance liftHomId (X : C) [LiftObj X] : LiftHom (𝟙 X) where lift := 𝟙 _

instance liftHomLeftUnitorHom (X : C) [LiftObj X] : LiftHom (λ_ X).Hom where lift := (λ_ (LiftObj.lift X)).Hom

instance liftHomLeftUnitorInv (X : C) [LiftObj X] : LiftHom (λ_ X).inv where lift := (λ_ (LiftObj.lift X)).inv

instance liftHomRightUnitorHom (X : C) [LiftObj X] : LiftHom (ρ_ X).Hom where lift := (ρ_ (LiftObj.lift X)).Hom

instance liftHomRightUnitorInv (X : C) [LiftObj X] : LiftHom (ρ_ X).inv where lift := (ρ_ (LiftObj.lift X)).inv

instance liftHomAssociatorHom (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] :
    LiftHom (α_ X Y Z).Hom where lift := (α_ (LiftObj.lift X) (LiftObj.lift Y) (LiftObj.lift Z)).Hom

instance liftHomAssociatorInv (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] :
    LiftHom (α_ X Y Z).inv where lift := (α_ (LiftObj.lift X) (LiftObj.lift Y) (LiftObj.lift Z)).inv

instance liftHomComp {X Y Z : C} [LiftObj X] [LiftObj Y] [LiftObj Z] (f : X ⟶ Y) (g : Y ⟶ Z) [LiftHom f] [LiftHom g] :
    LiftHom (f ≫ g) where lift := LiftHom.lift f ≫ LiftHom.lift g

instance liftHomTensor {W X Y Z : C} [LiftObj W] [LiftObj X] [LiftObj Y] [LiftObj Z] (f : W ⟶ X) (g : Y ⟶ Z) [LiftHom f]
    [LiftHom g] : LiftHom (f ⊗ g) where lift := LiftHom.lift f ⊗ LiftHom.lift g

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`Hom] []
/-- A typeclass carrying a choice of monoidal structural isomorphism between two objects.
Used by the `⊗≫` monoidal composition operator, and the `coherence` tactic.
-/
-- We could likely turn this into a `Prop` valued existential if that proves useful.
class MonoidalCoherence (X Y : C) [LiftObj X] [LiftObj Y] where
  Hom : X ⟶ Y
  [IsIso : IsIso hom]

attribute [instance] monoidal_coherence.is_iso

namespace MonoidalCoherence

@[simps]
instance refl (X : C) [LiftObj X] : MonoidalCoherence X X :=
  ⟨𝟙 _⟩

@[simps]
instance tensor (X Y Z : C) [LiftObj X] [LiftObj Y] [LiftObj Z] [MonoidalCoherence Y Z] :
    MonoidalCoherence (X ⊗ Y) (X ⊗ Z) :=
  ⟨𝟙 X ⊗ MonoidalCoherence.hom Y Z⟩

@[simps]
instance tensorRight (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence (𝟙_ C) Y] : MonoidalCoherence X (X ⊗ Y) :=
  ⟨(ρ_ X).inv ≫ (𝟙 X ⊗ MonoidalCoherence.hom (𝟙_ C) Y)⟩

@[simps]
instance tensorRight' (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence Y (𝟙_ C)] : MonoidalCoherence (X ⊗ Y) X :=
  ⟨(𝟙 X ⊗ MonoidalCoherence.hom Y (𝟙_ C)) ≫ (ρ_ X).Hom⟩

@[simps]
instance left (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] : MonoidalCoherence (𝟙_ C ⊗ X) Y :=
  ⟨(λ_ X).Hom ≫ MonoidalCoherence.hom X Y⟩

@[simps]
instance left' (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] : MonoidalCoherence X (𝟙_ C ⊗ Y) :=
  ⟨MonoidalCoherence.hom X Y ≫ (λ_ Y).inv⟩

@[simps]
instance right (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] : MonoidalCoherence (X ⊗ 𝟙_ C) Y :=
  ⟨(ρ_ X).Hom ≫ MonoidalCoherence.hom X Y⟩

@[simps]
instance right' (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] : MonoidalCoherence X (Y ⊗ 𝟙_ C) :=
  ⟨MonoidalCoherence.hom X Y ≫ (ρ_ Y).inv⟩

@[simps]
instance assoc (X Y Z W : C) [LiftObj W] [LiftObj X] [LiftObj Y] [LiftObj Z] [MonoidalCoherence (X ⊗ Y ⊗ Z) W] :
    MonoidalCoherence ((X ⊗ Y) ⊗ Z) W :=
  ⟨(α_ X Y Z).Hom ≫ MonoidalCoherence.hom (X ⊗ Y ⊗ Z) W⟩

@[simps]
instance assoc' (W X Y Z : C) [LiftObj W] [LiftObj X] [LiftObj Y] [LiftObj Z] [MonoidalCoherence W (X ⊗ Y ⊗ Z)] :
    MonoidalCoherence W ((X ⊗ Y) ⊗ Z) :=
  ⟨MonoidalCoherence.hom W (X ⊗ Y ⊗ Z) ≫ (α_ X Y Z).inv⟩

end MonoidalCoherence

/-- Construct an isomorphism between two objects in a monoidal category
out of unitors and associators. -/
def monoidalIso (X Y : C) [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] : X ≅ Y :=
  asIso (MonoidalCoherence.hom X Y)

example (X : C) : X ≅ X ⊗ 𝟙_ C ⊗ 𝟙_ C :=
  monoidalIso _ _

example (X1 X2 X3 X4 X5 X6 X7 X8 X9 : C) :
    𝟙_ C ⊗ (X1 ⊗ X2 ⊗ (X3 ⊗ X4) ⊗ X5) ⊗ X6 ⊗ X7 ⊗ X8 ⊗ X9 ≅ X1 ⊗ (X2 ⊗ X3) ⊗ X4 ⊗ (X5 ⊗ (𝟙_ C ⊗ X6) ⊗ X7) ⊗ X8 ⊗ X9 :=
  monoidalIso _ _

/-- Compose two morphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
def monoidalComp {W X Y Z : C} [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] (f : W ⟶ X) (g : Y ⟶ Z) : W ⟶ Z :=
  f ≫ MonoidalCoherence.hom X Y ≫ g

-- mathport name: «expr ⊗≫ »
infixr:80 " ⊗≫ " => monoidalComp

/-- Compose two isomorphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
-- type as \ot \gg
def monoidalIsoComp {W X Y Z : C} [LiftObj X] [LiftObj Y] [MonoidalCoherence X Y] (f : W ≅ X) (g : Y ≅ Z) : W ≅ Z :=
  f ≪≫ asIso (MonoidalCoherence.hom X Y) ≪≫ g

-- mathport name: «expr ≪⊗≫ »
infixr:80 " ≪⊗≫ " => monoidalIsoComp

-- type as \ot \gg
example {U V W X Y : C} (f : U ⟶ V ⊗ W ⊗ X) (g : (V ⊗ W) ⊗ X ⟶ Y) : U ⟶ Y :=
  f ⊗≫ g

-- To automatically insert unitors/associators at the beginning or end,
-- you can use `f ⊗≫ 𝟙 _`
example {W X Y Z : C} (f : W ⟶ (X ⊗ Y) ⊗ Z) : W ⟶ X ⊗ Y ⊗ Z :=
  f ⊗≫ 𝟙 _

@[simp]
theorem monoidal_comp_refl {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : f ⊗≫ g = f ≫ g := by
  dsimp' [← monoidal_comp]
  simp

example {U V W X Y : C} (f : U ⟶ V ⊗ W ⊗ X) (g : (V ⊗ W) ⊗ X ⟶ Y) : f ⊗≫ g = f ≫ (α_ _ _ _).inv ≫ g := by
  simp [← monoidal_comp]

end CategoryTheory.MonoidalCategory

open CategoryTheory.MonoidalCategory

namespace Tactic

open Tactic

setup_tactic_parser

/-- Auxilliary definition of `monoidal_coherence`,
being careful with namespaces to avoid shadowing.
-/
unsafe def mk_project_map_expr (e : expr) : tactic expr :=
  to_expr
    (pquote.1
      (CategoryTheory.FreeMonoidalCategory.projectMap id _ _ (CategoryTheory.MonoidalCategory.LiftHom.lift (%%ₓe))))

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- Coherence tactic for monoidal categories. -/
unsafe def monoidal_coherence : tactic Unit := do
  let o ← get_options
  set_options <| o `class.instance_max_depth 128
  try sorry
  let quote.1 ((%%ₓlhs) = %%ₓrhs) ← target
  let project_map_lhs ← mk_project_map_expr lhs
  let project_map_rhs ← mk_project_map_expr rhs
  to_expr (pquote.1 ((%%ₓproject_map_lhs) = %%ₓproject_map_rhs)) >>= tactic.change
  congr

/-- `pure_coherence` uses the coherence theorem for monoidal categories to prove the goal.
It can prove any equality made up only of associators, unitors, and identities.
```lean
example {C : Type} [category C] [monoidal_category C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
by pure_coherence
```

Users will typicall just use the `coherence` tactic, which can also cope with identities of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `pure_coherence`
-/
unsafe def pure_coherence : tactic Unit :=
  monoidal_coherence <|> bicategorical_coherence

example (X₁ X₂ : C) :
    ((λ_ (𝟙_ C)).inv ⊗ 𝟙 (X₁ ⊗ X₂)) ≫ (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).Hom ≫ (𝟙 (𝟙_ C) ⊗ (α_ (𝟙_ C) X₁ X₂).inv) =
      𝟙 (𝟙_ C) ⊗ (λ_ X₁).inv ⊗ 𝟙 X₂ :=
  by
  run_tac
    pure_coherence

namespace Coherence

/-- Auxiliary simp lemma for the `coherence` tactic:
this moves brackets to the left in order to expose a maximal prefix
built out of unitors and associators.
-/
-- We have unused typeclass arguments here.
-- They are intentional, to ensure that `simp only [assoc_lift_hom]` only left associates
-- monoidal structural morphisms.
@[nolint unused_arguments]
theorem assoc_lift_hom {W X Y Z : C} [LiftObj W] [LiftObj X] [LiftObj Y] (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) [LiftHom f]
    [LiftHom g] : f ≫ g ≫ h = (f ≫ g) ≫ h :=
  (Category.assoc _ _ _).symm

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- Internal tactic used in `coherence`.

Rewrites an equation `f = g` as `f₀ ≫ f₁ = g₀ ≫ g₁`,
where `f₀` and `g₀` are maximal prefixes of `f` and `g` (possibly after reassociating)
which are "liftable" (i.e. expressible as compositions of unitors and associators).
-/
unsafe def liftable_prefixes : tactic Unit := do
  let o ← get_options
  set_options <| o `class.instance_max_depth 128
  (try sorry >> sorry) >> try sorry

example {W X Y Z : C} (f : Y ⟶ Z) (g) (w : False) : (λ_ _).Hom ≫ f = g := by
  run_tac
    liftable_prefixes
  guard_target =ₐ (𝟙 _ ≫ (λ_ _).Hom) ≫ f = 𝟙 _ ≫ g
  cases w

theorem insert_id_lhs {C : Type _} [Category C] {X Y : C} (f g : X ⟶ Y) (w : f ≫ 𝟙 _ = g) : f = g := by
  simpa using w

theorem insert_id_rhs {C : Type _} [Category C] {X Y : C} (f g : X ⟶ Y) (w : f = g ≫ 𝟙 _) : f = g := by
  simpa using w

end Coherence

open Coherence

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- The main part of `coherence` tactic. -/
unsafe def coherence_loop : tactic Unit := do
  -- To prove an equality `f = g` in a monoidal category,
      -- first try the `pure_coherence` tactic on the entire equation:
      pure_coherence <|>
      do
      -- Otherwise, rearrange so we have a maximal prefix of each side
          -- that is built out of unitors and associators:
          liftable_prefixes <|>
          fail
            ("Something went wrong in the `coherence` tactic: " ++ "is the target an equation in a monoidal category?")
      -- The goal should now look like `f₀ ≫ f₁ = g₀ ≫ g₁`,
        tactic.congr_core'
      -- and now we have two goals `f₀ = g₀` and `f₁ = g₁`.
            -- Discharge the first using `coherence`,
            focus1
            pure_coherence <|>
          fail "`coherence` tactic failed, subgoal not true in the free monoidal_category"
      -- Then check that either `g₀` is identically `g₁`,
          reflexivity <|>
          do
          (-- or that both are compositions,
              do
                let quote.1 (_ ≫ _ = _) ← target
                skip) <|>
              sorry
          (do
                let quote.1 (_ = _ ≫ _) ← target
                skip) <|>
              sorry
          let quote.1 (_ ≫ _ = _ ≫ _) ← target | fail "`coherence` tactic failed, non-structural morphisms don't match"
          tactic.congr_core'
          -- with identical first terms,
              reflexivity <|>
              fail "`coherence` tactic failed, non-structural morphisms don't match"
          -- and whose second terms can be identified by recursively called `coherence`.
            coherence_loop

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- Use the coherence theorem for monoidal categories to solve equations in a monoidal equation,
where the two sides only differ by replacing strings of monoidal structural morphisms
(that is, associators, unitors, and identities)
with different strings of structural morphisms with the same source and target.

That is, `coherence` can handle goals of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `pure_coherence`.

(If you have very large equations on which `coherence` is unexpectedly failing,
you may need to increase the typeclass search depth,
using e.g. `set_option class.instance_max_depth 500`.)
-/
unsafe def coherence : tactic Unit := do
  try sorry
  try sorry
  -- TODO: put similar normalization simp lemmas for monoidal categories
      try
      bicategory.whisker_simps
  coherence_loop

run_cmd
  add_interactive [`pure_coherence, `coherence]

add_tactic_doc
  { Name := "coherence", category := DocCategory.tactic, declNames := [`tactic.interactive.coherence],
    tags := ["category theory"] }

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]
example (f) : (λ_ (𝟙_ C)).Hom ≫ f ≫ (λ_ (𝟙_ C)).Hom = (ρ_ (𝟙_ C)).Hom ≫ f ≫ (ρ_ (𝟙_ C)).Hom := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]"

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]
example {U V W X Y : C} (f : U ⟶ V ⊗ W ⊗ X) (g : (V ⊗ W) ⊗ X ⟶ Y) : f ⊗≫ g = f ≫ (α_ _ _ _).inv ≫ g := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]"

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]
example {U : C} (f : U ⟶ 𝟙_ C) : f ≫ (ρ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).Hom = f := by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]"

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]
example (W X Y Z : C) (f) :
    ((α_ W X Y).Hom ⊗ 𝟙 Z) ≫
        (α_ W (X ⊗ Y) Z).Hom ≫ (𝟙 W ⊗ (α_ X Y Z).Hom) ≫ f ≫ (α_ (W ⊗ X) Y Z).Hom ≫ (α_ W X (Y ⊗ Z)).Hom =
      (α_ (W ⊗ X) Y Z).Hom ≫
        (α_ W X (Y ⊗ Z)).Hom ≫ f ≫ ((α_ W X Y).Hom ⊗ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).Hom ≫ (𝟙 W ⊗ (α_ X Y Z).Hom) :=
  by
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `coherence #[]"

end Tactic


/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.CategoryTheory.DiscreteCategory
import Mathbin.CategoryTheory.EpiMono
import Mathbin.CategoryTheory.Over

/-!
# Binary (co)products

We define a category `walking_pair`, which is the index category
for a binary (co)product diagram. A convenience method `pair X Y`
constructs the functor from the walking pair, hitting the given objects.

We define `prod X Y` and `coprod X Y` as limits and colimits of such functors.

Typeclasses `has_binary_products` and `has_binary_coproducts` assert the existence
of (co)limits shaped as walking pairs.

We include lemmas for simplifying equations involving projections and coprojections, and define
braiding and associating isomorphisms, and the product comparison morphism.

## References
* [Stacks: Products of pairs](https://stacks.math.columbia.edu/tag/001R)
* [Stacks: coproducts of pairs](https://stacks.math.columbia.edu/tag/04AN)
-/


noncomputable section

universe v u u₂

open CategoryTheory

namespace CategoryTheory.Limits

/-- The type of objects for the diagram indexing a binary (co)product. -/
inductive WalkingPair : Type
  | left
  | right
  deriving DecidableEq, Inhabited

open WalkingPair

/-- The equivalence swapping left and right.
-/
def WalkingPair.swap : walking_pair ≃ walking_pair where
  toFun := fun j => WalkingPair.recOn j right left
  invFun := fun j => WalkingPair.recOn j right left
  left_inv := fun j => by
    cases j <;> rfl
  right_inv := fun j => by
    cases j <;> rfl

@[simp]
theorem WalkingPair.swap_apply_left : WalkingPair.swap left = right :=
  rfl

@[simp]
theorem WalkingPair.swap_apply_right : WalkingPair.swap right = left :=
  rfl

@[simp]
theorem WalkingPair.swap_symm_apply_tt : WalkingPair.swap.symm left = right :=
  rfl

@[simp]
theorem WalkingPair.swap_symm_apply_ff : WalkingPair.swap.symm right = left :=
  rfl

/-- An equivalence from `walking_pair` to `bool`, sometimes useful when reindexing limits.
-/
def WalkingPair.equivBool : walking_pair ≃ Bool where
  toFun := fun j => WalkingPair.recOn j true false
  -- to match equiv.sum_equiv_sigma_bool
  invFun := fun b => Bool.recOn b right left
  left_inv := fun j => by
    cases j <;> rfl
  right_inv := fun b => by
    cases b <;> rfl

@[simp]
theorem WalkingPair.equiv_bool_apply_left : WalkingPair.equivBool left = tt :=
  rfl

@[simp]
theorem WalkingPair.equiv_bool_apply_right : WalkingPair.equivBool right = ff :=
  rfl

@[simp]
theorem WalkingPair.equiv_bool_symm_apply_tt : WalkingPair.equivBool.symm true = left :=
  rfl

@[simp]
theorem WalkingPair.equiv_bool_symm_apply_ff : WalkingPair.equivBool.symm false = right :=
  rfl

variable {C : Type u}

/-- The function on the walking pair, sending the two points to `X` and `Y`. -/
def pairFunction (X Y : C) : WalkingPair → C := fun j => WalkingPair.casesOn j X Y

@[simp]
theorem pair_function_left (X Y : C) : pairFunction X Y left = X :=
  rfl

@[simp]
theorem pair_function_right (X Y : C) : pairFunction X Y right = Y :=
  rfl

variable [Category.{v} C]

/-- The diagram on the walking pair, sending the two points to `X` and `Y`. -/
def pair (X Y : C) : Discrete WalkingPair ⥤ C :=
  Discrete.functor fun j => WalkingPair.casesOn j X Y

@[simp]
theorem pair_obj_left (X Y : C) : (pair X Y).obj ⟨left⟩ = X :=
  rfl

@[simp]
theorem pair_obj_right (X Y : C) : (pair X Y).obj ⟨right⟩ = Y :=
  rfl

section

variable {F G : Discrete WalkingPair ⥤ C} (f : F.obj ⟨left⟩ ⟶ G.obj ⟨left⟩) (g : F.obj ⟨right⟩ ⟶ G.obj ⟨right⟩)

attribute [local tidy] tactic.discrete_cases

/-- The natural transformation between two functors out of the
 walking pair, specified by its
components. -/
def mapPair : F ⟶ G where app := fun j => Discrete.recOn j fun j => WalkingPair.casesOn j f g

@[simp]
theorem map_pair_left : (mapPair f g).app ⟨left⟩ = f :=
  rfl

@[simp]
theorem map_pair_right : (mapPair f g).app ⟨right⟩ = g :=
  rfl

/-- The natural isomorphism between two functors out of the walking pair, specified by its
components. -/
@[simps]
def mapPairIso (f : F.obj ⟨left⟩ ≅ G.obj ⟨left⟩) (g : F.obj ⟨right⟩ ≅ G.obj ⟨right⟩) : F ≅ G :=
  NatIso.ofComponents (fun j => Discrete.recOn j fun j => WalkingPair.casesOn j f g)
    (by
      tidy)

end

/-- Every functor out of the walking pair is naturally isomorphic (actually, equal) to a `pair` -/
@[simps]
def diagramIsoPair (F : Discrete WalkingPair ⥤ C) : F ≅ pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩) :=
  mapPairIso (Iso.refl _) (Iso.refl _)

section

variable {D : Type u} [Category.{v} D]

/-- The natural isomorphism between `pair X Y ⋙ F` and `pair (F.obj X) (F.obj Y)`. -/
def pairComp (X Y : C) (F : C ⥤ D) : pair X Y ⋙ F ≅ pair (F.obj X) (F.obj Y) :=
  diagramIsoPair _

end

/-- A binary fan is just a cone on a diagram indexing a product. -/
abbrev BinaryFan (X Y : C) :=
  Cone (pair X Y)

/-- The first projection of a binary fan. -/
abbrev BinaryFan.fst {X Y : C} (s : BinaryFan X Y) :=
  s.π.app ⟨WalkingPair.left⟩

/-- The second projection of a binary fan. -/
abbrev BinaryFan.snd {X Y : C} (s : BinaryFan X Y) :=
  s.π.app ⟨WalkingPair.right⟩

@[simp]
theorem BinaryFan.π_app_left {X Y : C} (s : BinaryFan X Y) : s.π.app ⟨WalkingPair.left⟩ = s.fst :=
  rfl

@[simp]
theorem BinaryFan.π_app_right {X Y : C} (s : BinaryFan X Y) : s.π.app ⟨WalkingPair.right⟩ = s.snd :=
  rfl

/-- A convenient way to show that a binary fan is a limit. -/
def BinaryFan.IsLimit.mk {X Y : C} (s : BinaryFan X Y) (lift : ∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y), T ⟶ s.x)
    (hl₁ : ∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ s.fst = f)
    (hl₂ : ∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ s.snd = g)
    (uniq : ∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y) (m : T ⟶ s.x) (h₁ : m ≫ s.fst = f) (h₂ : m ≫ s.snd = g), m = lift f g) :
    IsLimit s :=
  IsLimit.mk (fun t => lift (BinaryFan.fst t) (BinaryFan.snd t))
    (by
      rintro t (rfl | rfl)
      · exact hl₁ _ _
        
      · exact hl₂ _ _
        )
    fun t m h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)

theorem BinaryFan.IsLimit.hom_ext {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) {f g : W ⟶ s.x}
    (h₁ : f ≫ s.fst = g ≫ s.fst) (h₂ : f ≫ s.snd = g ≫ s.snd) : f = g :=
  h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂

/-- A binary cofan is just a cocone on a diagram indexing a coproduct. -/
abbrev BinaryCofan (X Y : C) :=
  Cocone (pair X Y)

/-- The first inclusion of a binary cofan. -/
abbrev BinaryCofan.inl {X Y : C} (s : BinaryCofan X Y) :=
  s.ι.app ⟨WalkingPair.left⟩

/-- The second inclusion of a binary cofan. -/
abbrev BinaryCofan.inr {X Y : C} (s : BinaryCofan X Y) :=
  s.ι.app ⟨WalkingPair.right⟩

@[simp]
theorem BinaryCofan.ι_app_left {X Y : C} (s : BinaryCofan X Y) : s.ι.app ⟨WalkingPair.left⟩ = s.inl :=
  rfl

@[simp]
theorem BinaryCofan.ι_app_right {X Y : C} (s : BinaryCofan X Y) : s.ι.app ⟨WalkingPair.right⟩ = s.inr :=
  rfl

/-- A convenient way to show that a binary cofan is a colimit. -/
def BinaryCofan.IsColimit.mk {X Y : C} (s : BinaryCofan X Y) (desc : ∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T), s.x ⟶ T)
    (hd₁ : ∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T), s.inl ≫ desc f g = f)
    (hd₂ : ∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T), s.inr ≫ desc f g = g)
    (uniq : ∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T) (m : s.x ⟶ T) (h₁ : s.inl ≫ m = f) (h₂ : s.inr ≫ m = g), m = desc f g) :
    IsColimit s :=
  IsColimit.mk (fun t => desc (BinaryCofan.inl t) (BinaryCofan.inr t))
    (by
      rintro t (rfl | rfl)
      · exact hd₁ _ _
        
      · exact hd₂ _ _
        )
    fun t m h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)

theorem BinaryCofan.IsColimit.hom_ext {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s) {f g : s.x ⟶ W}
    (h₁ : s.inl ≫ f = s.inl ≫ g) (h₂ : s.inr ≫ f = s.inr ≫ g) : f = g :=
  h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂

variable {X Y : C}

section

attribute [local tidy] tactic.discrete_cases

/-- A binary fan with vertex `P` consists of the two projections `π₁ : P ⟶ X` and `π₂ : P ⟶ Y`. -/
@[simps x]
def BinaryFan.mk {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : BinaryFan X Y where
  x := P
  π := { app := fun j => Discrete.recOn j fun j => WalkingPair.casesOn j π₁ π₂ }

/-- A binary cofan with vertex `P` consists of the two inclusions `ι₁ : X ⟶ P` and `ι₂ : Y ⟶ P`. -/
@[simps x]
def BinaryCofan.mk {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : BinaryCofan X Y where
  x := P
  ι := { app := fun j => Discrete.recOn j fun j => WalkingPair.casesOn j ι₁ ι₂ }

end

@[simp]
theorem BinaryFan.mk_fst {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : (BinaryFan.mk π₁ π₂).fst = π₁ :=
  rfl

@[simp]
theorem BinaryFan.mk_snd {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : (BinaryFan.mk π₁ π₂).snd = π₂ :=
  rfl

@[simp]
theorem BinaryCofan.mk_inl {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : (BinaryCofan.mk ι₁ ι₂).inl = ι₁ :=
  rfl

@[simp]
theorem BinaryCofan.mk_inr {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : (BinaryCofan.mk ι₁ ι₂).inr = ι₂ :=
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
/-- Every `binary_fan` is isomorphic to an application of `binary_fan.mk`. -/
def isoBinaryFanMk {X Y : C} (c : BinaryFan X Y) : c ≅ BinaryFan.mk c.fst c.snd :=
  Cones.ext (Iso.refl _) fun j => by
    trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]" <;>
      cases j <;> tidy

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
/-- Every `binary_fan` is isomorphic to an application of `binary_fan.mk`. -/
def isoBinaryCofanMk {X Y : C} (c : BinaryCofan X Y) : c ≅ BinaryCofan.mk c.inl c.inr :=
  Cocones.ext (Iso.refl _) fun j => by
    trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]" <;>
      cases j <;> tidy

/-- If `s` is a limit binary fan over `X` and `Y`, then every pair of morphisms `f : W ⟶ X` and
    `g : W ⟶ Y` induces a morphism `l : W ⟶ s.X` satisfying `l ≫ s.fst = f` and `l ≫ s.snd = g`.
    -/
@[simps]
def BinaryFan.IsLimit.lift' {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X) (g : W ⟶ Y) :
    { l : W ⟶ s.x // l ≫ s.fst = f ∧ l ≫ s.snd = g } :=
  ⟨h.lift <| BinaryFan.mk f g, h.fac _ _, h.fac _ _⟩

/-- If `s` is a colimit binary cofan over `X` and `Y`,, then every pair of morphisms `f : X ⟶ W` and
    `g : Y ⟶ W` induces a morphism `l : s.X ⟶ W` satisfying `s.inl ≫ l = f` and `s.inr ≫ l = g`.
    -/
@[simps]
def BinaryCofan.IsColimit.desc' {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s) (f : X ⟶ W) (g : Y ⟶ W) :
    { l : s.x ⟶ W // s.inl ≫ l = f ∧ s.inr ≫ l = g } :=
  ⟨h.desc <| BinaryCofan.mk f g, h.fac _ _, h.fac _ _⟩

/-- An abbreviation for `has_limit (pair X Y)`. -/
abbrev HasBinaryProduct (X Y : C) :=
  HasLimit (pair X Y)

/-- An abbreviation for `has_colimit (pair X Y)`. -/
abbrev HasBinaryCoproduct (X Y : C) :=
  HasColimit (pair X Y)

/-- If we have a product of `X` and `Y`, we can access it using `prod X Y` or
    `X ⨯ Y`. -/
abbrev prod (X Y : C) [HasBinaryProduct X Y] :=
  limit (pair X Y)

/-- If we have a coproduct of `X` and `Y`, we can access it using `coprod X Y ` or
    `X ⨿ Y`. -/
abbrev coprod (X Y : C) [HasBinaryCoproduct X Y] :=
  colimit (pair X Y)

-- mathport name: «expr ⨯ »
notation:20 X " ⨯ " Y:20 => prod X Y

-- mathport name: «expr ⨿ »
notation:20 X " ⨿ " Y:20 => coprod X Y

/-- The projection map to the first component of the product. -/
abbrev prod.fst {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ X :=
  limit.π (pair X Y) ⟨WalkingPair.left⟩

/-- The projecton map to the second component of the product. -/
abbrev prod.snd {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ Y :=
  limit.π (pair X Y) ⟨WalkingPair.right⟩

/-- The inclusion map from the first component of the coproduct. -/
abbrev coprod.inl {X Y : C} [HasBinaryCoproduct X Y] : X ⟶ X ⨿ Y :=
  colimit.ι (pair X Y) ⟨WalkingPair.left⟩

/-- The inclusion map from the second component of the coproduct. -/
abbrev coprod.inr {X Y : C} [HasBinaryCoproduct X Y] : Y ⟶ X ⨿ Y :=
  colimit.ι (pair X Y) ⟨WalkingPair.right⟩

/-- The binary fan constructed from the projection maps is a limit. -/
def prodIsProd (X Y : C) [HasBinaryProduct X Y] : IsLimit (BinaryFan.mk (prod.fst : X ⨯ Y ⟶ X) prod.snd) :=
  (limit.isLimit _).ofIsoLimit
    (Cones.ext (Iso.refl _)
      (by
        rintro (_ | _)
        tidy))

/-- The binary cofan constructed from the coprojection maps is a colimit. -/
def coprodIsCoprod (X Y : C) [HasBinaryCoproduct X Y] :
    IsColimit (BinaryCofan.mk (coprod.inl : X ⟶ X ⨿ Y) coprod.inr) :=
  (colimit.isColimit _).ofIsoColimit
    (Cocones.ext (Iso.refl _)
      (by
        rintro (_ | _)
        tidy))

@[ext]
theorem prod.hom_ext {W X Y : C} [HasBinaryProduct X Y] {f g : W ⟶ X ⨯ Y} (h₁ : f ≫ Prod.fst = g ≫ Prod.fst)
    (h₂ : f ≫ Prod.snd = g ≫ Prod.snd) : f = g :=
  BinaryFan.IsLimit.hom_ext (limit.isLimit _) h₁ h₂

@[ext]
theorem coprod.hom_ext {W X Y : C} [HasBinaryCoproduct X Y] {f g : X ⨿ Y ⟶ W} (h₁ : coprod.inl ≫ f = coprod.inl ≫ g)
    (h₂ : coprod.inr ≫ f = coprod.inr ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (colimit.isColimit _) h₁ h₂

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` and `g : W ⟶ Y`
    induces a morphism `prod.lift f g : W ⟶ X ⨯ Y`. -/
abbrev prod.lift {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⨯ Y :=
  limit.lift _ (BinaryFan.mk f g)

/-- diagonal arrow of the binary product in the category `fam I` -/
abbrev diag (X : C) [HasBinaryProduct X X] : X ⟶ X ⨯ X :=
  prod.lift (𝟙 _) (𝟙 _)

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W` and
    `g : Y ⟶ W` induces a morphism `coprod.desc f g : X ⨿ Y ⟶ W`. -/
abbrev coprod.desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) : X ⨿ Y ⟶ W :=
  colimit.desc _ (BinaryCofan.mk f g)

/-- codiagonal arrow of the binary coproduct -/
abbrev codiag (X : C) [HasBinaryCoproduct X X] : X ⨿ X ⟶ X :=
  coprod.desc (𝟙 _) (𝟙 _)

@[simp, reassoc]
theorem prod.lift_fst {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) : prod.lift f g ≫ Prod.fst = f :=
  limit.lift_π _ _

@[simp, reassoc]
theorem prod.lift_snd {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) : prod.lift f g ≫ Prod.snd = g :=
  limit.lift_π _ _

-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem coprod.inl_desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    coprod.inl ≫ coprod.desc f g = f :=
  colimit.ι_desc _ _

-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem coprod.inr_desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    coprod.inr ≫ coprod.desc f g = g :=
  colimit.ι_desc _ _

instance prod.mono_lift_of_mono_left {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) [Mono f] :
    Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_fst _ _

instance prod.mono_lift_of_mono_right {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) [Mono g] :
    Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_snd _ _

instance coprod.epi_desc_of_epi_left {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) [Epi f] :
    Epi (coprod.desc f g) :=
  epi_of_epi_fac <| coprod.inl_desc _ _

instance coprod.epi_desc_of_epi_right {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) [Epi g] :
    Epi (coprod.desc f g) :=
  epi_of_epi_fac <| coprod.inr_desc _ _

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` and `g : W ⟶ Y`
    induces a morphism `l : W ⟶ X ⨯ Y` satisfying `l ≫ prod.fst = f` and `l ≫ prod.snd = g`. -/
def prod.lift' {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    { l : W ⟶ X ⨯ Y // l ≫ Prod.fst = f ∧ l ≫ Prod.snd = g } :=
  ⟨prod.lift f g, prod.lift_fst _ _, prod.lift_snd _ _⟩

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W` and
    `g : Y ⟶ W` induces a morphism `l : X ⨿ Y ⟶ W` satisfying `coprod.inl ≫ l = f` and
    `coprod.inr ≫ l = g`. -/
def coprod.desc' {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    { l : X ⨿ Y ⟶ W // coprod.inl ≫ l = f ∧ coprod.inr ≫ l = g } :=
  ⟨coprod.desc f g, coprod.inl_desc _ _, coprod.inr_desc _ _⟩

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of morphisms `f : W ⟶ Y` and
    `g : X ⟶ Z` induces a morphism `prod.map f g : W ⨯ X ⟶ Y ⨯ Z`. -/
def prod.map {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) : W ⨯ X ⟶ Y ⨯ Z :=
  limMap (mapPair f g)

/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of morphisms `f : W ⟶ Y` and
    `g : W ⟶ Z` induces a morphism `coprod.map f g : W ⨿ X ⟶ Y ⨿ Z`. -/
def coprod.map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    W ⨿ X ⟶ Y ⨿ Z :=
  colimMap (mapPair f g)

section ProdLemmas

-- Making the reassoc version of this a simp lemma seems to be more harmful than helpful.
@[reassoc, simp]
theorem prod.comp_lift {V W X Y : C} [HasBinaryProduct X Y] (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) :
    f ≫ prod.lift g h = prod.lift (f ≫ g) (f ≫ h) := by
  ext <;> simp

theorem prod.comp_diag {X Y : C} [HasBinaryProduct Y Y] (f : X ⟶ Y) : f ≫ diag Y = prod.lift f f := by
  simp

@[simp, reassoc]
theorem prod.map_fst {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    prod.map f g ≫ Prod.fst = Prod.fst ≫ f :=
  lim_map_π _ _

@[simp, reassoc]
theorem prod.map_snd {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    prod.map f g ≫ Prod.snd = Prod.snd ≫ g :=
  lim_map_π _ _

@[simp]
theorem prod.map_id_id {X Y : C} [HasBinaryProduct X Y] : prod.map (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  ext <;> simp

@[simp]
theorem prod.lift_fst_snd {X Y : C} [HasBinaryProduct X Y] : prod.lift prod.fst prod.snd = 𝟙 (X ⨯ Y) := by
  ext <;> simp

@[simp, reassoc]
theorem prod.lift_map {V W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y)
    (k : X ⟶ Z) : prod.lift f g ≫ prod.map h k = prod.lift (f ≫ h) (g ≫ k) := by
  ext <;> simp

@[simp]
theorem prod.lift_fst_comp_snd_comp {W X Y Z : C} [HasBinaryProduct W Y] [HasBinaryProduct X Z] (g : W ⟶ X)
    (g' : Y ⟶ Z) : prod.lift (Prod.fst ≫ g) (Prod.snd ≫ g') = prod.map g g' := by
  rw [← prod.lift_map]
  simp

-- We take the right hand side here to be simp normal form, as this way composition lemmas for
-- `f ≫ h` and `g ≫ k` can fire (eg `id_comp`) , while `map_fst` and `map_snd` can still work just
-- as well.
@[simp, reassoc]
theorem prod.map_map {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryProduct A₁ B₁] [HasBinaryProduct A₂ B₂] [HasBinaryProduct A₃ B₃]
    (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) : prod.map f g ≫ prod.map h k = prod.map (f ≫ h) (g ≫ k) :=
  by
  ext <;> simp

-- TODO: is it necessary to weaken the assumption here?
@[reassoc]
theorem prod.map_swap {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y) [HasLimitsOfShape (Discrete WalkingPair) C] :
    prod.map (𝟙 X) f ≫ prod.map g (𝟙 B) = prod.map g (𝟙 A) ≫ prod.map (𝟙 Y) f := by
  simp

@[reassoc]
theorem prod.map_comp_id {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct X W] [HasBinaryProduct Z W]
    [HasBinaryProduct Y W] : prod.map (f ≫ g) (𝟙 W) = prod.map f (𝟙 W) ≫ prod.map g (𝟙 W) := by
  simp

@[reassoc]
theorem prod.map_id_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct W X] [HasBinaryProduct W Y]
    [HasBinaryProduct W Z] : prod.map (𝟙 W) (f ≫ g) = prod.map (𝟙 W) f ≫ prod.map (𝟙 W) g := by
  simp

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
    `g : X ≅ Z` induces an isomorphism `prod.map_iso f g : W ⨯ X ≅ Y ⨯ Z`. -/
@[simps]
def prod.mapIso {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ≅ Y) (g : X ≅ Z) :
    W ⨯ X ≅ Y ⨯ Z where
  Hom := prod.map f.Hom g.Hom
  inv := prod.map f.inv g.inv

instance is_iso_prod {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) [IsIso f]
    [IsIso g] : IsIso (prod.map f g) :=
  IsIso.of_iso (prod.mapIso (asIso f) (asIso g))

instance prod.map_mono {C : Type _} [Category C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f] [Mono g]
    [HasBinaryProduct W X] [HasBinaryProduct Y Z] : Mono (prod.map f g) :=
  ⟨fun A i₁ i₂ h => by
    ext
    · rw [← cancel_mono f]
      simpa using congr_arg (fun f => f ≫ Prod.fst) h
      
    · rw [← cancel_mono g]
      simpa using congr_arg (fun f => f ≫ Prod.snd) h
      ⟩

@[simp, reassoc]
theorem prod.diag_map {X Y : C} (f : X ⟶ Y) [HasBinaryProduct X X] [HasBinaryProduct Y Y] :
    diag X ≫ prod.map f f = f ≫ diag Y := by
  simp

@[simp, reassoc]
theorem prod.diag_map_fst_snd {X Y : C} [HasBinaryProduct X Y] [HasBinaryProduct (X ⨯ Y) (X ⨯ Y)] :
    diag (X ⨯ Y) ≫ prod.map prod.fst prod.snd = 𝟙 (X ⨯ Y) := by
  simp

@[simp, reassoc]
theorem prod.diag_map_fst_snd_comp [HasLimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C} (g : X ⟶ Y)
    (g' : X' ⟶ Y') : diag (X ⨯ X') ≫ prod.map (Prod.fst ≫ g) (Prod.snd ≫ g') = prod.map g g' := by
  simp

instance {X : C} [HasBinaryProduct X X] : SplitMono (diag X) where retraction := prod.fst

end ProdLemmas

section CoprodLemmas

@[simp, reassoc]
theorem coprod.desc_comp {V W X Y : C} [HasBinaryCoproduct X Y] (f : V ⟶ W) (g : X ⟶ V) (h : Y ⟶ V) :
    coprod.desc g h ≫ f = coprod.desc (g ≫ f) (h ≫ f) := by
  ext <;> simp

theorem coprod.diag_comp {X Y : C} [HasBinaryCoproduct X X] (f : X ⟶ Y) : codiag X ≫ f = coprod.desc f f := by
  simp

@[simp, reassoc]
theorem coprod.inl_map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    coprod.inl ≫ coprod.map f g = f ≫ coprod.inl :=
  ι_colim_map _ _

@[simp, reassoc]
theorem coprod.inr_map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    coprod.inr ≫ coprod.map f g = g ≫ coprod.inr :=
  ι_colim_map _ _

@[simp]
theorem coprod.map_id_id {X Y : C} [HasBinaryCoproduct X Y] : coprod.map (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  ext <;> simp

@[simp]
theorem coprod.desc_inl_inr {X Y : C} [HasBinaryCoproduct X Y] : coprod.desc coprod.inl coprod.inr = 𝟙 (X ⨿ Y) := by
  ext <;> simp

-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem coprod.map_desc {S T U V W : C} [HasBinaryCoproduct U W] [HasBinaryCoproduct T V] (f : U ⟶ S) (g : W ⟶ S)
    (h : T ⟶ U) (k : V ⟶ W) : coprod.map h k ≫ coprod.desc f g = coprod.desc (h ≫ f) (k ≫ g) := by
  ext <;> simp

@[simp]
theorem coprod.desc_comp_inl_comp_inr {W X Y Z : C} [HasBinaryCoproduct W Y] [HasBinaryCoproduct X Z] (g : W ⟶ X)
    (g' : Y ⟶ Z) : coprod.desc (g ≫ coprod.inl) (g' ≫ coprod.inr) = coprod.map g g' := by
  rw [← coprod.map_desc]
  simp

-- We take the right hand side here to be simp normal form, as this way composition lemmas for
-- `f ≫ h` and `g ≫ k` can fire (eg `id_comp`) , while `inl_map` and `inr_map` can still work just
-- as well.
@[simp, reassoc]
theorem coprod.map_map {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryCoproduct A₁ B₁] [HasBinaryCoproduct A₂ B₂]
    [HasBinaryCoproduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    coprod.map f g ≫ coprod.map h k = coprod.map (f ≫ h) (g ≫ k) := by
  ext <;> simp

-- I don't think it's a good idea to make any of the following three simp lemmas.
@[reassoc]
theorem coprod.map_swap {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y) [HasColimitsOfShape (Discrete WalkingPair) C] :
    coprod.map (𝟙 X) f ≫ coprod.map g (𝟙 B) = coprod.map g (𝟙 A) ≫ coprod.map (𝟙 Y) f := by
  simp

@[reassoc]
theorem coprod.map_comp_id {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryCoproduct Z W] [HasBinaryCoproduct Y W]
    [HasBinaryCoproduct X W] : coprod.map (f ≫ g) (𝟙 W) = coprod.map f (𝟙 W) ≫ coprod.map g (𝟙 W) := by
  simp

@[reassoc]
theorem coprod.map_id_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryCoproduct W X] [HasBinaryCoproduct W Y]
    [HasBinaryCoproduct W Z] : coprod.map (𝟙 W) (f ≫ g) = coprod.map (𝟙 W) f ≫ coprod.map (𝟙 W) g := by
  simp

/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
    `g : W ≅ Z` induces a isomorphism `coprod.map_iso f g : W ⨿ X ≅ Y ⨿ Z`. -/
@[simps]
def coprod.mapIso {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ≅ Y) (g : X ≅ Z) :
    W ⨿ X ≅ Y ⨿ Z where
  Hom := coprod.map f.Hom g.Hom
  inv := coprod.map f.inv g.inv

instance is_iso_coprod {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) [IsIso f]
    [IsIso g] : IsIso (coprod.map f g) :=
  IsIso.of_iso (coprod.mapIso (asIso f) (asIso g))

instance coprod.map_epi {C : Type _} [Category C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f] [Epi g]
    [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] : Epi (coprod.map f g) :=
  ⟨fun A i₁ i₂ h => by
    ext
    · rw [← cancel_epi f]
      simpa using congr_arg (fun f => coprod.inl ≫ f) h
      
    · rw [← cancel_epi g]
      simpa using congr_arg (fun f => coprod.inr ≫ f) h
      ⟩

-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem coprod.map_codiag {X Y : C} (f : X ⟶ Y) [HasBinaryCoproduct X X] [HasBinaryCoproduct Y Y] :
    coprod.map f f ≫ codiag Y = codiag X ≫ f := by
  simp

-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem coprod.map_inl_inr_codiag {X Y : C} [HasBinaryCoproduct X Y] [HasBinaryCoproduct (X ⨿ Y) (X ⨿ Y)] :
    coprod.map coprod.inl coprod.inr ≫ codiag (X ⨿ Y) = 𝟙 (X ⨿ Y) := by
  simp

-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem coprod.map_comp_inl_inr_codiag [HasColimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C} (g : X ⟶ Y)
    (g' : X' ⟶ Y') : coprod.map (g ≫ coprod.inl) (g' ≫ coprod.inr) ≫ codiag (Y ⨿ Y') = coprod.map g g' := by
  simp

end CoprodLemmas

variable (C)

/-- `has_binary_products` represents a choice of product for every pair of objects.

See <https://stacks.math.columbia.edu/tag/001T>.
-/
abbrev HasBinaryProducts :=
  HasLimitsOfShape (Discrete WalkingPair) C

/-- `has_binary_coproducts` represents a choice of coproduct for every pair of objects.

See <https://stacks.math.columbia.edu/tag/04AP>.
-/
abbrev HasBinaryCoproducts :=
  HasColimitsOfShape (Discrete WalkingPair) C

/-- If `C` has all limits of diagrams `pair X Y`, then it has all binary products -/
theorem has_binary_products_of_has_limit_pair [∀ {X Y : C}, HasLimit (pair X Y)] : HasBinaryProducts C :=
  { HasLimit := fun F => has_limit_of_iso (diagramIsoPair F).symm }

/-- If `C` has all colimits of diagrams `pair X Y`, then it has all binary coproducts -/
theorem has_binary_coproducts_of_has_colimit_pair [∀ {X Y : C}, HasColimit (pair X Y)] : HasBinaryCoproducts C :=
  { HasColimit := fun F => has_colimit_of_iso (diagramIsoPair F) }

section

variable {C}

/-- The braiding isomorphism which swaps a binary product. -/
@[simps]
def prod.braiding (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] : P ⨯ Q ≅ Q ⨯ P where
  Hom := prod.lift prod.snd prod.fst
  inv := prod.lift prod.snd prod.fst

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
theorem braid_natural [HasBinaryProducts C] {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    prod.map f g ≫ (prod.braiding _ _).Hom = (prod.braiding _ _).Hom ≫ prod.map g f := by
  simp

@[reassoc]
theorem prod.symmetry' (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    prod.lift prod.snd prod.fst ≫ prod.lift prod.snd prod.fst = 𝟙 (P ⨯ Q) :=
  (prod.braiding _ _).hom_inv_id

/-- The braiding isomorphism is symmetric. -/
@[reassoc]
theorem prod.symmetry (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    (prod.braiding P Q).Hom ≫ (prod.braiding Q P).Hom = 𝟙 _ :=
  (prod.braiding _ _).hom_inv_id

/-- The associator isomorphism for binary products. -/
@[simps]
def prod.associator [HasBinaryProducts C] (P Q R : C) : (P ⨯ Q) ⨯ R ≅ P ⨯ Q ⨯ R where
  Hom := prod.lift (Prod.fst ≫ Prod.fst) (prod.lift (Prod.fst ≫ Prod.snd) prod.snd)
  inv := prod.lift (prod.lift prod.fst (Prod.snd ≫ Prod.fst)) (Prod.snd ≫ Prod.snd)

@[reassoc]
theorem prod.pentagon [HasBinaryProducts C] (W X Y Z : C) :
    prod.map (prod.associator W X Y).Hom (𝟙 Z) ≫
        (prod.associator W (X ⨯ Y) Z).Hom ≫ prod.map (𝟙 W) (prod.associator X Y Z).Hom =
      (prod.associator (W ⨯ X) Y Z).Hom ≫ (prod.associator W X (Y ⨯ Z)).Hom :=
  by
  simp

@[reassoc]
theorem prod.associator_naturality [HasBinaryProducts C] {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    prod.map (prod.map f₁ f₂) f₃ ≫ (prod.associator Y₁ Y₂ Y₃).Hom =
      (prod.associator X₁ X₂ X₃).Hom ≫ prod.map f₁ (prod.map f₂ f₃) :=
  by
  simp

variable [HasTerminal C]

/-- The left unitor isomorphism for binary products with the terminal object. -/
@[simps]
def prod.leftUnitor (P : C) [HasBinaryProduct (⊤_ C) P] : (⊤_ C) ⨯ P ≅ P where
  Hom := prod.snd
  inv := prod.lift (terminal.from P) (𝟙 _)

/-- The right unitor isomorphism for binary products with the terminal object. -/
@[simps]
def prod.rightUnitor (P : C) [HasBinaryProduct P (⊤_ C)] : P ⨯ ⊤_ C ≅ P where
  Hom := prod.fst
  inv := prod.lift (𝟙 _) (terminal.from P)

@[reassoc]
theorem prod.left_unitor_hom_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    prod.map (𝟙 _) f ≫ (prod.leftUnitor Y).Hom = (prod.leftUnitor X).Hom ≫ f :=
  prod.map_snd _ _

@[reassoc]
theorem prod.left_unitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    (prod.leftUnitor X).inv ≫ prod.map (𝟙 _) f = f ≫ (prod.leftUnitor Y).inv := by
  rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, prod.left_unitor_hom_naturality]

@[reassoc]
theorem prod.right_unitor_hom_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    prod.map f (𝟙 _) ≫ (prod.rightUnitor Y).Hom = (prod.rightUnitor X).Hom ≫ f :=
  prod.map_fst _ _

@[reassoc]
theorem prod_right_unitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    (prod.rightUnitor X).inv ≫ prod.map f (𝟙 _) = f ≫ (prod.rightUnitor Y).inv := by
  rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, prod.right_unitor_hom_naturality]

theorem prod.triangle [HasBinaryProducts C] (X Y : C) :
    (prod.associator X (⊤_ C) Y).Hom ≫ prod.map (𝟙 X) (prod.leftUnitor Y).Hom =
      prod.map (prod.rightUnitor X).Hom (𝟙 Y) :=
  by
  tidy

end

section

variable {C} [HasBinaryCoproducts C]

/-- The braiding isomorphism which swaps a binary coproduct. -/
@[simps]
def coprod.braiding (P Q : C) : P ⨿ Q ≅ Q ⨿ P where
  Hom := coprod.desc coprod.inr coprod.inl
  inv := coprod.desc coprod.inr coprod.inl

@[reassoc]
theorem coprod.symmetry' (P Q : C) :
    coprod.desc coprod.inr coprod.inl ≫ coprod.desc coprod.inr coprod.inl = 𝟙 (P ⨿ Q) :=
  (coprod.braiding _ _).hom_inv_id

/-- The braiding isomorphism is symmetric. -/
theorem coprod.symmetry (P Q : C) : (coprod.braiding P Q).Hom ≫ (coprod.braiding Q P).Hom = 𝟙 _ :=
  coprod.symmetry' _ _

/-- The associator isomorphism for binary coproducts. -/
@[simps]
def coprod.associator (P Q R : C) : (P ⨿ Q) ⨿ R ≅ P ⨿ Q ⨿ R where
  Hom := coprod.desc (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr)
  inv := coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr)

theorem coprod.pentagon (W X Y Z : C) :
    coprod.map (coprod.associator W X Y).Hom (𝟙 Z) ≫
        (coprod.associator W (X ⨿ Y) Z).Hom ≫ coprod.map (𝟙 W) (coprod.associator X Y Z).Hom =
      (coprod.associator (W ⨿ X) Y Z).Hom ≫ (coprod.associator W X (Y ⨿ Z)).Hom :=
  by
  simp

theorem coprod.associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    coprod.map (coprod.map f₁ f₂) f₃ ≫ (coprod.associator Y₁ Y₂ Y₃).Hom =
      (coprod.associator X₁ X₂ X₃).Hom ≫ coprod.map f₁ (coprod.map f₂ f₃) :=
  by
  simp

variable [HasInitial C]

/-- The left unitor isomorphism for binary coproducts with the initial object. -/
@[simps]
def coprod.leftUnitor (P : C) : (⊥_ C) ⨿ P ≅ P where
  Hom := coprod.desc (initial.to P) (𝟙 _)
  inv := coprod.inr

/-- The right unitor isomorphism for binary coproducts with the initial object. -/
@[simps]
def coprod.rightUnitor (P : C) : P ⨿ ⊥_ C ≅ P where
  Hom := coprod.desc (𝟙 _) (initial.to P)
  inv := coprod.inl

theorem coprod.triangle (X Y : C) :
    (coprod.associator X (⊥_ C) Y).Hom ≫ coprod.map (𝟙 X) (coprod.leftUnitor Y).Hom =
      coprod.map (coprod.rightUnitor X).Hom (𝟙 Y) :=
  by
  tidy

end

section ProdFunctor

variable {C} [HasBinaryProducts C]

/-- The binary product functor. -/
@[simps]
def prod.functor : C ⥤ C ⥤ C where
  obj := fun X => { obj := fun Y => X ⨯ Y, map := fun Y Z => prod.map (𝟙 X) }
  map := fun Y Z f => { app := fun T => prod.map f (𝟙 T) }

/-- The product functor can be decomposed. -/
def prod.functorLeftComp (X Y : C) : prod.functor.obj (X ⨯ Y) ≅ prod.functor.obj Y ⋙ prod.functor.obj X :=
  NatIso.ofComponents (prod.associator _ _)
    (by
      tidy)

end ProdFunctor

section CoprodFunctor

variable {C} [HasBinaryCoproducts C]

/-- The binary coproduct functor. -/
@[simps]
def coprod.functor : C ⥤ C ⥤ C where
  obj := fun X => { obj := fun Y => X ⨿ Y, map := fun Y Z => coprod.map (𝟙 X) }
  map := fun Y Z f => { app := fun T => coprod.map f (𝟙 T) }

/-- The coproduct functor can be decomposed. -/
def coprod.functorLeftComp (X Y : C) : coprod.functor.obj (X ⨿ Y) ≅ coprod.functor.obj Y ⋙ coprod.functor.obj X :=
  NatIso.ofComponents (coprod.associator _ _)
    (by
      tidy)

end CoprodFunctor

section ProdComparison

universe w

variable {C} {D : Type u₂} [Category.{w} D]

variable (F : C ⥤ D) {A A' B B' : C}

variable [HasBinaryProduct A B] [HasBinaryProduct A' B']

variable [HasBinaryProduct (F.obj A) (F.obj B)] [HasBinaryProduct (F.obj A') (F.obj B')]

/-- The product comparison morphism.

In `category_theory/limits/preserves` we show this is always an iso iff F preserves binary products.
-/
def prodComparison (F : C ⥤ D) (A B : C) [HasBinaryProduct A B] [HasBinaryProduct (F.obj A) (F.obj B)] :
    F.obj (A ⨯ B) ⟶ F.obj A ⨯ F.obj B :=
  prod.lift (F.map prod.fst) (F.map prod.snd)

@[simp, reassoc]
theorem prod_comparison_fst : prodComparison F A B ≫ Prod.fst = F.map prod.fst :=
  prod.lift_fst _ _

@[simp, reassoc]
theorem prod_comparison_snd : prodComparison F A B ≫ Prod.snd = F.map prod.snd :=
  prod.lift_snd _ _

/-- Naturality of the prod_comparison morphism in both arguments. -/
@[reassoc]
theorem prod_comparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    F.map (prod.map f g) ≫ prodComparison F A' B' = prodComparison F A B ≫ prod.map (F.map f) (F.map g) := by
  rw [prod_comparison, prod_comparison, prod.lift_map, ← F.map_comp, ← F.map_comp, prod.comp_lift, ← F.map_comp,
    Prod.map_fst, ← F.map_comp, Prod.map_sndₓ]

/-- The product comparison morphism from `F(A ⨯ -)` to `FA ⨯ F-`, whose components are given by
`prod_comparison`.
-/
@[simps]
def prodComparisonNatTrans [HasBinaryProducts C] [HasBinaryProducts D] (F : C ⥤ D) (A : C) :
    prod.functor.obj A ⋙ F ⟶ F ⋙ prod.functor.obj (F.obj A) where
  app := fun B => prodComparison F A B
  naturality' := fun B B' f => by
    simp [← prod_comparison_natural]

@[reassoc]
theorem inv_prod_comparison_map_fst [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.fst = Prod.fst := by
  simp [← is_iso.inv_comp_eq]

@[reassoc]
theorem inv_prod_comparison_map_snd [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.snd = Prod.snd := by
  simp [← is_iso.inv_comp_eq]

/-- If the product comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
theorem prod_comparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A B)]
    [IsIso (prodComparison F A' B')] :
    inv (prodComparison F A B) ≫ F.map (prod.map f g) = prod.map (F.map f) (F.map g) ≫ inv (prodComparison F A' B') :=
  by
  rw [is_iso.eq_comp_inv, category.assoc, is_iso.inv_comp_eq, prod_comparison_natural]

/-- The natural isomorphism `F(A ⨯ -) ≅ FA ⨯ F-`, provided each `prod_comparison F A B` is an
isomorphism (as `B` changes).
-/
@[simps (config := { rhsMd := semireducible })]
def prodComparisonNatIso [HasBinaryProducts C] [HasBinaryProducts D] (A : C) [∀ B, IsIso (prodComparison F A B)] :
    prod.functor.obj A ⋙ F ≅ F ⋙ prod.functor.obj (F.obj A) :=
  { @asIso _ _ _ _ _ (NatIso.is_iso_of_is_iso_app ⟨_, _⟩) with Hom := prodComparisonNatTrans F A }

end ProdComparison

section CoprodComparison

universe w

variable {C} {D : Type u₂} [Category.{w} D]

variable (F : C ⥤ D) {A A' B B' : C}

variable [HasBinaryCoproduct A B] [HasBinaryCoproduct A' B']

variable [HasBinaryCoproduct (F.obj A) (F.obj B)] [HasBinaryCoproduct (F.obj A') (F.obj B')]

/-- The coproduct comparison morphism.

In `category_theory/limits/preserves` we show
this is always an iso iff F preserves binary coproducts.
-/
def coprodComparison (F : C ⥤ D) (A B : C) [HasBinaryCoproduct A B] [HasBinaryCoproduct (F.obj A) (F.obj B)] :
    F.obj A ⨿ F.obj B ⟶ F.obj (A ⨿ B) :=
  coprod.desc (F.map coprod.inl) (F.map coprod.inr)

@[simp, reassoc]
theorem coprod_comparison_inl : coprod.inl ≫ coprodComparison F A B = F.map coprod.inl :=
  coprod.inl_desc _ _

@[simp, reassoc]
theorem coprod_comparison_inr : coprod.inr ≫ coprodComparison F A B = F.map coprod.inr :=
  coprod.inr_desc _ _

/-- Naturality of the coprod_comparison morphism in both arguments. -/
@[reassoc]
theorem coprod_comparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    coprodComparison F A B ≫ F.map (coprod.map f g) = coprod.map (F.map f) (F.map g) ≫ coprodComparison F A' B' := by
  rw [coprod_comparison, coprod_comparison, coprod.map_desc, ← F.map_comp, ← F.map_comp, coprod.desc_comp, ← F.map_comp,
    coprod.inl_map, ← F.map_comp, coprod.inr_map]

/-- The coproduct comparison morphism from `FA ⨿ F-` to `F(A ⨿ -)`, whose components are given by
`coprod_comparison`.
-/
@[simps]
def coprodComparisonNatTrans [HasBinaryCoproducts C] [HasBinaryCoproducts D] (F : C ⥤ D) (A : C) :
    F ⋙ coprod.functor.obj (F.obj A) ⟶ coprod.functor.obj A ⋙ F where
  app := fun B => coprodComparison F A B
  naturality' := fun B B' f => by
    simp [← coprod_comparison_natural]

@[reassoc]
theorem map_inl_inv_coprod_comparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inl ≫ inv (coprodComparison F A B) = coprod.inl := by
  simp [← is_iso.inv_comp_eq]

@[reassoc]
theorem map_inr_inv_coprod_comparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inr ≫ inv (coprodComparison F A B) = coprod.inr := by
  simp [← is_iso.inv_comp_eq]

/-- If the coproduct comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
theorem coprod_comparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (coprodComparison F A B)]
    [IsIso (coprodComparison F A' B')] :
    inv (coprodComparison F A B) ≫ coprod.map (F.map f) (F.map g) =
      F.map (coprod.map f g) ≫ inv (coprodComparison F A' B') :=
  by
  rw [is_iso.eq_comp_inv, category.assoc, is_iso.inv_comp_eq, coprod_comparison_natural]

/-- The natural isomorphism `FA ⨿ F- ≅ F(A ⨿ -)`, provided each `coprod_comparison F A B` is an
isomorphism (as `B` changes).
-/
@[simps (config := { rhsMd := semireducible })]
def coprodComparisonNatIso [HasBinaryCoproducts C] [HasBinaryCoproducts D] (A : C)
    [∀ B, IsIso (coprodComparison F A B)] : F ⋙ coprod.functor.obj (F.obj A) ≅ coprod.functor.obj A ⋙ F :=
  { @asIso _ _ _ _ _ (NatIso.is_iso_of_is_iso_app ⟨_, _⟩) with Hom := coprodComparisonNatTrans F A }

end CoprodComparison

end CategoryTheory.Limits

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Auxiliary definition for `over.coprod`. -/
@[simps]
def Over.coprodObj [HasBinaryCoproducts C] {A : C} : Over A → Over A ⥤ Over A := fun f =>
  { obj := fun g => Over.mk (coprod.desc f.Hom g.Hom), map := fun g₁ g₂ k => Over.homMk (coprod.map (𝟙 _) k.left) }

/-- A category with binary coproducts has a functorial `sup` operation on over categories. -/
@[simps]
def Over.coprod [HasBinaryCoproducts C] {A : C} : Over A ⥤ Over A ⥤ Over A where
  obj := fun f => Over.coprodObj f
  map := fun f₁ f₂ k =>
    { app := fun g =>
        Over.homMk (coprod.map k.left (𝟙 _))
          (by
            dsimp'
            rw [coprod.map_desc, category.id_comp, over.w k]),
      naturality' := fun f g k => by
        ext <;>
          · dsimp'
            simp
             }
  map_id' := fun X => by
    ext <;>
      · dsimp'
        simp
        
  map_comp' := fun X Y Z f g => by
    ext <;>
      · dsimp'
        simp
        

end CategoryTheory


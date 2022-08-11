/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.CategoryTheory.DiscreteCategory

/-!
# Categorical (co)products

This file defines (co)products as special cases of (co)limits.

A product is the categorical generalization of the object `Π i, f i` where `f : ι → C`. It is a
limit cone over the diagram formed by `f`, implemented by converting `f` into a functor
`discrete ι ⥤ C`.

A coproduct is the dual concept.

## Main definitions

* a `fan` is a cone over a discrete category
* `fan.mk` constructs a fan from an indexed collection of maps
* a `pi` is a `limit (discrete.functor f)`

Each of these has a dual.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.
-/


noncomputable section

universe w v v₂ u u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {β : Type w}

variable {C : Type u} [Category.{v} C]

-- We don't need an analogue of `pair` (for binary products), `parallel_pair` (for equalizers),
-- or `(co)span`, since we already have `discrete.functor`.
attribute [local tidy] tactic.discrete_cases

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
abbrev Fan (f : β → C) :=
  Cone (Discrete.functor f)

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
abbrev Cofan (f : β → C) :=
  Cocone (Discrete.functor f)

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
@[simps]
def Fan.mk {f : β → C} (P : C) (p : ∀ b, P ⟶ f b) : Fan f where
  x := P
  π := { app := fun X => p X.as }

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
@[simps]
def Cofan.mk {f : β → C} (P : C) (p : ∀ b, f b ⟶ P) : Cofan f where
  x := P
  ι := { app := fun X => p X.as }

/-- Get the `j`th map in the fan -/
-- FIXME dualize as needed below (and rename?)
def Fan.proj {f : β → C} (p : Fan f) (j : β) : p.x ⟶ f j :=
  p.π.app (Discrete.mk j)

@[simp]
theorem fan_mk_proj {f : β → C} (P : C) (p : ∀ b, P ⟶ f b) (j : β) : (Fan.mk P p).proj j = p j :=
  rfl

/-- An abbreviation for `has_limit (discrete.functor f)`. -/
abbrev HasProduct (f : β → C) :=
  HasLimit (Discrete.functor f)

/-- An abbreviation for `has_colimit (discrete.functor f)`. -/
abbrev HasCoproduct (f : β → C) :=
  HasColimit (Discrete.functor f)

/-- Make a fan `f` into a limit fan by providing `lift`, `fac`, and `uniq` --
  just a convenience lemma to avoid having to go through `discrete` -/
@[simps]
def mkFanLimit {f : β → C} (t : Fan f) (lift : ∀ s : Fan f, s.x ⟶ t.x)
    (fac : ∀ (s : Fan f) (j : β), lift s ≫ t.proj j = s.proj j)
    (uniq : ∀ (s : Fan f) (m : s.x ⟶ t.x) (w : ∀ j : β, m ≫ t.proj j = s.proj j), m = lift s) : IsLimit t :=
  { lift,
    fac' := fun s j => by
      convert fac s j.as <;> simp ,
    uniq' := fun s m w => uniq s m fun j => w (Discrete.mk j) }

section

variable (C)

/-- An abbreviation for `has_limits_of_shape (discrete f)`. -/
abbrev HasProductsOfShape (β : Type v) :=
  HasLimitsOfShape.{v} (Discrete β)

/-- An abbreviation for `has_colimits_of_shape (discrete f)`. -/
abbrev HasCoproductsOfShape (β : Type v) :=
  HasColimitsOfShape.{v} (Discrete β)

end

/-- `pi_obj f` computes the product of a family of elements `f`.
(It is defined as an abbreviation for `limit (discrete.functor f)`,
so for most facts about `pi_obj f`, you will just use general facts about limits.) -/
abbrev piObj (f : β → C) [HasProduct f] :=
  limit (Discrete.functor f)

/-- `sigma_obj f` computes the coproduct of a family of elements `f`.
(It is defined as an abbreviation for `colimit (discrete.functor f)`,
so for most facts about `sigma_obj f`, you will just use general facts about colimits.) -/
abbrev sigmaObj (f : β → C) [HasCoproduct f] :=
  colimit (Discrete.functor f)

-- mathport name: «expr∏ »
notation "∏ " f:20 => piObj f

-- mathport name: «expr∐ »
notation "∐ " f:20 => sigmaObj f

/-- The `b`-th projection from the pi object over `f` has the form `∏ f ⟶ f b`. -/
abbrev Pi.π (f : β → C) [HasProduct f] (b : β) : ∏ f ⟶ f b :=
  limit.π (Discrete.functor f) (Discrete.mk b)

/-- The `b`-th inclusion into the sigma object over `f` has the form `f b ⟶ ∐ f`. -/
abbrev Sigma.ι (f : β → C) [HasCoproduct f] (b : β) : f b ⟶ ∐ f :=
  colimit.ι (Discrete.functor f) (Discrete.mk b)

/-- The fan constructed of the projections from the product is limiting. -/
def productIsProduct (f : β → C) [HasProduct f] : IsLimit (Fan.mk _ (Pi.π f)) :=
  IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f))
    (Cones.ext (Iso.refl _)
      (by
        tidy))

/-- The cofan constructed of the inclusions from the coproduct is colimiting. -/
def coproductIsCoproduct (f : β → C) [HasCoproduct f] : IsColimit (Cofan.mk _ (Sigma.ι f)) :=
  IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f))
    (Cocones.ext (Iso.refl _)
      (by
        tidy))

/-- A collection of morphisms `P ⟶ f b` induces a morphism `P ⟶ ∏ f`. -/
abbrev Pi.lift {f : β → C} [HasProduct f] {P : C} (p : ∀ b, P ⟶ f b) : P ⟶ ∏ f :=
  limit.lift _ (Fan.mk P p)

/-- A collection of morphisms `f b ⟶ P` induces a morphism `∐ f ⟶ P`. -/
abbrev Sigma.desc {f : β → C} [HasCoproduct f] {P : C} (p : ∀ b, f b ⟶ P) : ∐ f ⟶ P :=
  colimit.desc _ (Cofan.mk P p)

/-- Construct a morphism between categorical products (indexed by the same type)
from a family of morphisms between the factors.
-/
abbrev Pi.map {f g : β → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b) : ∏ f ⟶ ∏ g :=
  limMap (Discrete.natTrans fun X => p X.as)

/-- Construct an isomorphism between categorical products (indexed by the same type)
from a family of isomorphisms between the factors.
-/
abbrev Pi.mapIso {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ≅ g b) : ∏ f ≅ ∏ g :=
  lim.mapIso (Discrete.natIso fun X => p X.as)

/-- Construct a morphism between categorical coproducts (indexed by the same type)
from a family of morphisms between the factors.
-/
abbrev Sigma.map {f g : β → C} [HasCoproduct f] [HasCoproduct g] (p : ∀ b, f b ⟶ g b) : ∐ f ⟶ ∐ g :=
  colimMap (Discrete.natTrans fun X => p X.as)

/-- Construct an isomorphism between categorical coproducts (indexed by the same type)
from a family of isomorphisms between the factors.
-/
abbrev Sigma.mapIso {f g : β → C} [HasCoproductsOfShape β C] (p : ∀ b, f b ≅ g b) : ∐ f ≅ ∐ g :=
  colim.mapIso (Discrete.natIso fun X => p X.as)

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

variable (f : β → C)

/-- The comparison morphism for the product of `f`. This is an iso iff `G` preserves the product
of `f`, see `preserves_product.of_iso_comparison`. -/
def piComparison [HasProduct f] [HasProduct fun b => G.obj (f b)] : G.obj (∏ f) ⟶ ∏ fun b => G.obj (f b) :=
  Pi.lift fun b => G.map (Pi.π f b)

@[simp, reassoc]
theorem pi_comparison_comp_π [HasProduct f] [HasProduct fun b => G.obj (f b)] (b : β) :
    piComparison G f ≫ Pi.π _ b = G.map (Pi.π f b) :=
  limit.lift_π _ (Discrete.mk b)

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
@[simp, reassoc]
theorem map_lift_pi_comparison [HasProduct f] [HasProduct fun b => G.obj (f b)] (P : C) (g : ∀ j, P ⟶ f j) :
    G.map (Pi.lift g) ≫ piComparison G f = Pi.lift fun j => G.map (g j) := by
  ext
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]"
  simp [G.map_comp]

/-- The comparison morphism for the coproduct of `f`. This is an iso iff `G` preserves the coproduct
of `f`, see `preserves_coproduct.of_iso_comparison`. -/
def sigmaComparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] : (∐ fun b => G.obj (f b)) ⟶ G.obj (∐ f) :=
  Sigma.desc fun b => G.map (Sigma.ι f b)

@[simp, reassoc]
theorem ι_comp_sigma_comparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (b : β) :
    Sigma.ι _ b ≫ sigmaComparison G f = G.map (Sigma.ι f b) :=
  colimit.ι_desc _ (Discrete.mk b)

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
@[simp, reassoc]
theorem sigma_comparison_map_desc [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (P : C) (g : ∀ j, f j ⟶ P) :
    sigmaComparison G f ≫ G.map (Sigma.desc g) = Sigma.desc fun j => G.map (g j) := by
  ext
  trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]"
  simp [G.map_comp]

end Comparison

variable (C)

/-- An abbreviation for `Π J, has_limits_of_shape (discrete J) C` -/
abbrev HasProducts :=
  ∀ J : Type w, HasLimitsOfShape (Discrete J) C

/-- An abbreviation for `Π J, has_colimits_of_shape (discrete J) C` -/
abbrev HasCoproducts :=
  ∀ J : Type w, HasColimitsOfShape (Discrete J) C

variable {C}

theorem has_smallest_products_of_has_products [HasProducts.{w} C] : HasProducts.{0} C := fun J =>
  has_limits_of_shape_of_equivalence (Discrete.equivalence Equivₓ.ulift : Discrete (ULift.{w} J) ≌ _)

theorem has_smallest_coproducts_of_has_coproducts [HasCoproducts.{w} C] : HasCoproducts.{0} C := fun J =>
  has_colimits_of_shape_of_equivalence (Discrete.equivalence Equivₓ.ulift : Discrete (ULift.{w} J) ≌ _)

theorem has_products_of_limit_fans (lf : ∀ {J : Type w} (f : J → C), Fan f)
    (lf_is_limit : ∀ {J : Type w} (f : J → C), IsLimit (lf f)) : HasProducts.{w} C := fun J : Type w =>
  { HasLimit := fun F =>
      HasLimit.mk
        ⟨(Cones.postcompose Discrete.natIsoFunctor.inv).obj (lf fun j => F.obj ⟨j⟩),
          (IsLimit.postcomposeInvEquiv _ _).symm (lf_is_limit _)⟩ }

/-!
(Co)products over a type with a unique term.
-/


section Unique

variable {C} [Unique β] (f : β → C)

/-- The limit cone for the product over an index type with exactly one term. -/
@[simps]
def limitConeOfUnique : LimitCone (Discrete.functor f) where
  Cone :=
    { x := f default,
      π :=
        { app := fun j =>
            eqToHom
              (by
                dsimp'
                congr) } }
  IsLimit :=
    { lift := fun s => s.π.app default,
      fac' := fun s j => by
        have w := (s.π.naturality (eq_to_hom (Unique.default_eq _))).symm
        dsimp'  at w
        simpa [← eq_to_hom_map] using w,
      uniq' := fun s m w => by
        specialize w default
        dsimp'  at w
        simpa using w }

instance (priority := 100) has_product_unique : HasProduct f :=
  HasLimit.mk (limitConeOfUnique f)

/-- A product over a index type with exactly one term is just the object over that term. -/
@[simps]
def productUniqueIso : ∏ f ≅ f default :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitConeOfUnique f).IsLimit

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]
/-- The colimit cocone for the coproduct over an index type with exactly one term. -/
@[simps]
def colimitCoconeOfUnique : ColimitCocone (Discrete.functor f) where
  Cocone :=
    { x := f default,
      ι :=
        { app := fun j =>
            eqToHom
              (by
                trace "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `discrete_cases #[]"
                dsimp'
                congr) } }
  IsColimit :=
    { desc := fun s => s.ι.app default,
      fac' := fun s j => by
        have w := s.ι.naturality (eq_to_hom (Unique.eq_default _))
        dsimp'  at w
        simpa [← eq_to_hom_map] using w,
      uniq' := fun s m w => by
        specialize w default
        dsimp'  at w
        simpa using w }

instance (priority := 100) has_coproduct_unique : HasCoproduct f :=
  HasColimit.mk (colimitCoconeOfUnique f)

/-- A coproduct over a index type with exactly one term is just the object over that term. -/
@[simps]
def coproductUniqueIso : ∐ f ≅ f default :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (colimitCoconeOfUnique f).IsColimit

end Unique

section Reindex

variable {C} {γ : Type v} (ε : β ≃ γ) (f : γ → C)

section

variable [HasProduct f] [HasProduct (f ∘ ε)]

/-- Reindex a categorical product via an equivalence of the index types. -/
def Pi.reindex : piObj (f ∘ ε) ≅ piObj f :=
  HasLimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun i => Iso.refl _)

@[simp, reassoc]
theorem Pi.reindex_hom_π (b : β) : (Pi.reindex ε f).Hom ≫ Pi.π f (ε b) = Pi.π (f ∘ ε) b := by
  dsimp' [← pi.reindex]
  simp only [← has_limit.iso_of_equivalence_hom_π, ← discrete.nat_iso_inv_app, ← equivalence.equivalence_mk'_counit, ←
    discrete.equivalence_counit_iso, ← discrete.nat_iso_hom_app, ← eq_to_iso.hom, ← eq_to_hom_map]
  dsimp'
  simpa [← eq_to_hom_map] using limit.w (discrete.functor (f ∘ ε)) (discrete.eq_to_hom' (ε.symm_apply_apply b))

@[simp, reassoc]
theorem Pi.reindex_inv_π (b : β) : (Pi.reindex ε f).inv ≫ Pi.π (f ∘ ε) b = Pi.π f (ε b) := by
  simp [← iso.inv_comp_eq]

end

section

variable [HasCoproduct f] [HasCoproduct (f ∘ ε)]

/-- Reindex a categorical coproduct via an equivalence of the index types. -/
def Sigma.reindex : sigmaObj (f ∘ ε) ≅ sigmaObj f :=
  HasColimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun i => Iso.refl _)

@[simp, reassoc]
theorem Sigma.ι_reindex_hom (b : β) : Sigma.ι (f ∘ ε) b ≫ (Sigma.reindex ε f).Hom = Sigma.ι f (ε b) := by
  dsimp' [← sigma.reindex]
  simp only [← has_colimit.iso_of_equivalence_hom_π, ← equivalence.equivalence_mk'_unit, ←
    discrete.equivalence_unit_iso, ← discrete.nat_iso_hom_app, ← eq_to_iso.hom, ← eq_to_hom_map, ←
    discrete.nat_iso_inv_app]
  dsimp'
  simp [← eq_to_hom_map, colimit.w (discrete.functor f) (discrete.eq_to_hom' (ε.apply_symm_apply (ε b)))]

@[simp, reassoc]
theorem Sigma.ι_reindex_inv (b : β) : Sigma.ι f (ε b) ≫ (Sigma.reindex ε f).inv = Sigma.ι (f ∘ ε) b := by
  simp [← iso.comp_inv_eq]

end

end Reindex

end CategoryTheory.Limits


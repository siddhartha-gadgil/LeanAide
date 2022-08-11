/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison
-/
import Mathbin.CategoryTheory.Subobject.FactorThru
import Mathbin.CategoryTheory.Subobject.WellPowered

/-!
# The lattice of subobjects

We provide the `semilattice_inf` with `order_top (subobject X)` instance when `[has_pullback C]`,
and the `semilattice_sup (subobject X)` instance when `[has_images C] [has_binary_coproducts C]`.
-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}

variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory

namespace MonoOver

section HasTop

instance {X : C} : HasTop (MonoOver X) where top := mk' (𝟙 _)

instance {X : C} : Inhabited (MonoOver X) :=
  ⟨⊤⟩

/-- The morphism to the top object in `mono_over X`. -/
def leTop (f : MonoOver X) : f ⟶ ⊤ :=
  homMk f.arrow (comp_id _)

@[simp]
theorem top_left (X : C) : ((⊤ : MonoOver X) : C) = X :=
  rfl

@[simp]
theorem top_arrow (X : C) : (⊤ : MonoOver X).arrow = 𝟙 X :=
  rfl

/-- `map f` sends `⊤ : mono_over X` to `⟨X, f⟩ : mono_over Y`. -/
def mapTop (f : X ⟶ Y) [Mono f] : (map f).obj ⊤ ≅ mk' f :=
  isoOfBothWays (homMk (𝟙 _) rfl)
    (homMk (𝟙 _)
      (by
        simp [← id_comp f]))

section

variable [HasPullbacks C]

/-- The pullback of the top object in `mono_over Y`
is (isomorphic to) the top object in `mono_over X`. -/
def pullbackTop (f : X ⟶ Y) : (pullback f).obj ⊤ ≅ ⊤ :=
  isoOfBothWays (leTop _)
    (homMk
      (pullback.lift f (𝟙 _)
        (by
          tidy))
      (pullback.lift_snd _ _ _))

/-- There is a morphism from `⊤ : mono_over A` to the pullback of a monomorphism along itself;
as the category is thin this is an isomorphism. -/
def topLePullbackSelf {A B : C} (f : A ⟶ B) [Mono f] : (⊤ : MonoOver A) ⟶ (pullback f).obj (mk' f) :=
  homMk _ (pullback.lift_snd _ _ rfl)

/-- The pullback of a monomorphism along itself is isomorphic to the top object. -/
def pullbackSelf {A B : C} (f : A ⟶ B) [Mono f] : (pullback f).obj (mk' f) ≅ ⊤ :=
  isoOfBothWays (leTop _) (topLePullbackSelf _)

end

end HasTop

section HasBot

variable [HasInitial C] [InitialMonoClass C]

instance {X : C} : HasBot (MonoOver X) where bot := mk' (initial.to X)

@[simp]
theorem bot_left (X : C) : ((⊥ : MonoOver X) : C) = ⊥_ C :=
  rfl

@[simp]
theorem bot_arrow {X : C} : (⊥ : MonoOver X).arrow = initial.to X :=
  rfl

/-- The (unique) morphism from `⊥ : mono_over X` to any other `f : mono_over X`. -/
def botLe {X : C} (f : MonoOver X) : ⊥ ⟶ f :=
  homMk (initial.to _)
    (by
      simp )

/-- `map f` sends `⊥ : mono_over X` to `⊥ : mono_over Y`. -/
def mapBot (f : X ⟶ Y) [Mono f] : (map f).obj ⊥ ≅ ⊥ :=
  isoOfBothWays
    (homMk (initial.to _)
      (by
        simp ))
    (homMk (𝟙 _)
      (by
        simp ))

end HasBot

section ZeroOrderBot

variable [HasZeroObject C]

open ZeroObject

/-- The object underlying `⊥ : subobject B` is (up to isomorphism) the zero object. -/
def botCoeIsoZero {B : C} : ((⊥ : MonoOver B) : C) ≅ 0 :=
  initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial

@[simp]
theorem bot_arrow_eq_zero [HasZeroMorphisms C] {B : C} : (⊥ : MonoOver B).arrow = 0 :=
  zero_of_source_iso_zero _ botCoeIsoZero

end ZeroOrderBot

section Inf

variable [HasPullbacks C]

/-- When `[has_pullbacks C]`, `mono_over A` has "intersections", functorial in both arguments.

As `mono_over A` is only a preorder, this doesn't satisfy the axioms of `semilattice_inf`,
but we reuse all the names from `semilattice_inf` because they will be used to construct
`semilattice_inf (subobject A)` shortly.
-/
@[simps]
def inf {A : C} : MonoOver A ⥤ MonoOver A ⥤ MonoOver A where
  obj := fun f => pullback f.arrow ⋙ map f.arrow
  map := fun f₁ f₂ k =>
    { app := fun g => by
        apply hom_mk _ _
        apply pullback.lift pullback.fst (pullback.snd ≫ k.left) _
        rw [pullback.condition, assoc, w k]
        dsimp'
        rw [pullback.lift_snd_assoc, assoc, w k] }

/-- A morphism from the "infimum" of two objects in `mono_over A` to the first object. -/
def infLeLeft {A : C} (f g : MonoOver A) : (inf.obj f).obj g ⟶ f :=
  homMk _ rfl

/-- A morphism from the "infimum" of two objects in `mono_over A` to the second object. -/
def infLeRight {A : C} (f g : MonoOver A) : (inf.obj f).obj g ⟶ g :=
  homMk _ pullback.condition

/-- A morphism version of the `le_inf` axiom. -/
def leInf {A : C} (f g h : MonoOver A) : (h ⟶ f) → (h ⟶ g) → (h ⟶ (inf.obj f).obj g) := by
  intro k₁ k₂
  refine' hom_mk (pullback.lift k₂.left k₁.left _) _
  rw [w k₁, w k₂]
  erw [pullback.lift_snd_assoc, w k₁]

end Inf

section Sup

variable [HasImages C] [HasBinaryCoproducts C]

/-- When `[has_images C] [has_binary_coproducts C]`, `mono_over A` has a `sup` construction,
which is functorial in both arguments,
and which on `subobject A` will induce a `semilattice_sup`. -/
def sup {A : C} : MonoOver A ⥤ MonoOver A ⥤ MonoOver A :=
  curryObj ((forget A).Prod (forget A) ⋙ uncurry.obj Over.coprod ⋙ image)

/-- A morphism version of `le_sup_left`. -/
def leSupLeft {A : C} (f g : MonoOver A) : f ⟶ (sup.obj f).obj g := by
  refine' hom_mk (coprod.inl ≫ factor_thru_image _) _
  erw [category.assoc, image.fac, coprod.inl_desc]
  rfl

/-- A morphism version of `le_sup_right`. -/
def leSupRight {A : C} (f g : MonoOver A) : g ⟶ (sup.obj f).obj g := by
  refine' hom_mk (coprod.inr ≫ factor_thru_image _) _
  erw [category.assoc, image.fac, coprod.inr_desc]
  rfl

/-- A morphism version of `sup_le`. -/
def supLe {A : C} (f g h : MonoOver A) : (f ⟶ h) → (g ⟶ h) → ((sup.obj f).obj g ⟶ h) := by
  intro k₁ k₂
  refine' hom_mk _ _
  apply image.lift ⟨_, h.arrow, coprod.desc k₁.left k₂.left, _⟩
  · dsimp'
    ext1
    · simp [← w k₁]
      
    · simp [← w k₂]
      
    
  · apply image.lift_fac
    

end Sup

end MonoOver

namespace Subobject

section OrderTop

instance orderTop {X : C} : OrderTop (Subobject X) where
  top := Quotientₓ.mk' ⊤
  le_top := by
    refine' Quotientₓ.ind' fun f => _
    exact ⟨mono_over.le_top f⟩

instance {X : C} : Inhabited (Subobject X) :=
  ⟨⊤⟩

theorem top_eq_id (B : C) : (⊤ : Subobject B) = Subobject.mk (𝟙 B) :=
  rfl

theorem underlying_iso_top_hom {B : C} : (underlyingIso (𝟙 B)).Hom = (⊤ : Subobject B).arrow := by
  convert underlying_iso_hom_comp_eq_mk (𝟙 B)
  simp only [← comp_id]

instance top_arrow_is_iso {B : C} : IsIso (⊤ : Subobject B).arrow := by
  rw [← underlying_iso_top_hom]
  infer_instance

@[simp, reassoc]
theorem underlying_iso_inv_top_arrow {B : C} : (underlyingIso _).inv ≫ (⊤ : Subobject B).arrow = 𝟙 B :=
  underlying_iso_arrow _

@[simp]
theorem map_top (f : X ⟶ Y) [Mono f] : (map f).obj ⊤ = Subobject.mk f :=
  Quotientₓ.sound' ⟨MonoOver.mapTop f⟩

theorem top_factors {A B : C} (f : A ⟶ B) : (⊤ : Subobject B).Factors f :=
  ⟨f, comp_id _⟩

theorem is_iso_iff_mk_eq_top {X Y : C} (f : X ⟶ Y) [Mono f] : IsIso f ↔ mk f = ⊤ :=
  ⟨fun _ => mk_eq_mk_of_comm _ _ (as_iso f) (category.comp_id _), fun h => by
    rw [← of_mk_le_mk_comp h.le, category.comp_id]
    exact is_iso.of_iso (iso_of_mk_eq_mk _ _ h)⟩

theorem is_iso_arrow_iff_eq_top {Y : C} (P : Subobject Y) : IsIso P.arrow ↔ P = ⊤ := by
  rw [is_iso_iff_mk_eq_top, mk_arrow]

instance is_iso_top_arrow {Y : C} : IsIso (⊤ : Subobject Y).arrow := by
  rw [is_iso_arrow_iff_eq_top]

theorem mk_eq_top_of_is_iso {X Y : C} (f : X ⟶ Y) [IsIso f] : mk f = ⊤ :=
  (is_iso_iff_mk_eq_top f).mp inferInstance

theorem eq_top_of_is_iso_arrow {Y : C} (P : Subobject Y) [IsIso P.arrow] : P = ⊤ :=
  (is_iso_arrow_iff_eq_top P).mp inferInstance

section

variable [HasPullbacks C]

theorem pullback_top (f : X ⟶ Y) : (pullback f).obj ⊤ = ⊤ :=
  Quotientₓ.sound' ⟨MonoOver.pullbackTop f⟩

theorem pullback_self {A B : C} (f : A ⟶ B) [Mono f] : (pullback f).obj (mk f) = ⊤ :=
  Quotientₓ.sound' ⟨MonoOver.pullbackSelf f⟩

end

end OrderTop

section OrderBot

variable [HasInitial C] [InitialMonoClass C]

instance orderBot {X : C} : OrderBot (Subobject X) where
  bot := Quotientₓ.mk' ⊥
  bot_le := by
    refine' Quotientₓ.ind' fun f => _
    exact ⟨mono_over.bot_le f⟩

theorem bot_eq_initial_to {B : C} : (⊥ : Subobject B) = Subobject.mk (initial.to B) :=
  rfl

/-- The object underlying `⊥ : subobject B` is (up to isomorphism) the initial object. -/
def botCoeIsoInitial {B : C} : ((⊥ : Subobject B) : C) ≅ ⊥_ C :=
  underlyingIso _

theorem map_bot (f : X ⟶ Y) [Mono f] : (map f).obj ⊥ = ⊥ :=
  Quotientₓ.sound' ⟨MonoOver.mapBot f⟩

end OrderBot

section ZeroOrderBot

variable [HasZeroObject C]

open ZeroObject

/-- The object underlying `⊥ : subobject B` is (up to isomorphism) the zero object. -/
def botCoeIsoZero {B : C} : ((⊥ : Subobject B) : C) ≅ 0 :=
  bot_coe_iso_initial ≪≫ initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial

variable [HasZeroMorphisms C]

theorem bot_eq_zero {B : C} : (⊥ : Subobject B) = Subobject.mk (0 : 0 ⟶ B) :=
  mk_eq_mk_of_comm _ _ (initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial)
    (by
      simp )

@[simp]
theorem bot_arrow {B : C} : (⊥ : Subobject B).arrow = 0 :=
  zero_of_source_iso_zero _ botCoeIsoZero

theorem bot_factors_iff_zero {A B : C} (f : A ⟶ B) : (⊥ : Subobject B).Factors f ↔ f = 0 :=
  ⟨by
    rintro ⟨h, rfl⟩
    simp , by
    rintro rfl
    exact
      ⟨0, by
        simp ⟩⟩

theorem mk_eq_bot_iff_zero {f : X ⟶ Y} [Mono f] : Subobject.mk f = ⊥ ↔ f = 0 :=
  ⟨fun h => by
    simpa [← h, ← bot_factors_iff_zero] using mk_factors_self f, fun h =>
    mk_eq_mk_of_comm _ _ ((isoZeroOfMonoEqZero h).trans HasZeroObject.zeroIsoInitial)
      (by
        simp [← h])⟩

end ZeroOrderBot

section Functor

variable (C)

/-- Sending `X : C` to `subobject X` is a contravariant functor `Cᵒᵖ ⥤ Type`. -/
@[simps]
def functor [HasPullbacks C] : Cᵒᵖ ⥤ Type max u₁ v₁ where
  obj := fun X => Subobject X.unop
  map := fun X Y f => (pullback f.unop).obj
  map_id' := fun X => funext pullback_id
  map_comp' := fun X Y Z f g => funext (pullback_comp _ _)

end Functor

section SemilatticeInfTop

variable [HasPullbacks C]

/-- The functorial infimum on `mono_over A` descends to an infimum on `subobject A`. -/
def inf {A : C} : Subobject A ⥤ Subobject A ⥤ Subobject A :=
  ThinSkeleton.map₂ MonoOver.inf

theorem inf_le_left {A : C} (f g : Subobject A) : (inf.obj f).obj g ≤ f :=
  Quotientₓ.induction_on₂' f g fun a b => ⟨MonoOver.infLeLeft _ _⟩

theorem inf_le_right {A : C} (f g : Subobject A) : (inf.obj f).obj g ≤ g :=
  Quotientₓ.induction_on₂' f g fun a b => ⟨MonoOver.infLeRight _ _⟩

theorem le_inf {A : C} (h f g : Subobject A) : h ≤ f → h ≤ g → h ≤ (inf.obj f).obj g :=
  Quotientₓ.induction_on₃' h f g
    (by
      rintro f g h ⟨k⟩ ⟨l⟩
      exact ⟨mono_over.le_inf _ _ _ k l⟩)

instance {B : C} : SemilatticeInf (Subobject B) :=
  { Subobject.partialOrder _ with inf := fun m n => (inf.obj m).obj n, inf_le_left := inf_le_left,
    inf_le_right := inf_le_right, le_inf := le_inf }

theorem factors_left_of_inf_factors {A B : C} {X Y : Subobject B} {f : A ⟶ B} (h : (X⊓Y).Factors f) : X.Factors f :=
  factors_of_le _ (inf_le_left _ _) h

theorem factors_right_of_inf_factors {A B : C} {X Y : Subobject B} {f : A ⟶ B} (h : (X⊓Y).Factors f) : Y.Factors f :=
  factors_of_le _ (inf_le_right _ _) h

@[simp]
theorem inf_factors {A B : C} {X Y : Subobject B} (f : A ⟶ B) : (X⊓Y).Factors f ↔ X.Factors f ∧ Y.Factors f :=
  ⟨fun h => ⟨factors_left_of_inf_factors h, factors_right_of_inf_factors h⟩, by
    revert X Y
    refine' Quotientₓ.ind₂' _
    rintro X Y ⟨⟨g₁, rfl⟩, ⟨g₂, hg₂⟩⟩
    exact ⟨_, pullback.lift_snd_assoc _ _ hg₂ _⟩⟩

theorem inf_arrow_factors_left {B : C} (X Y : Subobject B) : X.Factors (X⊓Y).arrow :=
  (factors_iff _ _).mpr
    ⟨ofLe (X⊓Y) X (inf_le_left X Y), by
      simp ⟩

theorem inf_arrow_factors_right {B : C} (X Y : Subobject B) : Y.Factors (X⊓Y).arrow :=
  (factors_iff _ _).mpr
    ⟨ofLe (X⊓Y) Y (inf_le_right X Y), by
      simp ⟩

@[simp]
theorem finset_inf_factors {I : Type _} {A B : C} {s : Finset I} {P : I → Subobject B} (f : A ⟶ B) :
    (s.inf P).Factors f ↔ ∀, ∀ i ∈ s, ∀, (P i).Factors f := by
  classical
  apply Finset.induction_on s
  · simp [← top_factors]
    
  · intro i s nm ih
    simp [← ih]
    

-- `i` is explicit here because often we'd like to defer a proof of `m`
theorem finset_inf_arrow_factors {I : Type _} {B : C} (s : Finset I) (P : I → Subobject B) (i : I) (m : i ∈ s) :
    (P i).Factors (s.inf P).arrow := by
  revert i m
  classical
  apply Finset.induction_on s
  · rintro _ ⟨⟩
    
  · intro i s nm ih j m
    rw [Finset.inf_insert]
    simp only [← Finset.mem_insert] at m
    rcases m with (rfl | m)
    · rw [← factor_thru_arrow _ _ (inf_arrow_factors_left _ _)]
      exact factors_comp_arrow _
      
    · rw [← factor_thru_arrow _ _ (inf_arrow_factors_right _ _)]
      apply factors_of_factors_right
      exact ih _ m
      
    

theorem inf_eq_map_pullback' {A : C} (f₁ : MonoOver A) (f₂ : Subobject A) :
    (Subobject.inf.obj (Quotientₓ.mk' f₁)).obj f₂ =
      (Subobject.map f₁.arrow).obj ((Subobject.pullback f₁.arrow).obj f₂) :=
  by
  apply Quotientₓ.induction_on' f₂
  intro f₂
  rfl

theorem inf_eq_map_pullback {A : C} (f₁ : MonoOver A) (f₂ : Subobject A) :
    (Quotientₓ.mk' f₁⊓f₂ : Subobject A) = (map f₁.arrow).obj ((pullback f₁.arrow).obj f₂) :=
  inf_eq_map_pullback' f₁ f₂

theorem prod_eq_inf {A : C} {f₁ f₂ : Subobject A} [HasBinaryProduct f₁ f₂] : (f₁ ⨯ f₂) = f₁⊓f₂ :=
  le_antisymmₓ (le_inf Limits.prod.fst.le Limits.prod.snd.le) (prod.lift inf_le_left.Hom inf_le_right.Hom).le

theorem inf_def {B : C} (m m' : Subobject B) : m⊓m' = (inf.obj m).obj m' :=
  rfl

/-- `⊓` commutes with pullback. -/
theorem inf_pullback {X Y : C} (g : X ⟶ Y) (f₁ f₂) :
    (pullback g).obj (f₁⊓f₂) = (pullback g).obj f₁⊓(pullback g).obj f₂ := by
  revert f₁
  apply Quotientₓ.ind'
  intro f₁
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← pullback_comp, ←
    map_pullback pullback.condition (pullback_is_pullback f₁.arrow g), ← pullback_comp, pullback.condition]
  rfl

/-- `⊓` commutes with map. -/
theorem inf_map {X Y : C} (g : Y ⟶ X) [Mono g] (f₁ f₂) : (map g).obj (f₁⊓f₂) = (map g).obj f₁⊓(map g).obj f₂ := by
  revert f₁
  apply Quotientₓ.ind'
  intro f₁
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← map_comp]
  dsimp'
  rw [pullback_comp, pullback_map_self]

end SemilatticeInfTop

section SemilatticeSup

variable [HasImages C] [HasBinaryCoproducts C]

/-- The functorial supremum on `mono_over A` descends to an supremum on `subobject A`. -/
def sup {A : C} : Subobject A ⥤ Subobject A ⥤ Subobject A :=
  ThinSkeleton.map₂ MonoOver.sup

instance {B : C} : SemilatticeSup (Subobject B) :=
  { Subobject.partialOrder B with sup := fun m n => (sup.obj m).obj n,
    le_sup_left := fun m n => Quotientₓ.induction_on₂' m n fun a b => ⟨MonoOver.leSupLeft _ _⟩,
    le_sup_right := fun m n => Quotientₓ.induction_on₂' m n fun a b => ⟨MonoOver.leSupRight _ _⟩,
    sup_le := fun m n k => Quotientₓ.induction_on₃' m n k fun a b c ⟨i⟩ ⟨j⟩ => ⟨MonoOver.supLe _ _ _ i j⟩ }

theorem sup_factors_of_factors_left {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : X.Factors f) : (X⊔Y).Factors f :=
  factors_of_le f le_sup_left P

theorem sup_factors_of_factors_right {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : Y.Factors f) : (X⊔Y).Factors f :=
  factors_of_le f le_sup_right P

variable [HasInitial C] [InitialMonoClass C]

theorem finset_sup_factors {I : Type _} {A B : C} {s : Finset I} {P : I → Subobject B} {f : A ⟶ B}
    (h : ∃ i ∈ s, (P i).Factors f) : (s.sup P).Factors f := by
  classical
  revert h
  apply Finset.induction_on s
  · rintro ⟨_, ⟨⟨⟩, _⟩⟩
    
  · rintro i s nm ih ⟨j, ⟨m, h⟩⟩
    simp only [← Finset.sup_insert]
    simp at m
    rcases m with (rfl | m)
    · exact sup_factors_of_factors_left h
      
    · exact sup_factors_of_factors_right (ih ⟨j, ⟨m, h⟩⟩)
      
    

end SemilatticeSup

section Lattice

instance [HasInitial C] [InitialMonoClass C] {B : C} : BoundedOrder (Subobject B) :=
  { Subobject.orderTop, Subobject.orderBot with }

variable [HasPullbacks C] [HasImages C] [HasBinaryCoproducts C]

instance {B : C} : Lattice (Subobject B) :=
  { Subobject.semilatticeInf, Subobject.semilatticeSup with }

end Lattice

section Inf

variable [WellPowered C]

/-- The "wide cospan" diagram, with a small indexing type, constructed from a set of subobjects.
(This is just the diagram of all the subobjects pasted together, but using `well_powered C`
to make the diagram small.)
-/
def wideCospan {A : C} (s : Set (Subobject A)) : WidePullbackShape (equivShrink _ '' s) ⥤ C :=
  WidePullbackShape.wideCospan A (fun j : equivShrink _ '' s => ((equivShrink (Subobject A)).symm j : C)) fun j =>
    ((equivShrink (Subobject A)).symm j).arrow

@[simp]
theorem wide_cospan_map_term {A : C} (s : Set (Subobject A)) (j) :
    (wideCospan s).map (WidePullbackShape.Hom.term j) = ((equivShrink (Subobject A)).symm j).arrow :=
  rfl

/-- Auxiliary construction of a cone for `le_Inf`. -/
def leInfCone {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : ∀, ∀ g ∈ s, ∀, f ≤ g) : Cone (wideCospan s) :=
  WidePullbackShape.mkCone f.arrow
    (fun j =>
      underlying.map
        (homOfLe
          (k _
            (by
              rcases j with ⟨-, ⟨g, ⟨m, rfl⟩⟩⟩
              simpa using m))))
    (by
      tidy)

@[simp]
theorem le_Inf_cone_π_app_none {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : ∀, ∀ g ∈ s, ∀, f ≤ g) :
    (leInfCone s f k).π.app none = f.arrow :=
  rfl

variable [HasWidePullbacks.{v₁} C]

/-- The limit of `wide_cospan s`. (This will be the supremum of the set of subobjects.)
-/
def widePullback {A : C} (s : Set (Subobject A)) : C :=
  Limits.limit (wideCospan s)

/-- The inclusion map from `wide_pullback s` to `A`
-/
def widePullbackι {A : C} (s : Set (Subobject A)) : widePullback s ⟶ A :=
  Limits.limit.π (wideCospan s) none

instance wide_pullback_ι_mono {A : C} (s : Set (Subobject A)) : Mono (widePullbackι s) :=
  ⟨fun W u v h =>
    limit.hom_ext fun j => by
      cases j
      · exact h
        
      · apply (cancel_mono ((equivShrink (subobject A)).symm j).arrow).1
        rw [assoc, assoc]
        erw [limit.w (wide_cospan s) (wide_pullback_shape.hom.term j)]
        exact h
        ⟩

/-- When `[well_powered C]` and `[has_wide_pullbacks C]`, `subobject A` has arbitrary infimums.
-/
def infₓ {A : C} (s : Set (Subobject A)) : Subobject A :=
  Subobject.mk (widePullbackι s)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (f «expr ∈ » s)
theorem Inf_le {A : C} (s : Set (Subobject A)) (f) (_ : f ∈ s) : infₓ s ≤ f := by
  fapply le_of_comm
  · refine'
      (underlying_iso _).Hom ≫
        limits.limit.π (wide_cospan s) (some ⟨equivShrink _ f, Set.mem_image_of_mem (equivShrink (subobject A)) H⟩) ≫ _
    apply eq_to_hom
    apply congr_arg fun X : subobject A => (X : C)
    exact Equivₓ.symm_apply_apply _ _
    
  · dsimp' [← Inf]
    simp only [← category.comp_id, ← category.assoc, underlying_iso_hom_comp_eq_mk, ← subobject.arrow_congr, ←
      congr_arg_mpr_hom_left, ← iso.cancel_iso_hom_left]
    convert limit.w (wide_cospan s) (wide_pullback_shape.hom.term _)
    

theorem le_Inf {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : ∀, ∀ g ∈ s, ∀, f ≤ g) : f ≤ infₓ s := by
  fapply le_of_comm
  · exact limits.limit.lift _ (le_Inf_cone s f k) ≫ (underlying_iso _).inv
    
  · dsimp' [← Inf, ← wide_pullback_ι]
    simp
    

instance {B : C} : CompleteSemilatticeInf (Subobject B) :=
  { Subobject.partialOrder B with inf := infₓ, Inf_le := Inf_le, le_Inf := le_Inf }

end Inf

section Sup

variable [WellPowered C] [HasCoproducts.{v₁} C]

/-- The univesal morphism out of the coproduct of a set of subobjects,
after using `[well_powered C]` to reindex by a small type.
-/
def smallCoproductDesc {A : C} (s : Set (Subobject A)) : _ ⟶ A :=
  Limits.Sigma.desc fun j : equivShrink _ '' s => ((equivShrink (Subobject A)).symm j).arrow

variable [HasImages C]

/-- When `[well_powered C] [has_images C] [has_coproducts C]`,
`subobject A` has arbitrary supremums. -/
def supₓ {A : C} (s : Set (Subobject A)) : Subobject A :=
  Subobject.mk (image.ι (smallCoproductDesc s))

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (f «expr ∈ » s)
theorem le_Sup {A : C} (s : Set (Subobject A)) (f) (_ : f ∈ s) : f ≤ supₓ s := by
  fapply le_of_comm
  · dsimp' [← Sup]
    refine' _ ≫ factor_thru_image _ ≫ (underlying_iso _).inv
    refine'
      _ ≫
        sigma.ι _
          ⟨equivShrink _ f, by
            simpa [← Set.mem_image] using H⟩
    exact eq_to_hom (congr_arg (fun X : subobject A => (X : C)) (Equivₓ.symm_apply_apply _ _).symm)
    
  · dsimp' [← Sup, ← small_coproduct_desc]
    simp
    dsimp'
    simp
    

theorem symm_apply_mem_iff_mem_image {α β : Type _} (e : α ≃ β) (s : Set α) (x : β) : e.symm x ∈ s ↔ x ∈ e '' s :=
  ⟨fun h =>
    ⟨e.symm x, h, by
      simp ⟩,
    by
    rintro ⟨a, m, rfl⟩
    simpa using m⟩

theorem Sup_le {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : ∀, ∀ g ∈ s, ∀, g ≤ f) : supₓ s ≤ f := by
  fapply le_of_comm
  · dsimp' [← Sup]
    refine' (underlying_iso _).Hom ≫ image.lift ⟨_, f.arrow, _, _⟩
    · refine' sigma.desc _
      rintro ⟨g, m⟩
      refine' underlying.map (hom_of_le (k _ _))
      simpa [← symm_apply_mem_iff_mem_image] using m
      
    · ext j
      rcases j with ⟨j, m⟩
      dsimp' [← small_coproduct_desc]
      simp
      dsimp'
      simp
      
    
  · dsimp' [← Sup]
    simp
    

instance {B : C} : CompleteSemilatticeSup (Subobject B) :=
  { Subobject.partialOrder B with sup := supₓ, le_Sup := le_Sup, Sup_le := Sup_le }

end Sup

section CompleteLattice

variable [WellPowered C] [HasWidePullbacks.{v₁} C] [HasImages C] [HasCoproducts.{v₁} C] [InitialMonoClass C]

attribute [local instance] has_smallest_coproducts_of_has_coproducts

instance {B : C} : CompleteLattice (Subobject B) :=
  { Subobject.semilatticeInf, Subobject.semilatticeSup, Subobject.boundedOrder, Subobject.completeSemilatticeInf,
    Subobject.completeSemilatticeSup with }

end CompleteLattice

section ZeroObject

variable [HasZeroMorphisms C] [HasZeroObject C]

open ZeroObject

/-- A nonzero object has nontrivial subobject lattice. -/
theorem nontrivial_of_not_is_zero {X : C} (h : ¬IsZero X) : Nontrivial (Subobject X) :=
  ⟨⟨mk (0 : 0 ⟶ X), mk (𝟙 X), fun w => h (IsZero.of_iso (is_zero_zero C) (isoOfMkEqMk _ _ w).symm)⟩⟩

end ZeroObject

section SubobjectSubobject

/-- The subobject lattice of a subobject `Y` is order isomorphic to the interval `set.Iic Y`. -/
def subobjectOrderIso {X : C} (Y : Subobject X) : Subobject (Y : C) ≃o Set.Iic Y where
  toFun := fun Z =>
    ⟨Subobject.mk (Z.arrow ≫ Y.arrow),
      Set.mem_Iic.mpr
        (le_of_comm ((underlyingIso _).Hom ≫ Z.arrow)
          (by
            simp ))⟩
  invFun := fun Z => Subobject.mk (ofLe _ _ Z.2)
  left_inv := fun Z =>
    mk_eq_of_comm _ (underlyingIso _)
      (by
        ext
        simp )
  right_inv := fun Z =>
    Subtype.ext
      (mk_eq_of_comm _ (underlyingIso _)
        (by
          dsimp'
          simp [iso.eq_inv_comp]))
  map_rel_iff' := fun W Z =>
    ⟨fun h =>
      le_of_comm ((underlyingIso _).inv ≫ ofLe _ _ (Subtype.mk_le_mk.mp h) ≫ (underlyingIso _).Hom)
        (by
          ext
          simp ),
      fun h =>
      Subtype.mk_le_mk.mpr
        (le_of_comm ((underlyingIso _).Hom ≫ ofLe _ _ h ≫ (underlyingIso _).inv)
          (by
            simp ))⟩

end SubobjectSubobject

end Subobject

end CategoryTheory


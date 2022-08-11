/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Equivalence

/-!
# Adjunctions between functors

`F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

We provide various useful constructors:
* `mk_of_hom_equiv`
* `mk_of_unit_counit`
* `left_adjoint_of_equiv` / `right_adjoint_of equiv`
  construct a left/right adjoint of a given functor given the action on objects and
  the relevant equivalence of morphism spaces.
* `adjunction_of_equiv_left` / `adjunction_of_equiv_right` witness that these constructions
  give adjunctions.

There are also typeclasses `is_left_adjoint` / `is_right_adjoint`, carrying data witnessing
that a given functor is a left or right adjoint.
Given `[is_left_adjoint F]`, a right adjoint of `F` can be constructed as `right_adjoint F`.

`adjunction.comp` composes adjunctions.

`to_equivalence` upgrades an adjunction to an equivalence,
given witnesses that the unit and counit are pointwise isomorphisms.
Conversely `equivalence.to_adjunction` recovers the underlying adjunction from an equivalence.
-/


namespace CategoryTheory

open Category

-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

attribute [local elabWithoutExpectedType] whisker_left whisker_right

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- `F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

To construct an `adjunction` between two functors, it's often easier to instead use the
constructors `mk_of_hom_equiv` or `mk_of_unit_counit`. To construct a left adjoint,
there are also constructors `left_adjoint_of_equiv` and `adjunction_of_equiv_left` (as
well as their duals) which can be simpler in practice.

Uniqueness of adjoints is shown in `category_theory.adjunction.opposites`.

See <https://stacks.math.columbia.edu/tag/0037>.
-/
structure Adjunction (F : C ⥤ D) (G : D ⥤ C) where
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  Unit : 𝟭 C ⟶ F.comp G
  counit : G.comp F ⟶ 𝟭 D
  hom_equiv_unit' : ∀ {X Y f}, (hom_equiv X Y) f = (Unit : _ ⟶ _).app X ≫ G.map f := by
    run_tac
      obviously
  hom_equiv_counit' : ∀ {X Y g}, (hom_equiv X Y).symm g = F.map g ≫ counit.app Y := by
    run_tac
      obviously

-- mathport name: «expr ⊣ »
infixl:15 " ⊣ " => Adjunction

/-- A class giving a chosen right adjoint to the functor `left`. -/
class IsLeftAdjoint (left : C ⥤ D) where
  right : D ⥤ C
  adj : left ⊣ right

/-- A class giving a chosen left adjoint to the functor `right`. -/
class IsRightAdjoint (right : D ⥤ C) where
  left : C ⥤ D
  adj : left ⊣ right

/-- Extract the left adjoint from the instance giving the chosen adjoint. -/
def leftAdjoint (R : D ⥤ C) [IsRightAdjoint R] : C ⥤ D :=
  IsRightAdjoint.left R

/-- Extract the right adjoint from the instance giving the chosen adjoint. -/
def rightAdjoint (L : C ⥤ D) [IsLeftAdjoint L] : D ⥤ C :=
  IsLeftAdjoint.right L

/-- The adjunction associated to a functor known to be a left adjoint. -/
def Adjunction.ofLeftAdjoint (left : C ⥤ D) [IsLeftAdjoint left] : Adjunction left (rightAdjoint left) :=
  is_left_adjoint.adj

/-- The adjunction associated to a functor known to be a right adjoint. -/
def Adjunction.ofRightAdjoint (right : C ⥤ D) [IsRightAdjoint right] : Adjunction (leftAdjoint right) right :=
  is_right_adjoint.adj

namespace Adjunction

restate_axiom hom_equiv_unit'

restate_axiom hom_equiv_counit'

attribute [simp] hom_equiv_unit hom_equiv_counit

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X' X : C} {Y Y' : D}

theorem hom_equiv_id (X : C) : adj.homEquiv X _ (𝟙 _) = adj.Unit.app X := by
  simp

theorem hom_equiv_symm_id (X : D) : (adj.homEquiv _ X).symm (𝟙 _) = adj.counit.app X := by
  simp

@[simp]
theorem hom_equiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) :
    (adj.homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (adj.homEquiv X Y).symm g := by
  rw [hom_equiv_counit, F.map_comp, assoc, adj.hom_equiv_counit.symm]

@[simp]
theorem hom_equiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equivₓ.eq_symm_apply] <;> simp [-hom_equiv_unit]

@[simp]
theorem hom_equiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y') (f ≫ g) = (adj.homEquiv X Y) f ≫ G.map g := by
  rw [hom_equiv_unit, G.map_comp, ← assoc, ← hom_equiv_unit]

@[simp]
theorem hom_equiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [Equivₓ.symm_apply_eq] <;> simp [-hom_equiv_counit]

@[simp]
theorem left_triangle : whiskerRight adj.Unit F ≫ whiskerLeft F adj.counit = NatTrans.id _ := by
  ext
  dsimp'
  erw [← adj.hom_equiv_counit, Equivₓ.symm_apply_eq, adj.hom_equiv_unit]
  simp

@[simp]
theorem right_triangle : whiskerLeft G adj.Unit ≫ whiskerRight adj.counit G = NatTrans.id _ := by
  ext
  dsimp'
  erw [← adj.hom_equiv_unit, ← Equivₓ.eq_symm_apply, adj.hom_equiv_counit]
  simp

@[simp, reassoc]
theorem left_triangle_components : F.map (adj.Unit.app X) ≫ adj.counit.app (F.obj X) = 𝟙 (F.obj X) :=
  congr_arg (fun t : NatTrans _ (𝟭 C ⋙ F) => t.app X) adj.left_triangle

@[simp, reassoc]
theorem right_triangle_components {Y : D} : adj.Unit.app (G.obj Y) ≫ G.map (adj.counit.app Y) = 𝟙 (G.obj Y) :=
  congr_arg (fun t : NatTrans _ (G ⋙ 𝟭 C) => t.app Y) adj.right_triangle

@[simp, reassoc]
theorem counit_naturality {X Y : D} (f : X ⟶ Y) : F.map (G.map f) ≫ adj.counit.app Y = adj.counit.app X ≫ f :=
  adj.counit.naturality f

@[simp, reassoc]
theorem unit_naturality {X Y : C} (f : X ⟶ Y) : adj.Unit.app X ≫ G.map (F.map f) = f ≫ adj.Unit.app Y :=
  (adj.Unit.naturality f).symm

theorem hom_equiv_apply_eq {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    adj.homEquiv A B f = g ↔ f = (adj.homEquiv A B).symm g :=
  ⟨fun h => by
    cases h
    simp , fun h => by
    cases h
    simp ⟩

theorem eq_hom_equiv_apply {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    g = adj.homEquiv A B f ↔ (adj.homEquiv A B).symm g = f :=
  ⟨fun h => by
    cases h
    simp , fun h => by
    cases h
    simp ⟩

end

end Adjunction

namespace Adjunction

/-- This is an auxiliary data structure useful for constructing adjunctions.
See `adjunction.mk_of_hom_equiv`.
This structure won't typically be used anywhere else.
-/
@[nolint has_inhabited_instance]
structure CoreHomEquiv (F : C ⥤ D) (G : D ⥤ C) where
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  hom_equiv_naturality_left_symm' :
    ∀ {X' X Y} (f : X' ⟶ X) (g : X ⟶ G.obj Y), (hom_equiv X' Y).symm (f ≫ g) = F.map f ≫ (hom_equiv X Y).symm g := by
    run_tac
      obviously
  hom_equiv_naturality_right' :
    ∀ {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'), (hom_equiv X Y') (f ≫ g) = (hom_equiv X Y) f ≫ G.map g := by
    run_tac
      obviously

namespace CoreHomEquiv

restate_axiom hom_equiv_naturality_left_symm'

restate_axiom hom_equiv_naturality_right'

attribute [simp] hom_equiv_naturality_left_symm hom_equiv_naturality_right

variable {F : C ⥤ D} {G : D ⥤ C} (adj : CoreHomEquiv F G) {X' X : C} {Y Y' : D}

@[simp]
theorem hom_equiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equivₓ.eq_symm_apply] <;> simp

@[simp]
theorem hom_equiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [Equivₓ.symm_apply_eq] <;> simp

end CoreHomEquiv

/-- This is an auxiliary data structure useful for constructing adjunctions.
See `adjunction.mk_of_unit_counit`.
This structure won't typically be used anywhere else.
-/
@[nolint has_inhabited_instance]
structure CoreUnitCounit (F : C ⥤ D) (G : D ⥤ C) where
  Unit : 𝟭 C ⟶ F.comp G
  counit : G.comp F ⟶ 𝟭 D
  left_triangle' :
    whiskerRight Unit F ≫ (Functor.associator F G F).Hom ≫ whiskerLeft F counit = NatTrans.id (𝟭 C ⋙ F) := by
    run_tac
      obviously
  right_triangle' :
    whiskerLeft G Unit ≫ (Functor.associator G F G).inv ≫ whiskerRight counit G = NatTrans.id (G ⋙ 𝟭 C) := by
    run_tac
      obviously

namespace CoreUnitCounit

restate_axiom left_triangle'

restate_axiom right_triangle'

attribute [simp] left_triangle right_triangle

end CoreUnitCounit

variable {F : C ⥤ D} {G : D ⥤ C}

/-- Construct an adjunction between `F` and `G` out of a natural bijection between each
`F.obj X ⟶ Y` and `X ⟶ G.obj Y`. -/
@[simps]
def mkOfHomEquiv (adj : CoreHomEquiv F G) : F ⊣ G :=
  { -- See note [dsimp, simp].
    adj with
    Unit :=
      { app := fun X => (adj.homEquiv X (F.obj X)) (𝟙 (F.obj X)),
        naturality' := by
          intros
          erw [← adj.hom_equiv_naturality_left, ← adj.hom_equiv_naturality_right]
          dsimp'
          simp },
    counit :=
      { app := fun Y => (adj.homEquiv _ _).invFun (𝟙 (G.obj Y)),
        naturality' := by
          intros
          erw [← adj.hom_equiv_naturality_left_symm, ← adj.hom_equiv_naturality_right_symm]
          dsimp'
          simp },
    hom_equiv_unit' := fun X Y f => by
      erw [← adj.hom_equiv_naturality_right] <;> simp ,
    hom_equiv_counit' := fun X Y f => by
      erw [← adj.hom_equiv_naturality_left_symm] <;> simp }

/-- Construct an adjunction between functors `F` and `G` given a unit and counit for the adjunction
satisfying the triangle identities. -/
@[simps]
def mkOfUnitCounit (adj : CoreUnitCounit F G) : F ⊣ G :=
  { adj with
    homEquiv := fun X Y =>
      { toFun := fun f => adj.Unit.app X ≫ G.map f, invFun := fun g => F.map g ≫ adj.counit.app Y,
        left_inv := fun f => by
          change F.map (_ ≫ _) ≫ _ = _
          rw [F.map_comp, assoc, ← functor.comp_map, adj.counit.naturality, ← assoc]
          convert id_comp f
          have t := congr_arg (fun t : nat_trans _ _ => t.app _) adj.left_triangle
          dsimp'  at t
          simp only [← id_comp] at t
          exact t,
        right_inv := fun g => by
          change _ ≫ G.map (_ ≫ _) = _
          rw [G.map_comp, ← assoc, ← functor.comp_map, ← adj.unit.naturality, assoc]
          convert comp_id g
          have t := congr_arg (fun t : nat_trans _ _ => t.app _) adj.right_triangle
          dsimp'  at t
          simp only [← id_comp] at t
          exact t } }

/-- The adjunction between the identity functor on a category and itself. -/
def id : 𝟭 C ⊣ 𝟭 C where
  homEquiv := fun X Y => Equivₓ.refl _
  Unit := 𝟙 _
  counit := 𝟙 _

-- Satisfy the inhabited linter.
instance : Inhabited (Adjunction (𝟭 C) (𝟭 C)) :=
  ⟨id⟩

/-- If F and G are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[simps]
def equivHomsetLeftOfNatIso {F F' : C ⥤ D} (iso : F ≅ F') {X : C} {Y : D} : (F.obj X ⟶ Y) ≃ (F'.obj X ⟶ Y) where
  toFun := fun f => iso.inv.app _ ≫ f
  invFun := fun g => iso.Hom.app _ ≫ g
  left_inv := fun f => by
    simp
  right_inv := fun g => by
    simp

/-- If G and H are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[simps]
def equivHomsetRightOfNatIso {G G' : D ⥤ C} (iso : G ≅ G') {X : C} {Y : D} : (X ⟶ G.obj Y) ≃ (X ⟶ G'.obj Y) where
  toFun := fun f => f ≫ iso.Hom.app _
  invFun := fun g => g ≫ iso.inv.app _
  left_inv := fun f => by
    simp
  right_inv := fun g => by
    simp

/-- Transport an adjunction along an natural isomorphism on the left. -/
def ofNatIsoLeft {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) : G ⊣ H :=
  Adjunction.mkOfHomEquiv { homEquiv := fun X Y => (equivHomsetLeftOfNatIso iso.symm).trans (adj.homEquiv X Y) }

/-- Transport an adjunction along an natural isomorphism on the right. -/
def ofNatIsoRight {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) : F ⊣ H :=
  Adjunction.mkOfHomEquiv { homEquiv := fun X Y => (adj.homEquiv X Y).trans (equivHomsetRightOfNatIso iso) }

/-- Transport being a right adjoint along a natural isomorphism. -/
def rightAdjointOfNatIso {F G : C ⥤ D} (h : F ≅ G) [r : IsRightAdjoint F] : IsRightAdjoint G where
  left := r.left
  adj := ofNatIsoRight r.adj h

/-- Transport being a left adjoint along a natural isomorphism. -/
def leftAdjointOfNatIso {F G : C ⥤ D} (h : F ≅ G) [r : IsLeftAdjoint F] : IsLeftAdjoint G where
  right := r.right
  adj := ofNatIsoLeft r.adj h

section

variable {E : Type u₃} [ℰ : Category.{v₃} E] {H : D ⥤ E} {I : E ⥤ D}

/-- Composition of adjunctions.

See <https://stacks.math.columbia.edu/tag/0DV0>.
-/
def comp (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) : F ⋙ H ⊣ I ⋙ G where
  homEquiv := fun X Z => Equivₓ.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _)
  Unit := adj₁.Unit ≫ (whiskerLeft F <| whiskerRight adj₂.Unit G) ≫ (Functor.associator _ _ _).inv
  counit := (Functor.associator _ _ _).Hom ≫ (whiskerLeft I <| whiskerRight adj₁.counit H) ≫ adj₂.counit

/-- If `F` and `G` are left adjoints then `F ⋙ G` is a left adjoint too. -/
instance leftAdjointOfComp {E : Type u₃} [ℰ : Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) [Fl : IsLeftAdjoint F]
    [Gl : IsLeftAdjoint G] : IsLeftAdjoint (F ⋙ G) where
  right := Gl.right ⋙ Fl.right
  adj := Fl.adj.comp Gl.adj

/-- If `F` and `G` are right adjoints then `F ⋙ G` is a right adjoint too. -/
instance rightAdjointOfComp {E : Type u₃} [ℰ : Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E} [Fr : IsRightAdjoint F]
    [Gr : IsRightAdjoint G] : IsRightAdjoint (F ⋙ G) where
  left := Gr.left ⋙ Fr.left
  adj := Gr.adj.comp Fr.adj

end

section ConstructLeft

-- Construction of a left adjoint. In order to construct a left
-- adjoint to a functor G : D → C, it suffices to give the object part
-- of a functor F : C → D together with isomorphisms Hom(FX, Y) ≃
-- Hom(X, GY) natural in Y. The action of F on morphisms can be
-- constructed from this data.
variable {F_obj : C → D} {G}

variable (e : ∀ X Y, (F_obj X ⟶ Y) ≃ (X ⟶ G.obj Y))

variable (he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)

include he

private theorem he' {X Y Y'} (f g) : (e X Y').symm (f ≫ G.map g) = (e X Y).symm f ≫ g := by
  intros <;> rw [Equivₓ.symm_apply_eq, he] <;> simp

/-- Construct a left adjoint functor to `G`, given the functor's value on objects `F_obj` and
a bijection `e` between `F_obj X ⟶ Y` and `X ⟶ G.obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g`.
Dual to `right_adjoint_of_equiv`. -/
@[simps]
def leftAdjointOfEquiv : C ⥤ D where
  obj := F_obj
  map := fun X X' f => (e X (F_obj X')).symm (f ≫ e X' (F_obj X') (𝟙 _))
  map_comp' := fun X X' X'' f f' => by
    rw [Equivₓ.symm_apply_eq, he, Equivₓ.apply_symm_apply]
    conv => rhs rw [assoc, ← he, id_comp, Equivₓ.apply_symm_apply]
    simp

/-- Show that the functor given by `left_adjoint_of_equiv` is indeed left adjoint to `G`. Dual
to `adjunction_of_equiv_right`. -/
@[simps]
def adjunctionOfEquivLeft : leftAdjointOfEquiv e he ⊣ G :=
  mkOfHomEquiv
    { homEquiv := e,
      hom_equiv_naturality_left_symm' := by
        intros
        erw [← he' e he, ← Equivₓ.apply_eq_iff_eq]
        simp [← (he _ _ _ _ _).symm] }

end ConstructLeft

section ConstructRight

-- Construction of a right adjoint, analogous to the above.
variable {F} {G_obj : D → C}

variable (e : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G_obj Y))

variable (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)

include he

private theorem he' {X' X Y} (f g) : F.map f ≫ (e X Y).symm g = (e X' Y).symm (f ≫ g) := by
  intros <;> rw [Equivₓ.eq_symm_apply, he] <;> simp

/-- Construct a right adjoint functor to `F`, given the functor's value on objects `G_obj` and
a bijection `e` between `F.obj X ⟶ Y` and `X ⟶ G_obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X' Y (F.map f ≫ g) = f ≫ e X Y g`.
Dual to `left_adjoint_of_equiv`. -/
@[simps]
def rightAdjointOfEquiv : D ⥤ C where
  obj := G_obj
  map := fun Y Y' g => (e (G_obj Y) Y') ((e (G_obj Y) Y).symm (𝟙 _) ≫ g)
  map_comp' := fun Y Y' Y'' g g' => by
    rw [← Equivₓ.eq_symm_apply, ← he' e he, Equivₓ.symm_apply_apply]
    conv => rhs rw [← assoc, he' e he, comp_id, Equivₓ.symm_apply_apply]
    simp

/-- Show that the functor given by `right_adjoint_of_equiv` is indeed right adjoint to `F`. Dual
to `adjunction_of_equiv_left`. -/
@[simps]
def adjunctionOfEquivRight : F ⊣ rightAdjointOfEquiv e he :=
  mkOfHomEquiv
    { homEquiv := e,
      hom_equiv_naturality_left_symm' := by
        intros <;> rw [Equivₓ.symm_apply_eq, he] <;> simp ,
      hom_equiv_naturality_right' := by
        intro X Y Y' g h
        erw [← he, Equivₓ.apply_eq_iff_eq, ← assoc, he' e he, comp_id, Equivₓ.symm_apply_apply] }

end ConstructRight

/-- If the unit and counit of a given adjunction are (pointwise) isomorphisms, then we can upgrade the
adjunction to an equivalence.
-/
@[simps]
noncomputable def toEquivalence (adj : F ⊣ G) [∀ X, IsIso (adj.Unit.app X)] [∀ Y, IsIso (adj.counit.app Y)] :
    C ≌ D where
  Functor := F
  inverse := G
  unitIso :=
    NatIso.ofComponents (fun X => asIso (adj.Unit.app X))
      (by
        simp )
  counitIso :=
    NatIso.ofComponents (fun Y => asIso (adj.counit.app Y))
      (by
        simp )

/-- If the unit and counit for the adjunction corresponding to a right adjoint functor are (pointwise)
isomorphisms, then the functor is an equivalence of categories.
-/
@[simps]
noncomputable def isRightAdjointToIsEquivalence [IsRightAdjoint G]
    [∀ X, IsIso ((Adjunction.ofRightAdjoint G).Unit.app X)] [∀ Y, IsIso ((Adjunction.ofRightAdjoint G).counit.app Y)] :
    IsEquivalence G :=
  IsEquivalence.ofEquivalenceInverse (Adjunction.ofRightAdjoint G).toEquivalence

end Adjunction

open Adjunction

namespace Equivalenceₓ

/-- The adjunction given by an equivalence of categories. (To obtain the opposite adjunction,
simply use `e.symm.to_adjunction`. -/
def toAdjunction (e : C ≌ D) : e.Functor ⊣ e.inverse :=
  mkOfUnitCounit
    ⟨e.Unit, e.counit, by
      ext
      dsimp'
      simp only [← id_comp]
      exact e.functor_unit_comp _, by
      ext
      dsimp'
      simp only [← id_comp]
      exact e.unit_inverse_comp _⟩

@[simp]
theorem as_equivalence_to_adjunction_unit {e : C ≌ D} : e.Functor.asEquivalence.toAdjunction.Unit = e.Unit :=
  rfl

@[simp]
theorem as_equivalence_to_adjunction_counit {e : C ≌ D} : e.Functor.asEquivalence.toAdjunction.counit = e.counit :=
  rfl

end Equivalenceₓ

namespace Functor

/-- An equivalence `E` is left adjoint to its inverse. -/
def adjunction (E : C ⥤ D) [IsEquivalence E] : E ⊣ E.inv :=
  E.asEquivalence.toAdjunction

/-- If `F` is an equivalence, it's a left adjoint. -/
instance (priority := 10) leftAdjointOfEquivalence {F : C ⥤ D} [IsEquivalence F] : IsLeftAdjoint F where
  right := _
  adj := Functor.adjunction F

@[simp]
theorem right_adjoint_of_is_equivalence {F : C ⥤ D} [IsEquivalence F] : rightAdjoint F = inv F :=
  rfl

/-- If `F` is an equivalence, it's a right adjoint. -/
instance (priority := 10) rightAdjointOfEquivalence {F : C ⥤ D} [IsEquivalence F] : IsRightAdjoint F where
  left := _
  adj := Functor.adjunction F.inv

@[simp]
theorem left_adjoint_of_is_equivalence {F : C ⥤ D} [IsEquivalence F] : leftAdjoint F = inv F :=
  rfl

end Functor

end CategoryTheory


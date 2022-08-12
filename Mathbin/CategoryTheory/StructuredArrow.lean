/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Scott Morrison
-/
import Mathbin.CategoryTheory.Punit
import Mathbin.CategoryTheory.Comma
import Mathbin.CategoryTheory.Limits.Shapes.Terminal

/-!
# The category of "structured arrows"

For `T : C ⥤ D`, a `T`-structured arrow with source `S : D`
is just a morphism `S ⟶ T.obj Y`, for some `Y : C`.

These form a category with morphisms `g : Y ⟶ Y'` making the obvious diagram commute.

We prove that `𝟙 (T.obj Y)` is the initial object in `T`-structured objects with source `T.obj Y`.
-/


namespace CategoryTheory

-- morphism levels before object levels. See note [category_theory universes].
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The category of `T`-structured arrows with domain `S : D` (here `T : C ⥤ D`),
has as its objects `D`-morphisms of the form `S ⟶ T Y`, for some `Y : C`,
and morphisms `C`-morphisms `Y ⟶ Y'` making the obvious triangle commute.
-/
@[nolint has_inhabited_instance]
def StructuredArrow (S : D) (T : C ⥤ D) :=
  Comma (Functor.fromPunit S) T deriving Category

namespace StructuredArrow

/-- The obvious projection functor from structured arrows. -/
@[simps]
def proj (S : D) (T : C ⥤ D) : StructuredArrow S T ⥤ C :=
  Comma.snd _ _

variable {S S' S'' : D} {Y Y' : C} {T : C ⥤ D}

/-- Construct a structured arrow from a morphism. -/
def mk (f : S ⟶ T.obj Y) : StructuredArrow S T :=
  ⟨⟨⟨⟩⟩, Y, f⟩

@[simp]
theorem mk_left (f : S ⟶ T.obj Y) : (mk f).left = ⟨⟨⟩⟩ :=
  rfl

@[simp]
theorem mk_right (f : S ⟶ T.obj Y) : (mk f).right = Y :=
  rfl

@[simp]
theorem mk_hom_eq_self (f : S ⟶ T.obj Y) : (mk f).Hom = f :=
  rfl

@[simp, reassoc]
theorem w {A B : StructuredArrow S T} (f : A ⟶ B) : A.Hom ≫ T.map f.right = B.Hom := by
  have := f.w <;> tidy

theorem eq_mk (f : StructuredArrow S T) : f = mk f.Hom := by
  cases f
  congr
  ext

/-- To construct a morphism of structured arrows,
we need a morphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps]
def homMk {f f' : StructuredArrow S T} (g : f.right ⟶ f'.right) (w : f.Hom ≫ T.map g = f'.Hom) : f ⟶ f' where
  left :=
    eqToHom
      (by
        ext)
  right := g
  w' := by
    dsimp'
    simpa using w.symm

/-- Given a structured arrow `X ⟶ F(U)`, and an arrow `U ⟶ Y`, we can construct a morphism of
structured arrow given by `(X ⟶ F(U)) ⟶ (X ⟶ F(U) ⟶ F(Y))`.
-/
def homMk' {F : C ⥤ D} {X : D} {Y : C} (U : StructuredArrow X F) (f : U.right ⟶ Y) :
    U ⟶ mk (U.Hom ≫ F.map f) where right := f

/-- To construct an isomorphism of structured arrows,
we need an isomorphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps]
def isoMk {f f' : StructuredArrow S T} (g : f.right ≅ f'.right) (w : f.Hom ≫ T.map g.Hom = f'.Hom) : f ≅ f' :=
  Comma.isoMk
    (eqToIso
      (by
        ext))
    g
    (by
      simpa [← eq_to_hom_map] using w.symm)

/-- A morphism between source objects `S ⟶ S'`
contravariantly induces a functor between structured arrows,
`structured_arrow S' T ⥤ structured_arrow S T`.

Ideally this would be described as a 2-functor from `D`
(promoted to a 2-category with equations as 2-morphisms)
to `Cat`.
-/
@[simps]
def map (f : S ⟶ S') : StructuredArrow S' T ⥤ StructuredArrow S T :=
  Comma.mapLeft _ ((Functor.const _).map f)

@[simp]
theorem map_mk {f : S' ⟶ T.obj Y} (g : S ⟶ S') : (map g).obj (mk f) = mk (g ≫ f) :=
  rfl

@[simp]
theorem map_id {f : StructuredArrow S T} : (map (𝟙 S)).obj f = f := by
  rw [eq_mk f]
  simp

@[simp]
theorem map_comp {f : S ⟶ S'} {f' : S' ⟶ S''} {h : StructuredArrow S'' T} :
    (map (f ≫ f')).obj h = (map f).obj ((map f').obj h) := by
  rw [eq_mk h]
  simp

instance proj_reflects_iso :
    ReflectsIsomorphisms
      (proj S T) where reflects := fun Y Z f t =>
    ⟨⟨structured_arrow.hom_mk (inv ((proj S T).map f))
          (by
            simp ),
        by
        tidy⟩⟩

open CategoryTheory.Limits

attribute [local tidy] tactic.discrete_cases

/-- The identity structured arrow is initial. -/
def mkIdInitial [Full T] [Faithful T] : IsInitial (mk (𝟙 (T.obj Y))) where
  desc := fun c =>
    homMk (T.preimage c.x.Hom)
      (by
        dsimp'
        simp )
  uniq' := fun c m _ => by
    ext
    apply T.map_injective
    simpa only [← hom_mk_right, ← T.image_preimage, w m] using (category.id_comp _).symm

variable {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]

/-- The functor `(S, F ⋙ G) ⥤ (S, G)`. -/
@[simps]
def pre (S : D) (F : B ⥤ C) (G : C ⥤ D) : StructuredArrow S (F ⋙ G) ⥤ StructuredArrow S G :=
  Comma.preRight _ F G

/-- The functor `(S, F) ⥤ (G(S), F ⋙ G)`. -/
@[simps]
def post (S : C) (F : B ⥤ C) (G : C ⥤ D) : StructuredArrow S F ⥤ StructuredArrow (G.obj S) (F ⋙ G) where
  obj := fun X => { right := X.right, Hom := G.map X.Hom }
  map := fun X Y f =>
    { right := f.right,
      w' := by
        simp [← functor.comp_map, G.map_comp, f.w] }

end StructuredArrow

/-- The category of `S`-costructured arrows with target `T : D` (here `S : C ⥤ D`),
has as its objects `D`-morphisms of the form `S Y ⟶ T`, for some `Y : C`,
and morphisms `C`-morphisms `Y ⟶ Y'` making the obvious triangle commute.
-/
@[nolint has_inhabited_instance]
def CostructuredArrow (S : C ⥤ D) (T : D) :=
  Comma S (Functor.fromPunit T)deriving Category

namespace CostructuredArrow

/-- The obvious projection functor from costructured arrows. -/
@[simps]
def proj (S : C ⥤ D) (T : D) : CostructuredArrow S T ⥤ C :=
  Comma.fst _ _

variable {T T' T'' : D} {Y Y' : C} {S : C ⥤ D}

/-- Construct a costructured arrow from a morphism. -/
def mk (f : S.obj Y ⟶ T) : CostructuredArrow S T :=
  ⟨Y, ⟨⟨⟩⟩, f⟩

@[simp]
theorem mk_left (f : S.obj Y ⟶ T) : (mk f).left = Y :=
  rfl

@[simp]
theorem mk_right (f : S.obj Y ⟶ T) : (mk f).right = ⟨⟨⟩⟩ :=
  rfl

@[simp]
theorem mk_hom_eq_self (f : S.obj Y ⟶ T) : (mk f).Hom = f :=
  rfl

@[simp, reassoc]
theorem w {A B : CostructuredArrow S T} (f : A ⟶ B) : S.map f.left ≫ B.Hom = A.Hom := by
  tidy

theorem eq_mk (f : CostructuredArrow S T) : f = mk f.Hom := by
  cases f
  congr
  ext

/-- To construct a morphism of costructured arrows,
we need a morphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[simps]
def homMk {f f' : CostructuredArrow S T} (g : f.left ⟶ f'.left) (w : S.map g ≫ f'.Hom = f.Hom) : f ⟶ f' where
  left := g
  right :=
    eqToHom
      (by
        ext)
  w' := by
    simpa [← eq_to_hom_map] using w

/-- To construct an isomorphism of costructured arrows,
we need an isomorphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[simps]
def isoMk {f f' : CostructuredArrow S T} (g : f.left ≅ f'.left) (w : S.map g.Hom ≫ f'.Hom = f.Hom) : f ≅ f' :=
  Comma.isoMk g
    (eqToIso
      (by
        ext))
    (by
      simpa [← eq_to_hom_map] using w)

/-- A morphism between target objects `T ⟶ T'`
covariantly induces a functor between costructured arrows,
`costructured_arrow S T ⥤ costructured_arrow S T'`.

Ideally this would be described as a 2-functor from `D`
(promoted to a 2-category with equations as 2-morphisms)
to `Cat`.
-/
@[simps]
def map (f : T ⟶ T') : CostructuredArrow S T ⥤ CostructuredArrow S T' :=
  Comma.mapRight _ ((Functor.const _).map f)

@[simp]
theorem map_mk {f : S.obj Y ⟶ T} (g : T ⟶ T') : (map g).obj (mk f) = mk (f ≫ g) :=
  rfl

@[simp]
theorem map_id {f : CostructuredArrow S T} : (map (𝟙 T)).obj f = f := by
  rw [eq_mk f]
  simp

@[simp]
theorem map_comp {f : T ⟶ T'} {f' : T' ⟶ T''} {h : CostructuredArrow S T} :
    (map (f ≫ f')).obj h = (map f').obj ((map f).obj h) := by
  rw [eq_mk h]
  simp

instance proj_reflects_iso :
    ReflectsIsomorphisms
      (proj S T) where reflects := fun Y Z f t =>
    ⟨⟨costructured_arrow.hom_mk (inv ((proj S T).map f))
          (by
            simp ),
        by
        tidy⟩⟩

open CategoryTheory.Limits

attribute [local tidy] tactic.discrete_cases

/-- The identity costructured arrow is terminal. -/
def mkIdTerminal [Full S] [Faithful S] : IsTerminal (mk (𝟙 (S.obj Y))) where
  lift := fun c =>
    homMk (S.preimage c.x.Hom)
      (by
        dsimp'
        simp )
  uniq' := by
    rintro c m -
    ext
    apply S.map_injective
    simpa only [← hom_mk_left, ← S.image_preimage, w m] using (category.comp_id _).symm

variable {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]

/-- The functor `(F ⋙ G, S) ⥤ (G, S)`. -/
@[simps]
def pre (F : B ⥤ C) (G : C ⥤ D) (S : D) : CostructuredArrow (F ⋙ G) S ⥤ CostructuredArrow G S :=
  Comma.preLeft F G _

/-- The functor `(F, S) ⥤ (F ⋙ G, G(S))`. -/
@[simps]
def post (F : B ⥤ C) (G : C ⥤ D) (S : C) : CostructuredArrow F S ⥤ CostructuredArrow (F ⋙ G) (G.obj S) where
  obj := fun X => { left := X.left, Hom := G.map X.Hom }
  map := fun X Y f =>
    { left := f.left,
      w' := by
        simp [← functor.comp_map, G.map_comp, f.w] }

end CostructuredArrow

open Opposite

namespace StructuredArrow

/-- For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of structured arrows `d ⟶ F.obj c` to the category of costructured arrows
`F.op.obj c ⟶ (op d)`.
-/
@[simps]
def toCostructuredArrow (F : C ⥤ D) (d : D) : (StructuredArrow d F)ᵒᵖ ⥤ CostructuredArrow F.op (op d) where
  obj := fun X => @CostructuredArrow.mk _ _ _ _ _ (op X.unop.right) F.op X.unop.Hom.op
  map := fun X Y f =>
    CostructuredArrow.homMk f.unop.right.op
      (by
        dsimp'
        rw [← op_comp, ← f.unop.w, functor.const.obj_map]
        erw [category.id_comp])

/-- For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of structured arrows `op d ⟶ F.op.obj c` to the category of costructured arrows
`F.obj c ⟶ d`.
-/
@[simps]
def toCostructuredArrow' (F : C ⥤ D) (d : D) : (StructuredArrow (op d) F.op)ᵒᵖ ⥤ CostructuredArrow F d where
  obj := fun X => @CostructuredArrow.mk _ _ _ _ _ (unop X.unop.right) F X.unop.Hom.unop
  map := fun X Y f =>
    CostructuredArrow.homMk f.unop.right.unop
      (by
        dsimp'
        rw [← Quiver.Hom.unop_op (F.map (Quiver.Hom.unop f.unop.right)), ← unop_comp, ← F.op_map, ← f.unop.w,
          functor.const.obj_map]
        erw [category.id_comp])

end StructuredArrow

namespace CostructuredArrow

/-- For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of costructured arrows `F.obj c ⟶ d` to the category of structured arrows
`op d ⟶ F.op.obj c`.
-/
@[simps]
def toStructuredArrow (F : C ⥤ D) (d : D) : (CostructuredArrow F d)ᵒᵖ ⥤ StructuredArrow (op d) F.op where
  obj := fun X => @StructuredArrow.mk _ _ _ _ _ (op X.unop.left) F.op X.unop.Hom.op
  map := fun X Y f =>
    StructuredArrow.homMk f.unop.left.op
      (by
        dsimp'
        rw [← op_comp, f.unop.w, functor.const.obj_map]
        erw [category.comp_id])

/-- For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of costructured arrows `F.op.obj c ⟶ op d` to the category of structured arrows
`d ⟶ F.obj c`.
-/
@[simps]
def toStructuredArrow' (F : C ⥤ D) (d : D) : (CostructuredArrow F.op (op d))ᵒᵖ ⥤ StructuredArrow d F where
  obj := fun X => @StructuredArrow.mk _ _ _ _ _ (unop X.unop.left) F X.unop.Hom.unop
  map := fun X Y f =>
    StructuredArrow.homMk f.unop.left.unop
      (by
        dsimp'
        rw [← Quiver.Hom.unop_op (F.map f.unop.left.unop), ← unop_comp, ← F.op_map, f.unop.w, functor.const.obj_map]
        erw [category.comp_id])

end CostructuredArrow

/-- For a functor `F : C ⥤ D` and an object `d : D`, the category of structured arrows `d ⟶ F.obj c`
is contravariantly equivalent to the category of costructured arrows `F.op.obj c ⟶ op d`.
-/
def structuredArrowOpEquivalence (F : C ⥤ D) (d : D) : (StructuredArrow d F)ᵒᵖ ≌ CostructuredArrow F.op (op d) :=
  Equivalence.mk (StructuredArrow.toCostructuredArrow F d) (CostructuredArrow.toStructuredArrow' F d).rightOp
    (NatIso.ofComponents
      (fun X =>
        (@StructuredArrow.isoMk _ _ _ _ _ _ (StructuredArrow.mk (unop X).Hom) (unop X) (Iso.refl _)
            (by
              tidy)).op)
      fun X Y f =>
      Quiver.Hom.unop_inj <| by
        ext
        dsimp'
        simp )
    (NatIso.ofComponents
      (fun X =>
        @CostructuredArrow.isoMk _ _ _ _ _ _ (CostructuredArrow.mk X.Hom) X (Iso.refl _)
          (by
            tidy))
      fun X Y f => by
      ext
      dsimp'
      simp )

/-- For a functor `F : C ⥤ D` and an object `d : D`, the category of costructured arrows
`F.obj c ⟶ d` is contravariantly equivalent to the category of structured arrows
`op d ⟶ F.op.obj c`.
-/
def costructuredArrowOpEquivalence (F : C ⥤ D) (d : D) : (CostructuredArrow F d)ᵒᵖ ≌ StructuredArrow (op d) F.op :=
  Equivalence.mk (CostructuredArrow.toStructuredArrow F d) (StructuredArrow.toCostructuredArrow' F d).rightOp
    (NatIso.ofComponents
      (fun X =>
        (@CostructuredArrow.isoMk _ _ _ _ _ _ (CostructuredArrow.mk (unop X).Hom) (unop X) (Iso.refl _)
            (by
              tidy)).op)
      fun X Y f =>
      Quiver.Hom.unop_inj <| by
        ext
        dsimp'
        simp )
    (NatIso.ofComponents
      (fun X =>
        @StructuredArrow.isoMk _ _ _ _ _ _ (StructuredArrow.mk X.Hom) X (Iso.refl _)
          (by
            tidy))
      fun X Y f => by
      ext
      dsimp'
      simp )

end CategoryTheory


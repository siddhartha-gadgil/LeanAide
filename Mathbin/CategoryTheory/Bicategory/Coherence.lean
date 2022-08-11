/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Junyan Xu
-/
import Mathbin.CategoryTheory.PathCategory
import Mathbin.CategoryTheory.Functor.FullyFaithful
import Mathbin.CategoryTheory.Bicategory.Free
import Mathbin.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# The coherence theorem for bicategories

In this file, we prove the coherence theorem for bicategories, stated in the following form: the
free bicategory over any quiver is locally thin.

The proof is almost the same as the proof of the coherence theorem for monoidal categories that
has been previously formalized in mathlib, which is based on the proof described by Ilya Beylin
and Peter Dybjer. The idea is to view a path on a quiver as a normal form of a 1-morphism in the
free bicategory on the same quiver. A normalization procedure is then described by
`normalize : pseudofunctor (free_bicategory B) (locally_discrete (paths B))`, which is a
pseudofunctor from the free bicategory to the locally discrete bicategory on the path category.
It turns out that this pseudofunctor is locally an equivalence of categories, and the coherence
theorem follows immediately from this fact.

## Main statements

* `locally_thin` : the free bicategory is locally thin, that is, there is at most one
  2-morphism between two fixed 1-morphisms.

## References

* [Ilya Beylin and Peter Dybjer, Extracting a proof of coherence for monoidal categories from a
   proof of normalization for monoids][beylin1996]
-/


open Quiver (Path)

open Quiver.Path

namespace CategoryTheory

open Bicategory Category

open Bicategory

universe v u

namespace FreeBicategory

variable {B : Type u} [Quiver.{v + 1} B]

/-- Auxiliary definition for `inclusion_path`. -/
@[simp]
def inclusionPathAuxₓ {a : B} : ∀ {b : B}, Path a b → Hom a b
  | _, nil => Hom.id a
  | _, cons p f => (inclusion_path_aux p).comp (Hom.of f)

/-- The discrete category on the paths includes into the category of 1-morphisms in the free
bicategory.
-/
def inclusionPath (a b : B) : Discrete (Path.{v + 1} a b) ⥤ Hom a b :=
  Discrete.functor inclusionPathAuxₓ

/-- The inclusion from the locally discrete bicategory on the path category into the free bicategory
as a prelax functor. This will be promoted to a pseudofunctor after proving the coherence theorem.
See `inclusion`.
-/
def preinclusion (B : Type u) [Quiver.{v + 1} B] : PrelaxFunctor (LocallyDiscrete (Paths B)) (FreeBicategory B) where
  obj := id
  map := fun a b => (inclusionPath a b).obj
  map₂ := fun a b => (inclusionPath a b).map

@[simp]
theorem preinclusion_obj (a : B) : (preinclusion B).obj a = a :=
  rfl

@[simp]
theorem preinclusion_map₂ {a b : B} (f g : Discrete (Path.{v + 1} a b)) (η : f ⟶ g) :
    (preinclusion B).map₂ η = eqToHom (congr_arg _ (Discrete.ext _ _ (Discrete.eq_of_hom η))) := by
  rcases η with ⟨⟨⟩⟩
  cases discrete.ext _ _ η
  exact (inclusion_path a b).map_id _

/-- The normalization of the composition of `p : path a b` and `f : hom b c`.
`p` will eventually be taken to be `nil` and we then get the normalization
of `f` alone, but the auxiliary `p` is necessary for Lean to accept the definition of
`normalize_iso` and the `whisker_left` case of `normalize_aux_congr` and `normalize_naturality`.
-/
@[simp]
def normalizeAuxₓ {a : B} : ∀ {b c : B}, Path a b → Hom b c → Path a c
  | _, _, p, hom.of f => p.cons f
  | _, _, p, hom.id b => p
  | _, _, p, hom.comp f g => normalize_aux (normalize_aux p f) g

/-- A 2-isomorphism between a partially-normalized 1-morphism in the free bicategory to the
fully-normalized 1-morphism.
-/
/-
We may define
```
def normalize_aux' : ∀ {a b : B}, hom a b → path a b
| _ _ (hom.of f) := f.to_path
| _ _ (hom.id b) := nil
| _ _ (hom.comp f g) := (normalize_aux' f).comp (normalize_aux' g)
```
and define `normalize_aux p f` to be `p.comp (normalize_aux' f)` and this will be
equal to the above definition, but the equality proof requires `comp_assoc`, and it
thus lacks the correct definitional property to make the definition of `normalize_iso`
typecheck.
```
example {a b c : B} (p : path a b) (f : hom b c) :
  normalize_aux p f = p.comp (normalize_aux' f) :=
by { induction f, refl, refl,
  case comp : _ _ _ _ _ ihf ihg { rw [normalize_aux, ihf, ihg], apply comp_assoc } }
```
-/
@[simp]
def normalizeIsoₓ {a : B} :
    ∀ {b c : B} (p : Path a b) (f : Hom b c), (preinclusion B).map ⟨p⟩ ≫ f ≅ (preinclusion B).map ⟨normalizeAuxₓ p f⟩
  | _, _, p, hom.of f => Iso.refl _
  | _, _, p, hom.id b => ρ_ _
  | _, _, p, hom.comp f g =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalize_iso p f) g ≪≫ normalize_iso (normalizeAuxₓ p f) g

/-- Given a 2-morphism between `f` and `g` in the free bicategory, we have the equality
`normalize_aux p f = normalize_aux p g`.
-/
theorem normalize_aux_congr {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g) :
    normalizeAuxₓ p f = normalizeAuxₓ p g := by
  rcases η with ⟨⟩
  apply @congr_fun _ _ fun p => normalize_aux p f
  clear p
  induction η
  case vcomp =>
    apply Eq.trans <;> assumption
  -- p ≠ nil required! See the docstring of `normalize_aux`.
  case whisker_left _ _ _ _ _ _ _ ih =>
    funext
    apply congr_fun ih
  case whisker_right _ _ _ _ _ _ _ ih =>
    funext
    apply congr_arg2ₓ _ (congr_fun ih p) rfl
  all_goals
    funext
    rfl

/-- The 2-isomorphism `normalize_iso p f` is natural in `f`. -/
theorem normalize_naturality {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g) :
    (preinclusion B).map ⟨p⟩ ◁ η ≫ (normalizeIsoₓ p g).Hom =
      (normalizeIsoₓ p f).Hom ≫ (preinclusion B).map₂ (eqToHom (Discrete.ext _ _ (normalize_aux_congr p η))) :=
  by
  rcases η with ⟨⟩
  induction η
  case id =>
    simp
  case vcomp _ _ _ _ _ _ _ ihf ihg =>
    rw [mk_vcomp, bicategory.whisker_left_comp]
    slice_lhs 2 3 => rw [ihg]
    slice_lhs 1 2 => rw [ihf]
    simp
  case whisker_left _ _ _ _ _ _ _ ih =>
    -- p ≠ nil required! See the docstring of `normalize_aux`.
    dsimp'
    simp_rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ih, assoc]
  case whisker_right _ _ _ _ _ h η ih =>
    dsimp'
    rw [associator_inv_naturality_middle_assoc, ← comp_whisker_right_assoc, ih, comp_whisker_right]
    have := dcongr_arg (fun x => (normalize_iso x h).Hom) (normalize_aux_congr p (Quot.mk _ η))
    dsimp'  at this
    simp [← this]
  all_goals
    dsimp'
    dsimp' [← id_def, ← comp_def]
    simp

@[simp]
theorem normalize_aux_nil_comp {a b c : B} (f : Hom a b) (g : Hom b c) :
    normalizeAuxₓ nil (f.comp g) = (normalizeAuxₓ nil f).comp (normalizeAuxₓ nil g) := by
  induction g generalizing a
  case id =>
    rfl
  case of =>
    rfl
  case comp _ _ _ g _ ihf ihg =>
    erw [ihg (f.comp g), ihf f, ihg g, comp_assoc]

/-- The normalization pseudofunctor for the free bicategory on a quiver `B`. -/
def normalize (B : Type u) [Quiver.{v + 1} B] : Pseudofunctor (FreeBicategory B) (LocallyDiscrete (Paths B)) where
  obj := id
  map := fun a b f => ⟨normalizeAuxₓ nil f⟩
  map₂ := fun a b f g η => eq_to_hom <| Discrete.ext _ _ <| normalize_aux_congr nil η
  map_id := fun a => eq_to_iso <| Discrete.ext _ _ rfl
  map_comp := fun a b c f g => eq_to_iso <| Discrete.ext _ _ <| normalize_aux_nil_comp f g

/-- Auxiliary definition for `normalize_equiv`. -/
def normalizeUnitIso (a b : FreeBicategory B) : 𝟭 (a ⟶ b) ≅ (normalize B).mapFunctor a b ⋙ inclusionPath a b :=
  NatIso.ofComponents (fun f => (λ_ f).symm ≪≫ normalizeIsoₓ nil f)
    (by
      intro f g η
      erw [left_unitor_inv_naturality_assoc, assoc]
      congr 1
      exact normalize_naturality nil η)

/-- Normalization as an equivalence of categories. -/
def normalizeEquiv (a b : B) : Hom a b ≌ Discrete (Path.{v + 1} a b) :=
  Equivalence.mk ((normalize _).mapFunctor a b) (inclusionPath a b) (normalizeUnitIso a b)
    (Discrete.natIso fun f =>
      eqToIso
        (by
          induction f <;> induction f <;> tidy))

/-- The coherence theorem for bicategories. -/
instance locally_thin {a b : FreeBicategory B} (f g : a ⟶ b) : Subsingleton (f ⟶ g) :=
  ⟨fun η θ => (normalizeEquiv a b).Functor.map_injective (Subsingleton.elimₓ _ _)⟩

/-- Auxiliary definition for `inclusion`. -/
def inclusionMapCompAuxₓ {a b : B} :
    ∀ {c : B} (f : Path a b) (g : Path b c),
      (preinclusion _).map (⟨f⟩ ≫ ⟨g⟩) ≅ (preinclusion _).map ⟨f⟩ ≫ (preinclusion _).map ⟨g⟩
  | _, f, nil => (ρ_ ((preinclusion _).map ⟨f⟩)).symm
  | _, f, cons g₁ g₂ => whiskerRightIso (inclusion_map_comp_aux f g₁) (Hom.of g₂) ≪≫ α_ _ _ _

/-- The inclusion pseudofunctor from the locally discrete bicategory on the path category into the
free bicategory.
-/
def inclusion (B : Type u) [Quiver.{v + 1} B] : Pseudofunctor (LocallyDiscrete (Paths B)) (FreeBicategory B) :=
  { -- All the conditions for 2-morphisms are trivial thanks to the coherence theorem!
      preinclusion
      B with
    map_id := fun a => Iso.refl (𝟙 a), map_comp := fun a b c f g => inclusionMapCompAuxₓ f.as g.as }

end FreeBicategory

end CategoryTheory


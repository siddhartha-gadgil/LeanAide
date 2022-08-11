/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison, Jakob von Raumer
-/
import Mathbin.CategoryTheory.Monoidal.Braided
import Mathbin.CategoryTheory.Closed.Monoidal
import Mathbin.Algebra.Category.Module.Basic
import Mathbin.LinearAlgebra.TensorProduct
import Mathbin.CategoryTheory.Linear.Yoneda
import Mathbin.CategoryTheory.Monoidal.Linear

/-!
# The symmetric monoidal category structure on R-modules

Mostly this uses existing machinery in `linear_algebra.tensor_product`.
We just need to provide a few small missing pieces to build the
`monoidal_category` instance and then the `symmetric_category` instance.

Note the universe level of the modules must be at least the universe level of the ring,
so that we have a monoidal unit.
For now, we simplify by insisting both universe levels are the same.

We then construct the monoidal closed structure on `Module R`.

If you're happy using the bundled `Module R`, it may be possible to mostly
use this as an interface and not need to interact much with the implementation details.
-/


universe v w x u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRingₓ R]

namespace MonoidalCategory

-- The definitions inside this namespace are essentially private.
-- After we build the `monoidal_category (Module R)` instance,
-- you should use that API.
open TensorProduct

attribute [local ext] TensorProduct.ext

/-- (implementation) tensor product of R-modules -/
def tensorObj (M N : ModuleCat R) : ModuleCat R :=
  ModuleCat.of R (M ⊗[R] N)

/-- (implementation) tensor product of morphisms R-modules -/
def tensorHom {M N M' N' : ModuleCat R} (f : M ⟶ N) (g : M' ⟶ N') : tensorObj M M' ⟶ tensorObj N N' :=
  TensorProduct.map f g

theorem tensor_id (M N : ModuleCat R) : tensorHom (𝟙 M) (𝟙 N) = 𝟙 (ModuleCat.of R (M ⊗ N)) := by
  ext1
  rfl

theorem tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : ModuleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ := by
  ext1
  rfl

/-- (implementation) the associator for R-modules -/
def associator (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (K : ModuleCat.{x} R) :
    tensorObj (tensorObj M N) K ≅ tensorObj M (tensorObj N K) :=
  (TensorProduct.assoc R M N K).toModuleIso

section

/-! The `associator_naturality` and `pentagon` lemmas below are very slow to elaborate.

We give them some help by expressing the lemmas first non-categorically, then using
`convert _aux using 1` to have the elaborator work as little as possible. -/


open TensorProduct (assoc map)

private theorem associator_naturality_aux {X₁ X₂ X₃ : Type _} [AddCommMonoidₓ X₁] [AddCommMonoidₓ X₂]
    [AddCommMonoidₓ X₃] [Module R X₁] [Module R X₂] [Module R X₃] {Y₁ Y₂ Y₃ : Type _} [AddCommMonoidₓ Y₁]
    [AddCommMonoidₓ Y₂] [AddCommMonoidₓ Y₃] [Module R Y₁] [Module R Y₂] [Module R Y₃] (f₁ : X₁ →ₗ[R] Y₁)
    (f₂ : X₂ →ₗ[R] Y₂) (f₃ : X₃ →ₗ[R] Y₃) :
    ↑(assoc R Y₁ Y₂ Y₃) ∘ₗ map (map f₁ f₂) f₃ = map f₁ (map f₂ f₃) ∘ₗ ↑(assoc R X₁ X₂ X₃) := by
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

variable (R)

private theorem pentagon_aux (W X Y Z : Type _) [AddCommMonoidₓ W] [AddCommMonoidₓ X] [AddCommMonoidₓ Y]
    [AddCommMonoidₓ Z] [Module R W] [Module R X] [Module R Y] [Module R Z] :
    ((map (1 : W →ₗ[R] W) (assoc R X Y Z).toLinearMap).comp (assoc R W (X ⊗[R] Y) Z).toLinearMap).comp
        (map ↑(assoc R W X Y) (1 : Z →ₗ[R] Z)) =
      (assoc R W X (Y ⊗[R] Z)).toLinearMap.comp (assoc R (W ⊗[R] X) Y Z).toLinearMap :=
  by
  apply TensorProduct.ext_fourfold
  intro w x y z
  rfl

end

theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : ModuleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).Hom =
      (associator X₁ X₂ X₃).Hom ≫ tensorHom f₁ (tensorHom f₂ f₃) :=
  by
  convert associator_naturality_aux f₁ f₂ f₃ using 1

theorem pentagon (W X Y Z : ModuleCat R) :
    tensorHom (associator W X Y).Hom (𝟙 Z) ≫
        (associator W (tensorObj X Y) Z).Hom ≫ tensorHom (𝟙 W) (associator X Y Z).Hom =
      (associator (tensorObj W X) Y Z).Hom ≫ (associator W X (tensorObj Y Z)).Hom :=
  by
  convert pentagon_aux R W X Y Z using 1

/-- (implementation) the left unitor for R-modules -/
def leftUnitor (M : ModuleCat.{u} R) : ModuleCat.of R (R ⊗[R] M) ≅ M :=
  (LinearEquiv.toModuleIso (TensorProduct.lid R M) : of R (R ⊗ M) ≅ of R M).trans (ofSelfIso M)

theorem left_unitor_naturality {M N : ModuleCat R} (f : M ⟶ N) :
    tensorHom (𝟙 (ModuleCat.of R R)) f ≫ (leftUnitor N).Hom = (leftUnitor M).Hom ≫ f := by
  ext x y
  dsimp'
  erw [TensorProduct.lid_tmul, TensorProduct.lid_tmul]
  rw [LinearMap.map_smul]
  rfl

/-- (implementation) the right unitor for R-modules -/
def rightUnitor (M : ModuleCat.{u} R) : ModuleCat.of R (M ⊗[R] R) ≅ M :=
  (LinearEquiv.toModuleIso (TensorProduct.rid R M) : of R (M ⊗ R) ≅ of R M).trans (ofSelfIso M)

theorem right_unitor_naturality {M N : ModuleCat R} (f : M ⟶ N) :
    tensorHom f (𝟙 (ModuleCat.of R R)) ≫ (rightUnitor N).Hom = (rightUnitor M).Hom ≫ f := by
  ext x y
  dsimp'
  erw [TensorProduct.rid_tmul, TensorProduct.rid_tmul]
  rw [LinearMap.map_smul]
  rfl

theorem triangle (M N : ModuleCat.{u} R) :
    (associator M (ModuleCat.of R R) N).Hom ≫ tensorHom (𝟙 M) (leftUnitor N).Hom =
      tensorHom (rightUnitor M).Hom (𝟙 N) :=
  by
  apply TensorProduct.ext_threefold
  intro x y z
  change R at y
  dsimp' [← tensor_hom, ← associator]
  erw [TensorProduct.lid_tmul, TensorProduct.rid_tmul]
  exact (TensorProduct.smul_tmul _ _ _).symm

end MonoidalCategory

open MonoidalCategory

instance monoidalCategory : MonoidalCategory (ModuleCat.{u} R) where
  -- data
  tensorObj := tensorObj
  tensorHom := @tensorHom _ _
  tensorUnit := ModuleCat.of R R
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  -- properties
  tensor_id' := fun M N => tensor_id M N
  tensor_comp' := fun M N K M' N' K' f g h => tensor_comp f g h
  associator_naturality' := fun M N K M' N' K' f g h => associator_naturality f g h
  left_unitor_naturality' := fun M N f => left_unitor_naturality f
  right_unitor_naturality' := fun M N f => right_unitor_naturality f
  pentagon' := fun M N K L => pentagon M N K L
  triangle' := fun M N => triangle M N

/-- Remind ourselves that the monoidal unit, being just `R`, is still a commutative ring. -/
instance : CommRingₓ ((𝟙_ (ModuleCat.{u} R) : ModuleCat.{u} R) : Type u) :=
  (by
    infer_instance : CommRingₓ R)

namespace MonoidalCategory

@[simp]
theorem hom_apply {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) : (f ⊗ g) (k ⊗ₜ m) = f k ⊗ₜ g m :=
  rfl

@[simp]
theorem left_unitor_hom_apply {M : ModuleCat.{u} R} (r : R) (m : M) :
    ((λ_ M).Hom : 𝟙_ (ModuleCat R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r

@[simp]
theorem left_unitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((λ_ M).inv : M ⟶ 𝟙_ (ModuleCat.{u} R) ⊗ M) m = 1 ⊗ₜ[R] m :=
  TensorProduct.lid_symm_apply m

@[simp]
theorem right_unitor_hom_apply {M : ModuleCat.{u} R} (m : M) (r : R) :
    ((ρ_ M).Hom : M ⊗ 𝟙_ (ModuleCat R) ⟶ M) (m ⊗ₜ r) = r • m :=
  TensorProduct.rid_tmul m r

@[simp]
theorem right_unitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((ρ_ M).inv : M ⟶ M ⊗ 𝟙_ (ModuleCat.{u} R)) m = m ⊗ₜ[R] 1 :=
  TensorProduct.rid_symm_apply m

@[simp]
theorem associator_hom_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).Hom : M ⊗ N ⊗ K ⟶ M ⊗ (N ⊗ K)) (m ⊗ₜ n ⊗ₜ k) = m ⊗ₜ (n ⊗ₜ k) :=
  rfl

@[simp]
theorem associator_inv_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).inv : M ⊗ (N ⊗ K) ⟶ M ⊗ N ⊗ K) (m ⊗ₜ (n ⊗ₜ k)) = m ⊗ₜ n ⊗ₜ k :=
  rfl

end MonoidalCategory

/-- (implementation) the braiding for R-modules -/
def braiding (M N : ModuleCat R) : tensorObj M N ≅ tensorObj N M :=
  LinearEquiv.toModuleIso (TensorProduct.comm R M N)

@[simp]
theorem braiding_naturality {X₁ X₂ Y₁ Y₂ : ModuleCat.{u} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ g ≫ (Y₁.braiding Y₂).Hom = (X₁.braiding X₂).Hom ≫ g ⊗ f := by
  apply TensorProduct.ext'
  intro x y
  rfl

@[simp]
theorem hexagon_forward (X Y Z : ModuleCat.{u} R) :
    (α_ X Y Z).Hom ≫ (braiding X _).Hom ≫ (α_ Y Z X).Hom =
      (braiding X Y).Hom ⊗ 𝟙 Z ≫ (α_ Y X Z).Hom ≫ 𝟙 Y ⊗ (braiding X Z).Hom :=
  by
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

@[simp]
theorem hexagon_reverse (X Y Z : ModuleCat.{u} R) :
    (α_ X Y Z).inv ≫ (braiding _ Z).Hom ≫ (α_ Z X Y).inv =
      𝟙 X ⊗ (Y.braiding Z).Hom ≫ (α_ X Z Y).inv ≫ (X.braiding Z).Hom ⊗ 𝟙 Y :=
  by
  apply (cancel_epi (α_ X Y Z).Hom).1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

attribute [local ext] TensorProduct.ext

/-- The symmetric monoidal structure on `Module R`. -/
instance symmetricCategory : SymmetricCategory (ModuleCat.{u} R) where
  braiding := braiding
  braiding_naturality' := fun X₁ X₂ Y₁ Y₂ f g => braiding_naturality f g
  hexagon_forward' := hexagon_forward
  hexagon_reverse' := hexagon_reverse

namespace MonoidalCategory

@[simp]
theorem braiding_hom_apply {M N : ModuleCat.{u} R} (m : M) (n : N) : ((β_ M N).Hom : M ⊗ N ⟶ N ⊗ M) (m ⊗ₜ n) = n ⊗ₜ m :=
  rfl

@[simp]
theorem braiding_inv_apply {M N : ModuleCat.{u} R} (m : M) (n : N) : ((β_ M N).inv : N ⊗ M ⟶ M ⊗ N) (n ⊗ₜ m) = m ⊗ₜ n :=
  rfl

end MonoidalCategory

open Opposite

instance : MonoidalPreadditive (ModuleCat.{u} R) where
  tensor_zero' := by
    intros
    ext
    simp
  zero_tensor' := by
    intros
    ext
    simp
  tensor_add' := by
    intros
    ext
    simp [← TensorProduct.tmul_add]
  add_tensor' := by
    intros
    ext
    simp [← TensorProduct.add_tmul]

instance : MonoidalLinear R (ModuleCat.{u} R) where
  tensor_smul' := by
    intros
    ext
    simp
  smul_tensor' := by
    intros
    ext
    simp [← TensorProduct.smul_tmul]

/-- Auxiliary definition for the `monoidal_closed` instance on `Module R`.
(This is only a separate definition in order to speed up typechecking. )
-/
@[simps]
def monoidalClosedHomEquiv (M N P : ModuleCat.{u} R) :
    ((MonoidalCategory.tensorLeft M).obj N ⟶ P) ≃ (N ⟶ ((linearCoyoneda R (ModuleCat R)).obj (op M)).obj P) where
  toFun := fun f => LinearMap.compr₂ (TensorProduct.mk R N M) ((β_ N M).Hom ≫ f)
  invFun := fun f => (β_ M N).Hom ≫ TensorProduct.lift f
  left_inv := fun f => by
    ext m n
    simp only [← TensorProduct.mk_apply, ← TensorProduct.lift.tmul, ← LinearMap.compr₂_apply, ← Function.comp_app, ←
      coe_comp, ← monoidal_category.braiding_hom_apply]
  right_inv := fun f => by
    ext m n
    simp only [← TensorProduct.mk_apply, ← TensorProduct.lift.tmul, ← LinearMap.compr₂_apply, ←
      symmetric_category.symmetry_assoc]

instance :
    MonoidalClosed
      (ModuleCat.{u}
        R) where closed' := fun M =>
    { isAdj :=
        { right := (linearCoyoneda R (ModuleCat.{u} R)).obj (op M),
          adj := Adjunction.mkOfHomEquiv { homEquiv := fun N P => monoidalClosedHomEquiv M N P } } }

-- I can't seem to express the function coercion here without writing `@coe_fn`.
@[simp]
theorem monoidal_closed_curry {M N P : ModuleCat.{u} R} (f : M ⊗ N ⟶ P) (x : M) (y : N) :
    @coeFn _ _ LinearMap.hasCoeToFun ((MonoidalClosed.curry f : N →ₗ[R] M →ₗ[R] P) y) x = f (x ⊗ₜ[R] y) :=
  rfl

@[simp]
theorem monoidal_closed_uncurry {M N P : ModuleCat.{u} R} (f : N ⟶ M ⟶[ModuleCat.{u} R] P) (x : M) (y : N) :
    MonoidalClosed.uncurry f (x ⊗ₜ[R] y) = (@coeFn _ _ LinearMap.hasCoeToFun (f y)) x := by
  simp only [← monoidal_closed.uncurry, ← ihom.adjunction, ← is_left_adjoint.adj]
  simp

end ModuleCat


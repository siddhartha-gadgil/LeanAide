/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.RingTheory.TensorProduct
import Mathbin.Algebra.Category.Ring.Limits
import Mathbin.Algebra.Category.Ring.Colimits
import Mathbin.CategoryTheory.Limits.Shapes.StrictInitial
import Mathbin.RingTheory.Subring.Basic
import Mathbin.RingTheory.Ideal.LocalRing
import Mathbin.CategoryTheory.Limits.Preserves.Limits

/-!
# Constructions of (co)limits in CommRing

In this file we provide the explicit (co)cones for various (co)limits in `CommRing`, including
* tensor product is the pushout
* `Z` is the initial object
* `0` is the strict terminal object
* cartesian product is the product
* `ring_hom.eq_locus` is the equalizer

-/


universe u u'

open CategoryTheory CategoryTheory.Limits

open TensorProduct

namespace CommRingₓₓ

section Pushout

variable {R A B : CommRingₓₓ.{u}} (f : R ⟶ A) (g : R ⟶ B)

/-- The explicit cocone with tensor products as the fibered product in `CommRing`. -/
def pushoutCocone : Limits.PushoutCocone f g := by
  let this := RingHom.toAlgebra f
  let this := RingHom.toAlgebra g
  apply limits.pushout_cocone.mk
  show CommRingₓₓ
  exact CommRingₓₓ.of (A ⊗[R] B)
  show A ⟶ _
  exact algebra.tensor_product.include_left.to_ring_hom
  show B ⟶ _
  exact algebra.tensor_product.include_right.to_ring_hom
  ext r
  trans algebraMap R (A ⊗[R] B) r
  · exact algebra.tensor_product.include_left.commutes r
    
  · exact (algebra.tensor_product.include_right.commutes r).symm
    

@[simp]
theorem pushout_cocone_inl :
    (pushoutCocone f g).inl = by
      let this := f.to_algebra
      let this := g.to_algebra
      exact algebra.tensor_product.include_left.to_ring_hom :=
  rfl

@[simp]
theorem pushout_cocone_inr :
    (pushoutCocone f g).inr = by
      let this := f.to_algebra
      let this := g.to_algebra
      exact algebra.tensor_product.include_right.to_ring_hom :=
  rfl

@[simp]
theorem pushout_cocone_X :
    (pushoutCocone f g).x = by
      let this := f.to_algebra
      let this := g.to_algebra
      exact CommRingₓₓ.of (A ⊗[R] B) :=
  rfl

/-- Verify that the `pushout_cocone` is indeed the colimit. -/
def pushoutCoconeIsColimit : Limits.IsColimit (pushoutCocone f g) :=
  Limits.PushoutCocone.isColimitAux' _ fun s => by
    let this := RingHom.toAlgebra f
    let this := RingHom.toAlgebra g
    let this := RingHom.toAlgebra (f ≫ s.inl)
    let f' : A →ₐ[R] s.X :=
      { s.inl with
        commutes' := fun r => by
          change s.inl.to_fun (f r) = (f ≫ s.inl) r
          rfl }
    let g' : B →ₐ[R] s.X :=
      { s.inr with
        commutes' := fun r => by
          change (g ≫ s.inr) r = (f ≫ s.inl) r
          congr 1
          exact (s.ι.naturality limits.walking_span.hom.snd).trans (s.ι.naturality limits.walking_span.hom.fst).symm }
    -- The factor map is a ⊗ b ↦ f(a) * g(b).
    use AlgHom.toRingHom (Algebra.TensorProduct.productMap f' g')
    simp only [← pushout_cocone_inl, ← pushout_cocone_inr]
    constructor
    · ext x
      exact Algebra.TensorProduct.product_map_left_apply _ _ x
      
    constructor
    · ext x
      exact Algebra.TensorProduct.product_map_right_apply _ _ x
      
    intro h eq1 eq2
    let h' : A ⊗[R] B →ₐ[R] s.X :=
      { h with
        commutes' := fun r => by
          change h (f r ⊗ₜ[R] 1) = s.inl (f r)
          rw [← eq1]
          simp }
    suffices h' = Algebra.TensorProduct.productMap f' g' by
      ext x
      change h' x = Algebra.TensorProduct.productMap f' g' x
      rw [this]
    apply Algebra.TensorProduct.ext
    intro a b
    simp [eq1, eq2, h.map_mul]

end Pushout

section Terminal

/-- The trivial ring is the (strict) terminal object of `CommRing`. -/
def punitIsTerminal : IsTerminal (CommRingₓₓ.of.{u} PUnit) := by
  apply is_terminal.of_unique with { instances := false }
  tidy

instance CommRing_has_strict_terminal_objects : HasStrictTerminalObjects CommRingₓₓ.{u} := by
  apply has_strict_terminal_objects_of_terminal_is_strict (CommRingₓₓ.of PUnit)
  intro X f
  refine'
    ⟨⟨by
        tidy, by
        ext, _⟩⟩
  ext
  have e : (0 : X) = 1 := by
    rw [← f.map_one, ← f.map_zero]
    congr
  replace e : 0 * x = 1 * x := congr_arg (fun a => a * x) e
  rw [one_mulₓ, zero_mul, ← f.map_zero] at e
  exact e

theorem subsingleton_of_is_terminal {X : CommRingₓₓ} (hX : IsTerminal X) : Subsingleton X :=
  (hX.uniqueUpToIso punitIsTerminal).commRingIsoToRingEquiv.toEquiv.subsingleton_congr.mpr
    (show Subsingleton PUnit by
      infer_instance)

/-- `ℤ` is the initial object of `CommRing`. -/
def zIsInitial : IsInitial (CommRingₓₓ.of ℤ) := by
  apply is_initial.of_unique with { instances := false }
  exact fun R => ⟨⟨Int.castRingHom R⟩, fun a => a.ext_int _⟩

end Terminal

section Product

variable (A B : CommRingₓₓ.{u})

/-- The product in `CommRing` is the cartesian product. This is the binary fan. -/
@[simps x]
def prodFan : BinaryFan A B :=
  BinaryFan.mk (CommRingₓₓ.ofHom <| RingHom.fst A B) (CommRingₓₓ.ofHom <| RingHom.snd A B)

/-- The product in `CommRing` is the cartesian product. -/
def prodFanIsLimit : IsLimit (prodFan A B) where
  lift := fun c => RingHom.prod (c.π.app ⟨WalkingPair.left⟩) (c.π.app ⟨WalkingPair.right⟩)
  fac' := fun c j => by
    ext
    rcases j with ⟨⟨⟩⟩ <;>
      simpa only [← binary_fan.π_app_left, ← binary_fan.π_app_right, ← comp_apply, ← RingHom.prod_apply]
  uniq' := fun s m h => by
    ext
    · simpa using congr_hom (h ⟨walking_pair.left⟩) x
      
    · simpa using congr_hom (h ⟨walking_pair.right⟩) x
      

end Product

section Equalizer

variable {A B : CommRingₓₓ.{u}} (f g : A ⟶ B)

/-- The equalizer in `CommRing` is the equalizer as sets. This is the equalizer fork. -/
def equalizerFork : Fork f g :=
  Fork.ofι (CommRingₓₓ.ofHom (RingHom.eqLocus f g).Subtype)
    (by
      ext ⟨x, e⟩
      simpa using e)

/-- The equalizer in `CommRing` is the equalizer as sets. -/
def equalizerForkIsLimit : IsLimit (equalizerFork f g) := by
  fapply fork.is_limit.mk'
  intro s
  use s.ι.cod_restrict _ fun x => (concrete_category.congr_hom s.condition x : _)
  constructor
  · ext
    rfl
    
  · intro m hm
    ext x
    exact concrete_category.congr_hom hm x
    

instance : IsLocalRingHom (equalizerFork f g).ι := by
  constructor
  rintro ⟨a, h₁ : _ = _⟩ (⟨⟨x, y, h₃, h₄⟩, rfl : x = _⟩ : IsUnit a)
  have : y ∈ RingHom.eqLocus f g := by
    apply (f.is_unit_map ⟨⟨x, y, h₃, h₄⟩, rfl⟩ : IsUnit (f x)).mul_left_inj.mp
    conv_rhs => rw [h₁]
    rw [← f.map_mul, ← g.map_mul, h₄, f.map_one, g.map_one]
  rw [is_unit_iff_exists_inv]
  exact ⟨⟨y, this⟩, Subtype.eq h₃⟩

instance equalizer_ι_is_local_ring_hom (F : walking_parallel_pair ⥤ CommRingₓₓ.{u}) :
    IsLocalRingHom (limit.π F WalkingParallelPair.zero) := by
  have := lim_map_π (diagram_iso_parallel_pair F).Hom walking_parallel_pair.zero
  rw [← is_iso.comp_inv_eq] at this
  rw [← this]
  rw [←
    limit.iso_limit_cone_hom_π
      ⟨_, equalizer_fork_is_limit (F.map walking_parallel_pair_hom.left) (F.map walking_parallel_pair_hom.right)⟩
      walking_parallel_pair.zero]
  change IsLocalRingHom ((lim.map _ ≫ _ ≫ (equalizer_fork _ _).ι) ≫ _)
  infer_instance

open CategoryTheory.Limits.WalkingParallelPair Opposite

open CategoryTheory.Limits.WalkingParallelPairHom

instance equalizer_ι_is_local_ring_hom' (F : walking_parallel_pairᵒᵖ ⥤ CommRingₓₓ.{u}) :
    IsLocalRingHom (limit.π F (Opposite.op WalkingParallelPair.one)) := by
  have : _ = limit.π F (walking_parallel_pair_op_equiv.functor.obj _) :=
    (limit.iso_limit_cone_inv_π ⟨_, is_limit.whisker_equivalence (limit.is_limit F) walking_parallel_pair_op_equiv⟩
      walking_parallel_pair.zero :
      _)
  erw [← this]
  infer_instance

end Equalizer

end CommRingₓₓ


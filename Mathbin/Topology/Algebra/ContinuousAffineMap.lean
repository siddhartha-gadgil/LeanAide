/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.LinearAlgebra.AffineSpace.AffineMap
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Topology.Algebra.Module.Basic

/-!
# Continuous affine maps.

This file defines a type of bundled continuous affine maps.

Note that the definition and basic properties established here require minimal assumptions, and do
not even assume compatibility between the topological and algebraic structures. Of course it is
necessary to assume some compatibility in order to obtain a useful theory. Such a theory is
developed elsewhere for affine spaces modelled on _normed_ vector spaces, but not yet for general
topological affine spaces (since we have not defined these yet).

## Main definitions:

 * `continuous_affine_map`

## Notation:

We introduce the notation `P →A[R] Q` for `continuous_affine_map R P Q`. Note that this is parallel
to the notation `E →L[R] F` for `continuous_linear_map R E F`.
-/


/-- A continuous map of affine spaces. -/
structure ContinuousAffineMap (R : Type _) {V W : Type _} (P Q : Type _) [Ringₓ R] [AddCommGroupₓ V] [Module R V]
  [TopologicalSpace P] [AddTorsor V P] [AddCommGroupₓ W] [Module R W] [TopologicalSpace Q] [AddTorsor W Q] extends
  P →ᵃ[R] Q where
  cont : Continuous to_fun

-- mathport name: «expr →A[ ] »
notation:25 P " →A[" R "] " Q => ContinuousAffineMap R P Q

namespace ContinuousAffineMap

variable {R V W P Q : Type _} [Ringₓ R]

variable [AddCommGroupₓ V] [Module R V] [TopologicalSpace P] [AddTorsor V P]

variable [AddCommGroupₓ W] [Module R W] [TopologicalSpace Q] [AddTorsor W Q]

include V W

/-- see Note [function coercion] -/
instance : CoeFun (P →A[R] Q) fun _ => P → Q :=
  ⟨fun f => f.toAffineMap.toFun⟩

theorem to_fun_eq_coe (f : P →A[R] Q) : f.toFun = ⇑f :=
  rfl

theorem coe_injective : @Function.Injective (P →A[R] Q) (P → Q) coeFn := by
  rintro ⟨⟨f, ⟨f', hf₁, hf₂⟩, hf₀⟩, hf₁⟩ ⟨⟨g, ⟨g', hg₁, hg₂⟩, hg₀⟩, hg₁⟩ h
  have : f = g ∧ f' = g' := by
    simpa only using AffineMap.coe_fn_injective h
  congr
  exacts[this.1, this.2]

@[ext]
theorem ext {f g : P →A[R] Q} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h

theorem ext_iff {f g : P →A[R] Q} : f = g ↔ ∀ x, f x = g x :=
  ⟨by
    rintro rfl x
    rfl, ext⟩

theorem congr_fun {f g : P →A[R] Q} (h : f = g) (x : P) : f x = g x :=
  h ▸ rfl

instance : Coe (P →A[R] Q) (P →ᵃ[R] Q) :=
  ⟨toAffineMap⟩

/-- Forgetting its algebraic properties, a continuous affine map is a continuous map. -/
def toContinuousMap (f : P →A[R] Q) : C(P, Q) :=
  ⟨f, f.cont⟩

instance : Coe (P →A[R] Q) C(P, Q) :=
  ⟨toContinuousMap⟩

@[simp]
theorem to_affine_map_eq_coe (f : P →A[R] Q) : f.toAffineMap = ↑f :=
  rfl

@[simp]
theorem to_continuous_map_coe (f : P →A[R] Q) : f.toContinuousMap = ↑f :=
  rfl

@[simp, norm_cast]
theorem coe_to_affine_map (f : P →A[R] Q) : ((f : P →ᵃ[R] Q) : P → Q) = f :=
  rfl

@[simp, norm_cast]
theorem coe_to_continuous_map (f : P →A[R] Q) : ((f : C(P, Q)) : P → Q) = f :=
  rfl

theorem to_affine_map_injective {f g : P →A[R] Q} (h : (f : P →ᵃ[R] Q) = (g : P →ᵃ[R] Q)) : f = g := by
  ext a
  exact AffineMap.congr_fun h a

theorem to_continuous_map_injective {f g : P →A[R] Q} (h : (f : C(P, Q)) = (g : C(P, Q))) : f = g := by
  ext a
  exact ContinuousMap.congr_fun h a

@[norm_cast]
theorem coe_affine_map_mk (f : P →ᵃ[R] Q) (h) : ((⟨f, h⟩ : P →A[R] Q) : P →ᵃ[R] Q) = f :=
  rfl

@[norm_cast]
theorem coe_continuous_map_mk (f : P →ᵃ[R] Q) (h) : ((⟨f, h⟩ : P →A[R] Q) : C(P, Q)) = ⟨f, h⟩ :=
  rfl

@[simp]
theorem coe_mk (f : P →ᵃ[R] Q) (h) : ((⟨f, h⟩ : P →A[R] Q) : P → Q) = f :=
  rfl

@[simp]
theorem mk_coe (f : P →A[R] Q) (h) : (⟨(f : P →ᵃ[R] Q), h⟩ : P →A[R] Q) = f := by
  ext
  rfl

@[continuity]
protected theorem continuous (f : P →A[R] Q) : Continuous f :=
  f.2

variable (R P)

/-- The constant map is a continuous affine map. -/
def const (q : Q) : P →A[R] Q :=
  { AffineMap.const R P q with toFun := AffineMap.const R P q, cont := continuous_const }

@[simp]
theorem coe_const (q : Q) : (const R P q : P → Q) = Function.const P q :=
  rfl

noncomputable instance : Inhabited (P →A[R] Q) :=
  ⟨const R P <|
      Nonempty.some
        (by
          infer_instance : Nonempty Q)⟩

variable {R P} {W₂ Q₂ : Type _}

variable [AddCommGroupₓ W₂] [Module R W₂] [TopologicalSpace Q₂] [AddTorsor W₂ Q₂]

include W₂

/-- The composition of morphisms is a morphism. -/
def comp (f : Q →A[R] Q₂) (g : P →A[R] Q) : P →A[R] Q₂ :=
  { (f : Q →ᵃ[R] Q₂).comp (g : P →ᵃ[R] Q) with cont := f.cont.comp g.cont }

@[simp, norm_cast]
theorem coe_comp (f : Q →A[R] Q₂) (g : P →A[R] Q) : (f.comp g : P → Q₂) = (f : Q → Q₂) ∘ (g : P → Q) :=
  rfl

theorem comp_apply (f : Q →A[R] Q₂) (g : P →A[R] Q) (x : P) : f.comp g x = f (g x) :=
  rfl

omit W₂

section ModuleValuedMaps

variable {S : Type _}

variable [TopologicalSpace W]

instance : Zero (P →A[R] W) :=
  ⟨ContinuousAffineMap.const R P 0⟩

@[norm_cast, simp]
theorem coe_zero : ((0 : P →A[R] W) : P → W) = 0 :=
  rfl

theorem zero_apply (x : P) : (0 : P →A[R] W) x = 0 :=
  rfl

section MulAction

variable [Monoidₓ S] [DistribMulAction S W] [SmulCommClass R S W]

variable [HasContinuousConstSmul S W]

instance : HasSmul S (P →A[R] W) where smul := fun t f => { t • (f : P →ᵃ[R] W) with cont := f.Continuous.const_smul t }

@[norm_cast, simp]
theorem coe_smul (t : S) (f : P →A[R] W) : ⇑(t • f) = t • f :=
  rfl

theorem smul_apply (t : S) (f : P →A[R] W) (x : P) : (t • f) x = t • f x :=
  rfl

instance [DistribMulAction Sᵐᵒᵖ W] [IsCentralScalar S W] :
    IsCentralScalar S (P →A[R] W) where op_smul_eq_smul := fun t f => ext fun _ => op_smul_eq_smul _ _

instance : MulAction S (P →A[R] W) :=
  Function.Injective.mulAction _ coe_injective coe_smul

end MulAction

variable [TopologicalAddGroup W]

instance :
    Add
      (P →A[R]
        W) where add := fun f g => { (f : P →ᵃ[R] W) + (g : P →ᵃ[R] W) with cont := f.Continuous.add g.Continuous }

@[norm_cast, simp]
theorem coe_add (f g : P →A[R] W) : ⇑(f + g) = f + g :=
  rfl

theorem add_apply (f g : P →A[R] W) (x : P) : (f + g) x = f x + g x :=
  rfl

instance :
    Sub
      (P →A[R]
        W) where sub := fun f g => { (f : P →ᵃ[R] W) - (g : P →ᵃ[R] W) with cont := f.Continuous.sub g.Continuous }

@[norm_cast, simp]
theorem coe_sub (f g : P →A[R] W) : ⇑(f - g) = f - g :=
  rfl

theorem sub_apply (f g : P →A[R] W) (x : P) : (f - g) x = f x - g x :=
  rfl

instance : Neg (P →A[R] W) where neg := fun f => { -(f : P →ᵃ[R] W) with cont := f.Continuous.neg }

@[norm_cast, simp]
theorem coe_neg (f : P →A[R] W) : ⇑(-f) = -f :=
  rfl

theorem neg_apply (f : P →A[R] W) (x : P) : (-f) x = -f x :=
  rfl

instance : AddCommGroupₓ (P →A[R] W) :=
  coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

instance [Monoidₓ S] [DistribMulAction S W] [SmulCommClass R S W] [HasContinuousConstSmul S W] :
    DistribMulAction S (P →A[R] W) :=
  Function.Injective.distribMulAction ⟨fun f => f.toAffineMap.toFun, rfl, coe_add⟩ coe_injective coe_smul

instance [Semiringₓ S] [Module S W] [SmulCommClass R S W] [HasContinuousConstSmul S W] : Module S (P →A[R] W) :=
  Function.Injective.module S ⟨fun f => f.toAffineMap.toFun, rfl, coe_add⟩ coe_injective coe_smul

end ModuleValuedMaps

end ContinuousAffineMap

namespace ContinuousLinearMap

variable {R V W : Type _} [Ringₓ R]

variable [AddCommGroupₓ V] [Module R V] [TopologicalSpace V]

variable [AddCommGroupₓ W] [Module R W] [TopologicalSpace W]

/-- A continuous linear map can be regarded as a continuous affine map. -/
def toContinuousAffineMap (f : V →L[R] W) : V →A[R] W where
  toFun := f
  linear := f
  map_vadd' := by
    simp
  cont := f.cont

@[simp]
theorem coe_to_continuous_affine_map (f : V →L[R] W) : ⇑f.toContinuousAffineMap = f :=
  rfl

@[simp]
theorem to_continuous_affine_map_map_zero (f : V →L[R] W) : f.toContinuousAffineMap 0 = 0 := by
  simp

end ContinuousLinearMap


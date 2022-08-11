/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathbin.Topology.Algebra.GroupCompletion
import Mathbin.Topology.Algebra.Ring

/-!
# Completion of topological rings:

This files endows the completion of a topological ring with a ring structure.
More precisely the instance `uniform_space.completion.ring` builds a ring structure
on the completion of a ring endowed with a compatible uniform structure in the sense of
`uniform_add_group`. There is also a commutative version when the original ring is commutative.

The last part of the file builds a ring structure on the biggest separated quotient of a ring.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous ring morphisms.

* `uniform_space.completion.extension_hom`: extends a continuous ring morphism from `R`
  to a complete separated group `S` to `completion R`.
* `uniform_space.completion.map_ring_hom` : promotes a continuous ring morphism
  from `R` to `S` into a continuous ring morphism from `completion R` to `completion S`.
-/


open Classical Set Filter TopologicalSpace AddCommGroupₓ

open Classical

noncomputable section

universe u

namespace UniformSpace.Completion

open DenseInducing UniformSpace Function

variable (α : Type _) [Ringₓ α] [UniformSpace α]

instance : One (Completion α) :=
  ⟨(1 : α)⟩

instance : Mul (Completion α) :=
  ⟨curry <| (dense_inducing_coe.Prod dense_inducing_coe).extend (coe ∘ uncurry (· * ·))⟩

@[norm_cast]
theorem coe_one : ((1 : α) : Completion α) = 1 :=
  rfl

variable {α} [TopologicalRing α]

@[norm_cast]
theorem coe_mul (a b : α) : ((a * b : α) : Completion α) = a * b :=
  ((dense_inducing_coe.Prod dense_inducing_coe).extend_eq ((continuous_coe α).comp (@continuous_mul α _ _ _))
      (a, b)).symm

variable [UniformAddGroup α]

theorem continuous_mul : Continuous fun p : Completion α × Completion α => p.1 * p.2 := by
  let m := (AddMonoidHom.mul : α →+ α →+ α).compr₂ to_compl
  have : Continuous fun p : α × α => m p.1 p.2 := (continuous_coe α).comp continuous_mul
  have di : DenseInducing (to_compl : α → completion α) := dense_inducing_coe
  convert di.extend_Z_bilin di this
  ext ⟨x, y⟩
  rfl

theorem Continuous.mul {β : Type _} [TopologicalSpace β] {f g : β → Completion α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => f b * g b :=
  continuous_mul.comp (hf.prod_mk hg : _)

instance : Ringₓ (Completion α) :=
  { AddMonoidWithOneₓ.unary, Completion.addCommGroup, Completion.hasMul α, Completion.hasOne α with
    one_mul := fun a =>
      Completion.induction_on a (is_closed_eq (Continuous.mul continuous_const continuous_id) continuous_id) fun a => by
        rw [← coe_one, ← coe_mul, one_mulₓ],
    mul_one := fun a =>
      Completion.induction_on a (is_closed_eq (Continuous.mul continuous_id continuous_const) continuous_id) fun a => by
        rw [← coe_one, ← coe_mul, mul_oneₓ],
    mul_assoc := fun a b c =>
      Completion.induction_on₃ a b c
        (is_closed_eq
          (Continuous.mul (Continuous.mul continuous_fst (continuous_fst.comp continuous_snd))
            (continuous_snd.comp continuous_snd))
          (Continuous.mul continuous_fst
            (Continuous.mul (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
        fun a b c => by
        rw [← coe_mul, ← coe_mul, ← coe_mul, ← coe_mul, mul_assoc],
    left_distrib := fun a b c =>
      Completion.induction_on₃ a b c
        (is_closed_eq
          (Continuous.mul continuous_fst
            (Continuous.add (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)))
          (Continuous.add (Continuous.mul continuous_fst (continuous_fst.comp continuous_snd))
            (Continuous.mul continuous_fst (continuous_snd.comp continuous_snd))))
        fun a b c => by
        rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, mul_addₓ],
    right_distrib := fun a b c =>
      Completion.induction_on₃ a b c
        (is_closed_eq
          (Continuous.mul (Continuous.add continuous_fst (continuous_fst.comp continuous_snd))
            (continuous_snd.comp continuous_snd))
          (Continuous.add (Continuous.mul continuous_fst (continuous_snd.comp continuous_snd))
            (Continuous.mul (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
        fun a b c => by
        rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, add_mulₓ] }

/-- The map from a uniform ring to its completion, as a ring homomorphism. -/
def coeRingHom : α →+* Completion α :=
  ⟨coe, coe_one α, fun a b => coe_mul a b, coe_zero, fun a b => coe_add a b⟩

theorem continuous_coe_ring_hom : Continuous (coeRingHom : α → Completion α) :=
  continuous_coe α

variable {β : Type u} [UniformSpace β] [Ringₓ β] [UniformAddGroup β] [TopologicalRing β] (f : α →+* β)
  (hf : Continuous f)

/-- The completion extension as a ring morphism. -/
def extensionHom [CompleteSpace β] [SeparatedSpace β] : Completion α →+* β :=
  have hf' : Continuous (f : α →+ β) := hf
  -- helping the elaborator
  have hf : UniformContinuous f := uniform_continuous_add_monoid_hom_of_continuous hf'
  { toFun := Completion.extension f,
    map_zero' := by
      rw [← coe_zero, extension_coe hf, f.map_zero],
    map_add' := fun a b =>
      Completion.induction_on₂ a b
        (is_closed_eq (continuous_extension.comp continuous_add)
          ((continuous_extension.comp continuous_fst).add (continuous_extension.comp continuous_snd)))
        fun a b => by
        rw [← coe_add, extension_coe hf, extension_coe hf, extension_coe hf, f.map_add],
    map_one' := by
      rw [← coe_one, extension_coe hf, f.map_one],
    map_mul' := fun a b =>
      Completion.induction_on₂ a b
        (is_closed_eq (continuous_extension.comp continuous_mul)
          ((continuous_extension.comp continuous_fst).mul (continuous_extension.comp continuous_snd)))
        fun a b => by
        rw [← coe_mul, extension_coe hf, extension_coe hf, extension_coe hf, f.map_mul] }

instance top_ring_compl : TopologicalRing (Completion α) where
  continuous_add := continuous_add
  continuous_mul := continuous_mul

/-- The completion map as a ring morphism. -/
def mapRingHom (hf : Continuous f) : Completion α →+* Completion β :=
  extensionHom (coeRingHom.comp f) (continuous_coe_ring_hom.comp hf)

variable (R : Type _) [CommRingₓ R] [UniformSpace R] [UniformAddGroup R] [TopologicalRing R]

instance : CommRingₓ (Completion R) :=
  { Completion.ring with
    mul_comm := fun a b =>
      Completion.induction_on₂ a b
        (is_closed_eq (continuous_fst.mul continuous_snd) (continuous_snd.mul continuous_fst)) fun a b => by
        rw [← coe_mul, ← coe_mul, mul_comm] }

end UniformSpace.Completion

namespace UniformSpace

variable {α : Type _}

theorem ring_sep_rel (α) [CommRingₓ α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
    separationSetoid α = Submodule.quotientRel (Ideal.closure ⊥) :=
  Setoidₓ.ext fun x y =>
    (add_group_separation_rel x y).trans <|
      Iff.trans
        (by
          rfl)
        (Submodule.quotient_rel_r_def _).symm

theorem ring_sep_quot (α : Type u) [r : CommRingₓ α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
    Quotientₓ (separationSetoid α) = (α ⧸ (⊥ : Ideal α).closure) := by
  rw [@ring_sep_rel α r] <;> rfl

/-- Given a topological ring `α` equipped with a uniform structure that makes subtraction uniformly
continuous, get an equivalence between the separated quotient of `α` and the quotient ring
corresponding to the closure of zero. -/
def sepQuotEquivRingQuot (α) [r : CommRingₓ α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
    Quotientₓ (separationSetoid α) ≃ α ⧸ (⊥ : Ideal α).closure :=
  Quotientₓ.congrRight fun x y =>
    (add_group_separation_rel x y).trans <|
      Iff.trans
        (by
          rfl)
        (Submodule.quotient_rel_r_def _).symm

-- TODO: use a form of transport a.k.a. lift definition a.k.a. transfer
instance commRing [CommRingₓ α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
    CommRingₓ (Quotientₓ (separationSetoid α)) := by
  rw [ring_sep_quot α] <;> infer_instance

instance topological_ring [CommRingₓ α] [UniformSpace α] [UniformAddGroup α] [TopologicalRing α] :
    TopologicalRing (Quotientₓ (separationSetoid α)) := by
  convert topological_ring_quotient (⊥ : Ideal α).closure <;>
    try
      apply ring_sep_rel
  simp [← UniformSpace.commRing]

end UniformSpace


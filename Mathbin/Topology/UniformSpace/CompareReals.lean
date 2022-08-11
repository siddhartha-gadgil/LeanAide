/-
Copyright (c) 2019 Patrick MAssot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathbin.Topology.UniformSpace.AbsoluteValue
import Mathbin.Topology.Instances.Real
import Mathbin.Topology.Instances.Rat
import Mathbin.Topology.UniformSpace.Completion

/-!
# Comparison of Cauchy reals and Bourbaki reals

In `data.real.basic` real numbers are defined using the so called Cauchy construction (although
it is due to Georg Cantor). More precisely, this construction applies to commutative rings equipped
with an absolute value with values in a linear ordered field.

On the other hand, in the `uniform_space` folder, we construct completions of general uniform
spaces, which allows to construct the Bourbaki real numbers. In this file we build uniformly
continuous bijections from Cauchy reals to Bourbaki reals and back. This is a cross sanity check of
both constructions. Of course those two constructions are variations on the completion idea, simply
with different level of generality. Comparing with Dedekind cuts or quasi-morphisms would be of a
completely different nature.

Note that `metric_space/cau_seq_filter` also relates the notions of Cauchy sequences in metric
spaces and Cauchy filters in general uniform spaces, and `metric_space/completion` makes sure
the completion (as a uniform space) of a metric space is a metric space.

Historical note: mathlib used to define real numbers in an intermediate way, using completion
of uniform spaces but extending multiplication in an ad-hoc way.

TODO:
* Upgrade this isomorphism to a topological ring isomorphism.
* Do the same comparison for p-adic numbers

## Implementation notes

The heavy work is done in `topology/uniform_space/abstract_completion` which provides an abstract
caracterization of completions of uniform spaces, and isomorphisms between them. The only work left
here is to prove the uniform space structure coming from the absolute value on ℚ (with values in ℚ,
not referring to ℝ) coincides with the one coming from the metric space structure (which of course
does use ℝ).

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

real numbers, completion, uniform spaces
-/


open Set Function Filter CauSeq UniformSpace

/-- The metric space uniform structure on ℚ (which presupposes the existence
of real numbers) agrees with the one coming directly from (abs : ℚ → ℚ). -/
theorem Rat.uniform_space_eq : IsAbsoluteValue.uniformSpace (abs : ℚ → ℚ) = PseudoMetricSpace.toUniformSpace := by
  ext s
  erw [Metric.mem_uniformity_dist, IsAbsoluteValue.mem_uniformity]
  constructor <;> rintro ⟨ε, ε_pos, h⟩
  · use ε, by
      exact_mod_cast ε_pos
    intro a b hab
    apply h
    rw [Rat.dist_eq, abs_sub_comm] at hab
    exact_mod_cast hab
    
  · obtain ⟨ε', h', h''⟩ : ∃ ε' : ℚ, 0 < ε' ∧ (ε' : ℝ) < ε
    exact exists_pos_rat_lt ε_pos
    use ε', h'
    intro a b hab
    apply h
    rw [Rat.dist_eq, abs_sub_comm]
    refine' lt_transₓ _ h''
    exact_mod_cast hab
    

/-- Cauchy reals packaged as a completion of ℚ using the absolute value route. -/
noncomputable def rationalCauSeqPkg : @AbstractCompletion ℚ <| IsAbsoluteValue.uniformSpace (abs : ℚ → ℚ) where
  Space := ℝ
  coe := (coe : ℚ → ℝ)
  uniformStruct := by
    infer_instance
  complete := by
    infer_instance
  separation := by
    infer_instance
  UniformInducing := by
    rw [Rat.uniform_space_eq]
    exact rat.uniform_embedding_coe_real.to_uniform_inducing
  dense := Rat.dense_embedding_coe_real.dense

namespace CompareReals

/-- Type wrapper around ℚ to make sure the absolute value uniform space instance is picked up
instead of the metric space one. We proved in rat.uniform_space_eq that they are equal,
but they are not definitionaly equal, so it would confuse the type class system (and probably
also human readers). -/
def Q :=
  ℚ deriving CommRingₓ, Inhabited

instance : UniformSpace Q :=
  IsAbsoluteValue.uniformSpace (abs : ℚ → ℚ)

/-- Real numbers constructed as in Bourbaki. -/
def Bourbakiℝ : Type :=
  Completion Q deriving Inhabited

instance Bourbaki.uniformSpace : UniformSpace Bourbakiℝ :=
  Completion.uniformSpace Q

/-- Bourbaki reals packaged as a completion of Q using the general theory. -/
def bourbakiPkg : AbstractCompletion Q :=
  completion.cpkg

/-- The equivalence between Bourbaki and Cauchy reals-/
noncomputable def compareEquiv : Bourbakiℝ ≃ ℝ :=
  bourbakiPkg.compareEquiv rationalCauSeqPkg

theorem compare_uc : UniformContinuous compareEquiv :=
  bourbakiPkg.uniform_continuous_compare_equiv _

theorem compare_uc_symm : UniformContinuous compareEquiv.symm :=
  bourbakiPkg.uniform_continuous_compare_equiv_symm _

end CompareReals


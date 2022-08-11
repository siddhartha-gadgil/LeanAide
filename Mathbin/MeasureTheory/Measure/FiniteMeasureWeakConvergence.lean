/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathbin.MeasureTheory.Measure.MeasureSpace
import Mathbin.MeasureTheory.Integral.SetIntegral
import Mathbin.Topology.ContinuousFunction.Bounded
import Mathbin.Topology.Algebra.Module.WeakDual
import Mathbin.Topology.MetricSpace.ThickenedIndicator

/-!
# Weak convergence of (finite) measures

This file defines the topology of weak convergence of finite measures and probability measures
on topological spaces. The topology of weak convergence is the coarsest topology w.r.t. which
for every bounded continuous `ℝ≥0`-valued function `f`, the integration of `f` against the
measure is continuous.

TODOs:
* Include the portmanteau theorem on characterizations of weak convergence of (Borel) probability
  measures.

## Main definitions

The main definitions are the
 * types `finite_measure α` and `probability_measure α` with topologies of weak convergence;
 * `to_weak_dual_bcnn : finite_measure α → (weak_dual ℝ≥0 (α →ᵇ ℝ≥0))`
   allowing to interpret a finite measure as a continuous linear functional on the space of
   bounded continuous nonnegative functions on `α`. This is used for the definition of the
   topology of weak convergence.

## Main results

 * Finite measures `μ` on `α` give rise to continuous linear functionals on the space of
   bounded continuous nonnegative functions on `α` via integration:
   `to_weak_dual_bcnn : finite_measure α → (weak_dual ℝ≥0 (α →ᵇ ℝ≥0))`.
 * `tendsto_iff_forall_lintegral_tendsto`: Convergence of finite measures and probability measures
   is characterized by the convergence of integrals of all bounded continuous (nonnegative)
   functions. This essentially shows that the given definition of topology corresponds to the
   common textbook definition of weak convergence of measures.

TODO:
* Portmanteau theorem:
  * `finite_measure.limsup_measure_closed_le_of_tendsto` proves one implication.
    The current formulation assumes `pseudo_emetric_space`. The only reason is to have
    bounded continuous pointwise approximations to the indicator function of a closed set. Clearly
    for example metrizability or pseudo-emetrizability would be sufficient assumptions. The
    typeclass assumptions should be later adjusted in a way that takes into account use cases, but
    the proof will presumably remain essentially the same.
  * Prove the rest of the implications.

## Notations

No new notation is introduced.

## Implementation notes

The topology of weak convergence of finite Borel measures will be defined using a mapping from
`finite_measure α` to `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)`, inheriting the topology from the latter.

The current implementation of `finite_measure α` and `probability_measure α` is directly as
subtypes of `measure α`, and the coercion to a function is the composition `ennreal.to_nnreal`
and the coercion to function of `measure α`. Another alternative would be to use a bijection
with `vector_measure α ℝ≥0` as an intermediate step. The choice of implementation should not have
drastic downstream effects, so it can be changed later if appropriate.

Potential advantages of using the `nnreal`-valued vector measure alternative:
 * The coercion to function would avoid need to compose with `ennreal.to_nnreal`, the
   `nnreal`-valued API could be more directly available.
Potential drawbacks of the vector measure alternative:
 * The coercion to function would lose monotonicity, as non-measurable sets would be defined to
   have measure 0.
 * No integration theory directly. E.g., the topology definition requires `lintegral` w.r.t.
   a coercion to `measure α` in any case.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

weak convergence of measures, finite measure, probability measure

-/


noncomputable section

open MeasureTheory

open Set

open Filter

open BoundedContinuousFunction

open TopologicalSpace Ennreal Nnreal BoundedContinuousFunction

namespace MeasureTheory

namespace FiniteMeasure

section FiniteMeasure

/-! ### Finite measures

In this section we define the `Type` of `finite_measure α`, when `α` is a measurable space. Finite
measures on `α` are a module over `ℝ≥0`.

If `α` is moreover a topological space and the sigma algebra on `α` is finer than the Borel sigma
algebra (i.e. `[opens_measurable_space α]`), then `finite_measure α` is equipped with the topology
of weak convergence of measures. This is implemented by defining a pairing of finite measures `μ`
on `α` with continuous bounded nonnegative functions `f : α →ᵇ ℝ≥0` via integration, and using the
associated weak topology (essentially the weak-star topology on the dual of `α →ᵇ ℝ≥0`).
-/


variable {α : Type _} [MeasurableSpace α]

/-- Finite measures are defined as the subtype of measures that have the property of being finite
measures (i.e., their total mass is finite). -/
def _root_.measure_theory.finite_measure (α : Type _) [MeasurableSpace α] : Type _ :=
  { μ : Measure α // IsFiniteMeasure μ }

/-- A finite measure can be interpreted as a measure. -/
instance : Coe (FiniteMeasure α) (MeasureTheory.Measure α) :=
  coeSubtype

instance is_finite_measure (μ : FiniteMeasure α) : IsFiniteMeasure (μ : Measure α) :=
  μ.Prop

instance : CoeFun (FiniteMeasure α) fun _ => Set α → ℝ≥0 :=
  ⟨fun μ s => (μ s).toNnreal⟩

theorem coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : FiniteMeasure α) :
    (ν : Set α → ℝ≥0 ) = fun s => ((ν : Measure α) s).toNnreal :=
  rfl

@[simp]
theorem ennreal_coe_fn_eq_coe_fn_to_measure (ν : FiniteMeasure α) (s : Set α) : (ν s : ℝ≥0∞) = (ν : Measure α) s :=
  Ennreal.coe_to_nnreal (measure_lt_top (↑ν) s).Ne

@[simp]
theorem val_eq_to_measure (ν : FiniteMeasure α) : ν.val = (ν : Measure α) :=
  rfl

theorem coe_injective : Function.Injective (coe : FiniteMeasure α → Measure α) :=
  Subtype.coe_injective

/-- The (total) mass of a finite measure `μ` is `μ univ`, i.e., the cast to `nnreal` of
`(μ : measure α) univ`. -/
def mass (μ : FiniteMeasure α) : ℝ≥0 :=
  μ Univ

@[simp]
theorem ennreal_mass {μ : FiniteMeasure α} : (μ.mass : ℝ≥0∞) = (μ : Measure α) Univ :=
  ennreal_coe_fn_eq_coe_fn_to_measure μ Set.Univ

instance hasZero : Zero (FiniteMeasure α) where zero := ⟨0, MeasureTheory.is_finite_measure_zero⟩

@[simp]
theorem Zero.mass : (0 : FiniteMeasure α).mass = 0 := by
  simp only [← mass]
  rfl

@[simp]
theorem mass_zero_iff (μ : FiniteMeasure α) : μ.mass = 0 ↔ μ = 0 := by
  refine'
    ⟨fun μ_mass => _, fun hμ => by
      simp only [← hμ, ← zero.mass]⟩
  ext1
  apply measure.measure_univ_eq_zero.mp
  rwa [← ennreal_mass, Ennreal.coe_eq_zero]

@[ext]
theorem extensionality (μ ν : FiniteMeasure α) (h : ∀ s : Set α, MeasurableSet s → μ s = ν s) : μ = ν := by
  ext1
  ext1 s s_mble
  simpa [← ennreal_coe_fn_eq_coe_fn_to_measure] using congr_arg (coe : ℝ≥0 → ℝ≥0∞) (h s s_mble)

instance : Inhabited (FiniteMeasure α) :=
  ⟨0⟩

instance : Add (FiniteMeasure α) where add := fun μ ν => ⟨μ + ν, MeasureTheory.is_finite_measure_add⟩

variable {R : Type _} [HasSmul R ℝ≥0 ] [HasSmul R ℝ≥0∞] [IsScalarTower R ℝ≥0 ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]

instance :
    HasSmul R
      (FiniteMeasure α) where smul := fun (c : R) μ => ⟨c • μ, MeasureTheory.is_finite_measure_smul_of_nnreal_tower⟩

@[simp, norm_cast]
theorem coe_zero : (coe : FiniteMeasure α → Measure α) 0 = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_add (μ ν : FiniteMeasure α) : ↑(μ + ν) = (↑μ + ↑ν : Measure α) :=
  rfl

@[simp, norm_cast]
theorem coe_smul (c : R) (μ : FiniteMeasure α) : ↑(c • μ) = (c • ↑μ : Measure α) :=
  rfl

@[simp, norm_cast]
theorem coe_fn_zero : (⇑(0 : FiniteMeasure α) : Set α → ℝ≥0 ) = (0 : Set α → ℝ≥0 ) := by
  funext
  rfl

@[simp, norm_cast]
theorem coe_fn_add (μ ν : FiniteMeasure α) : (⇑(μ + ν) : Set α → ℝ≥0 ) = (⇑μ + ⇑ν : Set α → ℝ≥0 ) := by
  funext
  simp [Ennreal.coe_eq_coe]

@[simp, norm_cast]
theorem coe_fn_smul [IsScalarTower R ℝ≥0 ℝ≥0 ] (c : R) (μ : FiniteMeasure α) :
    (⇑(c • μ) : Set α → ℝ≥0 ) = c • (⇑μ : Set α → ℝ≥0 ) := by
  funext
  simp [Ennreal.coe_eq_coe, ← Ennreal.coe_smul]

instance : AddCommMonoidₓ (FiniteMeasure α) :=
  coe_injective.AddCommMonoid coe coe_zero coe_add fun _ _ => coe_smul _ _

/-- Coercion is an `add_monoid_hom`. -/
@[simps]
def coeAddMonoidHom : FiniteMeasure α →+ Measure α where
  toFun := coe
  map_zero' := coe_zero
  map_add' := coe_add

instance {α : Type _} [MeasurableSpace α] : Module ℝ≥0 (FiniteMeasure α) :=
  Function.Injective.module _ coeAddMonoidHom coe_injective coe_smul

@[simp]
theorem coe_fn_smul_apply [IsScalarTower R ℝ≥0 ℝ≥0 ] (c : R) (μ : FiniteMeasure α) (s : Set α) : (c • μ) s = c • μ s :=
  by
  simp only [← coe_fn_smul, ← Pi.smul_apply]

variable [TopologicalSpace α]

/-- The pairing of a finite (Borel) measure `μ` with a nonnegative bounded continuous
function is obtained by (Lebesgue) integrating the (test) function against the measure.
This is `finite_measure.test_against_nn`. -/
def testAgainstNn (μ : FiniteMeasure α) (f : α →ᵇ ℝ≥0 ) : ℝ≥0 :=
  (∫⁻ x, f x ∂(μ : Measure α)).toNnreal

theorem _root_.bounded_continuous_function.nnreal.to_ennreal_comp_measurable {α : Type _} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] (f : α →ᵇ ℝ≥0 ) : Measurable fun x => (f x : ℝ≥0∞) :=
  measurable_coe_nnreal_ennreal.comp f.Continuous.Measurable

theorem _root_.measure_theory.lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : Measure α) [IsFiniteMeasure μ]
    (f : α →ᵇ ℝ≥0 ) : (∫⁻ x, f x ∂μ) < ∞ := by
  apply IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
  use nndist f 0
  intro x
  have key := BoundedContinuousFunction.Nnreal.upper_bound f x
  rw [Ennreal.coe_le_coe]
  have eq : nndist f 0 = ⟨dist f 0, dist_nonneg⟩ := by
    ext
    simp only [← Real.coe_to_nnreal', ← max_eq_left_iff, ← Subtype.coe_mk, ← coe_nndist]
  rwa [Eq] at key

@[simp]
theorem test_against_nn_coe_eq {μ : FiniteMeasure α} {f : α →ᵇ ℝ≥0 } :
    (μ.testAgainstNn f : ℝ≥0∞) = ∫⁻ x, f x ∂(μ : Measure α) :=
  Ennreal.coe_to_nnreal (lintegral_lt_top_of_bounded_continuous_to_nnreal _ f).Ne

theorem test_against_nn_const (μ : FiniteMeasure α) (c : ℝ≥0 ) :
    μ.testAgainstNn (BoundedContinuousFunction.const α c) = c * μ.mass := by
  simp [Ennreal.coe_eq_coe]

theorem test_against_nn_mono (μ : FiniteMeasure α) {f g : α →ᵇ ℝ≥0 } (f_le_g : (f : α → ℝ≥0 ) ≤ g) :
    μ.testAgainstNn f ≤ μ.testAgainstNn g := by
  simp only [Ennreal.coe_le_coe, ← test_against_nn_coe_eq]
  apply lintegral_mono
  exact fun x => Ennreal.coe_mono (f_le_g x)

@[simp]
theorem Zero.test_against_nn_apply (f : α →ᵇ ℝ≥0 ) : (0 : FiniteMeasure α).testAgainstNn f = 0 := by
  simp only [← test_against_nn, ← coe_zero, ← lintegral_zero_measure, ← Ennreal.zero_to_nnreal]

theorem Zero.test_against_nn : (0 : FiniteMeasure α).testAgainstNn = 0 := by
  funext
  simp only [← zero.test_against_nn_apply, ← Pi.zero_apply]

@[simp]
theorem smul_test_against_nn_apply (c : ℝ≥0 ) (μ : FiniteMeasure α) (f : α →ᵇ ℝ≥0 ) :
    (c • μ).testAgainstNn f = c • μ.testAgainstNn f := by
  simp only [← test_against_nn, ← coe_smul, ← smul_eq_mul ℝ≥0 , Ennreal.smul_to_nnreal]
  congr
  rw
    [show c • (μ : Measureₓ α) = (c : ℝ≥0∞) • (μ : Measureₓ α) by
      rfl,
    lintegral_smul_measure]
  rfl

variable [OpensMeasurableSpace α]

theorem test_against_nn_add (μ : FiniteMeasure α) (f₁ f₂ : α →ᵇ ℝ≥0 ) :
    μ.testAgainstNn (f₁ + f₂) = μ.testAgainstNn f₁ + μ.testAgainstNn f₂ := by
  simp only [Ennreal.coe_eq_coe, ← BoundedContinuousFunction.coe_add, ← Ennreal.coe_add, ← Pi.add_apply, ←
    test_against_nn_coe_eq]
  exact lintegral_add_left (BoundedContinuousFunction.Nnreal.to_ennreal_comp_measurable _) _

theorem test_against_nn_smul [IsScalarTower R ℝ≥0 ℝ≥0 ] [PseudoMetricSpace R] [Zero R] [HasBoundedSmul R ℝ≥0 ]
    (μ : FiniteMeasure α) (c : R) (f : α →ᵇ ℝ≥0 ) : μ.testAgainstNn (c • f) = c • μ.testAgainstNn f := by
  simp only [Ennreal.coe_eq_coe, ← BoundedContinuousFunction.coe_smul, ← test_against_nn_coe_eq, ← Ennreal.coe_smul]
  simp_rw [← smul_one_smul ℝ≥0∞ c (f _ : ℝ≥0∞), ← smul_one_smul ℝ≥0∞ c (lintegral _ _ : ℝ≥0∞), smul_eq_mul]
  exact
    @lintegral_const_mul _ _ (μ : Measureₓ α) (c • 1) _ (BoundedContinuousFunction.Nnreal.to_ennreal_comp_measurable f)

theorem test_against_nn_lipschitz_estimate (μ : FiniteMeasure α) (f g : α →ᵇ ℝ≥0 ) :
    μ.testAgainstNn f ≤ μ.testAgainstNn g + nndist f g * μ.mass := by
  simp only [μ.test_against_nn_const (nndist f g), test_against_nn_add, Ennreal.coe_le_coe, ←
    BoundedContinuousFunction.coe_add, ← const_apply, ← Ennreal.coe_add, ← Pi.add_apply, ← coe_nnreal_ennreal_nndist, ←
    test_against_nn_coe_eq]
  apply lintegral_mono
  have le_dist : ∀ x, dist (f x) (g x) ≤ nndist f g := BoundedContinuousFunction.dist_coe_le_dist
  intro x
  have le' : f x ≤ g x + nndist f g := by
    apply (Nnreal.le_add_nndist (f x) (g x)).trans
    rw [add_le_add_iff_left]
    exact dist_le_coe.mp (le_dist x)
  have le : (f x : ℝ≥0∞) ≤ (g x : ℝ≥0∞) + nndist f g := by
    rw [← Ennreal.coe_add]
    exact Ennreal.coe_mono le'
  rwa [coe_nnreal_ennreal_nndist] at le

theorem test_against_nn_lipschitz (μ : FiniteMeasure α) : LipschitzWith μ.mass fun f : α →ᵇ ℝ≥0 => μ.testAgainstNn f :=
  by
  rw [lipschitz_with_iff_dist_le_mul]
  intro f₁ f₂
  suffices abs (μ.test_against_nn f₁ - μ.test_against_nn f₂ : ℝ) ≤ μ.mass * dist f₁ f₂ by
    rwa [Nnreal.dist_eq]
  apply abs_le.mpr
  constructor
  · have key' := μ.test_against_nn_lipschitz_estimate f₂ f₁
    rw [mul_comm] at key'
    suffices ↑(μ.test_against_nn f₂) ≤ ↑(μ.test_against_nn f₁) + ↑μ.mass * dist f₁ f₂ by
      linarith
    have key := Nnreal.coe_mono key'
    rwa [Nnreal.coe_add, Nnreal.coe_mul, nndist_comm] at key
    
  · have key' := μ.test_against_nn_lipschitz_estimate f₁ f₂
    rw [mul_comm] at key'
    suffices ↑(μ.test_against_nn f₁) ≤ ↑(μ.test_against_nn f₂) + ↑μ.mass * dist f₁ f₂ by
      linarith
    have key := Nnreal.coe_mono key'
    rwa [Nnreal.coe_add, Nnreal.coe_mul] at key
    

/-- Finite measures yield elements of the `weak_dual` of bounded continuous nonnegative
functions via `finite_measure.test_against_nn`, i.e., integration. -/
def toWeakDualBcnn (μ : FiniteMeasure α) : WeakDual ℝ≥0 (α →ᵇ ℝ≥0 ) where
  toFun := fun f => μ.testAgainstNn f
  map_add' := test_against_nn_add μ
  map_smul' := test_against_nn_smul μ
  cont := μ.test_against_nn_lipschitz.Continuous

@[simp]
theorem coe_to_weak_dual_bcnn (μ : FiniteMeasure α) : ⇑μ.toWeakDualBcnn = μ.testAgainstNn :=
  rfl

@[simp]
theorem to_weak_dual_bcnn_apply (μ : FiniteMeasure α) (f : α →ᵇ ℝ≥0 ) :
    μ.toWeakDualBcnn f = (∫⁻ x, f x ∂(μ : Measure α)).toNnreal :=
  rfl

/-- The topology of weak convergence on `finite_measures α` is inherited (induced) from the weak-*
topology on `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)` via the function `finite_measures.to_weak_dual_bcnn`. -/
instance : TopologicalSpace (FiniteMeasure α) :=
  TopologicalSpace.induced toWeakDualBcnn inferInstance

theorem to_weak_dual_bcnn_continuous : Continuous (@toWeakDualBcnn α _ _ _) :=
  continuous_induced_dom

/- Integration of (nonnegative bounded continuous) test functions against finite Borel measures
depends continuously on the measure. -/
theorem continuous_test_against_nn_eval (f : α →ᵇ ℝ≥0 ) : Continuous fun μ : FiniteMeasure α => μ.testAgainstNn f :=
  (by
    apply (WeakBilin.eval_continuous _ _).comp to_weak_dual_bcnn_continuous :
    Continuous ((fun φ : WeakDual ℝ≥0 (α →ᵇ ℝ≥0 ) => φ f) ∘ to_weak_dual_bcnn))

theorem tendsto_iff_weak_star_tendsto {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure α} {μ : FiniteMeasure α} :
    Tendsto μs F (𝓝 μ) ↔ Tendsto (fun i => (μs i).toWeakDualBcnn) F (𝓝 μ.toWeakDualBcnn) :=
  Inducing.tendsto_nhds_iff ⟨rfl⟩

theorem tendsto_iff_forall_test_against_nn_tendsto {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure α}
    {μ : FiniteMeasure α} :
    Tendsto μs F (𝓝 μ) ↔ ∀ f : α →ᵇ ℝ≥0 , Tendsto (fun i => (μs i).toWeakDualBcnn f) F (𝓝 (μ.toWeakDualBcnn f)) := by
  rw [tendsto_iff_weak_star_tendsto, tendsto_iff_forall_eval_tendsto_top_dual_pairing]
  rfl

/-- A characterization of weak convergence in terms of integrals of bounded continuous
nonnegative functions. -/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure α}
    {μ : FiniteMeasure α} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : α →ᵇ ℝ≥0 , Tendsto (fun i => ∫⁻ x, f x ∂(μs i : Measure α)) F (𝓝 (∫⁻ x, f x ∂(μ : Measure α))) :=
  by
  rw [tendsto_iff_forall_test_against_nn_tendsto]
  simp_rw [to_weak_dual_bcnn_apply _ _, ← test_against_nn_coe_eq, Ennreal.tendsto_coe, Ennreal.to_nnreal_coe]

end FiniteMeasure

-- section
section FiniteMeasureBoundedConvergence

/-! ### Bounded convergence results for finite measures

This section is about bounded convergence theorems for finite measures.
-/


variable {α : Type _} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]

/-- A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant and tend to a
limit, then their integrals against the finite measure tend to the integral of the limit.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere;
 * integration is `lintegral`, i.e., the functions and their integrals are `ℝ≥0∞`-valued.
-/
theorem tendsto_lintegral_nn_filter_of_le_const {ι : Type _} {L : Filter ι} [L.IsCountablyGenerated] (μ : Measure α)
    [IsFiniteMeasure μ] {fs : ι → α →ᵇ ℝ≥0 } {c : ℝ≥0 } (fs_le_const : ∀ᶠ i in L, ∀ᵐ a : α ∂(μ : Measure α), fs i a ≤ c)
    {f : α → ℝ≥0 } (fs_lim : ∀ᵐ a : α ∂(μ : Measure α), Tendsto (fun i => fs i a) L (𝓝 (f a))) :
    Tendsto (fun i => ∫⁻ a, fs i a ∂μ) L (𝓝 (∫⁻ a, f a ∂μ)) := by
  simpa only using
    tendsto_lintegral_filter_of_dominated_convergence (fun _ => c)
      (eventually_of_forall fun i => (ennreal.continuous_coe.comp (fs i).Continuous).Measurable) _
      (@lintegral_const_lt_top _ _ (μ : Measureₓ α) _ _ (@Ennreal.coe_ne_top c)).Ne _
  · simpa only [← Ennreal.coe_le_coe] using fs_le_const
    
  · simpa only [← Ennreal.tendsto_coe] using fs_lim
    

/-- A bounded convergence theorem for a finite measure:
If a sequence of bounded continuous non-negative functions are uniformly bounded by a constant
and tend pointwise to a limit, then their integrals (`lintegral`) against the finite measure tend
to the integral of the limit.

A related result with more general assumptions is `tendsto_lintegral_nn_filter_of_le_const`.
-/
theorem tendsto_lintegral_nn_of_le_const (μ : FiniteMeasure α) {fs : ℕ → α →ᵇ ℝ≥0 } {c : ℝ≥0 }
    (fs_le_const : ∀ n a, fs n a ≤ c) {f : α → ℝ≥0 } (fs_lim : ∀ a, Tendsto (fun n => fs n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, fs n a ∂(μ : Measure α)) atTop (𝓝 (∫⁻ a, f a ∂(μ : Measure α))) :=
  tendsto_lintegral_nn_filter_of_le_const μ (eventually_of_forall fun n => eventually_of_forall (fs_le_const n))
    (eventually_of_forall fs_lim)

/-- A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant and tend to a
limit, then their integrals against the finite measure tend to the integral of the limit.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere;
 * integration is the pairing against non-negative continuous test functions (`test_against_nn`).

A related result using `lintegral` for integration is `tendsto_lintegral_nn_filter_of_le_const`.
-/
theorem tendsto_test_against_nn_filter_of_le_const {ι : Type _} {L : Filter ι} [L.IsCountablyGenerated]
    {μ : FiniteMeasure α} {fs : ι → α →ᵇ ℝ≥0 } {c : ℝ≥0 }
    (fs_le_const : ∀ᶠ i in L, ∀ᵐ a : α ∂(μ : Measure α), fs i a ≤ c) {f : α →ᵇ ℝ≥0 }
    (fs_lim : ∀ᵐ a : α ∂(μ : Measure α), Tendsto (fun i => fs i a) L (𝓝 (f a))) :
    Tendsto (fun i => μ.testAgainstNn (fs i)) L (𝓝 (μ.testAgainstNn f)) := by
  apply (Ennreal.tendsto_to_nnreal (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : Measureₓ α) f).Ne).comp
  exact tendsto_lintegral_nn_filter_of_le_const μ fs_le_const fs_lim

/-- A bounded convergence theorem for a finite measure:
If a sequence of bounded continuous non-negative functions are uniformly bounded by a constant
and tend pointwise to a limit, then their integrals (`test_against_nn`) against the finite measure
tend to the integral of the limit.

Related results:
 * `tendsto_test_against_nn_filter_of_le_const`: more general assumptions
 * `tendsto_lintegral_nn_of_le_const`: using `lintegral` for integration.
-/
theorem tendsto_test_against_nn_of_le_const {μ : FiniteMeasure α} {fs : ℕ → α →ᵇ ℝ≥0 } {c : ℝ≥0 }
    (fs_le_const : ∀ n a, fs n a ≤ c) {f : α →ᵇ ℝ≥0 } (fs_lim : ∀ a, Tendsto (fun n => fs n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => μ.testAgainstNn (fs n)) atTop (𝓝 (μ.testAgainstNn f)) :=
  tendsto_test_against_nn_filter_of_le_const (eventually_of_forall fun n => eventually_of_forall (fs_le_const n))
    (eventually_of_forall fs_lim)

end FiniteMeasureBoundedConvergence

-- section
section FiniteMeasureConvergenceByBoundedContinuousFunctions

/-! ### Weak convergence of finite measures with bounded continuous real-valued functions

In this section we characterize the weak convergence of finite measures by the usual (defining)
condition that the integrals of all bounded continuous real-valued functions converge.
-/


variable {α : Type _} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]

theorem integrable_of_bounded_continuous_to_nnreal (μ : Measure α) [IsFiniteMeasure μ] (f : α →ᵇ ℝ≥0 ) :
    Integrable ((coe : ℝ≥0 → ℝ) ∘ ⇑f) μ := by
  refine' ⟨(nnreal.continuous_coe.comp f.continuous).Measurable.AeStronglyMeasurable, _⟩
  simp only [← has_finite_integral, ← Nnreal.nnnorm_eq]
  exact lintegral_lt_top_of_bounded_continuous_to_nnreal _ f

theorem integrable_of_bounded_continuous_to_real (μ : Measure α) [IsFiniteMeasure μ] (f : α →ᵇ ℝ) : Integrable (⇑f) μ :=
  by
  refine' ⟨f.continuous.measurable.ae_strongly_measurable, _⟩
  have aux : (coe : ℝ≥0 → ℝ) ∘ ⇑f.nnnorm = fun x => ∥f x∥ := by
    ext x
    simp only [← Function.comp_app, ← BoundedContinuousFunction.nnnorm_coe_fun_eq, ← coe_nnnorm]
  apply (has_finite_integral_iff_norm ⇑f).mpr
  rw [← of_real_integral_eq_lintegral_of_real]
  · exact Ennreal.of_real_lt_top
    
  · exact aux ▸ integrable_of_bounded_continuous_to_nnreal μ f.nnnorm
    
  · exact eventually_of_forall fun x => norm_nonneg (f x)
    

theorem _root_.bounded_continuous_function.integral_eq_integral_nnreal_part_sub (μ : Measure α) [IsFiniteMeasure μ]
    (f : α →ᵇ ℝ) : (∫ x, f x ∂μ) = (∫ x, f.nnrealPart x ∂μ) - ∫ x, (-f).nnrealPart x ∂μ := by
  simp only [← f.self_eq_nnreal_part_sub_nnreal_part_neg, ← Pi.sub_apply, ← integral_sub, ←
    integrable_of_bounded_continuous_to_nnreal]

theorem lintegral_lt_top_of_bounded_continuous_to_real {α : Type _} [MeasurableSpace α] [TopologicalSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α →ᵇ ℝ) : (∫⁻ x, Ennreal.ofReal (f x) ∂μ) < ∞ :=
  lintegral_lt_top_of_bounded_continuous_to_nnreal _ f.nnrealPart

theorem tendsto_of_forall_integral_tendsto {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure α} {μ : FiniteMeasure α}
    (h : ∀ f : α →ᵇ ℝ, Tendsto (fun i => ∫ x, f x ∂(μs i : Measure α)) F (𝓝 (∫ x, f x ∂(μ : Measure α)))) :
    Tendsto μs F (𝓝 μ) := by
  apply (@tendsto_iff_forall_lintegral_tendsto α _ _ _ γ F μs μ).mpr
  intro f
  have key :=
    @Ennreal.tendsto_to_real_iff _ F _
      (fun i => (lintegral_lt_top_of_bounded_continuous_to_nnreal (μs i : Measureₓ α) f).Ne) _
      (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : Measureₓ α) f).Ne
  simp only [← Ennreal.of_real_coe_nnreal] at key
  apply key.mp
  have lip : LipschitzWith 1 (coe : ℝ≥0 → ℝ) := isometry_subtype_coe.lipschitz
  set f₀ := BoundedContinuousFunction.comp _ lip f with def_f₀
  have f₀_eq : ⇑f₀ = (coe : ℝ≥0 → ℝ) ∘ ⇑f := by
    rfl
  have f₀_nn : 0 ≤ ⇑f₀ := fun _ => by
    simp only [← f₀_eq, ← Pi.zero_apply, ← Nnreal.zero_le_coe]
  have f₀_ae_nn : 0 ≤ᵐ[(μ : Measureₓ α)] ⇑f₀ := eventually_of_forall f₀_nn
  have f₀_ae_nns : ∀ i, 0 ≤ᵐ[(μs i : Measureₓ α)] ⇑f₀ := fun i => eventually_of_forall f₀_nn
  have aux := integral_eq_lintegral_of_nonneg_ae f₀_ae_nn f₀.continuous.measurable.ae_strongly_measurable
  have auxs := fun i => integral_eq_lintegral_of_nonneg_ae (f₀_ae_nns i) f₀.continuous.measurable.ae_strongly_measurable
  simp only [← f₀_eq, ← Ennreal.of_real_coe_nnreal] at aux auxs
  simpa only [aux, auxs] using h f₀

theorem _root_.bounded_continuous_function.nnreal.to_real_lintegral_eq_integral (f : α →ᵇ ℝ≥0 ) (μ : Measure α) :
    (∫⁻ x, (f x : ℝ≥0∞) ∂μ).toReal = ∫ x, f x ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae _ (nnreal.continuous_coe.comp f.continuous).Measurable.AeStronglyMeasurable]
  · simp only [← Ennreal.of_real_coe_nnreal]
    
  · apply eventually_of_forall
    simp only [← Pi.zero_apply, ← Nnreal.zero_le_coe, ← implies_true_iff]
    

/-- A characterization of weak convergence in terms of integrals of bounded continuous
real-valued functions. -/
theorem tendsto_iff_forall_integral_tendsto {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure α}
    {μ : FiniteMeasure α} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : α →ᵇ ℝ, Tendsto (fun i => ∫ x, f x ∂(μs i : Measure α)) F (𝓝 (∫ x, f x ∂(μ : Measure α))) :=
  by
  refine' ⟨_, tendsto_of_forall_integral_tendsto⟩
  rw [tendsto_iff_forall_lintegral_tendsto]
  intro h f
  simp_rw [BoundedContinuousFunction.integral_eq_integral_nnreal_part_sub]
  set f_pos := f.nnreal_part with def_f_pos
  set f_neg := (-f).nnrealPart with def_f_neg
  have tends_pos :=
    (Ennreal.tendsto_to_real (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : Measureₓ α) f_pos).Ne).comp
      (h f_pos)
  have tends_neg :=
    (Ennreal.tendsto_to_real (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : Measureₓ α) f_neg).Ne).comp
      (h f_neg)
  have aux :
    ∀ g : α →ᵇ ℝ≥0 ,
      (Ennreal.toReal ∘ fun i : γ => ∫⁻ x : α, ↑(g x) ∂(μs i : Measureₓ α)) = fun i : γ =>
        (∫⁻ x : α, ↑(g x) ∂(μs i : Measureₓ α)).toReal :=
    fun _ => rfl
  simp_rw [aux, BoundedContinuousFunction.Nnreal.to_real_lintegral_eq_integral] at tends_pos tends_neg
  exact tendsto.sub tends_pos tends_neg

end FiniteMeasureConvergenceByBoundedContinuousFunctions

-- section
end FiniteMeasure

-- namespace
section ProbabilityMeasure

/-! ### Probability measures

In this section we define the `Type*` of probability measures on a measurable space `α`, denoted by
`probability_measure α`. TODO: Probability measures form a convex space.

If `α` is moreover a topological space and the sigma algebra on `α` is finer than the Borel sigma
algebra (i.e. `[opens_measurable_space α]`), then `probability_measure α` is equipped with the
topology of weak convergence of measures. Since every probability measure is a finite measure, this
is implemented as the induced topology from the coercion `probability_measure.to_finite_measure`.
-/


/-- Probability measures are defined as the subtype of measures that have the property of being
probability measures (i.e., their total mass is one). -/
def ProbabilityMeasure (α : Type _) [MeasurableSpace α] : Type _ :=
  { μ : Measure α // IsProbabilityMeasure μ }

namespace ProbabilityMeasure

variable {α : Type _} [MeasurableSpace α]

instance [Inhabited α] : Inhabited (ProbabilityMeasure α) :=
  ⟨⟨Measure.dirac default, Measure.dirac.is_probability_measure⟩⟩

/-- A probability measure can be interpreted as a measure. -/
instance : Coe (ProbabilityMeasure α) (MeasureTheory.Measure α) :=
  coeSubtype

instance : CoeFun (ProbabilityMeasure α) fun _ => Set α → ℝ≥0 :=
  ⟨fun μ s => (μ s).toNnreal⟩

instance (μ : ProbabilityMeasure α) : IsProbabilityMeasure (μ : Measure α) :=
  μ.Prop

theorem coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : ProbabilityMeasure α) :
    (ν : Set α → ℝ≥0 ) = fun s => ((ν : Measure α) s).toNnreal :=
  rfl

@[simp]
theorem val_eq_to_measure (ν : ProbabilityMeasure α) : ν.val = (ν : Measure α) :=
  rfl

theorem coe_injective : Function.Injective (coe : ProbabilityMeasure α → Measure α) :=
  Subtype.coe_injective

@[simp]
theorem coe_fn_univ (ν : ProbabilityMeasure α) : ν Univ = 1 :=
  congr_arg Ennreal.toNnreal ν.Prop.measure_univ

/-- A probability measure can be interpreted as a finite measure. -/
def toFiniteMeasure (μ : ProbabilityMeasure α) : FiniteMeasure α :=
  ⟨μ, inferInstance⟩

@[simp]
theorem coe_comp_to_finite_measure_eq_coe (ν : ProbabilityMeasure α) :
    (ν.toFiniteMeasure : Measure α) = (ν : Measure α) :=
  rfl

@[simp]
theorem coe_fn_comp_to_finite_measure_eq_coe_fn (ν : ProbabilityMeasure α) :
    (ν.toFiniteMeasure : Set α → ℝ≥0 ) = (ν : Set α → ℝ≥0 ) :=
  rfl

@[simp]
theorem ennreal_coe_fn_eq_coe_fn_to_measure (ν : ProbabilityMeasure α) (s : Set α) : (ν s : ℝ≥0∞) = (ν : Measure α) s :=
  by
  rw [← coe_fn_comp_to_finite_measure_eq_coe_fn, finite_measure.ennreal_coe_fn_eq_coe_fn_to_measure]
  rfl

@[ext]
theorem extensionality (μ ν : ProbabilityMeasure α) (h : ∀ s : Set α, MeasurableSet s → μ s = ν s) : μ = ν := by
  ext1
  ext1 s s_mble
  simpa [← ennreal_coe_fn_eq_coe_fn_to_measure] using congr_arg (coe : ℝ≥0 → ℝ≥0∞) (h s s_mble)

@[simp]
theorem mass_to_finite_measure (μ : ProbabilityMeasure α) : μ.toFiniteMeasure.mass = 1 :=
  μ.coe_fn_univ

variable [TopologicalSpace α] [OpensMeasurableSpace α]

theorem test_against_nn_lipschitz (μ : ProbabilityMeasure α) :
    LipschitzWith 1 fun f : α →ᵇ ℝ≥0 => μ.toFiniteMeasure.testAgainstNn f :=
  μ.mass_to_finite_measure ▸ μ.toFiniteMeasure.test_against_nn_lipschitz

/-- The topology of weak convergence on `probability_measures α`. This is inherited (induced) from
the weak-*  topology on `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)` via the function
`probability_measures.to_weak_dual_bcnn`. -/
instance : TopologicalSpace (ProbabilityMeasure α) :=
  TopologicalSpace.induced toFiniteMeasure inferInstance

theorem to_finite_measure_continuous : Continuous (toFiniteMeasure : ProbabilityMeasure α → FiniteMeasure α) :=
  continuous_induced_dom

/-- Probability measures yield elements of the `weak_dual` of bounded continuous nonnegative
functions via `finite_measure.test_against_nn`, i.e., integration. -/
def toWeakDualBcnn : ProbabilityMeasure α → WeakDual ℝ≥0 (α →ᵇ ℝ≥0 ) :=
  finite_measure.to_weak_dual_bcnn ∘ to_finite_measure

@[simp]
theorem coe_to_weak_dual_bcnn (μ : ProbabilityMeasure α) : ⇑μ.toWeakDualBcnn = μ.toFiniteMeasure.testAgainstNn :=
  rfl

@[simp]
theorem to_weak_dual_bcnn_apply (μ : ProbabilityMeasure α) (f : α →ᵇ ℝ≥0 ) :
    μ.toWeakDualBcnn f = (∫⁻ x, f x ∂(μ : Measure α)).toNnreal :=
  rfl

theorem to_weak_dual_bcnn_continuous : Continuous fun μ : ProbabilityMeasure α => μ.toWeakDualBcnn :=
  FiniteMeasure.to_weak_dual_bcnn_continuous.comp to_finite_measure_continuous

/- Integration of (nonnegative bounded continuous) test functions against Borel probability
measures depends continuously on the measure. -/
theorem continuous_test_against_nn_eval (f : α →ᵇ ℝ≥0 ) :
    Continuous fun μ : ProbabilityMeasure α => μ.toFiniteMeasure.testAgainstNn f :=
  (FiniteMeasure.continuous_test_against_nn_eval f).comp to_finite_measure_continuous

-- The canonical mapping from probability measures to finite measures is an embedding.
theorem to_finite_measure_embedding (α : Type _) [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] :
    Embedding (toFiniteMeasure : ProbabilityMeasure α → FiniteMeasure α) :=
  { induced := rfl,
    inj := fun μ ν h =>
      Subtype.eq
        (by
          convert congr_arg coe h) }

theorem tendsto_nhds_iff_to_finite_measures_tendsto_nhds {δ : Type _} (F : Filter δ) {μs : δ → ProbabilityMeasure α}
    {μ₀ : ProbabilityMeasure α} : Tendsto μs F (𝓝 μ₀) ↔ Tendsto (to_finite_measure ∘ μs) F (𝓝 μ₀.toFiniteMeasure) :=
  Embedding.tendsto_nhds_iff (to_finite_measure_embedding α)

/-- A characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function converge to the integral of the function
against the limit measure. -/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type _} {F : Filter γ} {μs : γ → ProbabilityMeasure α}
    {μ : ProbabilityMeasure α} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : α →ᵇ ℝ≥0 , Tendsto (fun i => ∫⁻ x, f x ∂(μs i : Measure α)) F (𝓝 (∫⁻ x, f x ∂(μ : Measure α))) :=
  by
  rw [tendsto_nhds_iff_to_finite_measures_tendsto_nhds]
  exact finite_measure.tendsto_iff_forall_lintegral_tendsto

/-- The characterization of weak convergence of probability measures by the usual (defining)
condition that the integrals of every continuous bounded function converge to the integral of the
function against the limit measure. -/
theorem tendsto_iff_forall_integral_tendsto {γ : Type _} {F : Filter γ} {μs : γ → ProbabilityMeasure α}
    {μ : ProbabilityMeasure α} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : α →ᵇ ℝ, Tendsto (fun i => ∫ x, f x ∂(μs i : Measure α)) F (𝓝 (∫ x, f x ∂(μ : Measure α))) :=
  by
  rw [tendsto_nhds_iff_to_finite_measures_tendsto_nhds]
  rw [finite_measure.tendsto_iff_forall_integral_tendsto]
  simp only [← coe_comp_to_finite_measure_eq_coe]

end ProbabilityMeasure

-- namespace
end ProbabilityMeasure

-- section
section ConvergenceImpliesLimsupClosedLe

/-! ### Portmanteau implication: weak convergence implies a limsup condition for closed sets

In this section we prove, under the assumption that the underlying topological space `α` is
pseudo-emetrizable, that the weak convergence of measures on `finite_measure α` implies that for
any closed set `F` in `α` the limsup of the measures of `F` is at most the limit measure of `F`.
This is one implication of the portmanteau theorem characterizing weak convergence of measures.
-/


variable {α : Type _} [MeasurableSpace α]

/-- If bounded continuous functions tend to the indicator of a measurable set and are
uniformly bounded, then their integrals against a finite measure tend to the measure of the set.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere.
-/
theorem measure_of_cont_bdd_of_tendsto_filter_indicator {ι : Type _} {L : Filter ι} [L.IsCountablyGenerated]
    [TopologicalSpace α] [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] {c : ℝ≥0 } {E : Set α}
    (E_mble : MeasurableSet E) (fs : ι → α →ᵇ ℝ≥0 ) (fs_bdd : ∀ᶠ i in L, ∀ᵐ a : α ∂μ, fs i a ≤ c)
    (fs_lim :
      ∀ᵐ a : α ∂μ,
        Tendsto (fun i : ι => (coeFn : (α →ᵇ ℝ≥0 ) → α → ℝ≥0 ) (fs i) a) L (𝓝 (indicatorₓ E (fun x => (1 : ℝ≥0 )) a))) :
    Tendsto (fun n => lintegral μ fun a => fs n a) L (𝓝 (μ E)) := by
  convert finite_measure.tendsto_lintegral_nn_filter_of_le_const μ fs_bdd fs_lim
  have aux : ∀ a, indicator E (fun x => (1 : ℝ≥0∞)) a = ↑(indicator E (fun x => (1 : ℝ≥0 )) a) := fun a => by
    simp only [← Ennreal.coe_indicator, ← Ennreal.coe_one]
  simp_rw [← aux, lintegral_indicator _ E_mble]
  simp only [← lintegral_one, ← measure.restrict_apply, ← MeasurableSet.univ, ← univ_inter]

/-- If a sequence of bounded continuous functions tends to the indicator of a measurable set and
the functions are uniformly bounded, then their integrals against a finite measure tend to the
measure of the set.

A similar result with more general assumptions is `measure_of_cont_bdd_of_tendsto_filter_indicator`.
-/
theorem measure_of_cont_bdd_of_tendsto_indicator [TopologicalSpace α] [OpensMeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {c : ℝ≥0 } {E : Set α} (E_mble : MeasurableSet E) (fs : ℕ → α →ᵇ ℝ≥0 )
    (fs_bdd : ∀ n a, fs n a ≤ c)
    (fs_lim :
      Tendsto (fun n : ℕ => (coeFn : (α →ᵇ ℝ≥0 ) → α → ℝ≥0 ) (fs n)) atTop (𝓝 (indicatorₓ E fun x => (1 : ℝ≥0 )))) :
    Tendsto (fun n => lintegral μ fun a => fs n a) atTop (𝓝 (μ E)) := by
  have fs_lim' : ∀ a, tendsto (fun n : ℕ => (fs n a : ℝ≥0 )) at_top (𝓝 (indicator E (fun x => (1 : ℝ≥0 )) a)) := by
    rw [tendsto_pi_nhds] at fs_lim
    exact fun a => fs_lim a
  apply
    measure_of_cont_bdd_of_tendsto_filter_indicator μ E_mble fs
      (eventually_of_forall fun n => eventually_of_forall (fs_bdd n)) (eventually_of_forall fs_lim')

/-- The integrals of thickened indicators of a closed set against a finite measure tend to the
measure of the closed set if the thickening radii tend to zero.
-/
theorem tendsto_lintegral_thickened_indicator_of_is_closed {α : Type _} [MeasurableSpace α] [PseudoEmetricSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] {F : Set α} (F_closed : IsClosed F) {δs : ℕ → ℝ}
    (δs_pos : ∀ n, 0 < δs n) (δs_lim : Tendsto δs atTop (𝓝 0)) :
    Tendsto (fun n => lintegral μ fun a => (thickenedIndicator (δs_pos n) F a : ℝ≥0∞)) atTop (𝓝 (μ F)) := by
  apply
    measure_of_cont_bdd_of_tendsto_indicator μ F_closed.measurable_set (fun n => thickenedIndicator (δs_pos n) F)
      fun n a => thickened_indicator_le_one (δs_pos n) F a
  have key := thickened_indicator_tendsto_indicator_closure δs_pos δs_lim F
  rwa [F_closed.closure_eq] at key

/-- One implication of the portmanteau theorem:
Weak convergence of finite measures implies that the limsup of the measures of any closed set is
at most the measure of the closed set under the limit measure.
-/
theorem FiniteMeasure.limsup_measure_closed_le_of_tendsto {α ι : Type _} {L : Filter ι} [MeasurableSpace α]
    [PseudoEmetricSpace α] [OpensMeasurableSpace α] {μ : FiniteMeasure α} {μs : ι → FiniteMeasure α}
    (μs_lim : Tendsto μs L (𝓝 μ)) {F : Set α} (F_closed : IsClosed F) :
    (L.limsup fun i => (μs i : Measure α) F) ≤ (μ : Measure α) F := by
  by_cases' L = ⊥
  · simp only [← h, ← limsup, ← Filter.map_bot, ← Limsup_bot, ← Ennreal.bot_eq_zero, ← zero_le]
    
  apply Ennreal.le_of_forall_pos_le_add
  intro ε ε_pos μ_F_finite
  set δs := fun n : ℕ => (1 : ℝ) / (n + 1) with def_δs
  have δs_pos : ∀ n, 0 < δs n := fun n => Nat.one_div_pos_of_nat
  have δs_lim : tendsto δs at_top (𝓝 0) := tendsto_one_div_add_at_top_nhds_0_nat
  have key₁ := tendsto_lintegral_thickened_indicator_of_is_closed (μ : Measureₓ α) F_closed δs_pos δs_lim
  have room₁ : (μ : Measureₓ α) F < (μ : Measureₓ α) F + ε / 2 := by
    apply
      Ennreal.lt_add_right (measure_lt_top (μ : Measureₓ α) F).Ne
        (ennreal.div_pos_iff.mpr ⟨(ennreal.coe_pos.mpr ε_pos).Ne.symm, Ennreal.two_ne_top⟩).Ne.symm
  rcases eventually_at_top.mp (eventually_lt_of_tendsto_lt room₁ key₁) with ⟨M, hM⟩
  have key₂ := finite_measure.tendsto_iff_forall_lintegral_tendsto.mp μs_lim (thickenedIndicator (δs_pos M) F)
  have room₂ :
    (lintegral (μ : Measureₓ α) fun a => thickenedIndicator (δs_pos M) F a) <
      (lintegral (μ : Measureₓ α) fun a => thickenedIndicator (δs_pos M) F a) + ε / 2 :=
    by
    apply
      Ennreal.lt_add_right (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : Measureₓ α) _).Ne
        (ennreal.div_pos_iff.mpr ⟨(ennreal.coe_pos.mpr ε_pos).Ne.symm, Ennreal.two_ne_top⟩).Ne.symm
  have ev_near := eventually.mono (eventually_lt_of_tendsto_lt room₂ key₂) fun n => le_of_ltₓ
  have aux := fun n =>
    le_transₓ (measure_le_lintegral_thickened_indicator (μs n : Measureₓ α) F_closed.measurable_set (δs_pos M))
  have ev_near' := eventually.mono ev_near aux
  apply (Filter.limsup_le_limsup ev_near').trans
  have : ne_bot L := ⟨h⟩
  rw [limsup_const]
  apply le_transₓ (add_le_add (hM M rfl.le).le (le_reflₓ (ε / 2 : ℝ≥0∞)))
  simp only [← add_assocₓ, ← Ennreal.add_halves, ← le_reflₓ]

end ConvergenceImpliesLimsupClosedLe

--section
end MeasureTheory

--namespace

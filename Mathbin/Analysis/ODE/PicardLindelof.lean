/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Analysis.SpecialFunctions.Integrals
import Mathbin.Topology.MetricSpace.Contracting

/-!
# Picard-Lindelöf (Cauchy-Lipschitz) Theorem

In this file we prove that an ordinary differential equation $\dot x=v(t, x)$ such that $v$ is
Lipschitz continuous in $x$ and continuous in $t$ has a local solution, see
`exists_forall_deriv_within_Icc_eq_of_lipschitz_of_continuous`.

## Implementation notes

In order to split the proof into small lemmas, we introduce a structure `picard_lindelof` that holds
all assumptions of the main theorem. This structure and lemmas in the `picard_lindelof` namespace
should be treated as private implementation details.

We only prove existence of a solution in this file. For uniqueness see `ODE_solution_unique` and
related theorems in `analysis.ODE.gronwall`.

## Tags

differential equation
-/


open Filter Function Set Metric TopologicalSpace intervalIntegral MeasureTheory

open MeasureTheory.MeasureSpace (volume)

open Filter TopologicalSpace Nnreal Ennreal Nat Interval

noncomputable section

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E]

/-- This structure holds arguments of the Picard-Lipschitz (Cauchy-Lipschitz) theorem. Unless you
want to use one of the auxiliary lemmas, use
`exists_forall_deriv_within_Icc_eq_of_lipschitz_of_continuous` instead of using this structure. -/
structure PicardLindelof (E : Type _) [NormedGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E → E
  (tMin tMax : ℝ)
  t₀ : Icc t_min t_max
  x₀ : E
  (c r l : ℝ≥0 )
  lipschitz' : ∀, ∀ t ∈ Icc t_min t_max, ∀, LipschitzOnWith L (to_fun t) (ClosedBall x₀ R)
  cont : ∀, ∀ x ∈ ClosedBall x₀ R, ∀, ContinuousOn (fun t => to_fun t x) (Icc t_min t_max)
  norm_le' : ∀, ∀ t ∈ Icc t_min t_max, ∀, ∀ x ∈ ClosedBall x₀ R, ∀, ∥to_fun t x∥ ≤ C
  C_mul_le_R : (C : ℝ) * max (t_max - t₀) (t₀ - t_min) ≤ R

namespace PicardLindelof

variable (v : PicardLindelof E)

instance : CoeFun (PicardLindelof E) fun _ => ℝ → E → E :=
  ⟨toFun⟩

instance : Inhabited (PicardLindelof E) :=
  ⟨⟨0, 0, 0, ⟨0, le_rfl, le_rfl⟩, 0, 0, 0, 0, fun t ht => (LipschitzWith.const 0).LipschitzOnWith _, fun _ _ => by
      simpa only [← Pi.zero_apply] using continuous_on_const, fun t ht x hx => norm_zero.le, (zero_mul _).le⟩⟩

theorem t_min_le_t_max : v.tMin ≤ v.tMax :=
  v.t₀.2.1.trans v.t₀.2.2

protected theorem nonempty_Icc : (Icc v.tMin v.tMax).Nonempty :=
  nonempty_Icc.2 v.t_min_le_t_max

protected theorem lipschitz_on_with {t} (ht : t ∈ Icc v.tMin v.tMax) :
    LipschitzOnWith v.l (v t) (ClosedBall v.x₀ v.r) :=
  v.lipschitz' t ht

protected theorem continuous_on : ContinuousOn (uncurry v) (Icc v.tMin v.tMax ×ˢ ClosedBall v.x₀ v.r) :=
  have : ContinuousOn (uncurry (flip v)) (ClosedBall v.x₀ v.r ×ˢ Icc v.tMin v.tMax) :=
    continuous_on_prod_of_continuous_on_lipschitz_on _ v.l v.cont v.lipschitz'
  this.comp continuous_swap.ContinuousOn preimage_swap_prod.symm.Subset

theorem norm_le {t : ℝ} (ht : t ∈ Icc v.tMin v.tMax) {x : E} (hx : x ∈ ClosedBall v.x₀ v.r) : ∥v t x∥ ≤ v.c :=
  v.norm_le' _ ht _ hx

/-- The maximum of distances from `t₀` to the endpoints of `[t_min, t_max]`. -/
def tDist : ℝ :=
  max (v.tMax - v.t₀) (v.t₀ - v.tMin)

theorem t_dist_nonneg : 0 ≤ v.tDist :=
  le_max_iff.2 <| Or.inl <| sub_nonneg.2 v.t₀.2.2

theorem dist_t₀_le (t : Icc v.tMin v.tMax) : dist t v.t₀ ≤ v.tDist := by
  rw [Subtype.dist_eq, Real.dist_eq]
  cases' le_totalₓ t v.t₀ with ht ht
  · rw [abs_of_nonpos (sub_nonpos.2 <| Subtype.coe_le_coe.2 ht), neg_sub]
    exact (sub_le_sub_left t.2.1 _).trans (le_max_rightₓ _ _)
    
  · rw [abs_of_nonneg (sub_nonneg.2 <| Subtype.coe_le_coe.2 ht)]
    exact (sub_le_sub_right t.2.2 _).trans (le_max_leftₓ _ _)
    

/-- Projection $ℝ → [t_{\min}, t_{\max}]$ sending $(-∞, t_{\min}]$ to $t_{\min}$ and $[t_{\max}, ∞)$
to $t_{\max}$. -/
def proj : ℝ → Icc v.tMin v.tMax :=
  projIcc v.tMin v.tMax v.t_min_le_t_max

theorem proj_coe (t : Icc v.tMin v.tMax) : v.proj t = t :=
  proj_Icc_coe _ _

theorem proj_of_mem {t : ℝ} (ht : t ∈ Icc v.tMin v.tMax) : ↑(v.proj t) = t := by
  simp only [← proj, ← proj_Icc_of_mem _ ht, ← Subtype.coe_mk]

@[continuity]
theorem continuous_proj : Continuous v.proj :=
  continuous_proj_Icc

/-- The space of curves $γ \colon [t_{\min}, t_{\max}] \to E$ such that $γ(t₀) = x₀$ and $γ$ is
Lipschitz continuous with constant $C$. The map sending $γ$ to
$\mathbf Pγ(t)=x₀ + ∫_{t₀}^{t} v(τ, γ(τ))\,dτ$ is a contracting map on this space, and its fixed
point is a solution of the ODE $\dot x=v(t, x)$. -/
structure FunSpace where
  toFun : Icc v.tMin v.tMax → E
  map_t₀' : to_fun v.t₀ = v.x₀
  lipschitz' : LipschitzWith v.c to_fun

namespace FunSpace

variable {v} (f : FunSpace v)

instance : CoeFun (FunSpace v) fun _ => Icc v.tMin v.tMax → E :=
  ⟨toFun⟩

instance : Inhabited v.FunSpace :=
  ⟨⟨fun _ => v.x₀, rfl, (LipschitzWith.const _).weaken (zero_le _)⟩⟩

protected theorem lipschitz : LipschitzWith v.c f :=
  f.lipschitz'

protected theorem continuous : Continuous f :=
  f.lipschitz.Continuous

/-- Each curve in `picard_lindelof.fun_space` is continuous. -/
def toContinuousMap : v.FunSpace ↪ C(Icc v.tMin v.tMax, E) :=
  ⟨fun f => ⟨f, f.Continuous⟩, fun f g h => by
    cases f
    cases g
    simpa using h⟩

instance : MetricSpace v.FunSpace :=
  MetricSpace.induced toContinuousMap toContinuousMap.Injective inferInstance

theorem uniform_inducing_to_continuous_map : UniformInducing (@toContinuousMap _ _ _ v) :=
  ⟨rfl⟩

theorem range_to_continuous_map :
    Range toContinuousMap = { f : C(Icc v.tMin v.tMax, E) | f v.t₀ = v.x₀ ∧ LipschitzWith v.c f } := by
  ext f
  constructor
  · rintro ⟨⟨f, hf₀, hf_lip⟩, rfl⟩
    exact ⟨hf₀, hf_lip⟩
    
  · rcases f with ⟨f, hf⟩
    rintro ⟨hf₀, hf_lip⟩
    exact ⟨⟨f, hf₀, hf_lip⟩, rfl⟩
    

theorem map_t₀ : f v.t₀ = v.x₀ :=
  f.map_t₀'

protected theorem mem_closed_ball (t : Icc v.tMin v.tMax) : f t ∈ ClosedBall v.x₀ v.r :=
  calc
    dist (f t) v.x₀ = dist (f t) (f.toFun v.t₀) := by
      rw [f.map_t₀']
    _ ≤ v.c * dist t v.t₀ := f.lipschitz.dist_le_mul _ _
    _ ≤ v.c * v.tDist := mul_le_mul_of_nonneg_left (v.dist_t₀_le _) v.c.2
    _ ≤ v.r := v.C_mul_le_R
    

/-- Given a curve $γ \colon [t_{\min}, t_{\max}] → E$, `v_comp` is the function
$F(t)=v(π t, γ(π t))$, where `π` is the projection $ℝ → [t_{\min}, t_{\max}]$. The integral of this
function is the image of `γ` under the contracting map we are going to define below. -/
def vComp (t : ℝ) : E :=
  v (v.proj t) (f (v.proj t))

theorem v_comp_apply_coe (t : Icc v.tMin v.tMax) : f.vComp t = v t (f t) := by
  simp only [← v_comp, ← proj_coe]

theorem continuous_v_comp : Continuous f.vComp := by
  have := (continuous_subtype_coe.prod_mk f.continuous).comp v.continuous_proj
  refine' ContinuousOn.comp_continuous v.continuous_on this fun x => _
  exact ⟨(v.proj x).2, f.mem_closed_ball _⟩

theorem norm_v_comp_le (t : ℝ) : ∥f.vComp t∥ ≤ v.c :=
  v.norm_le (v.proj t).2 <| f.mem_closed_ball _

theorem dist_apply_le_dist (f₁ f₂ : FunSpace v) (t : Icc v.tMin v.tMax) : dist (f₁ t) (f₂ t) ≤ dist f₁ f₂ :=
  @ContinuousMap.dist_apply_le_dist _ _ _ _ _ f₁.toContinuousMap f₂.toContinuousMap _

theorem dist_le_of_forall {f₁ f₂ : FunSpace v} {d : ℝ} (h : ∀ t, dist (f₁ t) (f₂ t) ≤ d) : dist f₁ f₂ ≤ d :=
  (@ContinuousMap.dist_le_iff_of_nonempty _ _ _ _ _ f₁.toContinuousMap f₂.toContinuousMap _ v.nonempty_Icc.to_subtype).2
    h

instance [CompleteSpace E] : CompleteSpace v.FunSpace := by
  refine' (complete_space_iff_is_complete_range uniform_inducing_to_continuous_map).2 (IsClosed.is_complete _)
  rw [range_to_continuous_map, set_of_and]
  refine' (is_closed_eq (ContinuousMap.continuous_eval_const _) continuous_const).inter _
  have : IsClosed { f : Icc v.t_min v.t_max → E | LipschitzWith v.C f } := is_closed_set_of_lipschitz_with v.C
  exact this.preimage ContinuousMap.continuous_coe

theorem interval_integrable_v_comp (t₁ t₂ : ℝ) : IntervalIntegrable f.vComp volume t₁ t₂ :=
  f.continuous_v_comp.IntervalIntegrable _ _

variable [CompleteSpace E]

/-- The Picard-Lindelöf operator. This is a contracting map on `picard_lindelof.fun_space v` such
that the fixed point of this map is the solution of the corresponding ODE.

More precisely, some iteration of this map is a contracting map. -/
def next (f : FunSpace v) : FunSpace v where
  toFun := fun t => v.x₀ + ∫ τ : ℝ in v.t₀..t, f.vComp τ
  map_t₀' := by
    rw [integral_same, add_zeroₓ]
  lipschitz' :=
    LipschitzWith.of_dist_le_mul fun t₁ t₂ => by
      rw [dist_add_left, dist_eq_norm,
        integral_interval_sub_left (f.interval_integrable_v_comp _ _) (f.interval_integrable_v_comp _ _)]
      exact norm_integral_le_of_norm_le_const fun t ht => f.norm_v_comp_le _

theorem next_apply (t : Icc v.tMin v.tMax) : f.next t = v.x₀ + ∫ τ : ℝ in v.t₀..t, f.vComp τ :=
  rfl

theorem has_deriv_within_at_next (t : Icc v.tMin v.tMax) :
    HasDerivWithinAt (f.next ∘ v.proj) (v t (f t)) (Icc v.tMin v.tMax) t := by
  have : Fact ((t : ℝ) ∈ Icc v.t_min v.t_max) := ⟨t.2⟩
  simp only [← (· ∘ ·), ← next_apply]
  refine' HasDerivWithinAt.const_add _ _
  have : HasDerivWithinAt (fun t : ℝ => ∫ τ in v.t₀..t, f.v_comp τ) (f.v_comp t) (Icc v.t_min v.t_max) t :=
    integral_has_deriv_within_at_right (f.interval_integrable_v_comp _ _)
      (f.continuous_v_comp.strongly_measurable_at_filter _ _) f.continuous_v_comp.continuous_within_at
  rw [v_comp_apply_coe] at this
  refine' this.congr_of_eventually_eq_of_mem _ t.coe_prop
  filter_upwards [self_mem_nhds_within] with _ ht'
  rw [v.proj_of_mem ht']

theorem dist_next_apply_le_of_le {f₁ f₂ : FunSpace v} {n : ℕ} {d : ℝ}
    (h : ∀ t, dist (f₁ t) (f₂ t) ≤ (v.l * abs (t - v.t₀)) ^ n / n ! * d) (t : Icc v.tMin v.tMax) :
    dist (next f₁ t) (next f₂ t) ≤ (v.l * abs (t - v.t₀)) ^ (n + 1) / (n + 1)! * d := by
  simp only [← dist_eq_norm, ← next_apply, ← add_sub_add_left_eq_sub,
    intervalIntegral.integral_sub (interval_integrable_v_comp _ _ _) (interval_integrable_v_comp _ _ _), ←
    norm_integral_eq_norm_integral_Ioc] at *
  calc
    ∥∫ τ in Ι (v.t₀ : ℝ) t, f₁.v_comp τ - f₂.v_comp τ∥ ≤
        ∫ τ in Ι (v.t₀ : ℝ) t, v.L * ((v.L * abs (τ - v.t₀)) ^ n / n ! * d) :=
      by
      refine' norm_integral_le_of_norm_le (Continuous.integrable_on_interval_oc _) _
      · continuity
        
      · refine' (ae_restrict_mem measurable_set_Ioc).mono fun τ hτ => _
        refine'
          (v.lipschitz_on_with (v.proj τ).2).norm_sub_le_of_le (f₁.mem_closed_ball _) (f₂.mem_closed_ball _)
            ((h _).trans_eq _)
        rw [v.proj_of_mem]
        exact interval_subset_Icc v.t₀.2 t.2 <| Ioc_subset_Icc_self hτ
        _ = (v.L * abs (t - v.t₀)) ^ (n + 1) / (n + 1)! * d :=
      _
  simp_rw [mul_powₓ, div_eq_mul_inv, mul_assoc, MeasureTheory.integral_mul_left, MeasureTheory.integral_mul_right,
    integral_pow_abs_sub_interval_oc, div_eq_mul_inv, pow_succₓ (v.L : ℝ), Nat.factorial_succ, Nat.cast_mulₓ,
    Nat.cast_succₓ, mul_inv, mul_assoc]

theorem dist_iterate_next_apply_le (f₁ f₂ : FunSpace v) (n : ℕ) (t : Icc v.tMin v.tMax) :
    dist ((next^[n]) f₁ t) ((next^[n]) f₂ t) ≤ (v.l * abs (t - v.t₀)) ^ n / n ! * dist f₁ f₂ := by
  induction' n with n ihn generalizing t
  · rw [pow_zeroₓ, Nat.factorial_zero, Nat.cast_oneₓ, div_one, one_mulₓ]
    exact dist_apply_le_dist f₁ f₂ t
    
  · rw [iterate_succ_apply', iterate_succ_apply']
    exact dist_next_apply_le_of_le ihn _
    

theorem dist_iterate_next_le (f₁ f₂ : FunSpace v) (n : ℕ) :
    dist ((next^[n]) f₁) ((next^[n]) f₂) ≤ (v.l * v.tDist) ^ n / n ! * dist f₁ f₂ := by
  refine' dist_le_of_forall fun t => (dist_iterate_next_apply_le _ _ _ _).trans _
  have : 0 ≤ dist f₁ f₂ := dist_nonneg
  have : abs (t - v.t₀ : ℝ) ≤ v.t_dist := v.dist_t₀_le t
  mono* <;> simp only [← Nat.cast_nonneg, ← mul_nonneg, ← Nnreal.coe_nonneg, ← abs_nonneg, *]

end FunSpace

variable [CompleteSpace E]

section

theorem exists_contracting_iterate :
    ∃ (N : ℕ)(K : _), ContractingWith K ((FunSpace.next : v.FunSpace → v.FunSpace)^[N]) := by
  rcases((Real.tendsto_pow_div_factorial_at_top (v.L * v.t_dist)).Eventually (gt_mem_nhds zero_lt_one)).exists with
    ⟨N, hN⟩
  have : (0 : ℝ) ≤ (v.L * v.t_dist) ^ N / N ! :=
    div_nonneg (pow_nonneg (mul_nonneg v.L.2 v.t_dist_nonneg) _) (Nat.cast_nonneg _)
  exact ⟨N, ⟨_, this⟩, hN, LipschitzWith.of_dist_le_mul fun f g => fun_space.dist_iterate_next_le f g N⟩

theorem exists_fixed : ∃ f : v.FunSpace, f.next = f :=
  let ⟨N, K, hK⟩ := exists_contracting_iterate v
  ⟨_, hK.is_fixed_pt_fixed_point_iterate⟩

end

/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem. -/
theorem exists_solution :
    ∃ f : ℝ → E, f v.t₀ = v.x₀ ∧ ∀, ∀ t ∈ Icc v.tMin v.tMax, ∀, HasDerivWithinAt f (v t (f t)) (Icc v.tMin v.tMax) t :=
  by
  rcases v.exists_fixed with ⟨f, hf⟩
  refine' ⟨f ∘ v.proj, _, fun t ht => _⟩
  · simp only [← (· ∘ ·), ← proj_coe, ← f.map_t₀]
    
  · simp only [← (· ∘ ·), ← v.proj_of_mem ht]
    lift t to Icc v.t_min v.t_max using ht
    simpa only [← hf, ← v.proj_coe] using f.has_deriv_within_at_next t
    

end PicardLindelof

/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem. -/
theorem exists_forall_deriv_within_Icc_eq_of_lipschitz_of_continuous [CompleteSpace E] {v : ℝ → E → E}
    {t_min t₀ t_max : ℝ} (ht₀ : t₀ ∈ Icc t_min t_max) (x₀ : E) {C R : ℝ} (hR : 0 ≤ R) {L : ℝ≥0 }
    (Hlip : ∀, ∀ t ∈ Icc t_min t_max, ∀, LipschitzOnWith L (v t) (ClosedBall x₀ R))
    (Hcont : ∀, ∀ x ∈ ClosedBall x₀ R, ∀, ContinuousOn (fun t => v t x) (Icc t_min t_max))
    (Hnorm : ∀, ∀ t ∈ Icc t_min t_max, ∀, ∀ x ∈ ClosedBall x₀ R, ∀, ∥v t x∥ ≤ C)
    (Hmul_le : C * max (t_max - t₀) (t₀ - t_min) ≤ R) :
    ∃ f : ℝ → E, f t₀ = x₀ ∧ ∀, ∀ t ∈ Icc t_min t_max, ∀, HasDerivWithinAt f (v t (f t)) (Icc t_min t_max) t := by
  lift C to ℝ≥0 using (norm_nonneg _).trans <| Hnorm t₀ ht₀ x₀ (mem_closed_ball_self hR)
  lift R to ℝ≥0 using hR
  lift t₀ to Icc t_min t_max using ht₀
  exact PicardLindelof.exists_solution ⟨v, t_min, t_max, t₀, x₀, C, R, L, Hlip, Hcont, Hnorm, Hmul_le⟩


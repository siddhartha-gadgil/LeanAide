/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathbin.Analysis.Asymptotics.Asymptotics
import Mathbin.Analysis.NormedSpace.Ordered
import Mathbin.Data.Polynomial.Eval
import Mathbin.Topology.Algebra.Order.LiminfLimsup

/-!
# Super-Polynomial Function Decay

This file defines a predicate `asymptotics.superpolynomial_decay f` for a function satisfying
  one of following equivalent definitions (The definition is in terms of the first condition):

* `x ^ n * f` tends to `𝓝 0` for all (or sufficiently large) naturals `n`
* `|x ^ n * f|` tends to `𝓝 0` for all naturals `n` (`superpolynomial_decay_iff_abs_tendsto_zero`)
* `|x ^ n * f|` is bounded for all naturals `n` (`superpolynomial_decay_iff_abs_is_bounded_under`)
* `f` is `o(x ^ c)` for all integers `c` (`superpolynomial_decay_iff_is_o`)
* `f` is `O(x ^ c)` for all integers `c` (`superpolynomial_decay_iff_is_O`)

These conditions are all equivalent to conditions in terms of polynomials, replacing `x ^ c` with
  `p(x)` or `p(x)⁻¹` as appropriate, since asymptotically `p(x)` behaves like `X ^ p.nat_degree`.
These further equivalences are not proven in mathlib but would be good future projects.

The definition of superpolynomial decay for `f : α → β` is relative to a parameter `k : α → β`.
Super-polynomial decay then means `f x` decays faster than `(k x) ^ c` for all integers `c`.
Equivalently `f x` decays faster than `p.eval (k x)` for all polynomials `p : polynomial β`.
The definition is also relative to a filter `l : filter α` where the decay rate is compared.

When the map `k` is given by `n ↦ ↑n : ℕ → ℝ` this defines negligible functions:
https://en.wikipedia.org/wiki/Negligible_function

When the map `k` is given by `(r₁,...,rₙ) ↦ r₁*...*rₙ : ℝⁿ → ℝ` this is equivalent
  to the definition of rapidly decreasing functions given here:
https://ncatlab.org/nlab/show/rapidly+decreasing+function

# Main Theorems

* `superpolynomial_decay.polynomial_mul` says that if `f(x)` is negligible,
    then so is `p(x) * f(x)` for any polynomial `p`.
* `superpolynomial_decay_iff_zpow_tendsto_zero` gives an equivalence between definitions in terms
    of decaying faster than `k(x) ^ n` for all naturals `n` or `k(x) ^ c` for all integer `c`.
-/


namespace Asymptotics

open TopologicalSpace

open Filter

/-- `f` has superpolynomial decay in parameter `k` along filter `l` if
  `k ^ n * f` tends to zero at `l` for all naturals `n` -/
def SuperpolynomialDecay {α β : Type _} [TopologicalSpace β] [CommSemiringₓ β] (l : Filter α) (k : α → β) (f : α → β) :=
  ∀ n : ℕ, Tendsto (fun a : α => k a ^ n * f a) l (𝓝 0)

variable {α β : Type _} {l : Filter α} {k : α → β} {f g g' : α → β}

section CommSemiringₓ

variable [TopologicalSpace β] [CommSemiringₓ β]

theorem SuperpolynomialDecay.congr' (hf : SuperpolynomialDecay l k f) (hfg : f =ᶠ[l] g) : SuperpolynomialDecay l k g :=
  fun z => (hf z).congr' (EventuallyEq.mul (EventuallyEq.refl l _) hfg)

theorem SuperpolynomialDecay.congr (hf : SuperpolynomialDecay l k f) (hfg : ∀ x, f x = g x) :
    SuperpolynomialDecay l k g := fun z => (hf z).congr fun x => (congr_arg fun a => k x ^ z * a) <| hfg x

@[simp]
theorem superpolynomial_decay_zero (l : Filter α) (k : α → β) : SuperpolynomialDecay l k 0 := fun z => by
  simpa only [← Pi.zero_apply, ← mul_zero] using tendsto_const_nhds

theorem SuperpolynomialDecay.add [HasContinuousAdd β] (hf : SuperpolynomialDecay l k f)
    (hg : SuperpolynomialDecay l k g) : SuperpolynomialDecay l k (f + g) := fun z => by
  simpa only [← mul_addₓ, ← add_zeroₓ, ← Pi.add_apply] using (hf z).add (hg z)

theorem SuperpolynomialDecay.mul [HasContinuousMul β] (hf : SuperpolynomialDecay l k f)
    (hg : SuperpolynomialDecay l k g) : SuperpolynomialDecay l k (f * g) := fun z => by
  simpa only [← mul_assoc, ← one_mulₓ, ← mul_zero, ← pow_zeroₓ] using (hf z).mul (hg 0)

theorem SuperpolynomialDecay.mul_const [HasContinuousMul β] (hf : SuperpolynomialDecay l k f) (c : β) :
    SuperpolynomialDecay l k fun n => f n * c := fun z => by
  simpa only [mul_assoc, ← zero_mul] using tendsto.mul_const c (hf z)

theorem SuperpolynomialDecay.const_mul [HasContinuousMul β] (hf : SuperpolynomialDecay l k f) (c : β) :
    SuperpolynomialDecay l k fun n => c * f n :=
  (hf.mul_const c).congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.param_mul (hf : SuperpolynomialDecay l k f) : SuperpolynomialDecay l k (k * f) := fun z =>
  tendsto_nhds.2 fun s hs hs0 =>
    l.sets_of_superset ((tendsto_nhds.1 (hf <| z + 1)) s hs hs0) fun x hx => by
      simpa only [← Set.mem_preimage, ← Pi.mul_apply, mul_assoc, pow_succ'ₓ] using hx

theorem SuperpolynomialDecay.mul_param (hf : SuperpolynomialDecay l k f) : SuperpolynomialDecay l k (f * k) :=
  hf.param_mul.congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.param_pow_mul (hf : SuperpolynomialDecay l k f) (n : ℕ) :
    SuperpolynomialDecay l k (k ^ n * f) := by
  induction' n with n hn
  · simpa only [← one_mulₓ, ← pow_zeroₓ] using hf
    
  · simpa only [← pow_succₓ, ← mul_assoc] using hn.param_mul
    

theorem SuperpolynomialDecay.mul_param_pow (hf : SuperpolynomialDecay l k f) (n : ℕ) :
    SuperpolynomialDecay l k (f * k ^ n) :=
  (hf.param_pow_mul n).congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.polynomial_mul [HasContinuousAdd β] [HasContinuousMul β] (hf : SuperpolynomialDecay l k f)
    (p : Polynomial β) : SuperpolynomialDecay l k fun x => (p.eval <| k x) * f x :=
  Polynomial.induction_on' p
    (fun p q hp hq => by
      simpa [← add_mulₓ] using hp.add hq)
    fun n c => by
    simpa [← mul_assoc] using (hf.param_pow_mul n).const_mul c

theorem SuperpolynomialDecay.mul_polynomial [HasContinuousAdd β] [HasContinuousMul β] (hf : SuperpolynomialDecay l k f)
    (p : Polynomial β) : SuperpolynomialDecay l k fun x => f x * (p.eval <| k x) :=
  (hf.polynomial_mul p).congr fun _ => mul_comm _ _

end CommSemiringₓ

section OrderedCommSemiring

variable [TopologicalSpace β] [OrderedCommSemiring β] [OrderTopology β]

theorem SuperpolynomialDecay.trans_eventually_le (hk : 0 ≤ᶠ[l] k) (hg : SuperpolynomialDecay l k g)
    (hg' : SuperpolynomialDecay l k g') (hfg : g ≤ᶠ[l] f) (hfg' : f ≤ᶠ[l] g') : SuperpolynomialDecay l k f := fun z =>
  tendsto_of_tendsto_of_tendsto_of_le_of_le' (hg z) (hg' z)
    (hfg.mp (hk.mono fun x hx hx' => mul_le_mul_of_nonneg_left hx' (pow_nonneg hx z)))
    (hfg'.mp (hk.mono fun x hx hx' => mul_le_mul_of_nonneg_left hx' (pow_nonneg hx z)))

end OrderedCommSemiring

section LinearOrderedCommRing

variable [TopologicalSpace β] [LinearOrderedCommRing β] [OrderTopology β]

variable (l k f)

theorem superpolynomial_decay_iff_abs_tendsto_zero :
    SuperpolynomialDecay l k f ↔ ∀ n : ℕ, Tendsto (fun a : α => abs (k a ^ n * f a)) l (𝓝 0) :=
  ⟨fun h z => (tendsto_zero_iff_abs_tendsto_zero _).1 (h z), fun h z => (tendsto_zero_iff_abs_tendsto_zero _).2 (h z)⟩

theorem superpolynomial_decay_iff_superpolynomial_decay_abs :
    SuperpolynomialDecay l k f ↔ SuperpolynomialDecay l (fun a => abs (k a)) fun a => abs (f a) :=
  (superpolynomial_decay_iff_abs_tendsto_zero l k f).trans
    (by
      simp_rw [superpolynomial_decay, abs_mul, abs_pow])

variable {l k f}

theorem SuperpolynomialDecay.trans_eventually_abs_le (hf : SuperpolynomialDecay l k f) (hfg : abs ∘ g ≤ᶠ[l] abs ∘ f) :
    SuperpolynomialDecay l k g := by
  rw [superpolynomial_decay_iff_abs_tendsto_zero] at hf⊢
  refine' fun z =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hf z) (eventually_of_forall fun x => abs_nonneg _)
      (hfg.mono fun x hx => _)
  calc abs (k x ^ z * g x) = abs (k x ^ z) * abs (g x) := abs_mul (k x ^ z) (g x)_ ≤ abs (k x ^ z) * abs (f x) :=
      mul_le_mul le_rfl hx (abs_nonneg _) (abs_nonneg _)_ = abs (k x ^ z * f x) := (abs_mul (k x ^ z) (f x)).symm

theorem SuperpolynomialDecay.trans_abs_le (hf : SuperpolynomialDecay l k f) (hfg : ∀ x, abs (g x) ≤ abs (f x)) :
    SuperpolynomialDecay l k g :=
  hf.trans_eventually_abs_le (eventually_of_forall hfg)

end LinearOrderedCommRing

section Field

variable [TopologicalSpace β] [Field β] (l k f)

theorem superpolynomial_decay_mul_const_iff [HasContinuousMul β] {c : β} (hc0 : c ≠ 0) :
    (SuperpolynomialDecay l k fun n => f n * c) ↔ SuperpolynomialDecay l k f :=
  ⟨fun h =>
    (h.mul_const c⁻¹).congr fun x => by
      simp [← mul_assoc, ← mul_inv_cancel hc0],
    fun h => h.mul_const c⟩

theorem superpolynomial_decay_const_mul_iff [HasContinuousMul β] {c : β} (hc0 : c ≠ 0) :
    (SuperpolynomialDecay l k fun n => c * f n) ↔ SuperpolynomialDecay l k f :=
  ⟨fun h =>
    (h.const_mul c⁻¹).congr fun x => by
      simp [mul_assoc, ← inv_mul_cancel hc0],
    fun h => h.const_mul c⟩

variable {l k f}

end Field

section LinearOrderedField

variable [TopologicalSpace β] [LinearOrderedField β] [OrderTopology β]

variable (f)

theorem superpolynomial_decay_iff_abs_is_bounded_under (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℕ, IsBoundedUnder (· ≤ ·) l fun a : α => abs (k a ^ z * f a) := by
  refine'
    ⟨fun h z => tendsto.is_bounded_under_le (tendsto.abs (h z)), fun h =>
      (superpolynomial_decay_iff_abs_tendsto_zero l k f).2 fun z => _⟩
  obtain ⟨m, hm⟩ := h (z + 1)
  have h1 : tendsto (fun a : α => (0 : β)) l (𝓝 0) := tendsto_const_nhds
  have h2 : tendsto (fun a : α => abs (k a)⁻¹ * m) l (𝓝 0) :=
    zero_mul m ▸ tendsto.mul_const m ((tendsto_zero_iff_abs_tendsto_zero _).1 hk.inv_tendsto_at_top)
  refine'
    tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 (eventually_of_forall fun x => abs_nonneg _)
      ((eventually_map.1 hm).mp _)
  refine' (hk.eventually_ne_at_top 0).mono fun x hk0 hx => _
  refine' Eq.trans_le _ (mul_le_mul_of_nonneg_left hx <| abs_nonneg (k x)⁻¹)
  rw [← abs_mul, ← mul_assoc, pow_succₓ, ← mul_assoc, inv_mul_cancel hk0, one_mulₓ]

theorem superpolynomial_decay_iff_zpow_tendsto_zero (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ, Tendsto (fun a : α => k a ^ z * f a) l (𝓝 0) := by
  refine'
    ⟨fun h z => _, fun h n => by
      simpa only [← zpow_coe_nat] using h (n : ℤ)⟩
  by_cases' hz : 0 ≤ z
  · lift z to ℕ using hz
    simpa using h z
    
  · have : tendsto (fun a => k a ^ z) l (𝓝 0) := tendsto.comp (tendsto_zpow_at_top_zero (not_leₓ.1 hz)) hk
    have h : tendsto f l (𝓝 0) := by
      simpa using h 0
    exact zero_mul (0 : β) ▸ this.mul h
    

variable {f}

theorem SuperpolynomialDecay.param_zpow_mul (hk : Tendsto k l atTop) (hf : SuperpolynomialDecay l k f) (z : ℤ) :
    SuperpolynomialDecay l k fun a => k a ^ z * f a := by
  rw [superpolynomial_decay_iff_zpow_tendsto_zero _ hk] at hf⊢
  refine' fun z' => (hf <| z' + z).congr' ((hk.eventually_ne_at_top 0).mono fun x hx => _)
  simp [← zpow_add₀ hx, ← mul_assoc, ← Pi.mul_apply]

theorem SuperpolynomialDecay.mul_param_zpow (hk : Tendsto k l atTop) (hf : SuperpolynomialDecay l k f) (z : ℤ) :
    SuperpolynomialDecay l k fun a => f a * k a ^ z :=
  (hf.param_zpow_mul hk z).congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.inv_param_mul (hk : Tendsto k l atTop) (hf : SuperpolynomialDecay l k f) :
    SuperpolynomialDecay l k (k⁻¹ * f) := by
  simpa using hf.param_zpow_mul hk (-1)

theorem SuperpolynomialDecay.param_inv_mul (hk : Tendsto k l atTop) (hf : SuperpolynomialDecay l k f) :
    SuperpolynomialDecay l k (f * k⁻¹) :=
  (hf.inv_param_mul hk).congr fun _ => mul_comm _ _

variable (f)

theorem superpolynomial_decay_param_mul_iff (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k (k * f) ↔ SuperpolynomialDecay l k f :=
  ⟨fun h =>
    (h.inv_param_mul hk).congr'
      ((hk.eventually_ne_at_top 0).mono fun x hx => by
        simp [mul_assoc, ← inv_mul_cancel hx]),
    fun h => h.param_mul⟩

theorem superpolynomial_decay_mul_param_iff (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k (f * k) ↔ SuperpolynomialDecay l k f := by
  simpa [← mul_comm k] using superpolynomial_decay_param_mul_iff f hk

theorem superpolynomial_decay_param_pow_mul_iff (hk : Tendsto k l atTop) (n : ℕ) :
    SuperpolynomialDecay l k (k ^ n * f) ↔ SuperpolynomialDecay l k f := by
  induction' n with n hn
  · simp
    
  · simpa [← pow_succₓ, mul_comm k, ← mul_assoc, ← superpolynomial_decay_param_mul_iff (k ^ n * f) hk] using hn
    

theorem superpolynomial_decay_mul_param_pow_iff (hk : Tendsto k l atTop) (n : ℕ) :
    SuperpolynomialDecay l k (f * k ^ n) ↔ SuperpolynomialDecay l k f := by
  simpa [← mul_comm f] using superpolynomial_decay_param_pow_mul_iff f hk n

variable {f}

end LinearOrderedField

section NormedLinearOrderedField

variable [NormedLinearOrderedField β]

variable (l k f)

theorem superpolynomial_decay_iff_norm_tendsto_zero :
    SuperpolynomialDecay l k f ↔ ∀ n : ℕ, Tendsto (fun a : α => ∥k a ^ n * f a∥) l (𝓝 0) :=
  ⟨fun h z => tendsto_zero_iff_norm_tendsto_zero.1 (h z), fun h z => tendsto_zero_iff_norm_tendsto_zero.2 (h z)⟩

theorem superpolynomial_decay_iff_superpolynomial_decay_norm :
    SuperpolynomialDecay l k f ↔ SuperpolynomialDecay l (fun a => ∥k a∥) fun a => ∥f a∥ :=
  (superpolynomial_decay_iff_norm_tendsto_zero l k f).trans
    (by
      simp [← superpolynomial_decay])

variable {l k}

variable [OrderTopology β]

theorem superpolynomial_decay_iff_is_O (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ, f =O[l] fun a : α => k a ^ z := by
  refine' (superpolynomial_decay_iff_zpow_tendsto_zero f hk).trans _
  have hk0 : ∀ᶠ x in l, k x ≠ 0 := hk.eventually_ne_at_top 0
  refine' ⟨fun h z => _, fun h z => _⟩
  · refine' is_O_of_div_tendsto_nhds (hk0.mono fun x hx hxz => absurd (zpow_eq_zero hxz) hx) 0 _
    have : (fun a : α => k a ^ z)⁻¹ = fun a : α => k a ^ -z :=
      funext fun x => by
        simp
    rw [div_eq_mul_inv, mul_comm f, this]
    exact h (-z)
    
  · suffices : (fun a : α => k a ^ z * f a) =O[l] fun a : α => (k a)⁻¹
    exact is_O.trans_tendsto this hk.inv_tendsto_at_top
    refine' ((is_O_refl (fun a => k a ^ z) l).mul (h (-(z + 1)))).trans (is_O.of_bound 1 <| hk0.mono fun a ha0 => _)
    simp only [← one_mulₓ, ← neg_add z 1, ← zpow_add₀ ha0, mul_assoc, ← zpow_neg, ← mul_inv_cancel (zpow_ne_zero z ha0),
      ← zpow_one]
    

theorem superpolynomial_decay_iff_is_o (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ, f =o[l] fun a : α => k a ^ z := by
  refine' ⟨fun h z => _, fun h => (superpolynomial_decay_iff_is_O f hk).2 fun z => (h z).IsO⟩
  have hk0 : ∀ᶠ x in l, k x ≠ 0 := hk.eventually_ne_at_top 0
  have : (fun x : α => (1 : β)) =o[l] k :=
    is_o_of_tendsto' (hk0.mono fun x hkx hkx' => absurd hkx' hkx)
      (by
        simpa using hk.inv_tendsto_at_top)
  have : f =o[l] fun x : α => k x * k x ^ (z - 1) := by
    simpa using this.mul_is_O ((superpolynomial_decay_iff_is_O f hk).1 h <| z - 1)
  refine' this.trans_is_O (is_O.of_bound 1 (hk0.mono fun x hkx => le_of_eqₓ _))
  rw [one_mulₓ, zpow_sub_one₀ hkx, mul_comm (k x), mul_assoc, inv_mul_cancel hkx, mul_oneₓ]

end NormedLinearOrderedField

end Asymptotics


/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathbin.Analysis.Asymptotics.Asymptotics
import Mathbin.Analysis.NormedSpace.Ordered

/-!
# Asymptotic equivalence

In this file, we define the relation `is_equivalent l u v`, which means that `u-v` is little o of
`v` along the filter `l`.

Unlike `is_[oO]` relations, this one requires `u` and `v` to have the same codomain `β`. While the
definition only requires `β` to be a `normed_group`, most interesting properties require it to be a
`normed_field`.

## Notations

We introduce the notation `u ~[l] v := is_equivalent l u v`, which you can use by opening the
`asymptotics` locale.

## Main results

If `β` is a `normed_group` :

- `_ ~[l] _` is an equivalence relation
- Equivalent statements for `u ~[l] const _ c` :
  - If `c ≠ 0`, this is true iff `tendsto u l (𝓝 c)` (see `is_equivalent_const_iff_tendsto`)
  - For `c = 0`, this is true iff `u =ᶠ[l] 0` (see `is_equivalent_zero_iff_eventually_zero`)

If `β` is a `normed_field` :

- Alternative characterization of the relation (see `is_equivalent_iff_exists_eq_mul`) :

  `u ~[l] v ↔ ∃ (φ : α → β) (hφ : tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v`

- Provided some non-vanishing hypothesis, this can be seen as `u ~[l] v ↔ tendsto (u/v) l (𝓝 1)`
  (see `is_equivalent_iff_tendsto_one`)
- For any constant `c`, `u ~[l] v` implies `tendsto u l (𝓝 c) ↔ tendsto v l (𝓝 c)`
  (see `is_equivalent.tendsto_nhds_iff`)
- `*` and `/` are compatible with `_ ~[l] _` (see `is_equivalent.mul` and `is_equivalent.div`)

If `β` is a `normed_linear_ordered_field` :

- If `u ~[l] v`, we have `tendsto u l at_top ↔ tendsto v l at_top`
  (see `is_equivalent.tendsto_at_top_iff`)

## Implementation Notes

Note that `is_equivalent` takes the parameters `(l : filter α) (u v : α → β)` in that order.
This is to enable `calc` support, as `calc` requires that the last two explicit arguments are `u v`.

-/


namespace Asymptotics

open Filter Function

open TopologicalSpace

section NormedGroup

variable {α β : Type _} [NormedGroup β]

/-- Two functions `u` and `v` are said to be asymptotically equivalent along a filter `l` when
    `u x - v x = o(v x)` as x converges along `l`. -/
def IsEquivalent (l : Filter α) (u v : α → β) :=
  (u - v) =o[l] v

-- mathport name: «expr ~[ ] »
localized [Asymptotics] notation:50 u " ~[" l:50 "] " v:50 => Asymptotics.IsEquivalent l u v

variable {u v w : α → β} {l : Filter α}

theorem IsEquivalent.is_o (h : u ~[l] v) : (u - v) =o[l] v :=
  h

theorem IsEquivalent.is_O (h : u ~[l] v) : u =O[l] v :=
  (IsO.congr_of_sub h.IsO.symm).mp (is_O_refl _ _)

theorem IsEquivalent.is_O_symm (h : u ~[l] v) : v =O[l] u := by
  convert h.is_o.right_is_O_add
  ext
  simp

@[refl]
theorem IsEquivalent.refl : u ~[l] u := by
  rw [is_equivalent, sub_self]
  exact is_o_zero _ _

@[symm]
theorem IsEquivalent.symm (h : u ~[l] v) : v ~[l] u :=
  (h.IsO.trans_is_O h.is_O_symm).symm

@[trans]
theorem IsEquivalent.trans {l : Filter α} {u v w : α → β} (huv : u ~[l] v) (hvw : v ~[l] w) : u ~[l] w :=
  (huv.IsO.trans_is_O hvw.IsO).triangle hvw.IsO

theorem IsEquivalent.congr_left {u v w : α → β} {l : Filter α} (huv : u ~[l] v) (huw : u =ᶠ[l] w) : w ~[l] v :=
  huv.congr' (huw.sub (EventuallyEq.refl _ _)) (EventuallyEq.refl _ _)

theorem IsEquivalent.congr_right {u v w : α → β} {l : Filter α} (huv : u ~[l] v) (hvw : v =ᶠ[l] w) : u ~[l] w :=
  (huv.symm.congr_left hvw).symm

theorem is_equivalent_zero_iff_eventually_zero : u ~[l] 0 ↔ u =ᶠ[l] 0 := by
  rw [is_equivalent, sub_zero]
  exact is_o_zero_right_iff

theorem is_equivalent_zero_iff_is_O_zero : u ~[l] 0 ↔ u =O[l] (0 : α → β) := by
  refine' ⟨is_equivalent.is_O, fun h => _⟩
  rw [is_equivalent_zero_iff_eventually_zero, eventually_eq_iff_exists_mem]
  exact ⟨{ x : α | u x = 0 }, is_O_zero_right_iff.mp h, fun x hx => hx⟩

theorem is_equivalent_const_iff_tendsto {c : β} (h : c ≠ 0) : u ~[l] const _ c ↔ Tendsto u l (𝓝 c) := by
  rw [is_equivalent, is_o_const_iff h]
  constructor <;>
    intro h <;>
        [· have := h.sub tendsto_const_nhds
          rw [zero_sub (-c)] at this
          ,
        · have := h.sub tendsto_const_nhds
          rw [← sub_self c]
          ] <;>
      convert this <;>
        try
            ext <;>
          simp

theorem IsEquivalent.tendsto_const {c : β} (hu : u ~[l] const _ c) : Tendsto u l (𝓝 c) := by
  rcases em <| c = 0 with ⟨rfl, h⟩
  · exact (tendsto_congr' <| is_equivalent_zero_iff_eventually_zero.mp hu).mpr tendsto_const_nhds
    
  · exact (is_equivalent_const_iff_tendsto h).mp hu
    

theorem IsEquivalent.tendsto_nhds {c : β} (huv : u ~[l] v) (hu : Tendsto u l (𝓝 c)) : Tendsto v l (𝓝 c) := by
  by_cases' h : c = 0
  · subst c
    rw [← is_o_one_iff ℝ] at hu⊢
    simpa using (huv.symm.is_o.trans hu).add hu
    
  · rw [← is_equivalent_const_iff_tendsto h] at hu⊢
    exact huv.symm.trans hu
    

theorem IsEquivalent.tendsto_nhds_iff {c : β} (huv : u ~[l] v) : Tendsto u l (𝓝 c) ↔ Tendsto v l (𝓝 c) :=
  ⟨huv.tendsto_nhds, huv.symm.tendsto_nhds⟩

theorem IsEquivalent.add_is_o (huv : u ~[l] v) (hwv : w =o[l] v) : w + u ~[l] v := by
  simpa only [← is_equivalent, ← Pi.sub_apply, ← add_sub] using hwv.add huv

theorem IsOₓ.add_is_equivalent (hu : u =o[l] w) (hv : v ~[l] w) : u + v ~[l] w :=
  add_commₓ u v ▸ hv.add_is_o hu

theorem IsOₓ.is_equivalent (huv : (u - v) =o[l] v) : u ~[l] v :=
  huv

theorem IsEquivalent.neg (huv : u ~[l] v) : (fun x => -u x) ~[l] fun x => -v x := by
  rw [is_equivalent]
  convert huv.is_o.neg_left.neg_right
  ext
  simp

end NormedGroup

open Asymptotics

section NormedField

variable {α β : Type _} [NormedField β] {t u v w : α → β} {l : Filter α}

theorem is_equivalent_iff_exists_eq_mul : u ~[l] v ↔ ∃ (φ : α → β)(hφ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v := by
  rw [is_equivalent, is_o_iff_exists_eq_mul]
  constructor <;> rintro ⟨φ, hφ, h⟩ <;> [use φ + 1, use φ - 1] <;> constructor
  · conv in 𝓝 _ => rw [← zero_addₓ (1 : β)]
    exact hφ.add tendsto_const_nhds
    
  · convert h.add (eventually_eq.refl l v) <;> ext <;> simp [← add_mulₓ]
    
  · conv in 𝓝 _ => rw [← sub_self (1 : β)]
    exact hφ.sub tendsto_const_nhds
    
  · convert h.sub (eventually_eq.refl l v) <;> ext <;> simp [← sub_mul]
    

theorem IsEquivalent.exists_eq_mul (huv : u ~[l] v) : ∃ (φ : α → β)(hφ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v :=
  is_equivalent_iff_exists_eq_mul.mp huv

theorem is_equivalent_of_tendsto_one (hz : ∀ᶠ x in l, v x = 0 → u x = 0) (huv : Tendsto (u / v) l (𝓝 1)) : u ~[l] v :=
  by
  rw [is_equivalent_iff_exists_eq_mul]
  refine' ⟨u / v, huv, hz.mono fun x hz' => (div_mul_cancel_of_imp hz').symm⟩

theorem is_equivalent_of_tendsto_one' (hz : ∀ x, v x = 0 → u x = 0) (huv : Tendsto (u / v) l (𝓝 1)) : u ~[l] v :=
  is_equivalent_of_tendsto_one (eventually_of_forall hz) huv

theorem is_equivalent_iff_tendsto_one (hz : ∀ᶠ x in l, v x ≠ 0) : u ~[l] v ↔ Tendsto (u / v) l (𝓝 1) := by
  constructor
  · intro hequiv
    have := hequiv.is_o.tendsto_div_nhds_zero
    simp only [← Pi.sub_apply, ← sub_div] at this
    have key : tendsto (fun x => v x / v x) l (𝓝 1) :=
      (tendsto_congr' <| hz.mono fun x hnz => @div_self _ _ (v x) hnz).mpr tendsto_const_nhds
    convert this.add key
    · ext
      simp
      
    · norm_num
      
    
  · exact is_equivalent_of_tendsto_one (hz.mono fun x hnvz hz => (hnvz hz).elim)
    

end NormedField

section Smul

theorem IsEquivalent.smul {α E 𝕜 : Type _} [NormedField 𝕜] [NormedGroup E] [NormedSpace 𝕜 E] {a b : α → 𝕜} {u v : α → E}
    {l : Filter α} (hab : a ~[l] b) (huv : u ~[l] v) : (fun x => a x • u x) ~[l] fun x => b x • v x := by
  rcases hab.exists_eq_mul with ⟨φ, hφ, habφ⟩
  have : ((fun x : α => a x • u x) - fun x : α => b x • v x) =ᶠ[l] fun x => b x • (φ x • u x - v x) := by
    convert (habφ.comp₂ (· • ·) <| eventually_eq.refl _ u).sub (eventually_eq.refl _ fun x => b x • v x)
    ext
    rw [Pi.mul_apply, mul_comm, mul_smul, ← smul_sub]
  refine' (is_o_congr this.symm <| eventually_eq.rfl).mp ((is_O_refl b l).smul_is_o _)
  rcases huv.is_O.exists_pos with ⟨C, hC, hCuv⟩
  rw [is_equivalent] at *
  rw [is_o_iff] at *
  rw [is_O_with] at hCuv
  simp only [← Metric.tendsto_nhds, ← dist_eq_norm] at hφ
  intro c hc
  specialize
    hφ (c / 2 / C)
      (div_pos
        (by
          linarith)
        hC)
  specialize
    huv
      (show 0 < c / 2 by
        linarith)
  refine' hφ.mp (huv.mp <| hCuv.mono fun x hCuvx huvx hφx => _)
  have key :=
    calc
      ∥φ x - 1∥ * ∥u x∥ ≤ c / 2 / C * ∥u x∥ := mul_le_mul_of_nonneg_right hφx.le (norm_nonneg <| u x)
      _ ≤ c / 2 / C * (C * ∥v x∥) :=
        mul_le_mul_of_nonneg_left hCuvx
          (div_pos
              (by
                linarith)
              hC).le
      _ = c / 2 * ∥v x∥ := by
        field_simp [← hC.ne.symm]
        ring
      
  calc ∥((fun x : α => φ x • u x) - v) x∥ = ∥(φ x - 1) • u x + (u x - v x)∥ := by
      simp [← sub_smul, ← sub_add]_ ≤ ∥(φ x - 1) • u x∥ + ∥u x - v x∥ :=
      norm_add_le _ _ _ = ∥φ x - 1∥ * ∥u x∥ + ∥u x - v x∥ := by
      rw [norm_smul]_ ≤ c / 2 * ∥v x∥ + ∥u x - v x∥ := add_le_add_right key _ _ ≤ c / 2 * ∥v x∥ + c / 2 * ∥v x∥ :=
      add_le_add_left huvx _ _ = c * ∥v x∥ := by
      ring

end Smul

section mul_inv

variable {α β : Type _} [NormedField β] {t u v w : α → β} {l : Filter α}

theorem IsEquivalent.mul (htu : t ~[l] u) (hvw : v ~[l] w) : t * v ~[l] u * w :=
  htu.smul hvw

theorem IsEquivalent.inv (huv : u ~[l] v) : (fun x => (u x)⁻¹) ~[l] fun x => (v x)⁻¹ := by
  rw [is_equivalent_iff_exists_eq_mul] at *
  rcases huv with ⟨φ, hφ, h⟩
  rw [← inv_one]
  refine'
    ⟨fun x => (φ x)⁻¹,
      tendsto.inv₀ hφ
        (by
          norm_num),
      _⟩
  convert h.inv
  ext
  simp [← mul_inv]

theorem IsEquivalent.div (htu : t ~[l] u) (hvw : v ~[l] w) : (fun x => t x / v x) ~[l] fun x => u x / w x := by
  simpa only [← div_eq_mul_inv] using htu.mul hvw.inv

end mul_inv

section NormedLinearOrderedField

variable {α β : Type _} [NormedLinearOrderedField β] {u v : α → β} {l : Filter α}

theorem IsEquivalent.tendsto_at_top [OrderTopology β] (huv : u ~[l] v) (hu : Tendsto u l atTop) : Tendsto v l atTop :=
  let ⟨φ, hφ, h⟩ := huv.symm.exists_eq_mul
  Tendsto.congr' h.symm (mul_comm u φ ▸ hu.at_top_mul zero_lt_one hφ)

theorem IsEquivalent.tendsto_at_top_iff [OrderTopology β] (huv : u ~[l] v) : Tendsto u l atTop ↔ Tendsto v l atTop :=
  ⟨huv.tendsto_at_top, huv.symm.tendsto_at_top⟩

theorem IsEquivalent.tendsto_at_bot [OrderTopology β] (huv : u ~[l] v) (hu : Tendsto u l atBot) : Tendsto v l atBot :=
  by
  convert tendsto_neg_at_top_at_bot.comp (huv.neg.tendsto_at_top <| tendsto_neg_at_bot_at_top.comp hu)
  ext
  simp

theorem IsEquivalent.tendsto_at_bot_iff [OrderTopology β] (huv : u ~[l] v) : Tendsto u l atBot ↔ Tendsto v l atBot :=
  ⟨huv.tendsto_at_bot, huv.symm.tendsto_at_bot⟩

end NormedLinearOrderedField

end Asymptotics

open Filter Asymptotics

open Asymptotics

variable {α β : Type _} [NormedGroup β]

theorem Filter.EventuallyEq.is_equivalent {u v : α → β} {l : Filter α} (h : u =ᶠ[l] v) : u ~[l] v :=
  IsEquivalent.congr_right (is_o_refl_left _ _) h


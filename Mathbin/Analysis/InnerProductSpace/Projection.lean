/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
import Mathbin.Analysis.Convex.Basic
import Mathbin.Analysis.InnerProductSpace.Basic
import Mathbin.Analysis.NormedSpace.IsROrC

/-!
# The orthogonal projection

Given a nonempty complete subspace `K` of an inner product space `E`, this file constructs
`orthogonal_projection K : E →L[𝕜] K`, the orthogonal projection of `E` onto `K`.  This map
satisfies: for any point `u` in `E`, the point `v = orthogonal_projection K u` in `K` minimizes the
distance `∥u - v∥` to `u`.

Also a linear isometry equivalence `reflection K : E ≃ₗᵢ[𝕜] E` is constructed, by choosing, for
each `u : E`, the point `reflection K u` to satisfy
`u + (reflection K u) = 2 • orthogonal_projection K u`.

Basic API for `orthogonal_projection` and `reflection` is developed.

Next, the orthogonal projection is used to prove a series of more subtle lemmas about the
the orthogonal complement of complete subspaces of `E` (the orthogonal complement itself was
defined in `analysis.inner_product_space.basic`); the lemma
`submodule.sup_orthogonal_of_is_complete`, stating that for a complete subspace `K` of `E` we have
`K ⊔ Kᗮ = ⊤`, is a typical example.

## References

The orthogonal projection construction is adapted from
*  [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
*  [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/


noncomputable section

open IsROrC Real Filter

open BigOperators TopologicalSpace

variable {𝕜 E F : Type _} [IsROrC 𝕜]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

-- mathport name: «exprabsR»
local notation "absR" => HasAbs.abs

/-! ### Orthogonal projection in inner product spaces -/


/-- Existence of minimizers
Let `u` be a point in a real inner product space, and let `K` be a nonempty complete convex subset.
Then there exists a (unique) `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
 -/
-- FIXME this monolithic proof causes a deterministic timeout with `-T50000`
-- It should be broken in a sequence of more manageable pieces,
-- perhaps with individual statements for the three steps below.
theorem exists_norm_eq_infi_of_complete_convex {K : Set F} (ne : K.Nonempty) (h₁ : IsComplete K) (h₂ : Convex ℝ K) :
    ∀ u : F, ∃ v ∈ K, ∥u - v∥ = ⨅ w : K, ∥u - w∥ := fun u => by
  let δ := ⨅ w : K, ∥u - w∥
  let this : Nonempty K := ne.to_subtype
  have zero_le_δ : 0 ≤ δ := le_cinfi fun _ => norm_nonneg _
  have δ_le : ∀ w : K, δ ≤ ∥u - w∥ := cinfi_le ⟨0, Set.forall_range_iff.2 fun _ => norm_nonneg _⟩
  have δ_le' : ∀, ∀ w ∈ K, ∀, δ ≤ ∥u - w∥ := fun w hw => δ_le ⟨w, hw⟩
  -- Step 1: since `δ` is the infimum, can find a sequence `w : ℕ → K` in `K`
  -- such that `∥u - w n∥ < δ + 1 / (n + 1)` (which implies `∥u - w n∥ --> δ`);
  -- maybe this should be a separate lemma
  have exists_seq : ∃ w : ℕ → K, ∀ n, ∥u - w n∥ < δ + 1 / (n + 1) := by
    have hδ : ∀ n : ℕ, δ < δ + 1 / (n + 1) := fun n => lt_add_of_le_of_pos le_rfl Nat.one_div_pos_of_nat
    have h := fun n => exists_lt_of_cinfi_lt (hδ n)
    let w : ℕ → K := fun n => Classical.some (h n)
    exact ⟨w, fun n => Classical.some_spec (h n)⟩
  rcases exists_seq with ⟨w, hw⟩
  have norm_tendsto : tendsto (fun n => ∥u - w n∥) at_top (nhds δ) := by
    have h : tendsto (fun n : ℕ => δ) at_top (nhds δ) := tendsto_const_nhds
    have h' : tendsto (fun n : ℕ => δ + 1 / (n + 1)) at_top (nhds δ) := by
      convert h.add tendsto_one_div_add_at_top_nhds_0_nat
      simp only [← add_zeroₓ]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h h' (fun x => δ_le _) fun x => le_of_ltₓ (hw _)
  -- Step 2: Prove that the sequence `w : ℕ → K` is a Cauchy sequence
  have seq_is_cauchy : CauchySeq fun n => (w n : F) := by
    rw [cauchy_seq_iff_le_tendsto_0]
    -- splits into three goals
    let b := fun n : ℕ => 8 * δ * (1 / (n + 1)) + 4 * (1 / (n + 1)) * (1 / (n + 1))
    use fun n => sqrt (b n)
    constructor
    -- first goal :  `∀ (n : ℕ), 0 ≤ sqrt (b n)`
    intro n
    exact sqrt_nonneg _
    constructor
    -- second goal : `∀ (n m N : ℕ), N ≤ n → N ≤ m → dist ↑(w n) ↑(w m) ≤ sqrt (b N)`
    intro p q N hp hq
    let wp := (w p : F)
    let wq := (w q : F)
    let a := u - wq
    let b := u - wp
    let half := 1 / (2 : ℝ)
    let div := 1 / ((N : ℝ) + 1)
    have : 4 * ∥u - half • (wq + wp)∥ * ∥u - half • (wq + wp)∥ + ∥wp - wq∥ * ∥wp - wq∥ = 2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) :=
      calc
        4 * ∥u - half • (wq + wp)∥ * ∥u - half • (wq + wp)∥ + ∥wp - wq∥ * ∥wp - wq∥ =
            2 * ∥u - half • (wq + wp)∥ * (2 * ∥u - half • (wq + wp)∥) + ∥wp - wq∥ * ∥wp - wq∥ :=
          by
          ring
        _ = absR (2 : ℝ) * ∥u - half • (wq + wp)∥ * (absR (2 : ℝ) * ∥u - half • (wq + wp)∥) + ∥wp - wq∥ * ∥wp - wq∥ :=
          by
          rw [_root_.abs_of_nonneg]
          exact zero_le_two
        _ = ∥(2 : ℝ) • (u - half • (wq + wp))∥ * ∥(2 : ℝ) • (u - half • (wq + wp))∥ + ∥wp - wq∥ * ∥wp - wq∥ := by
          simp [← norm_smul]
        _ = ∥a + b∥ * ∥a + b∥ + ∥a - b∥ * ∥a - b∥ := by
          rw [smul_sub, smul_smul, mul_one_div_cancel (_root_.two_ne_zero : (2 : ℝ) ≠ 0), ← one_add_one_eq_two,
            add_smul]
          simp only [← one_smul]
          have eq₁ : wp - wq = a - b := (sub_sub_sub_cancel_left _ _ _).symm
          have eq₂ : u + u - (wq + wp) = a + b
          show u + u - (wq + wp) = u - wq + (u - wp)
          abel
          rw [eq₁, eq₂]
        _ = 2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) := parallelogram_law_with_norm _ _
        
    have eq : δ ≤ ∥u - half • (wq + wp)∥ := by
      rw [smul_add]
      apply δ_le'
      apply h₂
      repeat'
        exact Subtype.mem _
      repeat'
        exact le_of_ltₓ one_half_pos
      exact add_halves 1
    have eq₁ : 4 * δ * δ ≤ 4 * ∥u - half • (wq + wp)∥ * ∥u - half • (wq + wp)∥ := by
      mono
      mono
      norm_num
      apply mul_nonneg
      norm_num
      exact norm_nonneg _
    have eq₂ : ∥a∥ * ∥a∥ ≤ (δ + div) * (δ + div) :=
      mul_self_le_mul_self (norm_nonneg _)
        (le_transₓ (le_of_ltₓ <| hw q) (add_le_add_left (Nat.one_div_le_one_div hq) _))
    have eq₂' : ∥b∥ * ∥b∥ ≤ (δ + div) * (δ + div) :=
      mul_self_le_mul_self (norm_nonneg _)
        (le_transₓ (le_of_ltₓ <| hw p) (add_le_add_left (Nat.one_div_le_one_div hp) _))
    rw [dist_eq_norm]
    apply nonneg_le_nonneg_of_sq_le_sq
    · exact sqrt_nonneg _
      
    rw [mul_self_sqrt]
    calc ∥wp - wq∥ * ∥wp - wq∥ = 2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) - 4 * ∥u - half • (wq + wp)∥ * ∥u - half • (wq + wp)∥ := by
        rw [← this]
        simp _ ≤ 2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) - 4 * δ * δ :=
        sub_le_sub_left eq₁ _ _ ≤ 2 * ((δ + div) * (δ + div) + (δ + div) * (δ + div)) - 4 * δ * δ :=
        sub_le_sub_right
          (mul_le_mul_of_nonneg_left (add_le_add eq₂ eq₂')
            (by
              norm_num))
          _ _ = 8 * δ * div + 4 * div * div :=
        by
        ring
    exact
      add_nonneg
        (mul_nonneg
          (mul_nonneg
            (by
              norm_num)
            zero_le_δ)
          (le_of_ltₓ Nat.one_div_pos_of_nat))
        (mul_nonneg
          (mul_nonneg
            (by
              norm_num)
            nat.one_div_pos_of_nat.le)
          nat.one_div_pos_of_nat.le)
    -- third goal : `tendsto (λ (n : ℕ), sqrt (b n)) at_top (𝓝 0)`
    apply tendsto.comp
    · convert continuous_sqrt.continuous_at
      exact sqrt_zero.symm
      
    have eq₁ : tendsto (fun n : ℕ => 8 * δ * (1 / (n + 1))) at_top (nhds (0 : ℝ)) := by
      convert (@tendsto_const_nhds _ _ _ (8 * δ) _).mul tendsto_one_div_add_at_top_nhds_0_nat
      simp only [← mul_zero]
    have : tendsto (fun n : ℕ => (4 : ℝ) * (1 / (n + 1))) at_top (nhds (0 : ℝ)) := by
      convert (@tendsto_const_nhds _ _ _ (4 : ℝ) _).mul tendsto_one_div_add_at_top_nhds_0_nat
      simp only [← mul_zero]
    have eq₂ : tendsto (fun n : ℕ => (4 : ℝ) * (1 / (n + 1)) * (1 / (n + 1))) at_top (nhds (0 : ℝ)) := by
      convert this.mul tendsto_one_div_add_at_top_nhds_0_nat
      simp only [← mul_zero]
    convert eq₁.add eq₂
    simp only [← add_zeroₓ]
  -- Step 3: By completeness of `K`, let `w : ℕ → K` converge to some `v : K`.
  -- Prove that it satisfies all requirements.
  rcases cauchy_seq_tendsto_of_is_complete h₁ (fun n => _) seq_is_cauchy with ⟨v, hv, w_tendsto⟩
  use v
  use hv
  have h_cont : Continuous fun v => ∥u - v∥ :=
    Continuous.comp continuous_norm (Continuous.sub continuous_const continuous_id)
  have : tendsto (fun n => ∥u - w n∥) at_top (nhds ∥u - v∥)
  convert tendsto.comp h_cont.continuous_at w_tendsto
  exact tendsto_nhds_unique this norm_tendsto
  exact Subtype.mem _

/-- Characterization of minimizers for the projection on a convex set in a real inner product
space. -/
theorem norm_eq_infi_iff_real_inner_le_zero {K : Set F} (h : Convex ℝ K) {u : F} {v : F} (hv : v ∈ K) :
    (∥u - v∥ = ⨅ w : K, ∥u - w∥) ↔ ∀, ∀ w ∈ K, ∀, ⟪u - v, w - v⟫_ℝ ≤ 0 :=
  Iff.intro
    (by
      intro eq w hw
      let δ := ⨅ w : K, ∥u - w∥
      let p := ⟪u - v, w - v⟫_ℝ
      let q := ∥w - v∥ ^ 2
      let this : Nonempty K := ⟨⟨v, hv⟩⟩
      have zero_le_δ : 0 ≤ δ
      apply le_cinfi
      intro
      exact norm_nonneg _
      have δ_le : ∀ w : K, δ ≤ ∥u - w∥
      intro w
      apply cinfi_le
      use (0 : ℝ)
      rintro _ ⟨_, rfl⟩
      exact norm_nonneg _
      have δ_le' : ∀, ∀ w ∈ K, ∀, δ ≤ ∥u - w∥ := fun w hw => δ_le ⟨w, hw⟩
      have : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → 2 * p ≤ θ * q
      intro θ hθ₁ hθ₂
      have : ∥u - v∥ ^ 2 ≤ ∥u - v∥ ^ 2 - 2 * θ * ⟪u - v, w - v⟫_ℝ + θ * θ * ∥w - v∥ ^ 2 :=
        calc
          ∥u - v∥ ^ 2 ≤ ∥u - (θ • w + (1 - θ) • v)∥ ^ 2 := by
            simp only [← sq]
            apply mul_self_le_mul_self (norm_nonneg _)
            rw [Eq]
            apply δ_le'
            apply h hw hv
            exacts[le_of_ltₓ hθ₁, sub_nonneg.2 hθ₂, add_sub_cancel'_right _ _]
          _ = ∥u - v - θ • (w - v)∥ ^ 2 := by
            have : u - (θ • w + (1 - θ) • v) = u - v - θ • (w - v) := by
              rw [smul_sub, sub_smul, one_smul]
              simp only [← sub_eq_add_neg, ← add_commₓ, ← add_left_commₓ, ← add_assocₓ, ← neg_add_rev]
            rw [this]
          _ = ∥u - v∥ ^ 2 - 2 * θ * inner (u - v) (w - v) + θ * θ * ∥w - v∥ ^ 2 := by
            rw [norm_sub_sq, inner_smul_right, norm_smul]
            simp only [← sq]
            show
              ∥u - v∥ * ∥u - v∥ - 2 * (θ * inner (u - v) (w - v)) + absR θ * ∥w - v∥ * (absR θ * ∥w - v∥) =
                ∥u - v∥ * ∥u - v∥ - 2 * θ * inner (u - v) (w - v) + θ * θ * (∥w - v∥ * ∥w - v∥)
            rw [abs_of_pos hθ₁]
            ring
          
      have eq₁ :
        ∥u - v∥ ^ 2 - 2 * θ * inner (u - v) (w - v) + θ * θ * ∥w - v∥ ^ 2 =
          ∥u - v∥ ^ 2 + (θ * θ * ∥w - v∥ ^ 2 - 2 * θ * inner (u - v) (w - v)) :=
        by
        abel
      rw [eq₁, le_add_iff_nonneg_right] at this
      have eq₂ : θ * θ * ∥w - v∥ ^ 2 - 2 * θ * inner (u - v) (w - v) = θ * (θ * ∥w - v∥ ^ 2 - 2 * inner (u - v) (w - v))
      ring
      rw [eq₂] at this
      have := le_of_sub_nonneg (nonneg_of_mul_nonneg_right this hθ₁)
      exact this
      by_cases' hq : q = 0
      · rw [hq] at this
        have : p ≤ 0
        have :=
          this (1 : ℝ)
            (by
              norm_num)
            (by
              norm_num)
        linarith
        exact this
        
      · have q_pos : 0 < q
        apply lt_of_le_of_neₓ
        exact sq_nonneg _
        intro h
        exact hq h.symm
        by_contra hp
        rw [not_leₓ] at hp
        let θ := min (1 : ℝ) (p / q)
        have eq₁ : θ * q ≤ p :=
          calc
            θ * q ≤ p / q * q := mul_le_mul_of_nonneg_right (min_le_rightₓ _ _) (sq_nonneg _)
            _ = p := div_mul_cancel _ hq
            
        have : 2 * p ≤ p :=
          calc
            2 * p ≤ θ * q := by
              refine'
                this θ
                  (lt_minₓ
                    (by
                      norm_num)
                    (div_pos hp q_pos))
                  (by
                    norm_num)
            _ ≤ p := eq₁
            
        linarith
        )
    (by
      intro h
      let this : Nonempty K := ⟨⟨v, hv⟩⟩
      apply le_antisymmₓ
      · apply le_cinfi
        intro w
        apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
        have := h w w.2
        calc ∥u - v∥ * ∥u - v∥ ≤ ∥u - v∥ * ∥u - v∥ - 2 * inner (u - v) ((w : F) - v) := by
            linarith _ ≤ ∥u - v∥ ^ 2 - 2 * inner (u - v) ((w : F) - v) + ∥(w : F) - v∥ ^ 2 := by
            rw [sq]
            refine' le_add_of_nonneg_right _
            exact sq_nonneg _ _ = ∥u - v - (w - v)∥ ^ 2 := norm_sub_sq.symm _ = ∥u - w∥ * ∥u - w∥ := by
            have : u - v - (w - v) = u - w
            abel
            rw [this, sq]
        
      · show (⨅ w : K, ∥u - w∥) ≤ (fun w : K => ∥u - w∥) ⟨v, hv⟩
        apply cinfi_le
        use 0
        rintro y ⟨z, rfl⟩
        exact norm_nonneg _
        )

variable (K : Submodule 𝕜 E)

/-- Existence of projections on complete subspaces.
Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
Then there exists a (unique) `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
This point `v` is usually called the orthogonal projection of `u` onto `K`.
-/
theorem exists_norm_eq_infi_of_complete_subspace (h : IsComplete (↑K : Set E)) :
    ∀ u : E, ∃ v ∈ K, ∥u - v∥ = ⨅ w : (K : Set E), ∥u - w∥ := by
  let this : InnerProductSpace ℝ E := InnerProductSpace.isROrCToReal 𝕜 E
  let this : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  let K' : Submodule ℝ E := Submodule.restrictScalars ℝ K
  exact exists_norm_eq_infi_of_complete_convex ⟨0, K'.zero_mem⟩ h K'.convex

/-- Characterization of minimizers in the projection on a subspace, in the real case.
Let `u` be a point in a real inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `∥u - v∥` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`).
This is superceded by `norm_eq_infi_iff_inner_eq_zero` that gives the same conclusion over
any `is_R_or_C` field.
-/
theorem norm_eq_infi_iff_real_inner_eq_zero (K : Submodule ℝ F) {u : F} {v : F} (hv : v ∈ K) :
    (∥u - v∥ = ⨅ w : (↑K : Set F), ∥u - w∥) ↔ ∀, ∀ w ∈ K, ∀, ⟪u - v, w⟫_ℝ = 0 :=
  Iff.intro
    (by
      intro h
      have h : ∀, ∀ w ∈ K, ∀, ⟪u - v, w - v⟫_ℝ ≤ 0 := by
        rwa [norm_eq_infi_iff_real_inner_le_zero] at h
        exacts[K.convex, hv]
      intro w hw
      have le : ⟪u - v, w⟫_ℝ ≤ 0
      let w' := w + v
      have : w' ∈ K := Submodule.add_mem _ hw hv
      have h₁ := h w' this
      have h₂ : w' - v = w
      simp only [← add_neg_cancel_rightₓ, ← sub_eq_add_neg]
      rw [h₂] at h₁
      exact h₁
      have ge : ⟪u - v, w⟫_ℝ ≥ 0
      let w'' := -w + v
      have : w'' ∈ K := Submodule.add_mem _ (Submodule.neg_mem _ hw) hv
      have h₁ := h w'' this
      have h₂ : w'' - v = -w
      simp only [← neg_inj, ← add_neg_cancel_rightₓ, ← sub_eq_add_neg]
      rw [h₂, inner_neg_right] at h₁
      linarith
      exact le_antisymmₓ le Ge)
    (by
      intro h
      have : ∀, ∀ w ∈ K, ∀, ⟪u - v, w - v⟫_ℝ ≤ 0
      intro w hw
      let w' := w - v
      have : w' ∈ K := Submodule.sub_mem _ hw hv
      have h₁ := h w' this
      exact le_of_eqₓ h₁
      rwa [norm_eq_infi_iff_real_inner_le_zero]
      exacts[Submodule.convex _, hv])

/-- Characterization of minimizers in the projection on a subspace.
Let `u` be a point in an inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `∥u - v∥` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`)
-/
theorem norm_eq_infi_iff_inner_eq_zero {u : E} {v : E} (hv : v ∈ K) :
    (∥u - v∥ = ⨅ w : (↑K : Set E), ∥u - w∥) ↔ ∀, ∀ w ∈ K, ∀, ⟪u - v, w⟫ = 0 := by
  let this : InnerProductSpace ℝ E := InnerProductSpace.isROrCToReal 𝕜 E
  let this : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  let K' : Submodule ℝ E := K.restrict_scalars ℝ
  constructor
  · intro H
    have A : ∀, ∀ w ∈ K, ∀, re ⟪u - v, w⟫ = 0 := (norm_eq_infi_iff_real_inner_eq_zero K' hv).1 H
    intro w hw
    apply ext
    · simp [← A w hw]
      
    · symm
      calc im (0 : 𝕜) = 0 := im.map_zero _ = re ⟪u - v, -I • w⟫ :=
          (A _ (K.smul_mem (-I) hw)).symm _ = re (-I * ⟪u - v, w⟫) := by
          rw [inner_smul_right]_ = im ⟪u - v, w⟫ := by
          simp
      
    
  · intro H
    have : ∀, ∀ w ∈ K', ∀, ⟪u - v, w⟫_ℝ = 0 := by
      intro w hw
      rw [real_inner_eq_re_inner, H w hw]
      exact zero_re'
    exact (norm_eq_infi_iff_real_inner_eq_zero K' hv).2 this
    

section orthogonalProjection

variable [CompleteSpace K]

/-- The orthogonal projection onto a complete subspace, as an
unbundled function.  This definition is only intended for use in
setting up the bundled version `orthogonal_projection` and should not
be used once that is defined. -/
def orthogonalProjectionFn (v : E) :=
  (exists_norm_eq_infi_of_complete_subspace K (complete_space_coe_iff_is_complete.mp ‹_›) v).some

variable {K}

/-- The unbundled orthogonal projection is in the given subspace.
This lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
theorem orthogonal_projection_fn_mem (v : E) : orthogonalProjectionFn K v ∈ K :=
  (exists_norm_eq_infi_of_complete_subspace K (complete_space_coe_iff_is_complete.mp ‹_›) v).some_spec.some

/-- The characterization of the unbundled orthogonal projection.  This
lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
theorem orthogonal_projection_fn_inner_eq_zero (v : E) : ∀, ∀ w ∈ K, ∀, ⟪v - orthogonalProjectionFn K v, w⟫ = 0 := by
  rw [← norm_eq_infi_iff_inner_eq_zero K (orthogonal_projection_fn_mem v)]
  exact (exists_norm_eq_infi_of_complete_subspace K (complete_space_coe_iff_is_complete.mp ‹_›) v).some_spec.some_spec

/-- The unbundled orthogonal projection is the unique point in `K`
with the orthogonality property.  This lemma is only intended for use
in setting up the bundled version and should not be used once that is
defined. -/
theorem eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero {u v : E} (hvm : v ∈ K)
    (hvo : ∀, ∀ w ∈ K, ∀, ⟪u - v, w⟫ = 0) : orthogonalProjectionFn K u = v := by
  rw [← sub_eq_zero, ← inner_self_eq_zero]
  have hvs : orthogonalProjectionFn K u - v ∈ K := Submodule.sub_mem K (orthogonal_projection_fn_mem u) hvm
  have huo : ⟪u - orthogonalProjectionFn K u, orthogonalProjectionFn K u - v⟫ = 0 :=
    orthogonal_projection_fn_inner_eq_zero u _ hvs
  have huv : ⟪u - v, orthogonalProjectionFn K u - v⟫ = 0 := hvo _ hvs
  have houv : ⟪u - v - (u - orthogonalProjectionFn K u), orthogonalProjectionFn K u - v⟫ = 0 := by
    rw [inner_sub_left, huo, huv, sub_zero]
  rwa [sub_sub_sub_cancel_left] at houv

variable (K)

theorem orthogonal_projection_fn_norm_sq (v : E) :
    ∥v∥ * ∥v∥ =
      ∥v - orthogonalProjectionFn K v∥ * ∥v - orthogonalProjectionFn K v∥ +
        ∥orthogonalProjectionFn K v∥ * ∥orthogonalProjectionFn K v∥ :=
  by
  set p := orthogonalProjectionFn K v
  have h' : ⟪v - p, p⟫ = 0 := orthogonal_projection_fn_inner_eq_zero _ _ (orthogonal_projection_fn_mem v)
  convert norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v - p) p h' using 2 <;> simp

/-- The orthogonal projection onto a complete subspace. -/
def orthogonalProjection : E →L[𝕜] K :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨orthogonalProjectionFn K v, orthogonal_projection_fn_mem v⟩,
      map_add' := fun x y => by
        have hm : orthogonalProjectionFn K x + orthogonalProjectionFn K y ∈ K :=
          Submodule.add_mem K (orthogonal_projection_fn_mem x) (orthogonal_projection_fn_mem y)
        have ho : ∀, ∀ w ∈ K, ∀, ⟪x + y - (orthogonalProjectionFn K x + orthogonalProjectionFn K y), w⟫ = 0 := by
          intro w hw
          rw [add_sub_add_comm, inner_add_left, orthogonal_projection_fn_inner_eq_zero _ w hw,
            orthogonal_projection_fn_inner_eq_zero _ w hw, add_zeroₓ]
        ext
        simp [← eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hm ho],
      map_smul' := fun c x => by
        have hm : c • orthogonalProjectionFn K x ∈ K := Submodule.smul_mem K _ (orthogonal_projection_fn_mem x)
        have ho : ∀, ∀ w ∈ K, ∀, ⟪c • x - c • orthogonalProjectionFn K x, w⟫ = 0 := by
          intro w hw
          rw [← smul_sub, inner_smul_left, orthogonal_projection_fn_inner_eq_zero _ w hw, mul_zero]
        ext
        simp [← eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hm ho] }
    1 fun x => by
    simp only [← one_mulₓ, ← LinearMap.coe_mk]
    refine'
      le_of_pow_le_pow 2 (norm_nonneg _)
        (by
          norm_num)
        _
    change ∥orthogonalProjectionFn K x∥ ^ 2 ≤ ∥x∥ ^ 2
    nlinarith [orthogonal_projection_fn_norm_sq K x]

variable {K}

@[simp]
theorem orthogonal_projection_fn_eq (v : E) : orthogonalProjectionFn K v = (orthogonalProjection K v : E) :=
  rfl

/-- The characterization of the orthogonal projection.  -/
@[simp]
theorem orthogonal_projection_inner_eq_zero (v : E) : ∀, ∀ w ∈ K, ∀, ⟪v - orthogonalProjection K v, w⟫ = 0 :=
  orthogonal_projection_fn_inner_eq_zero v

/-- The difference of `v` from its orthogonal projection onto `K` is in `Kᗮ`.  -/
@[simp]
theorem sub_orthogonal_projection_mem_orthogonal (v : E) : v - orthogonalProjection K v ∈ Kᗮ := by
  intro w hw
  rw [inner_eq_zero_sym]
  exact orthogonal_projection_inner_eq_zero _ _ hw

/-- The orthogonal projection is the unique point in `K` with the
orthogonality property. -/
theorem eq_orthogonal_projection_of_mem_of_inner_eq_zero {u v : E} (hvm : v ∈ K) (hvo : ∀, ∀ w ∈ K, ∀, ⟪u - v, w⟫ = 0) :
    (orthogonalProjection K u : E) = v :=
  eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hvm hvo

/-- The orthogonal projections onto equal subspaces are coerced back to the same point in `E`. -/
theorem eq_orthogonal_projection_of_eq_submodule {K' : Submodule 𝕜 E} [CompleteSpace K'] (h : K = K') (u : E) :
    (orthogonalProjection K u : E) = (orthogonalProjection K' u : E) := by
  change orthogonalProjectionFn K u = orthogonalProjectionFn K' u
  congr
  exact h

/-- The orthogonal projection sends elements of `K` to themselves. -/
@[simp]
theorem orthogonal_projection_mem_subspace_eq_self (v : K) : orthogonalProjection K v = v := by
  ext
  apply eq_orthogonal_projection_of_mem_of_inner_eq_zero <;> simp

/-- A point equals its orthogonal projection if and only if it lies in the subspace. -/
theorem orthogonal_projection_eq_self_iff {v : E} : (orthogonalProjection K v : E) = v ↔ v ∈ K := by
  refine' ⟨fun h => _, fun h => eq_orthogonal_projection_of_mem_of_inner_eq_zero h _⟩
  · rw [← h]
    simp
    
  · simp
    

theorem LinearIsometry.map_orthogonal_projection {E E' : Type _} [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E']
    (f : E →ₗᵢ[𝕜] E') (p : Submodule 𝕜 E) [CompleteSpace p] (x : E) :
    f (orthogonalProjection p x) = orthogonalProjection (p.map f.toLinearMap) (f x) := by
  refine' ((eq_orthogonal_projection_of_mem_of_inner_eq_zero (Submodule.apply_coe_mem_map _ _)) fun y hy => _).symm
  rcases hy with ⟨x', hx', rfl : f x' = y⟩
  rw [f.coe_to_linear_map, ← f.map_sub, f.inner_map_map, orthogonal_projection_inner_eq_zero x x' hx']

/-- Orthogonal projection onto the `submodule.map` of a subspace. -/
theorem orthogonal_projection_map_apply {E E' : Type _} [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E']
    (f : E ≃ₗᵢ[𝕜] E') (p : Submodule 𝕜 E) [CompleteSpace p] (x : E') :
    (orthogonalProjection (p.map (f.toLinearEquiv : E →ₗ[𝕜] E')) x : E') = f (orthogonalProjection p (f.symm x)) := by
  simpa only [← f.coe_to_linear_isometry, ← f.apply_symm_apply] using
    (f.to_linear_isometry.map_orthogonal_projection p (f.symm x)).symm

/-- The orthogonal projection onto the trivial submodule is the zero map. -/
@[simp]
theorem orthogonal_projection_bot : orthogonalProjection (⊥ : Submodule 𝕜 E) = 0 := by
  ext

variable (K)

/-- The orthogonal projection has norm `≤ 1`. -/
theorem orthogonal_projection_norm_le : ∥orthogonalProjection K∥ ≤ 1 :=
  LinearMap.mk_continuous_norm_le _
    (by
      norm_num)
    _

variable (𝕜)

theorem smul_orthogonal_projection_singleton {v : E} (w : E) :
    (∥v∥ ^ 2 : 𝕜) • (orthogonalProjection (𝕜∙v) w : E) = ⟪v, w⟫ • v := by
  suffices ↑(orthogonalProjection (𝕜∙v) ((∥v∥ ^ 2 : 𝕜) • w)) = ⟪v, w⟫ • v by
    simpa using this
  apply eq_orthogonal_projection_of_mem_of_inner_eq_zero
  · rw [Submodule.mem_span_singleton]
    use ⟪v, w⟫
    
  · intro x hx
    obtain ⟨c, rfl⟩ := submodule.mem_span_singleton.mp hx
    have hv : ↑∥v∥ ^ 2 = ⟪v, v⟫ := by
      norm_cast
      simp [← norm_sq_eq_inner]
    simp [← inner_sub_left, ← inner_smul_left, ← inner_smul_right, ← RingEquiv.map_div, ← mul_comm, ← hv, ←
      InnerProductSpace.conj_sym, ← hv]
    

/-- Formula for orthogonal projection onto a single vector. -/
theorem orthogonal_projection_singleton {v : E} (w : E) : (orthogonalProjection (𝕜∙v) w : E) = (⟪v, w⟫ / ∥v∥ ^ 2) • v :=
  by
  by_cases' hv : v = 0
  · rw [hv, eq_orthogonal_projection_of_eq_submodule (Submodule.span_zero_singleton 𝕜)]
    · simp
      
    · infer_instance
      
    
  have hv' : ∥v∥ ≠ 0 := ne_of_gtₓ (norm_pos_iff.mpr hv)
  have key : ((∥v∥ ^ 2 : 𝕜)⁻¹ * ∥v∥ ^ 2) • ↑(orthogonalProjection (𝕜∙v) w) = ((∥v∥ ^ 2 : 𝕜)⁻¹ * ⟪v, w⟫) • v := by
    simp [← mul_smul, ← smul_orthogonal_projection_singleton 𝕜 w]
  convert key <;> field_simp [← hv']

/-- Formula for orthogonal projection onto a single unit vector. -/
theorem orthogonal_projection_unit_singleton {v : E} (hv : ∥v∥ = 1) (w : E) :
    (orthogonalProjection (𝕜∙v) w : E) = ⟪v, w⟫ • v := by
  rw [← smul_orthogonal_projection_singleton 𝕜 w]
  simp [← hv]

end orthogonalProjection

section reflection

variable {𝕜} (K) [CompleteSpace K]

/-- Auxiliary definition for `reflection`: the reflection as a linear equivalence. -/
def reflectionLinearEquiv : E ≃ₗ[𝕜] E :=
  LinearEquiv.ofInvolutive (bit0 (K.Subtype.comp (orthogonalProjection K).toLinearMap) - LinearMap.id) fun x => by
    simp [← bit0]

/-- Reflection in a complete subspace of an inner product space.  The word "reflection" is
sometimes understood to mean specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point.  The definition here, of
reflection in a subspace, is a more general sense of the word that includes both those common
cases. -/
def reflection : E ≃ₗᵢ[𝕜] E :=
  { reflectionLinearEquiv K with
    norm_map' := by
      intro x
      let w : K := orthogonalProjection K x
      let v := x - w
      have : ⟪v, w⟫ = 0 := orthogonal_projection_inner_eq_zero x w w.2
      convert norm_sub_eq_norm_add this using 2
      · rw [LinearEquiv.coe_mk, reflectionLinearEquiv, LinearEquiv.to_fun_eq_coe, LinearEquiv.coe_of_involutive,
          LinearMap.sub_apply, LinearMap.id_apply, bit0, LinearMap.add_apply, LinearMap.comp_apply,
          Submodule.subtype_apply, ContinuousLinearMap.to_linear_map_eq_coe, ContinuousLinearMap.coe_coe]
        dsimp' [← w, ← v]
        abel
        
      · simp only [← add_sub_cancel'_right, ← eq_self_iff_true]
         }

variable {K}

/-- The result of reflecting. -/
theorem reflection_apply (p : E) : reflection K p = bit0 ↑(orthogonalProjection K p) - p :=
  rfl

/-- Reflection is its own inverse. -/
@[simp]
theorem reflection_symm : (reflection K).symm = reflection K :=
  rfl

/-- Reflection is its own inverse. -/
@[simp]
theorem reflection_inv : (reflection K)⁻¹ = reflection K :=
  rfl

variable (K)

/-- Reflecting twice in the same subspace. -/
@[simp]
theorem reflection_reflection (p : E) : reflection K (reflection K p) = p :=
  (reflection K).left_inv p

/-- Reflection is involutive. -/
theorem reflection_involutive : Function.Involutive (reflection K) :=
  reflection_reflection K

/-- Reflection is involutive. -/
@[simp]
theorem reflection_trans_reflection : (reflection K).trans (reflection K) = LinearIsometryEquiv.refl 𝕜 E :=
  LinearIsometryEquiv.ext <| reflection_involutive K

/-- Reflection is involutive. -/
@[simp]
theorem reflection_mul_reflection : reflection K * reflection K = 1 :=
  reflection_trans_reflection _

variable {K}

/-- A point is its own reflection if and only if it is in the subspace. -/
theorem reflection_eq_self_iff (x : E) : reflection K x = x ↔ x ∈ K := by
  rw [← orthogonal_projection_eq_self_iff, reflection_apply, sub_eq_iff_eq_add', ← two_smul 𝕜, ← two_smul' 𝕜]
  refine' (smul_right_injective E _).eq_iff
  exact two_ne_zero

theorem reflection_mem_subspace_eq_self {x : E} (hx : x ∈ K) : reflection K x = x :=
  (reflection_eq_self_iff x).mpr hx

/-- Reflection in the `submodule.map` of a subspace. -/
theorem reflection_map_apply {E E' : Type _} [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E')
    (K : Submodule 𝕜 E) [CompleteSpace K] (x : E') :
    reflection (K.map (f.toLinearEquiv : E →ₗ[𝕜] E')) x = f (reflection K (f.symm x)) := by
  simp [← bit0, ← reflection_apply, ← orthogonal_projection_map_apply f K x]

/-- Reflection in the `submodule.map` of a subspace. -/
theorem reflection_map {E E' : Type _} [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E')
    (K : Submodule 𝕜 E) [CompleteSpace K] :
    reflection (K.map (f.toLinearEquiv : E →ₗ[𝕜] E')) = f.symm.trans ((reflection K).trans f) :=
  LinearIsometryEquiv.ext <| reflection_map_apply f K

/-- Reflection through the trivial subspace {0} is just negation. -/
@[simp]
theorem reflection_bot : reflection (⊥ : Submodule 𝕜 E) = LinearIsometryEquiv.neg 𝕜 := by
  ext <;> simp [← reflection_apply]

end reflection

section Orthogonal

/-- If `K₁` is complete and contained in `K₂`, `K₁` and `K₁ᗮ ⊓ K₂` span `K₂`. -/
theorem Submodule.sup_orthogonal_inf_of_complete_space {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) [CompleteSpace K₁] :
    K₁⊔K₁ᗮ⊓K₂ = K₂ := by
  ext x
  rw [Submodule.mem_sup]
  let v : K₁ := orthogonalProjection K₁ x
  have hvm : x - v ∈ K₁ᗮ := sub_orthogonal_projection_mem_orthogonal x
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact K₂.add_mem (h hy) hz.2
    
  · exact fun hx => ⟨v, v.prop, x - v, ⟨hvm, K₂.sub_mem hx (h v.prop)⟩, add_sub_cancel'_right _ _⟩
    

variable {K}

/-- If `K` is complete, `K` and `Kᗮ` span the whole space. -/
theorem Submodule.sup_orthogonal_of_complete_space [CompleteSpace K] : K⊔Kᗮ = ⊤ := by
  convert Submodule.sup_orthogonal_inf_of_complete_space (le_top : K ≤ ⊤)
  simp

variable (K)

/-- If `K` is complete, any `v` in `E` can be expressed as a sum of elements of `K` and `Kᗮ`. -/
theorem Submodule.exists_sum_mem_mem_orthogonal [CompleteSpace K] (v : E) : ∃ y ∈ K, ∃ z ∈ Kᗮ, v = y + z := by
  have h_mem : v ∈ K⊔Kᗮ := by
    simp [← Submodule.sup_orthogonal_of_complete_space]
  obtain ⟨y, hy, z, hz, hyz⟩ := submodule.mem_sup.mp h_mem
  exact ⟨y, hy, z, hz, hyz.symm⟩

/-- If `K` is complete, then the orthogonal complement of its orthogonal complement is itself. -/
@[simp]
theorem Submodule.orthogonal_orthogonal [CompleteSpace K] : Kᗮᗮ = K := by
  ext v
  constructor
  · obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_sum_mem_mem_orthogonal v
    intro hv
    have hz' : z = 0 := by
      have hyz : ⟪z, y⟫ = 0 := by
        simp [← hz y hy, ← inner_eq_zero_sym]
      simpa [← inner_add_right, ← hyz] using hv z hz
    simp [← hy, ← hz']
    
  · intro hv w hw
    rw [inner_eq_zero_sym]
    exact hw v hv
    

theorem Submodule.orthogonal_orthogonal_eq_closure [CompleteSpace E] : Kᗮᗮ = K.topologicalClosure := by
  refine' le_antisymmₓ _ _
  · convert Submodule.orthogonal_orthogonal_monotone K.submodule_topological_closure
    have : CompleteSpace K.topological_closure := K.is_closed_topological_closure.complete_space_coe
    rw [K.topological_closure.orthogonal_orthogonal]
    
  · exact K.topological_closure_minimal K.le_orthogonal_orthogonal Kᗮ.is_closed_orthogonal
    

variable {K}

/-- If `K` is complete, `K` and `Kᗮ` are complements of each other. -/
theorem Submodule.is_compl_orthogonal_of_complete_space [CompleteSpace K] : IsCompl K Kᗮ :=
  ⟨K.orthogonal_disjoint, le_of_eqₓ Submodule.sup_orthogonal_of_complete_space.symm⟩

@[simp]
theorem Submodule.orthogonal_eq_bot_iff [CompleteSpace (K : Set E)] : Kᗮ = ⊥ ↔ K = ⊤ := by
  refine'
    ⟨_, fun h => by
      rw [h, Submodule.top_orthogonal_eq_bot]⟩
  intro h
  have : K⊔Kᗮ = ⊤ := Submodule.sup_orthogonal_of_complete_space
  rwa [h, sup_comm, bot_sup_eq] at this

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
theorem eq_orthogonal_projection_of_mem_orthogonal [CompleteSpace K] {u v : E} (hv : v ∈ K) (hvo : u - v ∈ Kᗮ) :
    (orthogonalProjection K u : E) = v :=
  eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hv fun w => inner_eq_zero_sym.mp ∘ hvo w

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
theorem eq_orthogonal_projection_of_mem_orthogonal' [CompleteSpace K] {u v z : E} (hv : v ∈ K) (hz : z ∈ Kᗮ)
    (hu : u = v + z) : (orthogonalProjection K u : E) = v :=
  eq_orthogonal_projection_of_mem_orthogonal hv
    (by
      simpa [← hu] )

/-- The orthogonal projection onto `K` of an element of `Kᗮ` is zero. -/
theorem orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero [CompleteSpace K] {v : E} (hv : v ∈ Kᗮ) :
    orthogonalProjection K v = 0 := by
  ext
  convert eq_orthogonal_projection_of_mem_orthogonal _ _ <;> simp [← hv]

/-- The reflection in `K` of an element of `Kᗮ` is its negation. -/
theorem reflection_mem_subspace_orthogonal_complement_eq_neg [CompleteSpace K] {v : E} (hv : v ∈ Kᗮ) :
    reflection K v = -v := by
  simp [← reflection_apply, ← orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hv]

/-- The orthogonal projection onto `Kᗮ` of an element of `K` is zero. -/
theorem orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero [CompleteSpace E] {v : E} (hv : v ∈ K) :
    orthogonalProjection Kᗮ v = 0 :=
  orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero (K.le_orthogonal_orthogonal hv)

/-- The orthogonal complement satisfies `Kᗮᗮᗮ = Kᗮ`. -/
theorem Submodule.triorthogonal_eq_orthogonal [CompleteSpace E] : Kᗮᗮᗮ = Kᗮ := by
  rw [Kᗮ.orthogonal_orthogonal_eq_closure]
  exact K.is_closed_orthogonal.submodule_topological_closure_eq

/-- The closure of `K` is the full space iff `Kᗮ` is trivial. -/
theorem Submodule.topological_closure_eq_top_iff [CompleteSpace E] : K.topologicalClosure = ⊤ ↔ Kᗮ = ⊥ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  constructor <;> intro h
  · rw [← Submodule.triorthogonal_eq_orthogonal, h, Submodule.top_orthogonal_eq_bot]
    
  · rw [h, Submodule.bot_orthogonal_eq_top]
    

/-- The reflection in `Kᗮ` of an element of `K` is its negation. -/
theorem reflection_mem_subspace_orthogonal_precomplement_eq_neg [CompleteSpace E] {v : E} (hv : v ∈ K) :
    reflection Kᗮ v = -v :=
  reflection_mem_subspace_orthogonal_complement_eq_neg (K.le_orthogonal_orthogonal hv)

/-- The orthogonal projection onto `(𝕜 ∙ v)ᗮ` of `v` is zero. -/
theorem orthogonal_projection_orthogonal_complement_singleton_eq_zero [CompleteSpace E] (v : E) :
    orthogonalProjection (𝕜∙v)ᗮ v = 0 :=
  orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero (Submodule.mem_span_singleton_self v)

/-- The reflection in `(𝕜 ∙ v)ᗮ` of `v` is `-v`. -/
theorem reflection_orthogonal_complement_singleton_eq_neg [CompleteSpace E] (v : E) : reflection (𝕜∙v)ᗮ v = -v :=
  reflection_mem_subspace_orthogonal_precomplement_eq_neg (Submodule.mem_span_singleton_self v)

theorem reflection_sub [CompleteSpace F] {v w : F} (h : ∥v∥ = ∥w∥) : reflection (ℝ∙v - w)ᗮ v = w := by
  set R : F ≃ₗᵢ[ℝ] F := reflection (ℝ∙v - w)ᗮ
  suffices R v + R v = w + w by
    apply
      smul_right_injective F
        (by
          norm_num : (2 : ℝ) ≠ 0)
    simpa [← two_smul] using this
  have h₁ : R (v - w) = -(v - w) := reflection_orthogonal_complement_singleton_eq_neg (v - w)
  have h₂ : R (v + w) = v + w := by
    apply reflection_mem_subspace_eq_self
    apply mem_orthogonal_singleton_of_inner_left
    rw [real_inner_add_sub_eq_zero_iff]
    exact h
  convert congr_arg2ₓ (· + ·) h₂ h₁ using 1
  · simp
    
  · abel
    

variable (K)

/-- In a complete space `E`, a vector splits as the sum of its orthogonal projections onto a
complete submodule `K` and onto the orthogonal complement of `K`.-/
theorem eq_sum_orthogonal_projection_self_orthogonal_complement [CompleteSpace E] [CompleteSpace K] (w : E) :
    w = (orthogonalProjection K w : E) + (orthogonalProjection Kᗮ w : E) := by
  obtain ⟨y, hy, z, hz, hwyz⟩ := K.exists_sum_mem_mem_orthogonal w
  convert hwyz
  · exact eq_orthogonal_projection_of_mem_orthogonal' hy hz hwyz
    
  · rw [add_commₓ] at hwyz
    refine' eq_orthogonal_projection_of_mem_orthogonal' hz _ hwyz
    simp [← hy]
    

/-- The Pythagorean theorem, for an orthogonal projection.-/
theorem norm_sq_eq_add_norm_sq_projection (x : E) (S : Submodule 𝕜 E) [CompleteSpace E] [CompleteSpace S] :
    ∥x∥ ^ 2 = ∥orthogonalProjection S x∥ ^ 2 + ∥orthogonalProjection Sᗮ x∥ ^ 2 := by
  let p1 := orthogonalProjection S
  let p2 := orthogonalProjection Sᗮ
  have x_decomp : x = p1 x + p2 x := eq_sum_orthogonal_projection_self_orthogonal_complement S x
  have x_orth : ⟪p1 x, p2 x⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (SetLike.coe_mem (p1 x)) (SetLike.coe_mem (p2 x))
  nth_rw 0[x_decomp]
  simp only [← sq, ← norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (p1 x : E) (p2 x) x_orth, ← add_left_injₓ, ←
    mul_eq_mul_left_iff, ← norm_eq_zero, ← true_orₓ, ← eq_self_iff_true, ← Submodule.coe_norm, ← Submodule.coe_eq_zero]

/-- In a complete space `E`, the projection maps onto a complete subspace `K` and its orthogonal
complement sum to the identity. -/
theorem id_eq_sum_orthogonal_projection_self_orthogonal_complement [CompleteSpace E] [CompleteSpace K] :
    ContinuousLinearMap.id 𝕜 E =
      K.subtypeL.comp (orthogonalProjection K) + Kᗮ.subtypeL.comp (orthogonalProjection Kᗮ) :=
  by
  ext w
  exact eq_sum_orthogonal_projection_self_orthogonal_complement K w

/-- The orthogonal projection is self-adjoint. -/
theorem inner_orthogonal_projection_left_eq_right [CompleteSpace E] [CompleteSpace K] (u v : E) :
    ⟪↑(orthogonalProjection K u), v⟫ = ⟪u, orthogonalProjection K v⟫ := by
  nth_rw 0[eq_sum_orthogonal_projection_self_orthogonal_complement K v]
  nth_rw 1[eq_sum_orthogonal_projection_self_orthogonal_complement K u]
  rw [inner_add_left, inner_add_right,
    Submodule.inner_right_of_mem_orthogonal (Submodule.coe_mem (orthogonalProjection K u))
      (Submodule.coe_mem (orthogonalProjection Kᗮ v)),
    Submodule.inner_left_of_mem_orthogonal (Submodule.coe_mem (orthogonalProjection K v))
      (Submodule.coe_mem (orthogonalProjection Kᗮ u))]

open FiniteDimensional

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
containined in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
theorem Submodule.finrank_add_inf_finrank_orthogonal {K₁ K₂ : Submodule 𝕜 E} [FiniteDimensional 𝕜 K₂] (h : K₁ ≤ K₂) :
    finrank 𝕜 K₁ + finrank 𝕜 (K₁ᗮ⊓K₂ : Submodule 𝕜 E) = finrank 𝕜 K₂ := by
  have := Submodule.finite_dimensional_of_le h
  have := proper_is_R_or_C 𝕜 K₁
  have hd := Submodule.dim_sup_add_dim_inf_eq K₁ (K₁ᗮ⊓K₂)
  rw [← inf_assoc, (Submodule.orthogonal_disjoint K₁).eq_bot, bot_inf_eq, finrank_bot,
    Submodule.sup_orthogonal_inf_of_complete_space h] at hd
  rw [add_zeroₓ] at hd
  exact hd.symm

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
containined in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
theorem Submodule.finrank_add_inf_finrank_orthogonal' {K₁ K₂ : Submodule 𝕜 E} [FiniteDimensional 𝕜 K₂] (h : K₁ ≤ K₂)
    {n : ℕ} (h_dim : finrank 𝕜 K₁ + n = finrank 𝕜 K₂) : finrank 𝕜 (K₁ᗮ⊓K₂ : Submodule 𝕜 E) = n := by
  rw [← add_right_injₓ (finrank 𝕜 K₁)]
  simp [← Submodule.finrank_add_inf_finrank_orthogonal h, ← h_dim]

/-- Given a finite-dimensional space `E` and subspace `K`, the dimensions of `K` and `Kᗮ` add to
that of `E`. -/
theorem Submodule.finrank_add_finrank_orthogonal [FiniteDimensional 𝕜 E] (K : Submodule 𝕜 E) :
    finrank 𝕜 K + finrank 𝕜 Kᗮ = finrank 𝕜 E := by
  convert Submodule.finrank_add_inf_finrank_orthogonal (le_top : K ≤ ⊤) using 1
  · rw [inf_top_eq]
    
  · simp
    

/-- Given a finite-dimensional space `E` and subspace `K`, the dimensions of `K` and `Kᗮ` add to
that of `E`. -/
theorem Submodule.finrank_add_finrank_orthogonal' [FiniteDimensional 𝕜 E] {K : Submodule 𝕜 E} {n : ℕ}
    (h_dim : finrank 𝕜 K + n = finrank 𝕜 E) : finrank 𝕜 Kᗮ = n := by
  rw [← add_right_injₓ (finrank 𝕜 K)]
  simp [← Submodule.finrank_add_finrank_orthogonal, ← h_dim]

attribute [local instance] fact_finite_dimensional_of_finrank_eq_succ

/-- In a finite-dimensional inner product space, the dimension of the orthogonal complement of the
span of a nonzero vector is one less than the dimension of the space. -/
theorem finrank_orthogonal_span_singleton {n : ℕ} [_i : Fact (finrank 𝕜 E = n + 1)] {v : E} (hv : v ≠ 0) :
    finrank 𝕜 (𝕜∙v)ᗮ = n :=
  Submodule.finrank_add_finrank_orthogonal' <| by
    simp [← finrank_span_singleton hv, ← _i.elim, ← add_commₓ]

/-- An element `φ` of the orthogonal group of `F` can be factored as a product of reflections, and
specifically at most as many reflections as the dimension of the complement of the fixed subspace
of `φ`. -/
theorem LinearIsometryEquiv.reflections_generate_dim_aux [FiniteDimensional ℝ F] {n : ℕ} (φ : F ≃ₗᵢ[ℝ] F)
    (hn : finrank ℝ (ContinuousLinearMap.id ℝ F - φ.toContinuousLinearEquiv).kerᗮ ≤ n) :
    ∃ l : List F, l.length ≤ n ∧ φ = (l.map fun v => reflection (ℝ∙v)ᗮ).Prod := by
  -- We prove this by strong induction on `n`, the dimension of the orthogonal complement of the
  -- fixed subspace of the endomorphism `φ`
  induction' n with n IH generalizing φ
  · -- Base case: `n = 0`, the fixed subspace is the whole space, so `φ = id`
    refine' ⟨[], rfl.le, show φ = 1 from _⟩
    have : (ContinuousLinearMap.id ℝ F - φ.to_continuous_linear_equiv).ker = ⊤ := by
      rwa [Nat.le_zero_iffₓ, finrank_eq_zero, Submodule.orthogonal_eq_bot_iff] at hn
    symm
    ext x
    have := LinearMap.congr_fun (linear_map.ker_eq_top.mp this) x
    rwa [ContinuousLinearMap.coe_sub, LinearMap.zero_apply, LinearMap.sub_apply, sub_eq_zero] at this
    
  · -- Inductive step.  Let `W` be the fixed subspace of `φ`.  We suppose its complement to have
    -- dimension at most n + 1.
    let W := (ContinuousLinearMap.id ℝ F - φ.to_continuous_linear_equiv).ker
    have hW : ∀, ∀ w ∈ W, ∀, φ w = w := fun w hw => (sub_eq_zero.mp hw).symm
    by_cases' hn' : finrank ℝ Wᗮ ≤ n
    · obtain ⟨V, hV₁, hV₂⟩ := IH φ hn'
      exact ⟨V, hV₁.trans n.le_succ, hV₂⟩
      
    -- Take a nonzero element `v` of the orthogonal complement of `W`.
    have : Nontrivial Wᗮ :=
      nontrivial_of_finrank_pos
        (by
          linarith [zero_le n] : 0 < finrank ℝ Wᗮ)
    obtain ⟨v, hv⟩ := exists_ne (0 : Wᗮ)
    have hφv : φ v ∈ Wᗮ := by
      intro w hw
      rw [← hW w hw, LinearIsometryEquiv.inner_map_map]
      exact v.prop w hw
    have hv' : (v : F) ∉ W := by
      intro h
      exact hv ((Submodule.mem_left_iff_eq_zero_of_disjoint W.orthogonal_disjoint).mp h)
    -- Let `ρ` be the reflection in `v - φ v`; this is designed to swap `v` and `φ v`
    let x : F := v - φ v
    let ρ := reflection (ℝ∙x)ᗮ
    -- Notation: Let `V` be the fixed subspace of `φ.trans ρ`
    let V := (ContinuousLinearMap.id ℝ F - (φ.trans ρ).toContinuousLinearEquiv).ker
    have hV : ∀ w, ρ (φ w) = w → w ∈ V := by
      intro w hw
      change w - ρ (φ w) = 0
      rw [sub_eq_zero, hw]
    -- Everything fixed by `φ` is fixed by `φ.trans ρ`
    have H₂V : W ≤ V := by
      intro w hw
      apply hV
      rw [hW w hw]
      refine' reflection_mem_subspace_eq_self _
      apply mem_orthogonal_singleton_of_inner_left
      exact Submodule.sub_mem _ v.prop hφv _ hw
    -- `v` is also fixed by `φ.trans ρ`
    have H₁V : (v : F) ∈ V := by
      apply hV
      have : ρ v = φ v := reflection_sub (φ.norm_map v).symm
      rw [← this]
      exact reflection_reflection _ _
    -- By dimension-counting, the complement of the fixed subspace of `φ.trans ρ` has dimension at
    -- most `n`
    have : finrank ℝ Vᗮ ≤ n := by
      change finrank ℝ Wᗮ ≤ n + 1 at hn
      have : finrank ℝ W + 1 ≤ finrank ℝ V :=
        Submodule.finrank_lt_finrank_of_lt (SetLike.lt_iff_le_and_exists.2 ⟨H₂V, v, H₁V, hv'⟩)
      have : finrank ℝ V + finrank ℝ Vᗮ = finrank ℝ F := V.finrank_add_finrank_orthogonal
      have : finrank ℝ W + finrank ℝ Wᗮ = finrank ℝ F := W.finrank_add_finrank_orthogonal
      linarith
    -- So apply the inductive hypothesis to `φ.trans ρ`
    obtain ⟨l, hl, hφl⟩ := IH (ρ * φ) this
    -- Prepend `ρ` to the factorization into reflections obtained for `φ.trans ρ`; this gives a
    -- factorization into reflections for `φ`.
    refine' ⟨x :: l, Nat.succ_le_succₓ hl, _⟩
    rw [List.map_cons, List.prod_cons]
    have := congr_arg ((· * ·) ρ) hφl
    rwa [← mul_assoc, reflection_mul_reflection, one_mulₓ] at this
    

/-- The orthogonal group of `F` is generated by reflections; specifically each element `φ` of the
orthogonal group is a product of at most as many reflections as the dimension of `F`.

Special case of the **Cartan–Dieudonné theorem**. -/
theorem LinearIsometryEquiv.reflections_generate_dim [FiniteDimensional ℝ F] (φ : F ≃ₗᵢ[ℝ] F) :
    ∃ l : List F, l.length ≤ finrank ℝ F ∧ φ = (l.map fun v => reflection (ℝ∙v)ᗮ).Prod :=
  let ⟨l, hl₁, hl₂⟩ := φ.reflections_generate_dim_aux le_rfl
  ⟨l, hl₁.trans (Submodule.finrank_le _), hl₂⟩

/-- The orthogonal group of `F` is generated by reflections. -/
theorem LinearIsometryEquiv.reflections_generate [FiniteDimensional ℝ F] :
    Subgroup.closure (Set.Range fun v : F => reflection (ℝ∙v)ᗮ) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro φ
  rcases φ.reflections_generate_dim with ⟨l, _, rfl⟩
  apply (Subgroup.closure _).list_prod_mem
  intro x hx
  rcases list.mem_map.mp hx with ⟨a, _, hax⟩
  exact Subgroup.subset_closure ⟨a, hax⟩

end Orthogonal

section OrthogonalFamily

variable {ι : Type _}

/-- An orthogonal family of subspaces of `E` satisfies `direct_sum.is_internal` (that is,
they provide an internal direct sum decomposition of `E`) if and only if their span has trivial
orthogonal complement. -/
theorem OrthogonalFamily.is_internal_iff_of_is_complete [DecidableEq ι] {V : ι → Submodule 𝕜 E}
    (hV : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ) (hc : IsComplete (↑(supr V) : Set E)) :
    DirectSum.IsInternal V ↔ (supr V)ᗮ = ⊥ := by
  have : CompleteSpace ↥(supr V) := hc.complete_space_coe
  simp only [← DirectSum.is_internal_submodule_iff_independent_and_supr_eq_top, ← hV.independent, ← true_andₓ, ←
    Submodule.orthogonal_eq_bot_iff]

/-- An orthogonal family of subspaces of `E` satisfies `direct_sum.is_internal` (that is,
they provide an internal direct sum decomposition of `E`) if and only if their span has trivial
orthogonal complement. -/
theorem OrthogonalFamily.is_internal_iff [DecidableEq ι] [FiniteDimensional 𝕜 E] {V : ι → Submodule 𝕜 E}
    (hV : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ) :
    DirectSum.IsInternal V ↔ (supr V)ᗮ = ⊥ := by
  have h := FiniteDimensional.proper_is_R_or_C 𝕜 ↥(supr V)
  exact hV.is_internal_iff_of_is_complete (complete_space_coe_iff_is_complete.mp inferInstance)

end OrthogonalFamily

section OrthonormalBasis

variable {𝕜 E} {v : Set E}

open FiniteDimensional Submodule Set

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (u «expr ⊇ » v)
/-- An orthonormal set in an `inner_product_space` is maximal, if and only if the orthogonal
complement of its span is empty. -/
theorem maximal_orthonormal_iff_orthogonal_complement_eq_bot (hv : Orthonormal 𝕜 (coe : v → E)) :
    (∀ (u) (_ : u ⊇ v), Orthonormal 𝕜 (coe : u → E) → u = v) ↔ (span 𝕜 v)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  constructor
  · contrapose!
    -- ** direction 1: nonempty orthogonal complement implies nonmaximal
    rintro ⟨x, hx', hx⟩
    -- take a nonzero vector and normalize it
    let e := (∥x∥⁻¹ : 𝕜) • x
    have he : ∥e∥ = 1 := by
      simp [← e, ← norm_smul_inv_norm hx]
    have he' : e ∈ (span 𝕜 v)ᗮ := smul_mem' _ _ hx'
    have he'' : e ∉ v := by
      intro hev
      have : e = 0 := by
        have : e ∈ span 𝕜 v⊓(span 𝕜 v)ᗮ := ⟨subset_span hev, he'⟩
        simpa [← (span 𝕜 v).inf_orthogonal_eq_bot] using this
      have : e ≠ 0 := hv.ne_zero ⟨e, hev⟩
      contradiction
    -- put this together with `v` to provide a candidate orthonormal basis for the whole space
    refine' ⟨insert e v, v.subset_insert e, ⟨_, _⟩, (v.ne_insert_of_not_mem he'').symm⟩
    · -- show that the elements of `insert e v` have unit length
      rintro ⟨a, ha'⟩
      cases' eq_or_mem_of_mem_insert ha' with ha ha
      · simp [← ha, ← he]
        
      · exact hv.1 ⟨a, ha⟩
        
      
    · -- show that the elements of `insert e v` are orthogonal
      have h_end : ∀, ∀ a ∈ v, ∀, ⟪a, e⟫ = 0 := by
        intro a ha
        exact he' a (Submodule.subset_span ha)
      rintro ⟨a, ha'⟩
      cases' eq_or_mem_of_mem_insert ha' with ha ha
      · rintro ⟨b, hb'⟩ hab'
        have hb : b ∈ v := by
          refine' mem_of_mem_insert_of_ne hb' _
          intro hbe'
          apply hab'
          simp [← ha, ← hbe']
        rw [inner_eq_zero_sym]
        simpa [← ha] using h_end b hb
        
      rintro ⟨b, hb'⟩ hab'
      cases' eq_or_mem_of_mem_insert hb' with hb hb
      · simpa [← hb] using h_end a ha
        
      have : (⟨a, ha⟩ : v) ≠ ⟨b, hb⟩ := by
        intro hab''
        apply hab'
        simpa using hab''
      exact hv.2 this
      
    
  · -- ** direction 2: empty orthogonal complement implies maximal
    simp only [← subset.antisymm_iff]
    rintro h u (huv : v ⊆ u) hu
    refine' ⟨_, huv⟩
    intro x hxu
    refine' ((mt (h x)) (hu.ne_zero ⟨x, hxu⟩)).imp_symm _
    intro hxv y hy
    have hxv' : (⟨x, hxu⟩ : u) ∉ (coe ⁻¹' v : Set u) := by
      simp [← huv, ← hxv]
    obtain ⟨l, hl, rfl⟩ : ∃ l ∈ Finsupp.supported 𝕜 𝕜 (coe ⁻¹' v : Set u), (Finsupp.total (↥u) E 𝕜 coe) l = y := by
      rw [← Finsupp.mem_span_image_iff_total]
      simp [← huv, ← inter_eq_self_of_subset_left, ← hy]
    exact hu.inner_finsupp_eq_zero hxv' hl
    

variable [FiniteDimensional 𝕜 E]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (u «expr ⊇ » v)
/-- An orthonormal set in a finite-dimensional `inner_product_space` is maximal, if and only if it
is a basis. -/
theorem maximal_orthonormal_iff_basis_of_finite_dimensional (hv : Orthonormal 𝕜 (coe : v → E)) :
    (∀ (u) (_ : u ⊇ v), Orthonormal 𝕜 (coe : u → E) → u = v) ↔ ∃ b : Basis v 𝕜 E, ⇑b = coe := by
  have := proper_is_R_or_C 𝕜 (span 𝕜 v)
  rw [maximal_orthonormal_iff_orthogonal_complement_eq_bot hv]
  have hv_compl : IsComplete (span 𝕜 v : Set E) := (span 𝕜 v).complete_of_finite_dimensional
  rw [Submodule.orthogonal_eq_bot_iff]
  have hv_coe : range (coe : v → E) = v := by
    simp
  constructor
  · refine' fun h => ⟨Basis.mk hv.linear_independent _, Basis.coe_mk _ _⟩
    convert h
    
  · rintro ⟨h, coe_h⟩
    rw [← h.span_eq, coe_h, hv_coe]
    

end OrthonormalBasis


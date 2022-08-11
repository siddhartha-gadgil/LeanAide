/-
Copyright (c) 2022 Bhavik Mehta All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
import Mathbin.Analysis.Convex.Cone
import Mathbin.Analysis.Convex.Gauge

/-!
# Separation Hahn-Banach theorem

In this file we prove the geometric Hahn-Banach theorem. For any two disjoint convex sets, there
exists a continuous linear functional separating them, geometrically meaning that we can intercalate
a plane between them.

We provide many variations to stricten the result under more assumptions on the convex sets:
* `geometric_hahn_banach_open`: One set is open. Weak separation.
* `geometric_hahn_banach_open_point`, `geometric_hahn_banach_point_open`: One set is open, the
  other is a singleton. Weak separation.
* `geometric_hahn_banach_open_open`: Both sets are open. Semistrict separation.
* `geometric_hahn_banach_compact_closed`, `geometric_hahn_banach_closed_compact`: One set is closed,
  the other one is compact. Strict separation.
* `geometric_hahn_banach_point_closed`, `geometric_hahn_banach_closed_point`: One set is closed, the
  other one is a singleton. Strict separation.
* `geometric_hahn_banach_point_point`: Both sets are singletons. Strict separation.

## TODO

* Eidelheit's theorem
* `convex ℝ s → interior (closure s) ⊆ s`
-/


open Set

open Pointwise

variable {𝕜 E : Type _}

/-- Given a set `s` which is a convex neighbourhood of `0` and a point `x₀` outside of it, there is
a continuous linear functional `f` separating `x₀` and `s`, in the sense that it sends `x₀` to 1 and
all of `s` to values strictly below `1`. -/
theorem separate_convex_open_set [SemiNormedGroup E] [NormedSpace ℝ E] {s : Set E} (hs₀ : (0 : E) ∈ s)
    (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) {x₀ : E} (hx₀ : x₀ ∉ s) : ∃ f : E →L[ℝ] ℝ, f x₀ = 1 ∧ ∀, ∀ x ∈ s, ∀, f x < 1 :=
  by
  let f : LinearPmap ℝ E ℝ := LinearPmap.mkSpanSingleton x₀ 1 (ne_of_mem_of_not_mem hs₀ hx₀).symm
  obtain ⟨r, hr, hrs⟩ :=
    Metric.mem_nhds_iff.1
      (Filter.inter_mem (hs₂.mem_nhds hs₀) <|
        hs₂.neg.mem_nhds <| by
          rwa [mem_neg, neg_zero])
  obtain ⟨φ, hφ₁, hφ₂⟩ :=
    exists_extension_of_le_sublinear f (gauge s) (fun c hc => gauge_smul_of_nonneg hc.le)
      (gauge_add_le hs₁ <| absorbent_nhds_zero <| hs₂.mem_nhds hs₀) _
  · refine' ⟨(φ.mk_continuous r⁻¹) fun x => _, _, _⟩
    · rw [Real.norm_eq_abs, abs_le, neg_le, ← LinearMap.map_neg]
      nth_rw 0[← norm_neg x]
      suffices ∀ x, φ x ≤ r⁻¹ * ∥x∥ by
        exact ⟨this _, this _⟩
      refine' fun x => (hφ₂ _).trans _
      rw [← div_eq_inv_mul, ← gauge_ball hr]
      exact gauge_mono (absorbent_ball_zero hr) (hrs.trans <| inter_subset_left _ _) x
      
    · dsimp'
      rw [← Submodule.coe_mk x₀ (Submodule.mem_span_singleton_self _), hφ₁, LinearPmap.mk_span_singleton'_apply_self]
      
    · exact fun x hx => (hφ₂ x).trans_lt (gauge_lt_one_of_mem_of_open hs₁ hs₀ hs₂ hx)
      
    
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [LinearPmap.mk_span_singleton'_apply]
  simp only [← mul_oneₓ, ← Algebra.id.smul_eq_mul, ← Submodule.coe_mk]
  obtain h | h := le_or_ltₓ y 0
  · exact h.trans (gauge_nonneg _)
    
  · rw [gauge_smul_of_nonneg h.le, smul_eq_mul, le_mul_iff_one_le_right h]
    exact
      one_le_gauge_of_not_mem (hs₁.star_convex hs₀)
        ((absorbent_ball_zero hr).Subset <| hrs.trans <| inter_subset_left _ _).Absorbs hx₀
    infer_instance
    

variable [NormedGroup E] [NormedSpace ℝ E] {s t : Set E} {x y : E}

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is open,
there is a continuous linear functional which separates them. -/
theorem geometric_hahn_banach_open (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (ht : Convex ℝ t) (disj : Disjoint s t) :
    ∃ (f : E →L[ℝ] ℝ)(u : ℝ), (∀, ∀ a ∈ s, ∀, f a < u) ∧ ∀, ∀ b ∈ t, ∀, u ≤ f b := by
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty
  · exact
      ⟨0, 0, by
        simp , fun b hb => le_rfl⟩
    
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty
  · exact
      ⟨0, 1, fun a ha => zero_lt_one, by
        simp ⟩
    
  let x₀ := b₀ - a₀
  let C := x₀ +ᵥ (s - t)
  have : (0 : E) ∈ C :=
    ⟨a₀ - b₀, sub_mem_sub ha₀ hb₀, by
      rw [vadd_eq_add, sub_add_sub_cancel', sub_self]⟩
  have : Convex ℝ C := (hs₁.sub ht).vadd _
  have : x₀ ∉ C := by
    intro hx₀
    rw [← add_zeroₓ x₀] at hx₀
    exact disj.zero_not_mem_sub_set (vadd_mem_vadd_set_iff.1 hx₀)
  obtain ⟨f, hf₁, hf₂⟩ := separate_convex_open_set ‹0 ∈ C› ‹_› (hs₂.sub_right.vadd _) ‹x₀ ∉ C›
  have : f b₀ = f a₀ + 1 := by
    simp [hf₁]
  have forall_le : ∀, ∀ a ∈ s, ∀, ∀ b ∈ t, ∀, f a ≤ f b := by
    intro a ha b hb
    have := hf₂ (x₀ + (a - b)) (vadd_mem_vadd_set <| sub_mem_sub ha hb)
    simp only [← f.map_add, ← f.map_sub, ← hf₁] at this
    linarith
  refine' ⟨f, Inf (f '' t), image_subset_iff.1 (_ : f '' s ⊆ Iio (Inf (f '' t))), fun b hb => _⟩
  · rw [← interior_Iic]
    refine' interior_maximal (image_subset_iff.2 fun a ha => _) (f.is_open_map_of_ne_zero _ _ hs₂)
    · exact le_cInf (nonempty.image _ ⟨_, hb₀⟩) (ball_image_of_ball <| forall_le _ ha)
      
    · rintro rfl
      simpa using hf₁
      
    
  · exact cInf_le ⟨f a₀, ball_image_of_ball <| forall_le _ ha₀⟩ (mem_image_of_mem _ hb)
    

theorem geometric_hahn_banach_open_point (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (disj : x ∉ s) :
    ∃ f : E →L[ℝ] ℝ, ∀, ∀ a ∈ s, ∀, f a < f x :=
  let ⟨f, s, hs, hx⟩ := geometric_hahn_banach_open hs₁ hs₂ (convex_singleton x) (disjoint_singleton_right.2 disj)
  ⟨f, fun a ha => lt_of_lt_of_leₓ (hs a ha) (hx x (mem_singleton _))⟩

theorem geometric_hahn_banach_point_open (ht₁ : Convex ℝ t) (ht₂ : IsOpen t) (disj : x ∉ t) :
    ∃ f : E →L[ℝ] ℝ, ∀, ∀ b ∈ t, ∀, f x < f b :=
  let ⟨f, hf⟩ := geometric_hahn_banach_open_point ht₁ ht₂ disj
  ⟨-f, by
    simpa⟩

theorem geometric_hahn_banach_open_open (hs₁ : Convex ℝ s) (hs₂ : IsOpen s) (ht₁ : Convex ℝ t) (ht₃ : IsOpen t)
    (disj : Disjoint s t) : ∃ (f : E →L[ℝ] ℝ)(u : ℝ), (∀, ∀ a ∈ s, ∀, f a < u) ∧ ∀, ∀ b ∈ t, ∀, u < f b := by
  obtain rfl | ⟨a₀, ha₀⟩ := s.eq_empty_or_nonempty
  · exact
      ⟨0, -1, by
        simp , fun b hb => by
        norm_num⟩
    
  obtain rfl | ⟨b₀, hb₀⟩ := t.eq_empty_or_nonempty
  · exact
      ⟨0, 1, fun a ha => by
        norm_num, by
        simp ⟩
    
  obtain ⟨f, s, hf₁, hf₂⟩ := geometric_hahn_banach_open hs₁ hs₂ ht₁ disj
  have hf : IsOpenMap f := by
    refine' f.is_open_map_of_ne_zero _
    rintro rfl
    exact (hf₁ _ ha₀).not_le (hf₂ _ hb₀)
  refine' ⟨f, s, hf₁, image_subset_iff.1 (_ : f '' t ⊆ Ioi s)⟩
  rw [← interior_Ici]
  refine' interior_maximal (image_subset_iff.2 hf₂) (f.is_open_map_of_ne_zero _ _ ht₃)
  rintro rfl
  exact (hf₁ _ ha₀).not_le (hf₂ _ hb₀)

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is
compact and `t` is closed, there is a continuous linear functional which strongly separates them. -/
theorem geometric_hahn_banach_compact_closed (hs₁ : Convex ℝ s) (hs₂ : IsCompact s) (ht₁ : Convex ℝ t)
    (ht₂ : IsClosed t) (disj : Disjoint s t) :
    ∃ (f : E →L[ℝ] ℝ)(u v : ℝ), (∀, ∀ a ∈ s, ∀, f a < u) ∧ u < v ∧ ∀, ∀ b ∈ t, ∀, v < f b := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact
      ⟨0, -2, -1, by
        simp , by
        norm_num, fun b hb => by
        norm_num⟩
    
  obtain rfl | ht := t.eq_empty_or_nonempty
  · exact
      ⟨0, 1, 2, fun a ha => by
        norm_num, by
        norm_num, by
        simp ⟩
    
  obtain ⟨U, V, hU, hV, hU₁, hV₁, sU, tV, disj'⟩ := disj.exists_open_convexes hs₁ hs₂ ht₁ ht₂
  obtain ⟨f, u, hf₁, hf₂⟩ := geometric_hahn_banach_open_open hU₁ hU hV₁ hV disj'
  obtain ⟨x, hx₁, hx₂⟩ := hs₂.exists_forall_ge hs f.continuous.continuous_on
  have : f x < u := hf₁ x (sU hx₁)
  exact
    ⟨f, (f x + u) / 2, u, fun a ha => by
      linarith [hx₂ a ha], by
      linarith, fun b hb => hf₂ b (tV hb)⟩

/-- A version of the **Hahn-Banach theorem**: given disjoint convex sets `s`, `t` where `s` is
closed, and `t` is compact, there is a continuous linear functional which strongly separates them.
-/
theorem geometric_hahn_banach_closed_compact (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (ht₁ : Convex ℝ t)
    (ht₂ : IsCompact t) (disj : Disjoint s t) :
    ∃ (f : E →L[ℝ] ℝ)(u v : ℝ), (∀, ∀ a ∈ s, ∀, f a < u) ∧ u < v ∧ ∀, ∀ b ∈ t, ∀, v < f b :=
  let ⟨f, s, t, hs, st, ht⟩ := geometric_hahn_banach_compact_closed ht₁ ht₂ hs₁ hs₂ disj.symm
  ⟨-f, -t, -s, by
    simpa using ht, by
    simpa using st, by
    simpa using hs⟩

theorem geometric_hahn_banach_point_closed (ht₁ : Convex ℝ t) (ht₂ : IsClosed t) (disj : x ∉ t) :
    ∃ (f : E →L[ℝ] ℝ)(u : ℝ), f x < u ∧ ∀, ∀ b ∈ t, ∀, u < f b :=
  let ⟨f, u, v, ha, hst, hb⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) is_compact_singleton ht₁ ht₂
      (disjoint_singleton_left.2 disj)
  ⟨f, v, hst.trans' <| ha x <| mem_singleton _, hb⟩

theorem geometric_hahn_banach_closed_point (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (disj : x ∉ s) :
    ∃ (f : E →L[ℝ] ℝ)(u : ℝ), (∀, ∀ a ∈ s, ∀, f a < u) ∧ u < f x :=
  let ⟨f, s, t, ha, hst, hb⟩ :=
    geometric_hahn_banach_closed_compact hs₁ hs₂ (convex_singleton x) is_compact_singleton
      (disjoint_singleton_right.2 disj)
  ⟨f, s, ha, hst.trans <| hb x <| mem_singleton _⟩

/-- Special case of `normed_space.eq_iff_forall_dual_eq`. -/
theorem geometric_hahn_banach_point_point (hxy : x ≠ y) : ∃ f : E →L[ℝ] ℝ, f x < f y := by
  obtain ⟨f, s, t, hs, st, ht⟩ :=
    geometric_hahn_banach_compact_closed (convex_singleton x) is_compact_singleton (convex_singleton y)
      is_closed_singleton (disjoint_singleton.2 hxy)
  exact
    ⟨f, by
      linarith [hs x rfl, ht y rfl]⟩

/-- A closed convex set is the intersection of the halfspaces containing it. -/
theorem Inter_halfspaces_eq (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) : (⋂ l : E →L[ℝ] ℝ, { x | ∃ y ∈ s, l x ≤ l y }) = s :=
  by
  rw [Set.Inter_set_of]
  refine' Set.Subset.antisymm (fun x hx => _) fun x hx l => ⟨x, hx, le_rfl⟩
  by_contra
  obtain ⟨l, s, hlA, hl⟩ := geometric_hahn_banach_closed_point hs₁ hs₂ h
  obtain ⟨y, hy, hxy⟩ := hx l
  exact ((hxy.trans_lt (hlA y hy)).trans hl).not_le le_rfl


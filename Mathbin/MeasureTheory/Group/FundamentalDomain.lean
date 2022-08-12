/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.MeasureTheory.Group.Action
import Mathbin.MeasureTheory.Group.Pointwise
import Mathbin.MeasureTheory.Integral.SetIntegral

/-!
# Fundamental domain of a group action

A set `s` is said to be a *fundamental domain* of an action of a group `G` on a measurable space `α`
with respect to a measure `μ` if

* `s` is a measurable set;

* the sets `g • s` over all `g : G` cover almost all points of the whole space;

* the sets `g • s`, are pairwise a.e. disjoint, i.e., `μ (g₁ • s ∩ g₂ • s) = 0` whenever `g₁ ≠ g₂`;
  we require this for `g₂ = 1` in the definition, then deduce it for any two `g₁ ≠ g₂`.

In this file we prove that in case of a countable group `G` and a measure preserving action, any two
fundamental domains have the same measure, and for a `G`-invariant function, its integrals over any
two fundamental domains are equal to each other.

We also generate additive versions of all theorems in this file using the `to_additive` attribute.
-/


open Ennreal Pointwise TopologicalSpace Nnreal Ennreal MeasureTheory

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Filter

namespace MeasureTheory

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (g «expr ≠ » (0 : G))
/-- A measurable set `s` is a *fundamental domain* for an additive action of an additive group `G`
on a measurable space `α` with respect to a measure `α` if the sets `g +ᵥ s`, `g : G`, are pairwise
a.e. disjoint and cover the whole space. -/
@[protect_proj]
structure IsAddFundamentalDomain (G : Type _) {α : Type _} [Zero G] [HasVadd G α] [MeasurableSpace α] (s : Set α)
  (μ : Measure α := by
    run_tac
      volume_tac) :
  Prop where
  NullMeasurableSet : NullMeasurableSet s μ
  ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g +ᵥ x ∈ s
  AeDisjoint : ∀ (g) (_ : g ≠ (0 : G)), AeDisjoint μ (g +ᵥ s) s

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (g «expr ≠ » (1 : G))
/-- A measurable set `s` is a *fundamental domain* for an action of a group `G` on a measurable
space `α` with respect to a measure `α` if the sets `g • s`, `g : G`, are pairwise a.e. disjoint and
cover the whole space. -/
@[protect_proj, to_additive is_add_fundamental_domain]
structure IsFundamentalDomain (G : Type _) {α : Type _} [One G] [HasSmul G α] [MeasurableSpace α] (s : Set α)
  (μ : Measure α := by
    run_tac
      volume_tac) :
  Prop where
  NullMeasurableSet : NullMeasurableSet s μ
  ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ s
  AeDisjoint : ∀ (g) (_ : g ≠ (1 : G)), AeDisjoint μ (g • s) s

namespace IsFundamentalDomain

variable {G α E : Type _} [Groupₓ G] [MulAction G α] [MeasurableSpace α] [NormedGroup E] {s t : Set α} {μ : Measure α}

/-- If for each `x : α`, exactly one of `g • x`, `g : G`, belongs to a measurable set `s`, then `s`
is a fundamental domain for the action of `G` on `α`. -/
@[to_additive
      "If for each `x : α`, exactly one of `g +ᵥ x`, `g : G`, belongs to a measurable set\n`s`, then `s` is a fundamental domain for the additive action of `G` on `α`."]
theorem mk' (h_meas : NullMeasurableSet s μ) (h_exists : ∀ x : α, ∃! g : G, g • x ∈ s) : IsFundamentalDomain G s μ :=
  { NullMeasurableSet := h_meas, ae_covers := eventually_of_forall fun x => (h_exists x).exists,
    AeDisjoint := fun g hne =>
      Disjoint.ae_disjoint <|
        disjoint_left.2
          (by
            rintro _ ⟨x, hx, rfl⟩ hgx
            rw [← one_smul G x] at hx
            exact hne ((h_exists x).unique hgx hx)) }

@[to_additive]
theorem Union_smul_ae_eq (h : IsFundamentalDomain G s μ) : (⋃ g : G, g • s) =ᵐ[μ] univ :=
  eventually_eq_univ.2 <| h.ae_covers.mono fun x ⟨g, hg⟩ => mem_Union.2 ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[to_additive]
theorem mono (h : IsFundamentalDomain G s μ) {ν : Measure α} (hle : ν ≪ μ) : IsFundamentalDomain G s ν :=
  ⟨h.1.mono_ac hle, hle h.2, fun g hg => hle (h.3 g hg)⟩

variable [MeasurableSpace G] [HasMeasurableSmul G α] [SmulInvariantMeasure G α μ]

@[to_additive]
theorem null_measurable_set_smul (h : IsFundamentalDomain G s μ) (g : G) : NullMeasurableSet (g • s) μ :=
  h.NullMeasurableSet.smul g

@[to_additive]
theorem restrict_restrict (h : IsFundamentalDomain G s μ) (g : G) (t : Set α) :
    (μ.restrict t).restrict (g • s) = μ.restrict (g • s ∩ t) :=
  restrict_restrict₀ ((h.null_measurable_set_smul g).mono restrict_le_self)

@[to_additive]
theorem pairwise_ae_disjoint (h : IsFundamentalDomain G s μ) :
    Pairwise fun g₁ g₂ : G => AeDisjoint μ (g₁ • s) (g₂ • s) := fun g₁ g₂ hne =>
  calc
    μ (g₁ • s ∩ g₂ • s) = μ (g₂ • ((g₂⁻¹ * g₁) • s ∩ s)) := by
      rw [smul_set_inter, smul_smul, mul_inv_cancel_left]
    _ = μ ((g₂⁻¹ * g₁) • s ∩ s) := measure_smul_set _ _ _
    _ = 0 := h.AeDisjoint _ <| mt inv_mul_eq_one.1 hne.symm
    

@[to_additive]
theorem pairwise_ae_disjoint_of_ac {ν} (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) :
    Pairwise fun g₁ g₂ : G => AeDisjoint ν (g₁ • s) (g₂ • s) :=
  h.pairwise_ae_disjoint.mono fun g₁ g₂ H => hν H

@[to_additive]
theorem preimage_of_equiv (h : IsFundamentalDomain G s μ) {f : α → α} (hf : QuasiMeasurePreserving f μ μ) {e : G → G}
    (he : Bijective e) (hef : ∀ g, Semiconj f ((· • ·) (e g)) ((· • ·) g)) : IsFundamentalDomain G (f ⁻¹' s) μ :=
  { NullMeasurableSet := h.NullMeasurableSet.Preimage hf,
    ae_covers :=
      (hf.ae h.ae_covers).mono fun x ⟨g, hg⟩ =>
        ⟨e g, by
          rwa [mem_preimage, hef g x]⟩,
    AeDisjoint := fun g hg => by
      lift e to G ≃ G using he
      have : (e.symm g⁻¹)⁻¹ ≠ (e.symm 1)⁻¹ := by
        simp [← hg]
      convert (h.pairwise_ae_disjoint _ _ this).Preimage hf using 1
      · simp only [preimage_smul_inv, ← preimage_preimage, hef _ _, ← e.apply_symm_apply, ← inv_invₓ]
        
      · ext1 x
        simp only [← mem_preimage, preimage_smul, hef _ _, ← e.apply_symm_apply, ← one_smul]
         }

@[to_additive]
theorem image_of_equiv (h : IsFundamentalDomain G s μ) (f : α ≃ᵐ α) (hfμ : MeasurePreserving f μ μ) (e : Equivₓ.Perm G)
    (hef : ∀ g, Semiconj f ((· • ·) (e g)) ((· • ·) g)) : IsFundamentalDomain G (f '' s) μ := by
  rw [f.image_eq_preimage]
  refine' h.preimage_of_equiv (hfμ.symm f).QuasiMeasurePreserving e.symm.bijective fun g x => _
  rcases f.surjective x with ⟨x, rfl⟩
  rw [← hef _ _, f.symm_apply_apply, f.symm_apply_apply, e.apply_symm_apply]

@[to_additive]
theorem smul (h : IsFundamentalDomain G s μ) (g : G) : IsFundamentalDomain G (g • s) μ :=
  (h.image_of_equiv (MeasurableEquiv.smul g) (measure_preserving_smul _ _)
      ⟨fun g' => g⁻¹ * g' * g, fun g' => g * g' * g⁻¹, fun g' => by
        simp [← mul_assoc], fun g' => by
        simp [← mul_assoc]⟩)
    fun g' x => by
    simp [← smul_smul, ← mul_assoc]

@[to_additive]
theorem smul_of_comm {G' : Type _} [Groupₓ G'] [MulAction G' α] [MeasurableSpace G'] [HasMeasurableSmul G' α]
    [SmulInvariantMeasure G' α μ] [SmulCommClass G' G α] (h : IsFundamentalDomain G s μ) (g : G') :
    IsFundamentalDomain G (g • s) μ :=
  h.image_of_equiv (MeasurableEquiv.smul g) (measure_preserving_smul _ _) (Equivₓ.refl _) <| smul_comm g

variable [Encodable G] {ν : Measure α}

@[to_additive]
theorem sum_restrict_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) : (Sum fun g : G => ν.restrict (g • s)) = ν :=
  by
  rw [←
    restrict_Union_ae (h.pairwise_ae_disjoint.mono fun i j h => hν h) fun g =>
      (h.null_measurable_set_smul g).mono_ac hν,
    restrict_congr_set (hν h.Union_smul_ae_eq), restrict_univ]

@[to_additive]
theorem lintegral_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α → ℝ≥0∞) :
    (∫⁻ x, f x ∂ν) = ∑' g : G, ∫⁻ x in g • s, f x ∂ν := by
  rw [← lintegral_sum_measure, h.sum_restrict_of_ac hν]

@[to_additive]
theorem sum_restrict (h : IsFundamentalDomain G s μ) : (Sum fun g : G => μ.restrict (g • s)) = μ :=
  h.sum_restrict_of_ac (refl _)

@[to_additive]
theorem lintegral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) :
    (∫⁻ x, f x ∂μ) = ∑' g : G, ∫⁻ x in g • s, f x ∂μ :=
  h.lintegral_eq_tsum_of_ac (refl _) f

@[to_additive]
theorem set_lintegral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) (t : Set α) :
    (∫⁻ x in t, f x ∂μ) = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ :=
  calc
    (∫⁻ x in t, f x ∂μ) = ∑' g : G, ∫⁻ x in g • s, f x ∂μ.restrict t :=
      h.lintegral_eq_tsum_of_ac restrict_le_self.AbsolutelyContinuous _
    _ = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ := by
      simp only [← h.restrict_restrict, ← inter_comm]
    

@[to_additive]
theorem set_lintegral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α → ℝ≥0∞) (t : Set α) :
    (∫⁻ x in t, f x ∂μ) = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
  calc
    (∫⁻ x in t, f x ∂μ) = ∑' g : G, ∫⁻ x in t ∩ g • s, f x ∂μ := h.set_lintegral_eq_tsum' f t
    _ = ∑' g : G, ∫⁻ x in t ∩ g⁻¹ • s, f x ∂μ := ((Equivₓ.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • (g • t ∩ s), f x ∂μ := by
      simp only [← smul_set_inter, ← inv_smul_smul]
    _ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ :=
      tsum_congr fun g =>
        ((measure_preserving_smul g⁻¹ μ).set_lintegral_comp_emb (measurable_embedding_const_smul _) _ _).symm
    

@[to_additive]
theorem measure_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (t : Set α) :
    ν t = ∑' g : G, ν (t ∩ g • s) := by
  have H : ν.restrict t ≪ μ := Measure.restrict_le_self.AbsolutelyContinuous.trans hν
  simpa only [← set_lintegral_one, ← Pi.one_def, ← measure.restrict_apply₀ ((h.null_measurable_set_smul _).mono_ac H), ←
    inter_comm] using h.lintegral_eq_tsum_of_ac H 1

@[to_additive]
theorem measure_eq_tsum' (h : IsFundamentalDomain G s μ) (t : Set α) : μ t = ∑' g : G, μ (t ∩ g • s) :=
  h.measure_eq_tsum_of_ac AbsolutelyContinuous.rfl t

@[to_additive]
theorem measure_eq_tsum (h : IsFundamentalDomain G s μ) (t : Set α) : μ t = ∑' g : G, μ (g • t ∩ s) := by
  simpa only [← set_lintegral_one] using h.set_lintegral_eq_tsum (fun _ => 1) t

@[to_additive]
theorem measure_zero_of_invariant (h : IsFundamentalDomain G s μ) (t : Set α) (ht : ∀ g : G, g • t = t)
    (hts : μ (t ∩ s) = 0) : μ t = 0 := by
  simp [← measure_eq_tsum h, ← ht, ← hts]

@[to_additive]
protected theorem set_lintegral_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) (f : α → ℝ≥0∞)
    (hf : ∀ (g : G) (x), f (g • x) = f x) : (∫⁻ x in s, f x ∂μ) = ∫⁻ x in t, f x ∂μ :=
  calc
    (∫⁻ x in s, f x ∂μ) = ∑' g : G, ∫⁻ x in s ∩ g • t, f x ∂μ := ht.set_lintegral_eq_tsum' _ _
    _ = ∑' g : G, ∫⁻ x in g • t ∩ s, f (g⁻¹ • x) ∂μ := by
      simp only [← hf, ← inter_comm]
    _ = ∫⁻ x in t, f x ∂μ := (hs.set_lintegral_eq_tsum _ _).symm
    

@[to_additive]
theorem measure_set_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) {A : Set α}
    (hA₀ : MeasurableSet A) (hA : ∀ g : G, (fun x => g • x) ⁻¹' A = A) : μ (A ∩ s) = μ (A ∩ t) := by
  have : (∫⁻ x in s, A.indicator 1 x ∂μ) = ∫⁻ x in t, A.indicator 1 x ∂μ := by
    refine' hs.set_lintegral_eq ht (Set.indicatorₓ A fun _ => 1) _
    intro g x
    convert (Set.indicator_comp_right fun x : α => g • x).symm
    rw [hA g]
  simpa [← measure.restrict_apply hA₀, ← lintegral_indicator _ hA₀] using this

/-- If `s` and `t` are two fundamental domains of the same action, then their measures are equal. -/
@[to_additive "If `s` and `t` are two fundamental domains of the same action, then their measures\nare equal."]
protected theorem measure_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) : μ s = μ t := by
  simpa only [← set_lintegral_one] using hs.set_lintegral_eq ht (fun _ => 1) fun _ _ => rfl

@[to_additive]
protected theorem ae_strongly_measurable_on_iff {β : Type _} [TopologicalSpace β] [PseudoMetrizableSpace β]
    (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) {f : α → β}
    (hf : ∀ (g : G) (x), f (g • x) = f x) :
    AeStronglyMeasurable f (μ.restrict s) ↔ AeStronglyMeasurable f (μ.restrict t) :=
  calc
    AeStronglyMeasurable f (μ.restrict s) ↔ AeStronglyMeasurable f (measure.sum fun g : G => μ.restrict (g • t ∩ s)) :=
      by
      simp only [ht.restrict_restrict, ← ht.sum_restrict_of_ac restrict_le_self.absolutely_continuous]
    _ ↔ ∀ g : G, AeStronglyMeasurable f (μ.restrict (g • (g⁻¹ • s ∩ t))) := by
      simp only [← smul_set_inter, ← inter_comm, ← smul_inv_smul, ← ae_strongly_measurable_sum_measure_iff]
    _ ↔ ∀ g : G, AeStronglyMeasurable f (μ.restrict (g⁻¹ • (g⁻¹⁻¹ • s ∩ t))) := inv_surjective.forall
    _ ↔ ∀ g : G, AeStronglyMeasurable f (μ.restrict (g⁻¹ • (g • s ∩ t))) := by
      simp only [← inv_invₓ]
    _ ↔ ∀ g : G, AeStronglyMeasurable f (μ.restrict (g • s ∩ t)) := by
      refine' forall_congrₓ fun g => _
      have he : MeasurableEmbedding ((· • ·) g⁻¹ : α → α) := measurable_embedding_const_smul _
      rw [← image_smul, ← ((measure_preserving_smul g⁻¹ μ).restrict_image_emb he _).ae_strongly_measurable_comp_iff he]
      simp only [← (· ∘ ·), ← hf]
    _ ↔ AeStronglyMeasurable f (μ.restrict t) := by
      simp only [ae_strongly_measurable_sum_measure_iff, hs.restrict_restrict, ←
        hs.sum_restrict_of_ac restrict_le_self.absolutely_continuous]
    

@[to_additive]
protected theorem has_finite_integral_on_iff (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    {f : α → E} (hf : ∀ (g : G) (x), f (g • x) = f x) :
    HasFiniteIntegral f (μ.restrict s) ↔ HasFiniteIntegral f (μ.restrict t) := by
  dunfold has_finite_integral
  rw [hs.set_lintegral_eq ht]
  intro g x
  rw [hf]

@[to_additive]
protected theorem integrable_on_iff (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) {f : α → E}
    (hf : ∀ (g : G) (x), f (g • x) = f x) : IntegrableOn f s μ ↔ IntegrableOn f t μ :=
  and_congr (hs.ae_strongly_measurable_on_iff ht hf) (hs.has_finite_integral_on_iff ht hf)

variable [NormedSpace ℝ E] [CompleteSpace E]

@[to_additive]
protected theorem set_integral_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) {f : α → E}
    (hf : ∀ (g : G) (x), f (g • x) = f x) : (∫ x in s, f x ∂μ) = ∫ x in t, f x ∂μ := by
  by_cases' hfs : integrable_on f s μ
  · have hft : integrable_on f t μ := by
      rwa [ht.integrable_on_iff hs hf]
    have hac : ∀ {u}, μ.restrict u ≪ μ := fun u => restrict_le_self.absolutely_continuous
    calc (∫ x in s, f x ∂μ) = ∫ x in ⋃ g : G, g • t, f x ∂μ.restrict s := by
        rw [restrict_congr_set (hac ht.Union_smul_ae_eq), restrict_univ]_ = ∑' g : G, ∫ x in g • t, f x ∂μ.restrict s :=
        integral_Union_ae (fun g => (ht.null_measurable_set_smul g).mono_ac hac) (ht.pairwise_ae_disjoint_of_ac hac)
          hfs.integrable.integrable_on _ = ∑' g : G, ∫ x in s ∩ g • t, f x ∂μ :=
        by
        simp only [← ht.restrict_restrict, ← inter_comm]_ = ∑' g : G, ∫ x in s ∩ g⁻¹ • t, f x ∂μ :=
        ((Equivₓ.inv G).tsum_eq _).symm _ = ∑' g : G, ∫ x in g⁻¹ • (g • s ∩ t), f x ∂μ := by
        simp only [← smul_set_inter, ← inv_smul_smul]_ = ∑' g : G, ∫ x in g • s ∩ t, f (g⁻¹ • x) ∂μ :=
        tsum_congr fun g =>
          (measure_preserving_smul g⁻¹ μ).set_integral_image_emb (measurable_embedding_const_smul _) _
            _ _ = ∑' g : G, ∫ x in g • s, f x ∂μ.restrict t :=
        by
        simp only [← hf, ← hs.restrict_restrict]_ = ∫ x in ⋃ g : G, g • s, f x ∂μ.restrict t :=
        (integral_Union_ae (fun g => (hs.null_measurable_set_smul g).mono_ac hac)
            (hs.pairwise_ae_disjoint.mono fun i j h => hac h) hft.integrable.integrable_on).symm _ = ∫ x in t, f x ∂μ :=
        by
        rw [restrict_congr_set (hac hs.Union_smul_ae_eq), restrict_univ]
    
  · rw [integral_undef hfs, integral_undef]
    rwa [hs.integrable_on_iff ht hf] at hfs
    

/-- If `f` is invariant under the action of a countable group `G`, and `μ` is a `G`-invariant
  measure with a fundamental domain `s`, then the `ess_sup` of `f` restricted to `s` is the same as
  that of `f` on all of its domain. -/
@[to_additive
      "If `f` is invariant under the action of a countable additive group `G`, and `μ` is a\n`G`-invariant measure with a fundamental domain `s`, then the `ess_sup` of `f` restricted to `s` is\nthe same as that of `f` on all of its domain."]
theorem ess_sup_measure_restrict (hs : IsFundamentalDomain G s μ) {f : α → ℝ≥0∞}
    (hf : ∀ γ : G, ∀ x : α, f (γ • x) = f x) : essSup f (μ.restrict s) = essSup f μ := by
  refine' le_antisymmₓ (ess_sup_mono_measure' measure.restrict_le_self) _
  rw [ess_sup_eq_Inf (μ.restrict s) f, ess_sup_eq_Inf μ f]
  refine' Inf_le_Inf _
  rintro a (ha : (μ.restrict s) { x : α | a < f x } = 0)
  rw [measure.restrict_apply₀' hs.null_measurable_set] at ha
  refine' measure_zero_of_invariant hs _ _ ha
  intro γ
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  simp only [← mem_set_of_eq, ← hf γ⁻¹ x]

end IsFundamentalDomain

end MeasureTheory


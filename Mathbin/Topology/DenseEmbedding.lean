/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathbin.Topology.Separation
import Mathbin.Topology.Bases

/-!
# Dense embeddings

This file defines three properties of functions:

* `dense_range f`      means `f` has dense image;
* `dense_inducing i`   means `i` is also `inducing`;
* `dense_embedding e`  means `e` is also an `embedding`.

The main theorem `continuous_extend` gives a criterion for a function
`f : X → Z` to a T₃ space Z to extend along a dense embedding
`i : X → Y` to a continuous function `g : Y → Z`. Actually `i` only
has to be `dense_inducing` (not necessarily injective).

-/


noncomputable section

open Set Filter

open Classical TopologicalSpace Filter

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

/-- `i : α → β` is "dense inducing" if it has dense range and the topology on `α`
  is the one induced by `i` from the topology on `β`. -/
@[protect_proj]
structure DenseInducing [TopologicalSpace α] [TopologicalSpace β] (i : α → β) extends Inducing i : Prop where
  dense : DenseRange i

namespace DenseInducing

variable [TopologicalSpace α] [TopologicalSpace β]

variable {i : α → β} (di : DenseInducing i)

theorem nhds_eq_comap (di : DenseInducing i) : ∀ a : α, 𝓝 a = comap i (𝓝 <| i a) :=
  di.to_inducing.nhds_eq_comap

protected theorem continuous (di : DenseInducing i) : Continuous i :=
  di.to_inducing.Continuous

theorem closure_range : Closure (Range i) = univ :=
  di.dense.closure_range

protected theorem preconnected_space [PreconnectedSpace α] (di : DenseInducing i) : PreconnectedSpace β :=
  di.dense.PreconnectedSpace di.Continuous

theorem closure_image_mem_nhds {s : Set α} {a : α} (di : DenseInducing i) (hs : s ∈ 𝓝 a) : Closure (i '' s) ∈ 𝓝 (i a) :=
  by
  rw [di.nhds_eq_comap a, ((nhds_basis_opens _).comap _).mem_iff] at hs
  rcases hs with ⟨U, ⟨haU, hUo⟩, sub : i ⁻¹' U ⊆ s⟩
  refine' mem_of_superset (hUo.mem_nhds haU) _
  calc U ⊆ Closure (i '' (i ⁻¹' U)) := di.dense.subset_closure_image_preimage_of_is_open hUo _ ⊆ Closure (i '' s) :=
      closure_mono (image_subset i sub)

theorem dense_image (di : DenseInducing i) {s : Set α} : Dense (i '' s) ↔ Dense s := by
  refine' ⟨fun H x => _, di.dense.dense_image di.continuous⟩
  rw [di.to_inducing.closure_eq_preimage_closure_image, H.closure_eq, preimage_univ]
  trivial

/-- If `i : α → β` is a dense embedding with dense complement of the range, then any compact set in
`α` has empty interior. -/
theorem interior_compact_eq_empty [T2Space β] (di : DenseInducing i) (hd : Dense (Range iᶜ)) {s : Set α}
    (hs : IsCompact s) : Interior s = ∅ := by
  refine' eq_empty_iff_forall_not_mem.2 fun x hx => _
  rw [mem_interior_iff_mem_nhds] at hx
  have := di.closure_image_mem_nhds hx
  rw [(hs.image di.continuous).IsClosed.closure_eq] at this
  rcases hd.inter_nhds_nonempty this with ⟨y, hyi, hys⟩
  exact hyi (image_subset_range _ _ hys)

/-- The product of two dense inducings is a dense inducing -/
protected theorem prod [TopologicalSpace γ] [TopologicalSpace δ] {e₁ : α → β} {e₂ : γ → δ} (de₁ : DenseInducing e₁)
    (de₂ : DenseInducing e₂) : DenseInducing fun p : α × γ => (e₁ p.1, e₂ p.2) :=
  { induced := (de₁.to_inducing.prod_mk de₂.to_inducing).induced, dense := de₁.dense.prod_map de₂.dense }

open TopologicalSpace

/-- If the domain of a `dense_inducing` map is a separable space, then so is the codomain. -/
protected theorem separable_space [SeparableSpace α] : SeparableSpace β :=
  di.dense.SeparableSpace di.Continuous

variable [TopologicalSpace δ] {f : γ → α} {g : γ → δ} {h : δ → β}

/-- ```
 γ -f→ α
g↓     ↓e
 δ -h→ β
```
-/
theorem tendsto_comap_nhds_nhds {d : δ} {a : α} (di : DenseInducing i) (H : Tendsto h (𝓝 d) (𝓝 (i a)))
    (comm : h ∘ g = i ∘ f) : Tendsto f (comap g (𝓝 d)) (𝓝 a) := by
  have lim1 : map g (comap g (𝓝 d)) ≤ 𝓝 d := map_comap_le
  replace lim1 : map h (map g (comap g (𝓝 d))) ≤ map h (𝓝 d) := map_mono lim1
  rw [Filter.map_map, comm, ← Filter.map_map, map_le_iff_le_comap] at lim1
  have lim2 : comap i (map h (𝓝 d)) ≤ comap i (𝓝 (i a)) := comap_mono H
  rw [← di.nhds_eq_comap] at lim2
  exact le_transₓ lim1 lim2

protected theorem nhds_within_ne_bot (di : DenseInducing i) (b : β) : NeBot (𝓝[Range i] b) :=
  di.dense.nhds_within_ne_bot b

theorem comap_nhds_ne_bot (di : DenseInducing i) (b : β) : NeBot (comap i (𝓝 b)) :=
  comap_ne_bot fun s hs =>
    let ⟨_, ⟨ha, a, rfl⟩⟩ := mem_closure_iff_nhds.1 (di.dense b) s hs
    ⟨a, ha⟩

variable [TopologicalSpace γ]

/-- If `i : α → β` is a dense inducing, then any function `f : α → γ` "extends"
  to a function `g = extend di f : β → γ`. If `γ` is Hausdorff and `f` has a
  continuous extension, then `g` is the unique such extension. In general,
  `g` might not be continuous or even extend `f`. -/
def extend (di : DenseInducing i) (f : α → γ) (b : β) : γ :=
  @limₓ _ ⟨f (di.dense.some b)⟩ (comap i (𝓝 b)) f

theorem extend_eq_of_tendsto [T2Space γ] {b : β} {c : γ} {f : α → γ} (hf : Tendsto f (comap i (𝓝 b)) (𝓝 c)) :
    di.extend f b = c :=
  have := di.comap_nhds_ne_bot
  hf.lim_eq

theorem extend_eq_at [T2Space γ] {f : α → γ} {a : α} (hf : ContinuousAt f a) : di.extend f (i a) = f a :=
  extend_eq_of_tendsto _ <| di.nhds_eq_comap a ▸ hf

theorem extend_eq_at' [T2Space γ] {f : α → γ} {a : α} (c : γ) (hf : Tendsto f (𝓝 a) (𝓝 c)) : di.extend f (i a) = f a :=
  di.extend_eq_at (continuous_at_of_tendsto_nhds hf)

theorem extend_eq [T2Space γ] {f : α → γ} (hf : Continuous f) (a : α) : di.extend f (i a) = f a :=
  di.extend_eq_at hf.ContinuousAt

/-- Variation of `extend_eq` where we ask that `f` has a limit along `comap i (𝓝 b)` for each
`b : β`. This is a strictly stronger assumption than continuity of `f`, but in a lot of cases
you'd have to prove it anyway to use `continuous_extend`, so this avoids doing the work twice. -/
theorem extend_eq' [T2Space γ] {f : α → γ} (di : DenseInducing i) (hf : ∀ b, ∃ c, Tendsto f (comap i (𝓝 b)) (𝓝 c))
    (a : α) : di.extend f (i a) = f a := by
  rcases hf (i a) with ⟨b, hb⟩
  refine' di.extend_eq_at' b _
  rwa [← di.to_inducing.nhds_eq_comap] at hb

theorem extend_unique_at [T2Space γ] {b : β} {f : α → γ} {g : β → γ} (di : DenseInducing i)
    (hf : ∀ᶠ x in comap i (𝓝 b), g (i x) = f x) (hg : ContinuousAt g b) : di.extend f b = g b := by
  refine' di.extend_eq_of_tendsto fun s hs => mem_map.2 _
  suffices : ∀ᶠ x : α in comap i (𝓝 b), g (i x) ∈ s
  exact hf.mp (this.mono fun x hgx hfx => hfx ▸ hgx)
  clear hf f
  refine' eventually_comap.2 ((hg.eventually hs).mono _)
  rintro _ hxs x rfl
  exact hxs

theorem extend_unique [T2Space γ] {f : α → γ} {g : β → γ} (di : DenseInducing i) (hf : ∀ x, g (i x) = f x)
    (hg : Continuous g) : di.extend f = g :=
  funext fun b => extend_unique_at di (eventually_of_forall hf) hg.ContinuousAt

theorem continuous_at_extend [T3Space γ] {b : β} {f : α → γ} (di : DenseInducing i)
    (hf : ∀ᶠ x in 𝓝 b, ∃ c, Tendsto f (comap i <| 𝓝 x) (𝓝 c)) : ContinuousAt (di.extend f) b := by
  set φ := di.extend f
  have := di.comap_nhds_ne_bot
  suffices ∀, ∀ V' ∈ 𝓝 (φ b), ∀, IsClosed V' → φ ⁻¹' V' ∈ 𝓝 b by
    simpa [← ContinuousAt, ← (closed_nhds_basis _).tendsto_right_iff]
  intro V' V'_in V'_closed
  set V₁ := { x | tendsto f (comap i <| 𝓝 x) (𝓝 <| φ x) }
  have V₁_in : V₁ ∈ 𝓝 b := by
    filter_upwards [hf]
    rintro x ⟨c, hc⟩
    dsimp' [← V₁, ← φ]
    rwa [di.extend_eq_of_tendsto hc]
  obtain ⟨V₂, V₂_in, V₂_op, hV₂⟩ : ∃ V₂ ∈ 𝓝 b, IsOpen V₂ ∧ ∀, ∀ x ∈ i ⁻¹' V₂, ∀, f x ∈ V' := by
    simpa [← and_assoc] using
      ((nhds_basis_opens' b).comap i).tendsto_left_iff.mp (mem_of_mem_nhds V₁_in : b ∈ V₁) V' V'_in
  suffices ∀, ∀ x ∈ V₁ ∩ V₂, ∀, φ x ∈ V' by
    filter_upwards [inter_mem V₁_in V₂_in] using this
  rintro x ⟨x_in₁, x_in₂⟩
  have hV₂x : V₂ ∈ 𝓝 x := IsOpen.mem_nhds V₂_op x_in₂
  apply V'_closed.mem_of_tendsto x_in₁
  use V₂
  tauto

theorem continuous_extend [T3Space γ] {f : α → γ} (di : DenseInducing i)
    (hf : ∀ b, ∃ c, Tendsto f (comap i (𝓝 b)) (𝓝 c)) : Continuous (di.extend f) :=
  continuous_iff_continuous_at.mpr fun b => di.continuous_at_extend <| univ_mem' hf

theorem mk' (i : α → β) (c : Continuous i) (dense : ∀ x, x ∈ Closure (Range i))
    (H : ∀ (a : α), ∀ s ∈ 𝓝 a, ∀, ∃ t ∈ 𝓝 (i a), ∀ b, i b ∈ t → b ∈ s) : DenseInducing i :=
  { induced :=
      (induced_iff_nhds_eq i).2 fun a =>
        le_antisymmₓ (tendsto_iff_comap.1 <| c.Tendsto _)
          (by
            simpa [← Filter.le_def] using H a),
    dense }

end DenseInducing

/-- A dense embedding is an embedding with dense image. -/
structure DenseEmbedding [TopologicalSpace α] [TopologicalSpace β] (e : α → β) extends DenseInducing e : Prop where
  inj : Function.Injective e

theorem DenseEmbedding.mk' [TopologicalSpace α] [TopologicalSpace β] (e : α → β) (c : Continuous e)
    (dense : DenseRange e) (inj : Function.Injective e)
    (H : ∀ (a : α), ∀ s ∈ 𝓝 a, ∀, ∃ t ∈ 𝓝 (e a), ∀ b, e b ∈ t → b ∈ s) : DenseEmbedding e :=
  { DenseInducing.mk' e c Dense H with inj }

namespace DenseEmbedding

open TopologicalSpace

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

variable {e : α → β} (de : DenseEmbedding e)

theorem inj_iff {x y} : e x = e y ↔ x = y :=
  de.inj.eq_iff

theorem to_embedding : Embedding e :=
  { induced := de.induced, inj := de.inj }

/-- If the domain of a `dense_embedding` is a separable space, then so is its codomain. -/
protected theorem separable_space [SeparableSpace α] : SeparableSpace β :=
  de.to_dense_inducing.SeparableSpace

/-- The product of two dense embeddings is a dense embedding. -/
protected theorem prod {e₁ : α → β} {e₂ : γ → δ} (de₁ : DenseEmbedding e₁) (de₂ : DenseEmbedding e₂) :
    DenseEmbedding fun p : α × γ => (e₁ p.1, e₂ p.2) :=
  { DenseInducing.prod de₁.to_dense_inducing de₂.to_dense_inducing with
    inj := fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ => by
      simp <;> exact fun h₁ h₂ => ⟨de₁.inj h₁, de₂.inj h₂⟩ }

/-- The dense embedding of a subtype inside its closure. -/
@[simps]
def subtypeEmb {α : Type _} (p : α → Prop) (e : α → β) (x : { x // p x }) : { x // x ∈ Closure (e '' { x | p x }) } :=
  ⟨e x, subset_closure <| mem_image_of_mem e x.Prop⟩

protected theorem subtype (p : α → Prop) : DenseEmbedding (subtypeEmb p e) :=
  { dense :=
      dense_iff_closure_eq.2 <| by
        ext ⟨x, hx⟩
        rw [image_eq_range] at hx
        simpa [← closure_subtype, range_comp, ← (· ∘ ·)] ,
    inj := (de.inj.comp Subtype.coe_injective).codRestrict _,
    induced :=
      (induced_iff_nhds_eq _).2 fun ⟨x, hx⟩ => by
        simp [← subtype_emb, ← nhds_subtype_eq_comap, ← de.to_inducing.nhds_eq_comap, ← comap_comap, ← (· ∘ ·)] }

theorem dense_image {s : Set α} : Dense (e '' s) ↔ Dense s :=
  de.to_dense_inducing.dense_image

end DenseEmbedding

theorem Dense.dense_embedding_coe [TopologicalSpace α] {s : Set α} (hs : Dense s) : DenseEmbedding (coe : s → α) :=
  { embedding_subtype_coe with dense := hs.dense_range_coe }

theorem is_closed_property [TopologicalSpace β] {e : α → β} {p : β → Prop} (he : DenseRange e)
    (hp : IsClosed { x | p x }) (h : ∀ a, p (e a)) : ∀ b, p b :=
  have : univ ⊆ { b | p b } :=
    calc
      univ = Closure (Range e) := he.closure_range.symm
      _ ⊆ Closure { b | p b } := closure_mono <| range_subset_iff.mpr h
      _ = _ := hp.closure_eq
      
  fun b => this trivialₓ

theorem is_closed_property2 [TopologicalSpace β] {e : α → β} {p : β → β → Prop} (he : DenseRange e)
    (hp : IsClosed { q : β × β | p q.1 q.2 }) (h : ∀ a₁ a₂, p (e a₁) (e a₂)) : ∀ b₁ b₂, p b₁ b₂ :=
  have : ∀ q : β × β, p q.1 q.2 := (is_closed_property (he.prod_map he) hp) fun _ => h _ _
  fun b₁ b₂ => this ⟨b₁, b₂⟩

theorem is_closed_property3 [TopologicalSpace β] {e : α → β} {p : β → β → β → Prop} (he : DenseRange e)
    (hp : IsClosed { q : β × β × β | p q.1 q.2.1 q.2.2 }) (h : ∀ a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) :
    ∀ b₁ b₂ b₃, p b₁ b₂ b₃ :=
  have : ∀ q : β × β × β, p q.1 q.2.1 q.2.2 := (is_closed_property (he.prod_map <| he.prod_map he) hp) fun _ => h _ _ _
  fun b₁ b₂ b₃ => this ⟨b₁, b₂, b₃⟩

@[elab_as_eliminator]
theorem DenseRange.induction_on [TopologicalSpace β] {e : α → β} (he : DenseRange e) {p : β → Prop} (b₀ : β)
    (hp : IsClosed { b | p b }) (ih : ∀ a : α, p <| e a) : p b₀ :=
  is_closed_property he hp ih b₀

@[elab_as_eliminator]
theorem DenseRange.induction_on₂ [TopologicalSpace β] {e : α → β} {p : β → β → Prop} (he : DenseRange e)
    (hp : IsClosed { q : β × β | p q.1 q.2 }) (h : ∀ a₁ a₂, p (e a₁) (e a₂)) (b₁ b₂ : β) : p b₁ b₂ :=
  is_closed_property2 he hp h _ _

@[elab_as_eliminator]
theorem DenseRange.induction_on₃ [TopologicalSpace β] {e : α → β} {p : β → β → β → Prop} (he : DenseRange e)
    (hp : IsClosed { q : β × β × β | p q.1 q.2.1 q.2.2 }) (h : ∀ a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) (b₁ b₂ b₃ : β) :
    p b₁ b₂ b₃ :=
  is_closed_property3 he hp h _ _ _

section

variable [TopologicalSpace β] [TopologicalSpace γ] [T2Space γ]

variable {f : α → β}

/-- Two continuous functions to a t2-space that agree on the dense range of a function are equal. -/
theorem DenseRange.equalizer (hfd : DenseRange f) {g h : β → γ} (hg : Continuous g) (hh : Continuous h)
    (H : g ∘ f = h ∘ f) : g = h :=
  funext fun y => hfd.induction_on y (is_closed_eq hg hh) <| congr_fun H

end

-- Bourbaki GT III §3 no.4 Proposition 7 (generalised to any dense-inducing map to a T₃ space)
theorem Filter.HasBasis.has_basis_of_dense_inducing [TopologicalSpace α] [TopologicalSpace β] [T3Space β] {ι : Type _}
    {s : ι → Set α} {p : ι → Prop} {x : α} (h : (𝓝 x).HasBasis p s) {f : α → β} (hf : DenseInducing f) :
    ((𝓝 (f x)).HasBasis p) fun i => Closure <| f '' s i := by
  rw [Filter.has_basis_iff] at h⊢
  intro T
  refine' ⟨fun hT => _, fun hT => _⟩
  · obtain ⟨T', hT₁, hT₂, hT₃⟩ := nhds_is_closed hT
    have hT₄ : f ⁻¹' T' ∈ 𝓝 x := by
      rw [hf.to_inducing.nhds_eq_comap x]
      exact ⟨T', hT₁, subset.rfl⟩
    obtain ⟨i, hi, hi'⟩ := (h _).mp hT₄
    exact
      ⟨i, hi,
        (closure_mono (image_subset f hi')).trans
          (subset.trans (closure_minimal (image_subset_iff.mpr subset.rfl) hT₃) hT₂)⟩
    
  · obtain ⟨i, hi, hi'⟩ := hT
    suffices Closure (f '' s i) ∈ 𝓝 (f x) by
      filter_upwards [this] using hi'
    replace h := (h (s i)).mpr ⟨i, hi, subset.rfl⟩
    exact hf.closure_image_mem_nhds h
    


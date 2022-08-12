/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathbin.Topology.Maps
import Mathbin.Order.Filter.Pi
import Mathbin.Data.Fin.Tuple.Default

/-!
# Constructions of new topological spaces from old ones

This file constructs products, sums, subtypes and quotients of topological spaces
and sets up their basic theory, such as criteria for maps into or out of these
constructions to be continuous; descriptions of the open sets, neighborhood filters,
and generators of these constructions; and their behavior with respect to embeddings
and other specific classes of maps.

## Implementation note

The constructed topologies are defined using induced and coinduced topologies
along with the complete lattice structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags

product, sum, disjoint union, subspace, quotient space

-/


noncomputable section

open TopologicalSpace Set Filter

open Classical TopologicalSpace Filter

universe u v

variable {α : Type u} {β : Type v} {γ δ ε ζ : Type _}

section Constructions

instance {p : α → Prop} [t : TopologicalSpace α] : TopologicalSpace (Subtype p) :=
  induced coe t

instance {r : α → α → Prop} [t : TopologicalSpace α] : TopologicalSpace (Quot r) :=
  coinduced (Quot.mk r) t

instance {s : Setoidₓ α} [t : TopologicalSpace α] : TopologicalSpace (Quotientₓ s) :=
  coinduced Quotientₓ.mk t

instance [t₁ : TopologicalSpace α] [t₂ : TopologicalSpace β] : TopologicalSpace (α × β) :=
  induced Prod.fst t₁⊓induced Prod.snd t₂

instance [t₁ : TopologicalSpace α] [t₂ : TopologicalSpace β] : TopologicalSpace (Sum α β) :=
  coinduced Sum.inl t₁⊔coinduced Sum.inr t₂

instance {β : α → Type v} [t₂ : ∀ a, TopologicalSpace (β a)] : TopologicalSpace (Sigma β) :=
  ⨆ a, coinduced (Sigma.mk a) (t₂ a)

instance Pi.topologicalSpace {β : α → Type v} [t₂ : ∀ a, TopologicalSpace (β a)] : TopologicalSpace (∀ a, β a) :=
  ⨅ a, induced (fun f => f a) (t₂ a)

instance ULift.topologicalSpace [t : TopologicalSpace α] : TopologicalSpace (ULift.{v, u} α) :=
  t.induced ULift.down

theorem Quotientₓ.preimage_mem_nhds [TopologicalSpace α] [s : Setoidₓ α] {V : Set <| Quotientₓ s} {a : α}
    (hs : V ∈ 𝓝 (Quotientₓ.mk a)) : Quotientₓ.mk ⁻¹' V ∈ 𝓝 a :=
  preimage_nhds_coinduced hs

/-- The image of a dense set under `quotient.mk` is a dense set. -/
theorem Dense.quotient [Setoidₓ α] [TopologicalSpace α] {s : Set α} (H : Dense s) : Dense (Quotientₓ.mk '' s) :=
  (surjective_quotient_mk α).DenseRange.dense_image continuous_coinduced_rng H

/-- The composition of `quotient.mk` and a function with dense range has dense range. -/
theorem DenseRange.quotient [Setoidₓ α] [TopologicalSpace α] {f : β → α} (hf : DenseRange f) :
    DenseRange (Quotientₓ.mk ∘ f) :=
  (surjective_quotient_mk α).DenseRange.comp hf continuous_coinduced_rng

instance {p : α → Prop} [TopologicalSpace α] [DiscreteTopology α] : DiscreteTopology (Subtype p) :=
  ⟨bot_unique fun s hs => ⟨coe '' s, is_open_discrete _, Set.preimage_image_eq _ Subtype.coe_injective⟩⟩

instance Sum.discrete_topology [TopologicalSpace α] [TopologicalSpace β] [hα : DiscreteTopology α]
    [hβ : DiscreteTopology β] : DiscreteTopology (Sum α β) :=
  ⟨by
    unfold Sum.topologicalSpace <;> simp [← hα.eq_bot, ← hβ.eq_bot]⟩

instance Sigma.discrete_topology {β : α → Type v} [∀ a, TopologicalSpace (β a)] [h : ∀ a, DiscreteTopology (β a)] :
    DiscreteTopology (Sigma β) :=
  ⟨by
    unfold Sigma.topologicalSpace
    simp [← fun a => (h a).eq_bot]⟩

section Topα

variable [TopologicalSpace α]

/-
The 𝓝 filter and the subspace topology.
-/
theorem mem_nhds_subtype (s : Set α) (a : { x // x ∈ s }) (t : Set { x // x ∈ s }) :
    t ∈ 𝓝 a ↔ ∃ u ∈ 𝓝 (a : α), coe ⁻¹' u ⊆ t :=
  mem_nhds_induced coe a t

theorem nhds_subtype (s : Set α) (a : { x // x ∈ s }) : 𝓝 a = comap coe (𝓝 (a : α)) :=
  nhds_induced coe a

end Topα

/-- A type synonym equiped with the topology whose open sets are the empty set and the sets with
finite complements. -/
def CofiniteTopology (α : Type _) :=
  α

namespace CofiniteTopology

/-- The identity equivalence between `α` and `cofinite_topology α`. -/
def of : α ≃ CofiniteTopology α :=
  Equivₓ.refl α

instance [Inhabited α] : Inhabited (CofiniteTopology α) where default := of default

instance : TopologicalSpace (CofiniteTopology α) where
  IsOpen := fun s => s.Nonempty → Set.Finite (sᶜ)
  is_open_univ := by
    simp
  is_open_inter := fun s t => by
    rintro hs ht ⟨x, hxs, hxt⟩
    rw [compl_inter]
    exact (hs ⟨x, hxs⟩).union (ht ⟨x, hxt⟩)
  is_open_sUnion := by
    rintro s h ⟨x, t, hts, hzt⟩
    rw [Set.compl_sUnion]
    exact Set.Finite.sInter (mem_image_of_mem _ hts) (h t hts ⟨x, hzt⟩)

theorem is_open_iff {s : Set (CofiniteTopology α)} : IsOpen s ↔ s.Nonempty → sᶜ.Finite :=
  Iff.rfl

theorem is_open_iff' {s : Set (CofiniteTopology α)} : IsOpen s ↔ s = ∅ ∨ sᶜ.Finite := by
  simp only [← is_open_iff, ne_empty_iff_nonempty, ← or_iff_not_imp_left]

theorem is_closed_iff {s : Set (CofiniteTopology α)} : IsClosed s ↔ s = univ ∨ s.Finite := by
  simp [is_open_compl_iff, ← is_open_iff']

theorem nhds_eq (a : CofiniteTopology α) : 𝓝 a = pure a⊔cofinite := by
  ext U
  rw [mem_nhds_iff]
  constructor
  · rintro ⟨V, hVU, V_op, haV⟩
    exact mem_sup.mpr ⟨hVU haV, mem_of_superset (V_op ⟨_, haV⟩) hVU⟩
    
  · rintro ⟨hU : a ∈ U, hU' : Uᶜ.Finite⟩
    exact ⟨U, subset.rfl, fun h => hU', hU⟩
    

theorem mem_nhds_iff {a : CofiniteTopology α} {s : Set (CofiniteTopology α)} : s ∈ 𝓝 a ↔ a ∈ s ∧ sᶜ.Finite := by
  simp [← nhds_eq]

end CofiniteTopology

end Constructions

section Prod

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ] [TopologicalSpace ε]
  [TopologicalSpace ζ]

@[continuity]
theorem continuous_fst : Continuous (@Prod.fst α β) :=
  continuous_inf_dom_left continuous_induced_dom

/-- Postcomposing `f` with `prod.fst` is continuous -/
theorem Continuous.fst {f : α → β × γ} (hf : Continuous f) : Continuous fun a : α => (f a).1 :=
  continuous_fst.comp hf

/-- Precomposing `f` with `prod.fst` is continuous -/
theorem Continuous.fst' {f : α → γ} (hf : Continuous f) : Continuous fun x : α × β => f x.fst :=
  hf.comp continuous_fst

theorem continuous_at_fst {p : α × β} : ContinuousAt Prod.fst p :=
  continuous_fst.ContinuousAt

/-- Postcomposing `f` with `prod.fst` is continuous at `x` -/
theorem ContinuousAt.fst {f : α → β × γ} {x : α} (hf : ContinuousAt f x) : ContinuousAt (fun a : α => (f a).1) x :=
  continuous_at_fst.comp hf

/-- Precomposing `f` with `prod.fst` is continuous at `(x, y)` -/
theorem ContinuousAt.fst' {f : α → γ} {x : α} {y : β} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : α × β => f x.fst) (x, y) :=
  ContinuousAt.comp hf continuous_at_fst

/-- Precomposing `f` with `prod.fst` is continuous at `x : α × β` -/
theorem ContinuousAt.fst'' {f : α → γ} {x : α × β} (hf : ContinuousAt f x.fst) :
    ContinuousAt (fun x : α × β => f x.fst) x :=
  hf.comp continuous_at_fst

@[continuity]
theorem continuous_snd : Continuous (@Prod.snd α β) :=
  continuous_inf_dom_right continuous_induced_dom

/-- Postcomposing `f` with `prod.snd` is continuous -/
theorem Continuous.snd {f : α → β × γ} (hf : Continuous f) : Continuous fun a : α => (f a).2 :=
  continuous_snd.comp hf

/-- Precomposing `f` with `prod.snd` is continuous -/
theorem Continuous.snd' {f : β → γ} (hf : Continuous f) : Continuous fun x : α × β => f x.snd :=
  hf.comp continuous_snd

theorem continuous_at_snd {p : α × β} : ContinuousAt Prod.snd p :=
  continuous_snd.ContinuousAt

/-- Postcomposing `f` with `prod.snd` is continuous at `x` -/
theorem ContinuousAt.snd {f : α → β × γ} {x : α} (hf : ContinuousAt f x) : ContinuousAt (fun a : α => (f a).2) x :=
  continuous_at_snd.comp hf

/-- Precomposing `f` with `prod.snd` is continuous at `(x, y)` -/
theorem ContinuousAt.snd' {f : β → γ} {x : α} {y : β} (hf : ContinuousAt f y) :
    ContinuousAt (fun x : α × β => f x.snd) (x, y) :=
  ContinuousAt.comp hf continuous_at_snd

/-- Precomposing `f` with `prod.snd` is continuous at `x : α × β` -/
theorem ContinuousAt.snd'' {f : β → γ} {x : α × β} (hf : ContinuousAt f x.snd) :
    ContinuousAt (fun x : α × β => f x.snd) x :=
  hf.comp continuous_at_snd

@[continuity]
theorem Continuous.prod_mk {f : γ → α} {g : γ → β} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => (f x, g x) :=
  continuous_inf_rng (continuous_induced_rng hf) (continuous_induced_rng hg)

@[continuity]
theorem Continuous.Prod.mk (a : α) : Continuous fun b : β => (a, b) :=
  continuous_const.prod_mk continuous_id'

@[continuity]
theorem Continuous.Prod.mk_left (b : β) : Continuous fun a : α => (a, b) :=
  continuous_id'.prod_mk continuous_const

theorem Continuous.comp₂ {g : α × β → γ} (hg : Continuous g) {e : δ → α} (he : Continuous e) {f : δ → β}
    (hf : Continuous f) : Continuous fun x => g (e x, f x) :=
  hg.comp <| he.prod_mk hf

theorem Continuous.comp₃ {g : α × β × γ → ε} (hg : Continuous g) {e : δ → α} (he : Continuous e) {f : δ → β}
    (hf : Continuous f) {k : δ → γ} (hk : Continuous k) : Continuous fun x => g (e x, f x, k x) :=
  hg.comp₂ he <| hf.prod_mk hk

theorem Continuous.comp₄ {g : α × β × γ × ζ → ε} (hg : Continuous g) {e : δ → α} (he : Continuous e) {f : δ → β}
    (hf : Continuous f) {k : δ → γ} (hk : Continuous k) {l : δ → ζ} (hl : Continuous l) :
    Continuous fun x => g (e x, f x, k x, l x) :=
  hg.comp₃ he hf <| hk.prod_mk hl

theorem Continuous.prod_map {f : γ → α} {g : δ → β} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x : γ × δ => (f x.1, g x.2) :=
  hf.fst'.prod_mk hg.snd'

/-- A version of `continuous_inf_dom_left` for binary functions -/
theorem continuous_inf_dom_left₂ {α β γ} {f : α → β → γ} {ta1 ta2 : TopologicalSpace α} {tb1 tb2 : TopologicalSpace β}
    {tc1 : TopologicalSpace γ}
    (h : by
      have := ta1 <;> have := tb1 <;> exact Continuous fun p : α × β => f p.1 p.2) :
    by
    have := ta1⊓ta2 <;> have := tb1⊓tb2 <;> exact Continuous fun p : α × β => f p.1 p.2 := by
  have ha := @continuous_inf_dom_left _ _ id ta1 ta2 ta1 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_left _ _ id tb1 tb2 tb1 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prod_map _ _ _ _ ta1 tb1 (ta1⊓ta2) (tb1⊓tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id

/-- A version of `continuous_inf_dom_right` for binary functions -/
theorem continuous_inf_dom_right₂ {α β γ} {f : α → β → γ} {ta1 ta2 : TopologicalSpace α} {tb1 tb2 : TopologicalSpace β}
    {tc1 : TopologicalSpace γ}
    (h : by
      have := ta2 <;> have := tb2 <;> exact Continuous fun p : α × β => f p.1 p.2) :
    by
    have := ta1⊓ta2 <;> have := tb1⊓tb2 <;> exact Continuous fun p : α × β => f p.1 p.2 := by
  have ha := @continuous_inf_dom_right _ _ id ta1 ta2 ta2 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_right _ _ id tb1 tb2 tb2 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prod_map _ _ _ _ ta2 tb2 (ta1⊓ta2) (tb1⊓tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id

/-- A version of `continuous_Inf_dom` for binary functions -/
theorem continuous_Inf_dom₂ {α β γ} {f : α → β → γ} {tas : Set (TopologicalSpace α)} {tbs : Set (TopologicalSpace β)}
    {ta : TopologicalSpace α} {tb : TopologicalSpace β} {tc : TopologicalSpace γ} (ha : ta ∈ tas) (hb : tb ∈ tbs)
    (hf : Continuous fun p : α × β => f p.1 p.2) : by
    have := Inf tas <;> have := Inf tbs <;> exact @Continuous _ _ _ tc fun p : α × β => f p.1 p.2 := by
  let t : TopologicalSpace (α × β) := Prod.topologicalSpace
  have ha := continuous_Inf_dom ha continuous_id
  have hb := continuous_Inf_dom hb continuous_id
  have h_continuous_id := @Continuous.prod_map _ _ _ _ ta tb (Inf tas) (Inf tbs) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ hf h_continuous_id

theorem Filter.Eventually.prod_inl_nhds {p : α → Prop} {a : α} (h : ∀ᶠ x in 𝓝 a, p x) (b : β) :
    ∀ᶠ x in 𝓝 (a, b), p (x : α × β).1 :=
  continuous_at_fst h

theorem Filter.Eventually.prod_inr_nhds {p : β → Prop} {b : β} (h : ∀ᶠ x in 𝓝 b, p x) (a : α) :
    ∀ᶠ x in 𝓝 (a, b), p (x : α × β).2 :=
  continuous_at_snd h

theorem Filter.Eventually.prod_mk_nhds {pa : α → Prop} {a} (ha : ∀ᶠ x in 𝓝 a, pa x) {pb : β → Prop} {b}
    (hb : ∀ᶠ y in 𝓝 b, pb y) : ∀ᶠ p in 𝓝 (a, b), pa (p : α × β).1 ∧ pb p.2 :=
  (ha.prod_inl_nhds b).And (hb.prod_inr_nhds a)

theorem continuous_swap : Continuous (Prod.swap : α × β → β × α) :=
  continuous_snd.prod_mk continuous_fst

theorem continuous_uncurry_left {f : α → β → γ} (a : α) (h : Continuous (Function.uncurry f)) : Continuous (f a) :=
  show Continuous (Function.uncurry f ∘ fun b => (a, b)) from
    h.comp
      (by
        continuity)

theorem continuous_uncurry_right {f : α → β → γ} (b : β) (h : Continuous (Function.uncurry f)) :
    Continuous fun a => f a b :=
  show Continuous (Function.uncurry f ∘ fun a => (a, b)) from
    h.comp
      (by
        continuity)

theorem continuous_curry {g : α × β → γ} (a : α) (h : Continuous g) : Continuous (Function.curry g a) :=
  show Continuous (g ∘ fun b => (a, b)) from
    h.comp
      (by
        continuity)

theorem IsOpen.prod {s : Set α} {t : Set β} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ×ˢ t) :=
  (hs.Preimage continuous_fst).inter (ht.Preimage continuous_snd)

theorem nhds_prod_eq {a : α} {b : β} : 𝓝 (a, b) = 𝓝 a ×ᶠ 𝓝 b := by
  rw [Filter.prod, Prod.topologicalSpace, nhds_inf, nhds_induced, nhds_induced]

/-- If a function `f x y` is such that `y ↦ f x y` is continuous for all `x`, and `x` lives in a
discrete space, then `f` is continuous. -/
theorem continuous_uncurry_of_discrete_topology [DiscreteTopology α] {f : α → β → γ} (hf : ∀ a, Continuous (f a)) :
    Continuous (Function.uncurry f) := by
  apply continuous_iff_continuous_at.2
  rintro ⟨a, x⟩
  change map _ _ ≤ _
  rw [nhds_prod_eq, nhds_discrete, Filter.map_pure_prod]
  exact (hf a).ContinuousAt

theorem mem_nhds_prod_iff {a : α} {b : β} {s : Set (α × β)} : s ∈ 𝓝 (a, b) ↔ ∃ u ∈ 𝓝 a, ∃ v ∈ 𝓝 b, u ×ˢ v ⊆ s := by
  rw [nhds_prod_eq, mem_prod_iff]

theorem mem_nhds_prod_iff' {a : α} {b : β} {s : Set (α × β)} :
    s ∈ 𝓝 (a, b) ↔ ∃ (u : Set α)(v : Set β), IsOpen u ∧ a ∈ u ∧ IsOpen v ∧ b ∈ v ∧ u ×ˢ v ⊆ s := by
  rw [mem_nhds_prod_iff]
  constructor
  · rintro ⟨u, Hu, v, Hv, h⟩
    rcases mem_nhds_iff.1 Hu with ⟨u', u'u, u'_open, Hu'⟩
    rcases mem_nhds_iff.1 Hv with ⟨v', v'v, v'_open, Hv'⟩
    exact ⟨u', v', u'_open, Hu', v'_open, Hv', (Set.prod_mono u'u v'v).trans h⟩
    
  · rintro ⟨u, v, u_open, au, v_open, bv, huv⟩
    exact ⟨u, u_open.mem_nhds au, v, v_open.mem_nhds bv, huv⟩
    

theorem _root_.prod.tendsto_iff {α} (seq : α → β × γ) {f : Filter α} (x : β × γ) :
    Tendsto seq f (𝓝 x) ↔ Tendsto (fun n => (seq n).fst) f (𝓝 x.fst) ∧ Tendsto (fun n => (seq n).snd) f (𝓝 x.snd) := by
  cases x
  rw [nhds_prod_eq, Filter.tendsto_prod_iff']

theorem Filter.HasBasis.prod_nhds {ιa ιb : Type _} {pa : ιa → Prop} {pb : ιb → Prop} {sa : ιa → Set α} {sb : ιb → Set β}
    {a : α} {b : β} (ha : (𝓝 a).HasBasis pa sa) (hb : (𝓝 b).HasBasis pb sb) :
    (𝓝 (a, b)).HasBasis (fun i : ιa × ιb => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 := by
  rw [nhds_prod_eq]
  exact ha.prod hb

theorem Filter.HasBasis.prod_nhds' {ιa ιb : Type _} {pa : ιa → Prop} {pb : ιb → Prop} {sa : ιa → Set α}
    {sb : ιb → Set β} {ab : α × β} (ha : (𝓝 ab.1).HasBasis pa sa) (hb : (𝓝 ab.2).HasBasis pb sb) :
    (𝓝 ab).HasBasis (fun i : ιa × ιb => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 := by
  cases ab
  exact ha.prod_nhds hb

instance [DiscreteTopology α] [DiscreteTopology β] : DiscreteTopology (α × β) :=
  ⟨eq_of_nhds_eq_nhds fun ⟨a, b⟩ => by
      rw [nhds_prod_eq, nhds_discrete α, nhds_discrete β, nhds_bot, Filter.prod_pure_pure]⟩

theorem prod_mem_nhds_iff {s : Set α} {t : Set β} {a : α} {b : β} : s ×ˢ t ∈ 𝓝 (a, b) ↔ s ∈ 𝓝 a ∧ t ∈ 𝓝 b := by
  rw [nhds_prod_eq, prod_mem_prod_iff]

theorem prod_mem_nhds {s : Set α} {t : Set β} {a : α} {b : β} (ha : s ∈ 𝓝 a) (hb : t ∈ 𝓝 b) : s ×ˢ t ∈ 𝓝 (a, b) :=
  prod_mem_nhds_iff.2 ⟨ha, hb⟩

theorem Filter.Eventually.prod_nhds {p : α → Prop} {q : β → Prop} {a : α} {b : β} (ha : ∀ᶠ x in 𝓝 a, p x)
    (hb : ∀ᶠ y in 𝓝 b, q y) : ∀ᶠ z : α × β in 𝓝 (a, b), p z.1 ∧ q z.2 :=
  prod_mem_nhds ha hb

theorem nhds_swap (a : α) (b : β) : 𝓝 (a, b) = (𝓝 (b, a)).map Prod.swap := by
  rw [nhds_prod_eq, Filter.prod_comm, nhds_prod_eq] <;> rfl

theorem Filter.Tendsto.prod_mk_nhds {γ} {a : α} {b : β} {f : Filter γ} {ma : γ → α} {mb : γ → β}
    (ha : Tendsto ma f (𝓝 a)) (hb : Tendsto mb f (𝓝 b)) : Tendsto (fun c => (ma c, mb c)) f (𝓝 (a, b)) := by
  rw [nhds_prod_eq] <;> exact Filter.Tendsto.prod_mk ha hb

theorem Filter.Eventually.curry_nhds {p : α × β → Prop} {x : α} {y : β} (h : ∀ᶠ x in 𝓝 (x, y), p x) :
    ∀ᶠ x' in 𝓝 x, ∀ᶠ y' in 𝓝 y, p (x', y') := by
  rw [nhds_prod_eq] at h
  exact h.curry

theorem ContinuousAt.prod {f : α → β} {g : α → γ} {x : α} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => (f x, g x)) x :=
  hf.prod_mk_nhds hg

theorem ContinuousAt.prod_map {f : α → γ} {g : β → δ} {p : α × β} (hf : ContinuousAt f p.fst)
    (hg : ContinuousAt g p.snd) : ContinuousAt (fun p : α × β => (f p.1, g p.2)) p :=
  hf.fst''.Prod hg.snd''

theorem ContinuousAt.prod_map' {f : α → γ} {g : β → δ} {x : α} {y : β} (hf : ContinuousAt f x) (hg : ContinuousAt g y) :
    ContinuousAt (fun p : α × β => (f p.1, g p.2)) (x, y) :=
  hf.fst'.Prod hg.snd'

theorem prod_generate_from_generate_from_eq {α β : Type _} {s : Set (Set α)} {t : Set (Set β)} (hs : ⋃₀s = univ)
    (ht : ⋃₀t = univ) :
    @Prod.topologicalSpace α β (generateFrom s) (generateFrom t) = generateFrom { g | ∃ u ∈ s, ∃ v ∈ t, g = u ×ˢ v } :=
  let G := generateFrom { g | ∃ u ∈ s, ∃ v ∈ t, g = u ×ˢ v }
  le_antisymmₓ
    (le_generate_from fun g ⟨u, hu, v, hv, g_eq⟩ =>
      g_eq.symm ▸
        @IsOpen.prod _ _ (generateFrom s) (generateFrom t) _ _ (GenerateOpen.basic _ hu) (GenerateOpen.basic _ hv))
    (le_inf
      (coinduced_le_iff_le_induced.mp <|
        le_generate_from fun u hu =>
          have : (⋃ v ∈ t, u ×ˢ v) = Prod.fst ⁻¹' u := by
            simp_rw [← prod_Union, ← sUnion_eq_bUnion, ht, prod_univ]
          show G.IsOpen (Prod.fst ⁻¹' u) by
            rw [← this]
            exact is_open_Union fun v => is_open_Union fun hv => generate_open.basic _ ⟨_, hu, _, hv, rfl⟩)
      (coinduced_le_iff_le_induced.mp <|
        le_generate_from fun v hv =>
          have : (⋃ u ∈ s, u ×ˢ v) = Prod.snd ⁻¹' v := by
            simp_rw [← Union_prod_const, ← sUnion_eq_bUnion, hs, univ_prod]
          show G.IsOpen (Prod.snd ⁻¹' v) by
            rw [← this]
            exact is_open_Union fun u => is_open_Union fun hu => generate_open.basic _ ⟨_, hu, _, hv, rfl⟩))

theorem prod_eq_generate_from :
    Prod.topologicalSpace = generateFrom { g | ∃ (s : Set α)(t : Set β), IsOpen s ∧ IsOpen t ∧ g = s ×ˢ t } :=
  le_antisymmₓ (le_generate_from fun g ⟨s, t, hs, ht, g_eq⟩ => g_eq.symm ▸ hs.Prod ht)
    (le_inf
      (ball_image_of_ball fun t ht =>
        GenerateOpen.basic _
          ⟨t, Univ, by
            simpa [← Set.prod_eq] using ht⟩)
      (ball_image_of_ball fun t ht =>
        GenerateOpen.basic _
          ⟨Univ, t, by
            simpa [← Set.prod_eq] using ht⟩))

theorem is_open_prod_iff {s : Set (α × β)} :
    IsOpen s ↔ ∀ a b, (a, b) ∈ s → ∃ (u : Set α)(v : Set β), IsOpen u ∧ IsOpen v ∧ a ∈ u ∧ b ∈ v ∧ u ×ˢ v ⊆ s := by
  rw [is_open_iff_nhds]
  simp_rw [le_principal_iff, Prod.forall, ((nhds_basis_opens _).prod_nhds (nhds_basis_opens _)).mem_iff, Prod.exists,
    exists_prop]
  simp only [← and_assoc, ← And.left_comm]

/-- A product of induced topologies is induced by the product map -/
theorem prod_induced_induced {α γ : Type _} (f : α → β) (g : γ → δ) :
    @Prod.topologicalSpace α γ (induced f ‹_›) (induced g ‹_›) =
      induced (fun p => (f p.1, g p.2)) Prod.topologicalSpace :=
  by
  simp_rw [Prod.topologicalSpace, induced_inf, induced_compose]

theorem continuous_uncurry_of_discrete_topology_left [DiscreteTopology α] {f : α → β → γ} (h : ∀ a, Continuous (f a)) :
    Continuous (Function.uncurry f) :=
  continuous_iff_continuous_at.2 fun ⟨a, b⟩ => by
    simp only [← ContinuousAt, ← nhds_prod_eq, ← nhds_discrete α, ← pure_prod, ← tendsto_map'_iff, ← (· ∘ ·), ←
      Function.uncurry, ← (h a).Tendsto]

/-- Given a neighborhood `s` of `(x, x)`, then `(x, x)` has a square open neighborhood
  that is a subset of `s`. -/
theorem exists_nhds_square {s : Set (α × α)} {x : α} (hx : s ∈ 𝓝 (x, x)) : ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ U ×ˢ U ⊆ s :=
  by
  simpa [← nhds_prod_eq, ← (nhds_basis_opens x).prod_self.mem_iff, ← And.assoc, ← And.left_comm] using hx

/-- `prod.fst` maps neighborhood of `x : α × β` within the section `prod.snd ⁻¹' {x.2}`
to `𝓝 x.1`. -/
theorem map_fst_nhds_within (x : α × β) : map Prod.fst (𝓝[Prod.snd ⁻¹' {x.2}] x) = 𝓝 x.1 := by
  refine' le_antisymmₓ (continuous_at_fst.mono_left inf_le_left) fun s hs => _
  rcases x with ⟨x, y⟩
  rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [← prod_subset_iff, ← mem_singleton_iff, ← mem_set_of_eq, ← mem_preimage] at H
  exact mem_of_superset hu fun z hz => H _ hz _ (mem_of_mem_nhds hv) rfl

@[simp]
theorem map_fst_nhds (x : α × β) : map Prod.fst (𝓝 x) = 𝓝 x.1 :=
  le_antisymmₓ continuous_at_fst <| (map_fst_nhds_within x).symm.trans_le (map_mono inf_le_left)

/-- The first projection in a product of topological spaces sends open sets to open sets. -/
theorem is_open_map_fst : IsOpenMap (@Prod.fst α β) :=
  is_open_map_iff_nhds_le.2 fun x => (map_fst_nhds x).Ge

/-- `prod.snd` maps neighborhood of `x : α × β` within the section `prod.fst ⁻¹' {x.1}`
to `𝓝 x.2`. -/
theorem map_snd_nhds_within (x : α × β) : map Prod.snd (𝓝[Prod.fst ⁻¹' {x.1}] x) = 𝓝 x.2 := by
  refine' le_antisymmₓ (continuous_at_snd.mono_left inf_le_left) fun s hs => _
  rcases x with ⟨x, y⟩
  rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [← prod_subset_iff, ← mem_singleton_iff, ← mem_set_of_eq, ← mem_preimage] at H
  exact mem_of_superset hv fun z hz => H _ (mem_of_mem_nhds hu) _ hz rfl

@[simp]
theorem map_snd_nhds (x : α × β) : map Prod.snd (𝓝 x) = 𝓝 x.2 :=
  le_antisymmₓ continuous_at_snd <| (map_snd_nhds_within x).symm.trans_le (map_mono inf_le_left)

/-- The second projection in a product of topological spaces sends open sets to open sets. -/
theorem is_open_map_snd : IsOpenMap (@Prod.snd α β) :=
  is_open_map_iff_nhds_le.2 fun x => (map_snd_nhds x).Ge

/-- A product set is open in a product space if and only if each factor is open, or one of them is
empty -/
theorem is_open_prod_iff' {s : Set α} {t : Set β} : IsOpen (s ×ˢ t) ↔ IsOpen s ∧ IsOpen t ∨ s = ∅ ∨ t = ∅ := by
  cases' (s ×ˢ t : Set _).eq_empty_or_nonempty with h h
  · simp [← h, ← prod_eq_empty_iff.1 h]
    
  · have st : s.nonempty ∧ t.nonempty := prod_nonempty_iff.1 h
    constructor
    · intro (H : IsOpen (s ×ˢ t))
      refine' Or.inl ⟨_, _⟩
      show IsOpen s
      · rw [← fst_image_prod s st.2]
        exact is_open_map_fst _ H
        
      show IsOpen t
      · rw [← snd_image_prod st.1 t]
        exact is_open_map_snd _ H
        
      
    · intro H
      simp only [← st.1.ne_empty, ← st.2.ne_empty, ← not_false_iff, ← or_falseₓ] at H
      exact H.1.Prod H.2
      
    

theorem closure_prod_eq {s : Set α} {t : Set β} : Closure (s ×ˢ t) = Closure s ×ˢ Closure t :=
  Set.ext fun ⟨a, b⟩ => by
    have : (𝓝 a ×ᶠ 𝓝 b)⊓𝓟 (s ×ˢ t) = 𝓝 a⊓𝓟 s ×ᶠ 𝓝 b⊓𝓟 t := by
      rw [← prod_inf_prod, prod_principal_principal]
    simp [← closure_eq_cluster_pts, ← ClusterPt, ← nhds_prod_eq, ← this] <;> exact prod_ne_bot

theorem interior_prod_eq (s : Set α) (t : Set β) : Interior (s ×ˢ t) = Interior s ×ˢ Interior t :=
  Set.ext fun ⟨a, b⟩ => by
    simp only [← mem_interior_iff_mem_nhds, ← mem_prod, ← prod_mem_nhds_iff]

theorem frontier_prod_eq (s : Set α) (t : Set β) :
    Frontier (s ×ˢ t) = Closure s ×ˢ Frontier t ∪ Frontier s ×ˢ Closure t := by
  simp only [← Frontier, ← closure_prod_eq, ← interior_prod_eq, ← prod_diff_prod]

@[simp]
theorem frontier_prod_univ_eq (s : Set α) : Frontier (s ×ˢ (Univ : Set β)) = Frontier s ×ˢ (Univ : Set β) := by
  simp [← frontier_prod_eq]

@[simp]
theorem frontier_univ_prod_eq (s : Set β) : Frontier ((Univ : Set α) ×ˢ s) = (Univ : Set α) ×ˢ Frontier s := by
  simp [← frontier_prod_eq]

theorem map_mem_closure2 {s : Set α} {t : Set β} {u : Set γ} {f : α → β → γ} {a : α} {b : β}
    (hf : Continuous fun p : α × β => f p.1 p.2) (ha : a ∈ Closure s) (hb : b ∈ Closure t)
    (hu : ∀ a b, a ∈ s → b ∈ t → f a b ∈ u) : f a b ∈ Closure u :=
  have : (a, b) ∈ Closure (s ×ˢ t) := by
    rw [closure_prod_eq] <;> exact ⟨ha, hb⟩
  show (fun p : α × β => f p.1 p.2) (a, b) ∈ Closure u from
    (map_mem_closure hf this) fun ⟨a, b⟩ ⟨ha, hb⟩ => hu a b ha hb

theorem IsClosed.prod {s₁ : Set α} {s₂ : Set β} (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : IsClosed (s₁ ×ˢ s₂) :=
  closure_eq_iff_is_closed.mp <| by
    simp only [← h₁.closure_eq, ← h₂.closure_eq, ← closure_prod_eq]

/-- The product of two dense sets is a dense set. -/
theorem Dense.prod {s : Set α} {t : Set β} (hs : Dense s) (ht : Dense t) : Dense (s ×ˢ t) := fun x => by
  rw [closure_prod_eq]
  exact ⟨hs x.1, ht x.2⟩

/-- If `f` and `g` are maps with dense range, then `prod.map f g` has dense range. -/
theorem DenseRange.prod_map {ι : Type _} {κ : Type _} {f : ι → β} {g : κ → γ} (hf : DenseRange f) (hg : DenseRange g) :
    DenseRange (Prod.map f g) := by
  simpa only [← DenseRange, ← prod_range_range_eq] using hf.prod hg

theorem Inducing.prod_mk {f : α → β} {g : γ → δ} (hf : Inducing f) (hg : Inducing g) :
    Inducing fun x : α × γ => (f x.1, g x.2) :=
  ⟨by
    rw [Prod.topologicalSpace, Prod.topologicalSpace, hf.induced, hg.induced, induced_compose, induced_compose,
      induced_inf, induced_compose, induced_compose]⟩

theorem Embedding.prod_mk {f : α → β} {g : γ → δ} (hf : Embedding f) (hg : Embedding g) :
    Embedding fun x : α × γ => (f x.1, g x.2) :=
  { hf.to_inducing.prod_mk hg.to_inducing with
    inj := fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ => by
      simp <;> exact fun h₁ h₂ => ⟨hf.inj h₁, hg.inj h₂⟩ }

protected theorem IsOpenMap.prod {f : α → β} {g : γ → δ} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap fun p : α × γ => (f p.1, g p.2) := by
  rw [is_open_map_iff_nhds_le]
  rintro ⟨a, b⟩
  rw [nhds_prod_eq, nhds_prod_eq, ← Filter.prod_map_map_eq]
  exact Filter.prod_mono (is_open_map_iff_nhds_le.1 hf a) (is_open_map_iff_nhds_le.1 hg b)

protected theorem OpenEmbedding.prod {f : α → β} {g : γ → δ} (hf : OpenEmbedding f) (hg : OpenEmbedding g) :
    OpenEmbedding fun x : α × γ => (f x.1, g x.2) :=
  open_embedding_of_embedding_open (hf.1.prod_mk hg.1) (hf.IsOpenMap.Prod hg.IsOpenMap)

theorem embedding_graph {f : α → β} (hf : Continuous f) : Embedding fun x => (x, f x) :=
  embedding_of_embedding_compose (continuous_id.prod_mk hf) continuous_fst embedding_id

end Prod

section Sum

open Sum

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

@[continuity]
theorem continuous_inl : Continuous (@inl α β) :=
  continuous_sup_rng_left continuous_coinduced_rng

@[continuity]
theorem continuous_inr : Continuous (@inr α β) :=
  continuous_sup_rng_right continuous_coinduced_rng

@[continuity]
theorem Continuous.sum_elim {f : α → γ} {g : β → γ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.elim f g) := by
  apply continuous_sup_dom <;> rw [continuous_def] at hf hg⊢ <;> assumption

@[continuity]
theorem Continuous.sum_map {f : α → β} {g : γ → δ} (hf : Continuous f) (hg : Continuous g) : Continuous (Sum.map f g) :=
  (continuous_inl.comp hf).sum_elim (continuous_inr.comp hg)

theorem is_open_sum_iff {s : Set (Sum α β)} : IsOpen s ↔ IsOpen (inl ⁻¹' s) ∧ IsOpen (inr ⁻¹' s) :=
  Iff.rfl

theorem is_open_map_sum {f : Sum α β → γ} (h₁ : IsOpenMap fun a => f (inl a)) (h₂ : IsOpenMap fun b => f (inr b)) :
    IsOpenMap f := by
  intro u hu
  rw [is_open_sum_iff] at hu
  cases' hu with hu₁ hu₂
  have : u = inl '' (inl ⁻¹' u) ∪ inr '' (inr ⁻¹' u) := by
    ext (_ | _) <;> simp
  rw [this, Set.image_union, Set.image_image, Set.image_image]
  exact IsOpen.union (h₁ _ hu₁) (h₂ _ hu₂)

theorem embedding_inl : Embedding (@inl α β) :=
  { induced := by
      unfold Sum.topologicalSpace
      apply le_antisymmₓ
      · rw [← coinduced_le_iff_le_induced]
        exact le_sup_left
        
      · intro u hu
        exists inl '' u
        change (IsOpen (inl ⁻¹' (@inl α β '' u)) ∧ IsOpen (inr ⁻¹' (@inl α β '' u))) ∧ inl ⁻¹' (inl '' u) = u
        rw [preimage_image_eq u Sum.inl_injective, preimage_inr_image_inl]
        exact ⟨⟨hu, is_open_empty⟩, rfl⟩
        ,
    inj := fun _ _ => inl.inj_iff.mp }

theorem embedding_inr : Embedding (@inr α β) :=
  { induced := by
      unfold Sum.topologicalSpace
      apply le_antisymmₓ
      · rw [← coinduced_le_iff_le_induced]
        exact le_sup_right
        
      · intro u hu
        exists inr '' u
        change (IsOpen (inl ⁻¹' (@inr α β '' u)) ∧ IsOpen (inr ⁻¹' (@inr α β '' u))) ∧ inr ⁻¹' (inr '' u) = u
        rw [preimage_inl_image_inr, preimage_image_eq u Sum.inr_injective]
        exact ⟨⟨is_open_empty, hu⟩, rfl⟩
        ,
    inj := fun _ _ => inr.inj_iff.mp }

theorem is_open_range_inl : IsOpen (Range (inl : α → Sum α β)) :=
  is_open_sum_iff.2 <| by
    simp

theorem is_open_range_inr : IsOpen (Range (inr : β → Sum α β)) :=
  is_open_sum_iff.2 <| by
    simp

theorem is_closed_range_inl : IsClosed (Range (inl : α → Sum α β)) := by
  rw [← is_open_compl_iff, compl_range_inl]
  exact is_open_range_inr

theorem is_closed_range_inr : IsClosed (Range (inr : β → Sum α β)) := by
  rw [← is_open_compl_iff, compl_range_inr]
  exact is_open_range_inl

theorem open_embedding_inl : OpenEmbedding (inl : α → Sum α β) :=
  { embedding_inl with open_range := is_open_range_inl }

theorem open_embedding_inr : OpenEmbedding (inr : β → Sum α β) :=
  { embedding_inr with open_range := is_open_range_inr }

theorem closed_embedding_inl : ClosedEmbedding (inl : α → Sum α β) :=
  { embedding_inl with closed_range := is_closed_range_inl }

theorem closed_embedding_inr : ClosedEmbedding (inr : β → Sum α β) :=
  { embedding_inr with closed_range := is_closed_range_inr }

end Sum

section Subtype

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {p : α → Prop}

theorem inducing_coe {b : Set β} : Inducing (coe : b → β) :=
  ⟨rfl⟩

theorem Inducing.of_cod_restrict {f : α → β} {b : Set β} (hb : ∀ a, f a ∈ b) (h : Inducing (b.codRestrict f hb)) :
    Inducing f :=
  inducing_coe.comp h

theorem embedding_subtype_coe : Embedding (coe : Subtype p → α) :=
  ⟨⟨rfl⟩, Subtype.coe_injective⟩

theorem closed_embedding_subtype_coe (h : IsClosed { a | p a }) : ClosedEmbedding (coe : Subtype p → α) :=
  ⟨embedding_subtype_coe, by
    rwa [Subtype.range_coe_subtype]⟩

@[continuity]
theorem continuous_subtype_val : Continuous (@Subtype.val α p) :=
  continuous_induced_dom

theorem continuous_subtype_coe : Continuous (coe : Subtype p → α) :=
  continuous_subtype_val

theorem Continuous.subtype_coe {f : β → Subtype p} (hf : Continuous f) : Continuous fun x => (f x : α) :=
  continuous_subtype_coe.comp hf

theorem IsOpen.open_embedding_subtype_coe {s : Set α} (hs : IsOpen s) : OpenEmbedding (coe : s → α) :=
  { induced := rfl, inj := Subtype.coe_injective, open_range := (Subtype.range_coe : Range coe = s).symm ▸ hs }

theorem IsOpen.is_open_map_subtype_coe {s : Set α} (hs : IsOpen s) : IsOpenMap (coe : s → α) :=
  hs.open_embedding_subtype_coe.IsOpenMap

theorem IsOpenMap.restrict {f : α → β} (hf : IsOpenMap f) {s : Set α} (hs : IsOpen s) : IsOpenMap (s.restrict f) :=
  hf.comp hs.is_open_map_subtype_coe

theorem IsClosed.closed_embedding_subtype_coe {s : Set α} (hs : IsClosed s) :
    ClosedEmbedding (coe : { x // x ∈ s } → α) :=
  { induced := rfl, inj := Subtype.coe_injective, closed_range := (Subtype.range_coe : Range coe = s).symm ▸ hs }

@[continuity]
theorem continuous_subtype_mk {f : β → α} (hp : ∀ x, p (f x)) (h : Continuous f) :
    Continuous fun x => (⟨f x, hp x⟩ : Subtype p) :=
  continuous_induced_rng h

theorem continuous_inclusion {s t : Set α} (h : s ⊆ t) : Continuous (inclusion h) :=
  continuous_subtype_mk _ continuous_subtype_coe

theorem continuous_at_subtype_coe {p : α → Prop} {a : Subtype p} : ContinuousAt (coe : Subtype p → α) a :=
  continuous_iff_continuous_at.mp continuous_subtype_coe _

theorem Subtype.dense_iff {s : Set α} {t : Set s} : Dense t ↔ s ⊆ Closure (coe '' t) := by
  rw [inducing_coe.dense_iff, SetCoe.forall]
  rfl

theorem map_nhds_subtype_coe_eq {a : α} (ha : p a) (h : { a | p a } ∈ 𝓝 a) :
    map (coe : Subtype p → α) (𝓝 ⟨a, ha⟩) = 𝓝 a :=
  map_nhds_induced_of_mem <| by
    simpa only [← Subtype.coe_mk, ← Subtype.range_coe] using h

theorem nhds_subtype_eq_comap {a : α} {h : p a} : 𝓝 (⟨a, h⟩ : Subtype p) = comap coe (𝓝 a) :=
  nhds_induced _ _

theorem tendsto_subtype_rng {β : Type _} {p : α → Prop} {b : Filter β} {f : β → Subtype p} :
    ∀ {a : Subtype p}, Tendsto f b (𝓝 a) ↔ Tendsto (fun x => (f x : α)) b (𝓝 (a : α))
  | ⟨a, ha⟩ => by
    rw [nhds_subtype_eq_comap, tendsto_comap_iff, Subtype.coe_mk]

theorem continuous_subtype_nhds_cover {ι : Sort _} {f : α → β} {c : ι → α → Prop}
    (c_cover : ∀ x : α, ∃ i, { x | c i x } ∈ 𝓝 x) (f_cont : ∀ i, Continuous fun x : Subtype (c i) => f x) :
    Continuous f :=
  continuous_iff_continuous_at.mpr fun x =>
    let ⟨i, (c_sets : { x | c i x } ∈ 𝓝 x)⟩ := c_cover x
    let x' : Subtype (c i) := ⟨x, mem_of_mem_nhds c_sets⟩
    calc
      map f (𝓝 x) = map f (map coe (𝓝 x')) := congr_arg (map f) (map_nhds_subtype_coe_eq _ <| c_sets).symm
      _ = map (fun x : Subtype (c i) => f x) (𝓝 x') := rfl
      _ ≤ 𝓝 (f x) := continuous_iff_continuous_at.mp (f_cont i) x'
      

theorem continuous_subtype_is_closed_cover {ι : Sort _} {f : α → β} (c : ι → α → Prop)
    (h_lf : LocallyFinite fun i => { x | c i x }) (h_is_closed : ∀ i, IsClosed { x | c i x })
    (h_cover : ∀ x, ∃ i, c i x) (f_cont : ∀ i, Continuous fun x : Subtype (c i) => f x) : Continuous f :=
  continuous_iff_is_closed.mpr fun s hs => by
    have : ∀ i, IsClosed ((coe : { x | c i x } → α) '' (f ∘ coe ⁻¹' s)) := fun i =>
      (closed_embedding_subtype_coe (h_is_closed _)).IsClosedMap _ (hs.Preimage (f_cont i))
    have : IsClosed (⋃ i, (coe : { x | c i x } → α) '' (f ∘ coe ⁻¹' s)) :=
      LocallyFinite.is_closed_Union (h_lf.Subset fun i x ⟨⟨x', hx'⟩, _, HEq⟩ => HEq ▸ hx') this
    have : f ⁻¹' s = ⋃ i, (coe : { x | c i x } → α) '' (f ∘ coe ⁻¹' s) := by
      apply Set.ext
      have : ∀ x : α, f x ∈ s ↔ ∃ i : ι, c i x ∧ f x ∈ s := fun x =>
        ⟨fun hx =>
          let ⟨i, hi⟩ := h_cover x
          ⟨i, hi, hx⟩,
          fun ⟨i, hi, hx⟩ => hx⟩
      simpa [← And.comm, ← @And.left_comm (c _ _), exists_and_distrib_right]
    rwa [this]

theorem closure_subtype {x : { a // p a }} {s : Set { a // p a }} :
    x ∈ Closure s ↔ (x : α) ∈ Closure ((coe : _ → α) '' s) :=
  closure_induced

@[continuity]
theorem Continuous.cod_restrict {f : α → β} {s : Set β} (hf : Continuous f) (hs : ∀ a, f a ∈ s) :
    Continuous (s.codRestrict f hs) :=
  continuous_subtype_mk hs hf

theorem Inducing.cod_restrict {e : α → β} (he : Inducing e) {s : Set β} (hs : ∀ x, e x ∈ s) :
    Inducing (codRestrict e s hs) :=
  inducing_of_inducing_compose (he.Continuous.codRestrict hs) continuous_subtype_coe he

theorem Embedding.cod_restrict {e : α → β} (he : Embedding e) (s : Set β) (hs : ∀ x, e x ∈ s) :
    Embedding (codRestrict e s hs) :=
  embedding_of_embedding_compose (he.Continuous.codRestrict hs) continuous_subtype_coe he

end Subtype

section Quotientₓ

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

variable {r : α → α → Prop} {s : Setoidₓ α}

theorem quotient_map_quot_mk : QuotientMap (@Quot.mk α r) :=
  ⟨Quot.exists_rep, rfl⟩

@[continuity]
theorem continuous_quot_mk : Continuous (@Quot.mk α r) :=
  continuous_coinduced_rng

@[continuity]
theorem continuous_quot_lift {f : α → β} (hr : ∀ a b, r a b → f a = f b) (h : Continuous f) :
    Continuous (Quot.lift f hr : Quot r → β) :=
  continuous_coinduced_dom h

theorem quotient_map_quotient_mk : QuotientMap (@Quotientₓ.mk α s) :=
  quotient_map_quot_mk

theorem continuous_quotient_mk : Continuous (@Quotientₓ.mk α s) :=
  continuous_coinduced_rng

theorem continuous_quotient_lift {f : α → β} (hs : ∀ a b, a ≈ b → f a = f b) (h : Continuous f) :
    Continuous (Quotientₓ.lift f hs : Quotientₓ s → β) :=
  continuous_coinduced_dom h

theorem continuous_quotient_lift_on' {f : α → β} (hs : ∀ a b, a ≈ b → f a = f b) (h : Continuous f) :
    Continuous (fun x => Quotientₓ.liftOn' x f hs : Quotientₓ s → β) :=
  continuous_coinduced_dom h

end Quotientₓ

section Pi

variable {ι : Type _} {π : ι → Type _}

@[continuity]
theorem continuous_pi [TopologicalSpace α] [∀ i, TopologicalSpace (π i)] {f : α → ∀ i : ι, π i}
    (h : ∀ i, Continuous fun a => f a i) : Continuous f :=
  continuous_infi_rng fun i => continuous_induced_rng <| h i

@[continuity]
theorem continuous_apply [∀ i, TopologicalSpace (π i)] (i : ι) : Continuous fun p : ∀ i, π i => p i :=
  continuous_infi_dom continuous_induced_dom

@[continuity]
theorem continuous_apply_apply {κ : Type _} {ρ : κ → ι → Type _} [∀ j i, TopologicalSpace (ρ j i)] (j : κ) (i : ι) :
    Continuous fun p : ∀ j, ∀ i, ρ j i => p j i :=
  (continuous_apply i).comp (continuous_apply j)

theorem continuous_at_apply [∀ i, TopologicalSpace (π i)] (i : ι) (x : ∀ i, π i) :
    ContinuousAt (fun p : ∀ i, π i => p i) x :=
  (continuous_apply i).ContinuousAt

theorem Filter.Tendsto.apply [∀ i, TopologicalSpace (π i)] {l : Filter α} {f : α → ∀ i, π i} {x : ∀ i, π i}
    (h : Tendsto f l (𝓝 x)) (i : ι) : Tendsto (fun a => f a i) l (𝓝 <| x i) :=
  (continuous_at_apply i _).Tendsto.comp h

theorem continuous_pi_iff [TopologicalSpace α] [∀ i, TopologicalSpace (π i)] {f : α → ∀ i, π i} :
    Continuous f ↔ ∀ i, Continuous fun y => f y i :=
  Iff.intro (fun h i => (continuous_apply i).comp h) continuous_pi

theorem nhds_pi [t : ∀ i, TopologicalSpace (π i)] {a : ∀ i, π i} : 𝓝 a = pi fun i => 𝓝 (a i) :=
  calc
    𝓝 a = ⨅ i, @nhds _ (@TopologicalSpace.induced _ _ (fun x : ∀ i, π i => x i) (t i)) a := nhds_infi
    _ = ⨅ i, comap (fun x => x i) (𝓝 (a i)) := by
      simp [← nhds_induced]
    

theorem tendsto_pi_nhds [t : ∀ i, TopologicalSpace (π i)] {f : α → ∀ i, π i} {g : ∀ i, π i} {u : Filter α} :
    Tendsto f u (𝓝 g) ↔ ∀ x, Tendsto (fun i => f i x) u (𝓝 (g x)) := by
  rw [nhds_pi, Filter.tendsto_pi]

theorem continuous_at_pi [∀ i, TopologicalSpace (π i)] [TopologicalSpace α] {f : α → ∀ i, π i} {x : α} :
    ContinuousAt f x ↔ ∀ i, ContinuousAt (fun y => f y i) x :=
  tendsto_pi_nhds

theorem Filter.Tendsto.update [∀ i, TopologicalSpace (π i)] [DecidableEq ι] {l : Filter α} {f : α → ∀ i, π i}
    {x : ∀ i, π i} (hf : Tendsto f l (𝓝 x)) (i : ι) {g : α → π i} {xi : π i} (hg : Tendsto g l (𝓝 xi)) :
    Tendsto (fun a => Function.update (f a) i (g a)) l (𝓝 <| Function.update x i xi) :=
  tendsto_pi_nhds.2 fun j => by
    rcases em (j = i) with (rfl | hj) <;> simp [*, ← hf.apply]

theorem ContinuousAt.update [∀ i, TopologicalSpace (π i)] [TopologicalSpace α] [DecidableEq ι] {f : α → ∀ i, π i}
    {a : α} (hf : ContinuousAt f a) (i : ι) {g : α → π i} (hg : ContinuousAt g a) :
    ContinuousAt (fun a => Function.update (f a) i (g a)) a :=
  hf.update i hg

theorem Continuous.update [∀ i, TopologicalSpace (π i)] [TopologicalSpace α] [DecidableEq ι] {f : α → ∀ i, π i}
    (hf : Continuous f) (i : ι) {g : α → π i} (hg : Continuous g) : Continuous fun a => Function.update (f a) i (g a) :=
  continuous_iff_continuous_at.2 fun x => hf.ContinuousAt.update i hg.ContinuousAt

/-- `function.update f i x` is continuous in `(f, x)`. -/
@[continuity]
theorem continuous_update [∀ i, TopologicalSpace (π i)] [DecidableEq ι] (i : ι) :
    Continuous fun f : (∀ j, π j) × π i => Function.update f.1 i f.2 :=
  continuous_fst.update i continuous_snd

theorem Filter.Tendsto.fin_insert_nth {n} {π : Finₓ (n + 1) → Type _} [∀ i, TopologicalSpace (π i)] (i : Finₓ (n + 1))
    {f : α → π i} {l : Filter α} {x : π i} (hf : Tendsto f l (𝓝 x)) {g : α → ∀ j : Finₓ n, π (i.succAbove j)}
    {y : ∀ j, π (i.succAbove j)} (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => i.insertNth (f a) (g a)) l (𝓝 <| i.insertNth x y) :=
  tendsto_pi_nhds.2 fun j =>
    Finₓ.succAboveCases i
      (by
        simpa)
      (by
        simpa using tendsto_pi_nhds.1 hg)
      j

theorem ContinuousAt.fin_insert_nth {n} {π : Finₓ (n + 1) → Type _} [∀ i, TopologicalSpace (π i)] [TopologicalSpace α]
    (i : Finₓ (n + 1)) {f : α → π i} {a : α} (hf : ContinuousAt f a) {g : α → ∀ j : Finₓ n, π (i.succAbove j)}
    (hg : ContinuousAt g a) : ContinuousAt (fun a => i.insertNth (f a) (g a)) a :=
  hf.fin_insert_nth i hg

theorem Continuous.fin_insert_nth {n} {π : Finₓ (n + 1) → Type _} [∀ i, TopologicalSpace (π i)] [TopologicalSpace α]
    (i : Finₓ (n + 1)) {f : α → π i} (hf : Continuous f) {g : α → ∀ j : Finₓ n, π (i.succAbove j)} (hg : Continuous g) :
    Continuous fun a => i.insertNth (f a) (g a) :=
  continuous_iff_continuous_at.2 fun a => hf.ContinuousAt.fin_insert_nth i hg.ContinuousAt

theorem is_open_set_pi [∀ a, TopologicalSpace (π a)] {i : Set ι} {s : ∀ a, Set (π a)} (hi : i.Finite)
    (hs : ∀, ∀ a ∈ i, ∀, IsOpen (s a)) : IsOpen (pi i s) := by
  rw [pi_def] <;> exact (is_open_bInter hi) fun a ha => (hs _ ha).Preimage (continuous_apply _)

theorem is_closed_set_pi [∀ a, TopologicalSpace (π a)] {i : Set ι} {s : ∀ a, Set (π a)}
    (hs : ∀, ∀ a ∈ i, ∀, IsClosed (s a)) : IsClosed (pi i s) := by
  rw [pi_def] <;> exact is_closed_Inter fun a => is_closed_Inter fun ha => (hs _ ha).Preimage (continuous_apply _)

theorem mem_nhds_of_pi_mem_nhds {ι : Type _} {α : ι → Type _} [∀ i : ι, TopologicalSpace (α i)] {I : Set ι}
    {s : ∀ i, Set (α i)} (a : ∀ i, α i) (hs : I.pi s ∈ 𝓝 a) {i : ι} (hi : i ∈ I) : s i ∈ 𝓝 (a i) := by
  rw [nhds_pi] at hs
  exact mem_of_pi_mem_pi hs hi

theorem set_pi_mem_nhds [∀ a, TopologicalSpace (π a)] {i : Set ι} {s : ∀ a, Set (π a)} {x : ∀ a, π a} (hi : i.Finite)
    (hs : ∀, ∀ a ∈ i, ∀, s a ∈ 𝓝 (x a)) : pi i s ∈ 𝓝 x := by
  rw [pi_def, bInter_mem hi]
  exact fun a ha => (continuous_apply a).ContinuousAt (hs a ha)

theorem set_pi_mem_nhds_iff {α : ι → Type _} [∀ i : ι, TopologicalSpace (α i)] {I : Set ι} (hI : I.Finite)
    {s : ∀ i, Set (α i)} (a : ∀ i, α i) : I.pi s ∈ 𝓝 a ↔ ∀ i : ι, i ∈ I → s i ∈ 𝓝 (a i) := by
  rw [nhds_pi, pi_mem_pi_iff hI]
  infer_instance

theorem interior_pi_set {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {I : Set ι} (hI : I.Finite)
    {s : ∀ i, Set (α i)} : Interior (pi I s) = I.pi fun i => Interior (s i) := by
  ext a
  simp only [← Set.mem_pi, ← mem_interior_iff_mem_nhds, ← set_pi_mem_nhds_iff hI]

theorem exists_finset_piecewise_mem_of_mem_nhds [DecidableEq ι] [∀ i, TopologicalSpace (π i)] {s : Set (∀ a, π a)}
    {x : ∀ a, π a} (hs : s ∈ 𝓝 x) (y : ∀ a, π a) : ∃ I : Finset ι, I.piecewise x y ∈ s := by
  simp only [← nhds_pi, ← Filter.mem_pi'] at hs
  rcases hs with ⟨I, t, htx, hts⟩
  refine' ⟨I, hts fun i hi => _⟩
  simpa [← Finset.mem_coe.1 hi] using mem_of_mem_nhds (htx i)

theorem pi_eq_generate_from [∀ a, TopologicalSpace (π a)] :
    Pi.topologicalSpace =
      generateFrom { g | ∃ (s : ∀ a, Set (π a))(i : Finset ι), (∀, ∀ a ∈ i, ∀, IsOpen (s a)) ∧ g = pi (↑i) s } :=
  le_antisymmₓ (le_generate_from fun g ⟨s, i, hi, Eq⟩ => Eq.symm ▸ is_open_set_pi (Finset.finite_to_set _) hi)
    (le_infi fun a s ⟨t, ht, s_eq⟩ =>
      GenerateOpen.basic _ <|
        ⟨Function.update (fun a => Univ) a t, {a}, by
          simpa using ht,
          s_eq ▸ by
            ext f <;> simp [← Set.Pi]⟩)

theorem pi_generate_from_eq {g : ∀ a, Set (Set (π a))} :
    (@Pi.topologicalSpace ι π fun a => generateFrom (g a)) =
      generateFrom { t | ∃ (s : ∀ a, Set (π a))(i : Finset ι), (∀, ∀ a ∈ i, ∀, s a ∈ g a) ∧ t = pi (↑i) s } :=
  by
  let G := { t | ∃ (s : ∀ a, Set (π a))(i : Finset ι), (∀, ∀ a ∈ i, ∀, s a ∈ g a) ∧ t = pi (↑i) s }
  rw [pi_eq_generate_from]
  refine' le_antisymmₓ (generate_from_mono _) (le_generate_from _)
  exact fun s ⟨t, i, ht, Eq⟩ => ⟨t, i, fun a ha => generate_open.basic _ (ht a ha), Eq⟩
  · rintro s ⟨t, i, hi, rfl⟩
    rw [pi_def]
    apply is_open_bInter (Finset.finite_to_set _)
    intro a ha
    show ((generate_from G).coinduced fun f : ∀ a, π a => f a).IsOpen (t a)
    refine' le_generate_from _ _ (hi a ha)
    exact fun s hs =>
      generate_open.basic _
        ⟨Function.update (fun a => univ) a s, {a}, by
          simp [← hs]⟩
    

theorem pi_generate_from_eq_fintype {g : ∀ a, Set (Set (π a))} [Fintype ι] (hg : ∀ a, ⋃₀g a = univ) :
    (@Pi.topologicalSpace ι π fun a => generateFrom (g a)) =
      generateFrom { t | ∃ s : ∀ a, Set (π a), (∀ a, s a ∈ g a) ∧ t = pi Univ s } :=
  by
  rw [pi_generate_from_eq]
  refine' le_antisymmₓ (generate_from_mono _) (le_generate_from _)
  exact fun s ⟨t, ht, Eq⟩ =>
    ⟨t, Finset.univ, by
      simp [← ht, ← Eq]⟩
  · rintro s ⟨t, i, ht, rfl⟩
    apply is_open_iff_forall_mem_open.2 _
    intro f hf
    choose c hc using
      show ∀ a, ∃ s, s ∈ g a ∧ f a ∈ s by
        intro a
        have : f a ∈ ⋃₀g a := by
          rw [hg]
          apply mem_univ
        simpa
    refine' ⟨pi univ fun a => if a ∈ i then t a else (c : ∀ a, Set (π a)) a, _, _, _⟩
    · simp [← pi_if]
      
    · refine' generate_open.basic _ ⟨_, fun a => _, rfl⟩
      by_cases' a ∈ i <;> simp_all [← Set.Pi]
      
    · have : f ∈ pi { a | a ∉ i } c := by
        simp_all [← Set.Pi]
      simpa [← pi_if, ← hf]
      
    

/-- Suppose `π i` is a family of topological spaces indexed by `i : ι`, and `X` is a type
endowed with a family of maps `f i : X → π i` for every `i : ι`, hence inducing a
map `g : X → Π i, π i`. This lemma shows that infimum of the topologies on `X` induced by
the `f i` as `i : ι` varies is simply the topology on `X` induced by `g : X → Π i, π i`
where `Π i, π i` is endowed with the usual product topology. -/
theorem inducing_infi_to_pi {X : Type _} [∀ i, TopologicalSpace (π i)] (f : ∀ i, X → π i) :
    @Inducing X (∀ i, π i) (⨅ i, induced (f i) inferInstance) _ fun x i => f i x := by
  constructor
  erw [induced_infi]
  congr 1
  funext
  erw [induced_compose]

variable [Fintype ι] [∀ i, TopologicalSpace (π i)] [∀ i, DiscreteTopology (π i)]

/-- A finite product of discrete spaces is discrete. -/
instance Pi.discrete_topology : DiscreteTopology (∀ i, π i) :=
  singletons_open_iff_discrete.mp fun x => by
    rw
      [show {x} = ⋂ i, { y : ∀ i, π i | y i = x i } by
        ext
        simp only [← Function.funext_iffₓ, ← Set.mem_singleton_iff, ← Set.mem_Inter, ← Set.mem_set_of_eq]]
    exact is_open_Inter fun i => (continuous_apply i).is_open_preimage {x i} (is_open_discrete {x i})

end Pi

section Sigma

variable {ι : Type _} {σ : ι → Type _} [∀ i, TopologicalSpace (σ i)]

@[continuity]
theorem continuous_sigma_mk {i : ι} : Continuous (@Sigma.mk ι σ i) :=
  continuous_supr_rng continuous_coinduced_rng

theorem is_open_sigma_iff {s : Set (Sigma σ)} : IsOpen s ↔ ∀ i, IsOpen (Sigma.mk i ⁻¹' s) := by
  simp only [← is_open_supr_iff, ← is_open_coinduced]

theorem is_closed_sigma_iff {s : Set (Sigma σ)} : IsClosed s ↔ ∀ i, IsClosed (Sigma.mk i ⁻¹' s) := by
  simp only [is_open_compl_iff, ← is_open_sigma_iff, ← preimage_compl]

theorem is_open_map_sigma_mk {i : ι} : IsOpenMap (@Sigma.mk ι σ i) := by
  intro s hs
  rw [is_open_sigma_iff]
  intro j
  rcases eq_or_ne i j with (rfl | hne)
  · rwa [Set.preimage_image_eq _ sigma_mk_injective]
    
  · convert is_open_empty
    apply Set.eq_empty_of_subset_empty
    rintro x ⟨y, _, hy⟩
    have : i = j := by
      cc
    contradiction
    

theorem is_open_range_sigma_mk {i : ι} : IsOpen (Set.Range (@Sigma.mk ι σ i)) :=
  is_open_map_sigma_mk.is_open_range

theorem is_closed_map_sigma_mk {i : ι} : IsClosedMap (@Sigma.mk ι σ i) := by
  intro s hs
  rw [is_closed_sigma_iff]
  intro j
  rcases eq_or_ne i j with (rfl | hne)
  · rwa [Set.preimage_image_eq _ sigma_mk_injective]
    
  · convert is_closed_empty
    apply Set.eq_empty_of_subset_empty
    rintro x ⟨y, _, hy⟩
    have : i = j := by
      cc
    contradiction
    

theorem is_closed_sigma_mk {i : ι} : IsClosed (Set.Range (@Sigma.mk ι σ i)) := by
  rw [← Set.image_univ]
  exact is_closed_map_sigma_mk _ is_closed_univ

theorem open_embedding_sigma_mk {i : ι} : OpenEmbedding (@Sigma.mk ι σ i) :=
  open_embedding_of_continuous_injective_open continuous_sigma_mk sigma_mk_injective is_open_map_sigma_mk

theorem closed_embedding_sigma_mk {i : ι} : ClosedEmbedding (@Sigma.mk ι σ i) :=
  closed_embedding_of_continuous_injective_closed continuous_sigma_mk sigma_mk_injective is_closed_map_sigma_mk

theorem embedding_sigma_mk {i : ι} : Embedding (@Sigma.mk ι σ i) :=
  closed_embedding_sigma_mk.1

theorem is_open_sigma_fst_preimage (s : Set ι) : IsOpen (Sigma.fst ⁻¹' s : Set (Σa, σ a)) := by
  rw [← bUnion_of_singleton s, preimage_Union₂]
  simp only [range_sigma_mk]
  exact is_open_bUnion fun _ _ => is_open_range_sigma_mk

/-- A map out of a sum type is continuous if its restriction to each summand is. -/
@[continuity]
theorem continuous_sigma [TopologicalSpace β] {f : Sigma σ → β} (h : ∀ i, Continuous fun a => f ⟨i, a⟩) :
    Continuous f :=
  continuous_supr_dom fun i => continuous_coinduced_dom (h i)

@[continuity]
theorem continuous_sigma_map {κ : Type _} {τ : κ → Type _} [∀ k, TopologicalSpace (τ k)] {f₁ : ι → κ}
    {f₂ : ∀ i, σ i → τ (f₁ i)} (hf : ∀ i, Continuous (f₂ i)) : Continuous (Sigma.map f₁ f₂) :=
  continuous_sigma fun i => show Continuous fun a => Sigma.mk (f₁ i) (f₂ i a) from continuous_sigma_mk.comp (hf i)

theorem is_open_map_sigma [TopologicalSpace β] {f : Sigma σ → β} (h : ∀ i, IsOpenMap fun a => f ⟨i, a⟩) : IsOpenMap f :=
  by
  intro s hs
  rw [is_open_sigma_iff] at hs
  rw [← Union_image_preimage_sigma_mk_eq_self s, image_Union]
  apply is_open_Union
  intro i
  rw [image_image]
  exact h i _ (hs i)

/-- The sum of embeddings is an embedding. -/
theorem embedding_sigma_map {τ : ι → Type _} [∀ i, TopologicalSpace (τ i)] {f : ∀ i, σ i → τ i}
    (hf : ∀ i, Embedding (f i)) : Embedding (Sigma.map id f) := by
  refine' ⟨⟨_⟩, function.injective_id.sigma_map fun i => (hf i).inj⟩
  refine' le_antisymmₓ (continuous_iff_le_induced.mp (continuous_sigma_map fun i => (hf i).Continuous)) _
  intro s hs
  replace hs := is_open_sigma_iff.mp hs
  have : ∀ i, ∃ t, IsOpen t ∧ f i ⁻¹' t = Sigma.mk i ⁻¹' s := by
    intro i
    apply is_open_induced_iff.mp
    convert hs i
    exact (hf i).induced.symm
  choose t ht using this
  apply is_open_induced_iff.mpr
  refine' ⟨⋃ i, Sigma.mk i '' t i, is_open_Union fun i => is_open_map_sigma_mk _ (ht i).1, _⟩
  ext ⟨i, x⟩
  change (Sigma.mk i (f i x) ∈ ⋃ i : ι, Sigma.mk i '' t i) ↔ x ∈ Sigma.mk i ⁻¹' s
  rw [← (ht i).2, mem_Union]
  constructor
  · rintro ⟨j, hj⟩
    rw [mem_image] at hj
    rcases hj with ⟨y, hy₁, hy₂⟩
    rcases sigma.mk.inj_iff.mp hy₂ with ⟨rfl, hy⟩
    replace hy := eq_of_heq hy
    subst y
    exact hy₁
    
  · intro hx
    use i
    rw [mem_image]
    exact ⟨f i x, hx, rfl⟩
    

end Sigma

section ULift

@[continuity]
theorem continuous_ulift_down [TopologicalSpace α] : Continuous (ULift.down : ULift.{v, u} α → α) :=
  continuous_induced_dom

@[continuity]
theorem continuous_ulift_up [TopologicalSpace α] : Continuous (ULift.up : α → ULift.{v, u} α) :=
  continuous_induced_rng continuous_id

end ULift

theorem mem_closure_of_continuous [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {a : α} {s : Set α} {t : Set β}
    (hf : Continuous f) (ha : a ∈ Closure s) (h : MapsTo f s (Closure t)) : f a ∈ Closure t :=
  calc
    f a ∈ f '' Closure s := mem_image_of_mem _ ha
    _ ⊆ Closure (f '' s) := image_closure_subset_closure_image hf
    _ ⊆ Closure t := closure_minimal h.image_subset is_closed_closure
    

theorem mem_closure_of_continuous2 [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {f : α → β → γ}
    {a : α} {b : β} {s : Set α} {t : Set β} {u : Set γ} (hf : Continuous fun p : α × β => f p.1 p.2)
    (ha : a ∈ Closure s) (hb : b ∈ Closure t) (h : ∀, ∀ a ∈ s, ∀, ∀, ∀ b ∈ t, ∀, f a b ∈ Closure u) :
    f a b ∈ Closure u :=
  have : (a, b) ∈ Closure (s ×ˢ t) := by
    simp [← closure_prod_eq, ← ha, ← hb]
  show f (a, b).1 (a, b).2 ∈ Closure u from
    (@mem_closure_of_continuous (α × β) _ _ _ (fun p : α × β => f p.1 p.2) (a, b) _ u hf this) fun ⟨p₁, p₂⟩ ⟨h₁, h₂⟩ =>
      h p₁ h₁ p₂ h₂


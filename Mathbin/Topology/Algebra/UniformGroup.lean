/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathbin.Topology.UniformSpace.UniformConvergence
import Mathbin.Topology.UniformSpace.UniformEmbedding
import Mathbin.Topology.UniformSpace.CompleteSeparated
import Mathbin.Topology.Algebra.Group
import Mathbin.Tactic.Abel

/-!
# Uniform structure on topological groups

This file defines uniform groups and its additive counterpart. These typeclasses should be
preferred over using `[topological_space α] [topological_group α]` since every topological
group naturally induces a uniform structure.

## Main declarations
* `uniform_group` and `uniform_add_group`: Multiplicative and additive uniform groups, that
  i.e., groups with uniformly continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`.

## Main results

* `topological_add_group.to_uniform_space` and `topological_add_group_is_uniform` can be used to
  construct a canonical uniformity for a topological add group.

* extension of ℤ-bilinear maps to complete groups (useful for ring completions)
-/


noncomputable section

open Classical uniformity TopologicalSpace Filter Pointwise

section UniformGroup

open Filter Set

variable {α : Type _} {β : Type _}

/-- A uniform group is a group in which multiplication and inversion are uniformly continuous. -/
class UniformGroup (α : Type _) [UniformSpace α] [Groupₓ α] : Prop where
  uniform_continuous_div : UniformContinuous fun p : α × α => p.1 / p.2

/-- A uniform additive group is an additive group in which addition
  and negation are uniformly continuous.-/
class UniformAddGroup (α : Type _) [UniformSpace α] [AddGroupₓ α] : Prop where
  uniform_continuous_sub : UniformContinuous fun p : α × α => p.1 - p.2

attribute [to_additive] UniformGroup

@[to_additive]
theorem UniformGroup.mk' {α} [UniformSpace α] [Groupₓ α] (h₁ : UniformContinuous fun p : α × α => p.1 * p.2)
    (h₂ : UniformContinuous fun p : α => p⁻¹) : UniformGroup α :=
  ⟨by
    simpa only [← div_eq_mul_inv] using h₁.comp (uniform_continuous_fst.prod_mk (h₂.comp uniform_continuous_snd))⟩

variable [UniformSpace α] [Groupₓ α] [UniformGroup α]

@[to_additive]
theorem uniform_continuous_div : UniformContinuous fun p : α × α => p.1 / p.2 :=
  UniformGroup.uniform_continuous_div

@[to_additive]
theorem UniformContinuous.div [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x / g x :=
  uniform_continuous_div.comp (hf.prod_mk hg)

@[to_additive]
theorem UniformContinuous.inv [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    UniformContinuous fun x => (f x)⁻¹ := by
  have : UniformContinuous fun x => 1 / f x := uniform_continuous_const.div hf
  simp_all

@[to_additive]
theorem uniform_continuous_inv : UniformContinuous fun x : α => x⁻¹ :=
  uniform_continuous_id.inv

@[to_additive]
theorem UniformContinuous.mul [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x * g x := by
  have : UniformContinuous fun x => f x / (g x)⁻¹ := hf.div hg.inv
  simp_all

@[to_additive]
theorem uniform_continuous_mul : UniformContinuous fun p : α × α => p.1 * p.2 :=
  uniform_continuous_fst.mul uniform_continuous_snd

@[to_additive UniformContinuous.const_nsmul]
theorem UniformContinuous.pow_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    ∀ n : ℕ, UniformContinuous fun x => f x ^ n
  | 0 => by
    simp_rw [pow_zeroₓ]
    exact uniform_continuous_const
  | n + 1 => by
    simp_rw [pow_succₓ]
    exact hf.mul (UniformContinuous.pow_const n)

@[to_additive uniform_continuous_const_nsmul]
theorem uniform_continuous_pow_const (n : ℕ) : UniformContinuous fun x : α => x ^ n :=
  uniform_continuous_id.pow_const n

@[to_additive UniformContinuous.const_zsmul]
theorem UniformContinuous.zpow_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    ∀ n : ℤ, UniformContinuous fun x => f x ^ n
  | (n : ℕ) => by
    simp_rw [zpow_coe_nat]
    exact hf.pow_const _
  | -[1+ n] => by
    simp_rw [zpow_neg_succ_of_nat]
    exact (hf.pow_const _).inv

@[to_additive uniform_continuous_const_zsmul]
theorem uniform_continuous_zpow_const (n : ℤ) : UniformContinuous fun x : α => x ^ n :=
  uniform_continuous_id.zpow_const n

@[to_additive]
instance (priority := 10) UniformGroup.to_topological_group : TopologicalGroup α where
  continuous_mul := uniform_continuous_mul.Continuous
  continuous_inv := uniform_continuous_inv.Continuous

@[to_additive]
instance [UniformSpace β] [Groupₓ β] [UniformGroup β] : UniformGroup (α × β) :=
  ⟨((uniform_continuous_fst.comp uniform_continuous_fst).div
          (uniform_continuous_fst.comp uniform_continuous_snd)).prod_mk
      ((uniform_continuous_snd.comp uniform_continuous_fst).div (uniform_continuous_snd.comp uniform_continuous_snd))⟩

@[to_additive]
theorem uniformity_translate_mul (a : α) : ((𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a)) = 𝓤 α :=
  le_antisymmₓ (uniform_continuous_id.mul uniform_continuous_const)
    (calc
      𝓤 α = ((𝓤 α).map fun x : α × α => (x.1 * a⁻¹, x.2 * a⁻¹)).map fun x : α × α => (x.1 * a, x.2 * a) := by
        simp [← Filter.map_map, ← (· ∘ ·)] <;> exact filter.map_id.symm
      _ ≤ (𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a) :=
        Filter.map_mono (uniform_continuous_id.mul uniform_continuous_const)
      )

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:92:4: warning: unsupported: rw with cfg: { occs := occurrences.pos «expr[ ,]»([1]) }
@[to_additive]
theorem uniform_embedding_translate_mul (a : α) : UniformEmbedding fun x : α => x * a :=
  { comap_uniformity := by
      rw [← uniformity_translate_mul a, comap_map]
      rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
      simp (config := { contextual := true })[← Prod.eq_iff_fst_eq_snd_eq],
    inj := mul_left_injective a }

namespace MulOpposite

@[to_additive]
instance : UniformGroup αᵐᵒᵖ :=
  ⟨uniform_continuous_op.comp
      ((uniform_continuous_unop.comp uniform_continuous_snd).inv.mul <|
        uniform_continuous_unop.comp uniform_continuous_fst)⟩

end MulOpposite

namespace Subgroup

@[to_additive]
instance (S : Subgroup α) : UniformGroup S :=
  ⟨uniform_continuous_comap'
      (uniform_continuous_div.comp <| uniform_continuous_subtype_val.prod_map uniform_continuous_subtype_val)⟩

end Subgroup

section LatticeOps

variable [Groupₓ β]

@[to_additive]
theorem uniform_group_Inf {us : Set (UniformSpace β)} (h : ∀, ∀ u ∈ us, ∀, @UniformGroup β u _) :
    @UniformGroup β (inf us) _ :=
  { uniform_continuous_div :=
      uniform_continuous_Inf_rng fun u hu =>
        uniform_continuous_Inf_dom₂ hu hu (@UniformGroup.uniform_continuous_div β u _ (h u hu)) }

@[to_additive]
theorem uniform_group_infi {ι : Sort _} {us' : ι → UniformSpace β} (h' : ∀ i, @UniformGroup β (us' i) _) :
    @UniformGroup β (⨅ i, us' i) _ := by
  rw [← Inf_range]
  exact uniform_group_Inf (set.forall_range_iff.mpr h')

@[to_additive]
theorem uniform_group_inf {u₁ u₂ : UniformSpace β} (h₁ : @UniformGroup β u₁ _) (h₂ : @UniformGroup β u₂ _) :
    @UniformGroup β (u₁⊓u₂) _ := by
  rw [inf_eq_infi]
  refine' uniform_group_infi fun b => _
  cases b <;> assumption

@[to_additive]
theorem uniform_group_comap {γ : Type _} [Groupₓ γ] {u : UniformSpace γ} [UniformGroup γ] {F : Type _}
    [MonoidHomClass F β γ] (f : F) : @UniformGroup β (u.comap f) _ :=
  { uniform_continuous_div := by
      let this : UniformSpace β := u.comap f
      refine' uniform_continuous_comap' _
      simp_rw [Function.comp, map_div]
      change UniformContinuous ((fun p : γ × γ => p.1 / p.2) ∘ Prod.map f f)
      exact uniform_continuous_div.comp (uniform_continuous_comap.prod_map uniform_continuous_comap) }

end LatticeOps

section

variable (α)

@[to_additive]
theorem uniformity_eq_comap_nhds_one : 𝓤 α = comap (fun x : α × α => x.2 / x.1) (𝓝 (1 : α)) := by
  rw [nhds_eq_comap_uniformity, Filter.comap_comap]
  refine' le_antisymmₓ (Filter.map_le_iff_le_comap.1 _) _
  · intro s hs
    rcases mem_uniformity_of_uniform_continuous_invariant uniform_continuous_div hs with ⟨t, ht, hts⟩
    refine' mem_map.2 (mem_of_superset ht _)
    rintro ⟨a, b⟩
    simpa [← subset_def] using hts a b a
    
  · intro s hs
    rcases mem_uniformity_of_uniform_continuous_invariant uniform_continuous_mul hs with ⟨t, ht, hts⟩
    refine' ⟨_, ht, _⟩
    rintro ⟨a, b⟩
    simpa [← subset_def] using hts 1 (b / a) a
    

@[to_additive]
theorem uniformity_eq_comap_nhds_one_swapped : 𝓤 α = comap (fun x : α × α => x.1 / x.2) (𝓝 (1 : α)) := by
  rw [← comap_swap_uniformity, uniformity_eq_comap_nhds_one, comap_comap, (· ∘ ·)]
  rfl

open MulOpposite

@[to_additive]
theorem uniformity_eq_comap_inv_mul_nhds_one : 𝓤 α = comap (fun x : α × α => x.1⁻¹ * x.2) (𝓝 (1 : α)) := by
  rw [← comap_uniformity_mul_opposite, uniformity_eq_comap_nhds_one, ← op_one, ← comap_unop_nhds, comap_comap,
    comap_comap]
  simp [← (· ∘ ·)]

@[to_additive]
theorem uniformity_eq_comap_inv_mul_nhds_one_swapped : 𝓤 α = comap (fun x : α × α => x.2⁻¹ * x.1) (𝓝 (1 : α)) := by
  rw [← comap_swap_uniformity, uniformity_eq_comap_inv_mul_nhds_one, comap_comap, (· ∘ ·)]
  rfl

end

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one {ι} {p : ι → Prop} {U : ι → Set α} (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.2 / x.1 ∈ U i } := by
  rw [uniformity_eq_comap_nhds_one]
  exact h.comap _

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x : α × α | x.1⁻¹ * x.2 ∈ U i } := by
  rw [uniformity_eq_comap_inv_mul_nhds_one]
  exact h.comap _

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_swapped {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x : α × α | x.1 / x.2 ∈ U i } := by
  rw [uniformity_eq_comap_nhds_one_swapped]
  exact h.comap _

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x : α × α | x.2⁻¹ * x.1 ∈ U i } := by
  rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
  exact h.comap _

@[to_additive]
theorem group_separation_rel (x y : α) : (x, y) ∈ SeparationRel α ↔ x / y ∈ Closure ({1} : Set α) :=
  have : Embedding fun a => a * (y / x) := (uniform_embedding_translate_mul (y / x)).Embedding
  show (x, y) ∈ ⋂₀ (𝓤 α).Sets ↔ x / y ∈ Closure ({1} : Set α) by
    rw [this.closure_eq_preimage_closure_image, uniformity_eq_comap_nhds_one α, sInter_comap_sets]
    simp [← mem_closure_iff_nhds, ← inter_singleton_nonempty, ← sub_eq_add_neg, ← add_assocₓ]

@[to_additive]
theorem uniform_continuous_of_tendsto_one {hom : Type _} [UniformSpace β] [Groupₓ β] [UniformGroup β]
    [MonoidHomClass hom α β] {f : hom} (h : Tendsto f (𝓝 1) (𝓝 1)) : UniformContinuous f := by
  have : ((fun x : β × β => x.2 / x.1) ∘ fun x : α × α => (f x.1, f x.2)) = fun x : α × α => f (x.2 / x.1) := by
    simp only [← map_div]
  rw [UniformContinuous, uniformity_eq_comap_nhds_one α, uniformity_eq_comap_nhds_one β, tendsto_comap_iff, this]
  exact tendsto.comp h tendsto_comap

/-- A group homomorphism (a bundled morphism of a type that implements `monoid_hom_class`) between
two uniform groups is uniformly continuous provided that it is continuous at one. See also
`continuous_of_continuous_at_one`. -/
@[to_additive
      "An additive group homomorphism (a bundled morphism of a type that implements\n`add_monoid_hom_class`) between two uniform additive groups is uniformly continuous provided that it\nis continuous at zero. See also `continuous_of_continuous_at_zero`."]
theorem uniform_continuous_of_continuous_at_one {hom : Type _} [UniformSpace β] [Groupₓ β] [UniformGroup β]
    [MonoidHomClass hom α β] (f : hom) (hf : ContinuousAt f 1) : UniformContinuous f :=
  uniform_continuous_of_tendsto_one
    (by
      simpa using hf.tendsto)

@[to_additive]
theorem MonoidHom.uniform_continuous_of_continuous_at_one [UniformSpace β] [Groupₓ β] [UniformGroup β] (f : α →* β)
    (hf : ContinuousAt f 1) : UniformContinuous f :=
  uniform_continuous_of_continuous_at_one f hf

/-- A homomorphism from a uniform group to a discrete uniform group is continuous if and only if
its kernel is open. -/
@[to_additive
      "A homomorphism from a uniform additive group to a discrete uniform additive group is\ncontinuous if and only if its kernel is open."]
theorem UniformGroup.uniform_continuous_iff_open_ker {hom : Type _} [UniformSpace β] [DiscreteTopology β] [Groupₓ β]
    [UniformGroup β] [MonoidHomClass hom α β] {f : hom} : UniformContinuous f ↔ IsOpen ((f : α →* β).ker : Set α) := by
  refine' ⟨fun hf => _, fun hf => _⟩
  · apply (is_open_discrete ({1} : Set β)).Preimage (UniformContinuous.continuous hf)
    
  · apply uniform_continuous_of_continuous_at_one
    rw [ContinuousAt, nhds_discrete β, map_one, tendsto_pure]
    exact hf.mem_nhds (map_one f)
    

@[to_additive]
theorem uniform_continuous_monoid_hom_of_continuous {hom : Type _} [UniformSpace β] [Groupₓ β] [UniformGroup β]
    [MonoidHomClass hom α β] {f : hom} (h : Continuous f) : UniformContinuous f :=
  uniform_continuous_of_tendsto_one <|
    suffices Tendsto f (𝓝 1) (𝓝 (f 1)) by
      rwa [map_one] at this
    h.Tendsto 1

@[to_additive]
theorem CauchySeq.mul {ι : Type _} [SemilatticeSup ι] {u v : ι → α} (hu : CauchySeq u) (hv : CauchySeq v) :
    CauchySeq (u * v) :=
  uniform_continuous_mul.comp_cauchy_seq (hu.Prod hv)

@[to_additive]
theorem CauchySeq.mul_const {ι : Type _} [SemilatticeSup ι] {u : ι → α} {x : α} (hu : CauchySeq u) :
    CauchySeq fun n => u n * x :=
  (uniform_continuous_id.mul uniform_continuous_const).comp_cauchy_seq hu

@[to_additive]
theorem CauchySeq.const_mul {ι : Type _} [SemilatticeSup ι] {u : ι → α} {x : α} (hu : CauchySeq u) :
    CauchySeq fun n => x * u n :=
  (uniform_continuous_const.mul uniform_continuous_id).comp_cauchy_seq hu

@[to_additive]
theorem CauchySeq.inv {ι : Type _} [SemilatticeSup ι] {u : ι → α} (h : CauchySeq u) : CauchySeq u⁻¹ :=
  uniform_continuous_inv.comp_cauchy_seq h

@[to_additive]
theorem totally_bounded_iff_subset_finite_Union_nhds_one {s : Set α} :
    TotallyBounded s ↔ ∀, ∀ U ∈ 𝓝 (1 : α), ∀, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, y • U :=
  (𝓝 (1 : α)).basis_sets.uniformity_of_nhds_one_inv_mul_swapped.totally_bounded_iff.trans <| by
    simp [preimage_smul_inv, ← preimage]

section UniformConvergence

variable {ι : Type _} {l : Filter ι} {f f' : ι → β → α} {g g' : β → α} {s : Set β}

@[to_additive]
theorem TendstoUniformlyOn.mul (hf : TendstoUniformlyOn f g l s) (hf' : TendstoUniformlyOn f' g' l s) :
    TendstoUniformlyOn (f * f') (g * g') l s := fun u hu =>
  ((uniform_continuous_mul.comp_tendsto_uniformly_on (hf.Prod hf')) u hu).diag_of_prod

@[to_additive]
theorem TendstoUniformlyOn.div (hf : TendstoUniformlyOn f g l s) (hf' : TendstoUniformlyOn f' g' l s) :
    TendstoUniformlyOn (f / f') (g / g') l s := fun u hu =>
  ((uniform_continuous_div.comp_tendsto_uniformly_on (hf.Prod hf')) u hu).diag_of_prod

@[to_additive]
theorem UniformCauchySeqOn.mul (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s) :
    UniformCauchySeqOn (f * f') l s := fun u hu => by
  simpa using (uniform_continuous_mul.comp_uniform_cauchy_seq_on (hf.prod' hf')) u hu

@[to_additive]
theorem UniformCauchySeqOn.div (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s) :
    UniformCauchySeqOn (f / f') l s := fun u hu => by
  simpa using (uniform_continuous_div.comp_uniform_cauchy_seq_on (hf.prod' hf')) u hu

end UniformConvergence

end UniformGroup

section TopologicalCommGroup

open Filter

variable (G : Type _) [CommGroupₓ G] [TopologicalSpace G] [TopologicalGroup G]

/-- The right uniformity on a topological group. -/
@[to_additive "The right uniformity on a topological group"]
def TopologicalGroup.toUniformSpace : UniformSpace G where
  uniformity := comap (fun p : G × G => p.2 / p.1) (𝓝 1)
  refl := by
    refine' map_le_iff_le_comap.1 (le_transₓ _ (pure_le_nhds 1)) <;>
      simp (config := { contextual := true })[← Set.subset_def]
  symm := by
    suffices tendsto (fun p : G × G => (p.2 / p.1)⁻¹) (comap (fun p : G × G => p.2 / p.1) (𝓝 1)) (𝓝 1⁻¹) by
      simpa [← tendsto_comap_iff]
    exact tendsto.comp (tendsto.inv tendsto_id) tendsto_comap
  comp := by
    intro D H
    rw [mem_lift'_sets]
    · rcases H with ⟨U, U_nhds, U_sub⟩
      rcases exists_nhds_one_split U_nhds with ⟨V, ⟨V_nhds, V_sum⟩⟩
      exists (fun p : G × G => p.2 / p.1) ⁻¹' V
      have H : (fun p : G × G => p.2 / p.1) ⁻¹' V ∈ comap (fun p : G × G => p.2 / p.1) (𝓝 (1 : G)) := by
        exists V, V_nhds <;> rfl
      exists H
      have comp_rel_sub :
        CompRel ((fun p : G × G => p.2 / p.1) ⁻¹' V) ((fun p => p.2 / p.1) ⁻¹' V) ⊆
          (fun p : G × G => p.2 / p.1) ⁻¹' U :=
        by
        intro p p_comp_rel
        rcases p_comp_rel with ⟨z, ⟨Hz1, Hz2⟩⟩
        simpa [← sub_eq_add_neg, ← add_commₓ, ← add_left_commₓ] using V_sum _ Hz1 _ Hz2
      exact Set.Subset.trans comp_rel_sub U_sub
      
    · exact monotone_comp_rel monotone_id monotone_id
      
  is_open_uniformity := by
    intro S
    let S' := fun x => { p : G × G | p.1 = x → p.2 ∈ S }
    show IsOpen S ↔ ∀ x : G, x ∈ S → S' x ∈ comap (fun p : G × G => p.2 / p.1) (𝓝 (1 : G))
    rw [is_open_iff_mem_nhds]
    refine' forall₂_congrₓ fun a ha => _
    rw [← nhds_translation_div, mem_comap, mem_comap]
    refine' exists₂_congrₓ fun t ht => _
    show (fun y : G => y / a) ⁻¹' t ⊆ S ↔ (fun p : G × G => p.snd / p.fst) ⁻¹' t ⊆ S' a
    constructor
    · rintro h ⟨x, y⟩ hx rfl
      exact h hx
      
    · rintro h x hx
      exact @h (a, x) hx rfl
      

variable {G}

@[to_additive]
theorem TopologicalGroup.tendsto_uniformly_iff {ι α : Type _} (F : ι → α → G) (f : α → G) (p : Filter ι) :
    @TendstoUniformly α G ι (TopologicalGroup.toUniformSpace G) F f p ↔
      ∀, ∀ u ∈ 𝓝 (1 : G), ∀, ∀ᶠ i in p, ∀ a, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h v ⟨u, hu, hv⟩ => mem_of_superset (h u hu) fun i hi a => hv (hi a)⟩

@[to_additive]
theorem TopologicalGroup.tendsto_uniformly_on_iff {ι α : Type _} (F : ι → α → G) (f : α → G) (p : Filter ι)
    (s : Set α) :
    @TendstoUniformlyOn α G ι (TopologicalGroup.toUniformSpace G) F f p s ↔
      ∀, ∀ u ∈ 𝓝 (1 : G), ∀, ∀ᶠ i in p, ∀, ∀ a ∈ s, ∀, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h v ⟨u, hu, hv⟩ =>
    mem_of_superset (h u hu) fun i hi a ha => hv (hi a ha)⟩

@[to_additive]
theorem TopologicalGroup.tendsto_locally_uniformly_iff {ι α : Type _} [TopologicalSpace α] (F : ι → α → G) (f : α → G)
    (p : Filter ι) :
    @TendstoLocallyUniformly α G ι (TopologicalGroup.toUniformSpace G) _ F f p ↔
      ∀, ∀ u ∈ 𝓝 (1 : G), ∀ (x : α), ∃ t ∈ 𝓝 x, ∀ᶠ i in p, ∀, ∀ a ∈ t, ∀, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h v ⟨u, hu, hv⟩ x =>
    exists_imp_exists (fun a => exists_imp_exists fun ha hp => mem_of_superset hp fun i hi a ha => hv (hi a ha))
      (h u hu x)⟩

@[to_additive]
theorem TopologicalGroup.tendsto_locally_uniformly_on_iff {ι α : Type _} [TopologicalSpace α] (F : ι → α → G)
    (f : α → G) (p : Filter ι) (s : Set α) :
    @TendstoLocallyUniformlyOn α G ι (TopologicalGroup.toUniformSpace G) _ F f p s ↔
      ∀, ∀ u ∈ 𝓝 (1 : G), ∀, ∀ x ∈ s, ∀, ∃ t ∈ 𝓝[s] x, ∀ᶠ i in p, ∀, ∀ a ∈ t, ∀, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h v ⟨u, hu, hv⟩ x =>
    (exists_imp_exists fun a => exists_imp_exists fun ha hp => mem_of_superset hp fun i hi a ha => hv (hi a ha)) ∘
      h u hu x⟩

end TopologicalCommGroup

section TopologicalCommGroup

universe u v w x

open Filter

variable (G : Type _) [CommGroupₓ G] [TopologicalSpace G] [TopologicalGroup G]

section

attribute [local instance] TopologicalGroup.toUniformSpace

@[to_additive]
theorem uniformity_eq_comap_nhds_one' : 𝓤 G = comap (fun p : G × G => p.2 / p.1) (𝓝 (1 : G)) :=
  rfl

variable {G}

@[to_additive]
theorem topological_group_is_uniform : UniformGroup G := by
  have :
    Tendsto ((fun p : G × G => p.1 / p.2) ∘ fun p : (G × G) × G × G => (p.1.2 / p.1.1, p.2.2 / p.2.1))
      (comap (fun p : (G × G) × G × G => (p.1.2 / p.1.1, p.2.2 / p.2.1)) ((𝓝 1).Prod (𝓝 1))) (𝓝 (1 / 1)) :=
    (tendsto_fst.div' tendsto_snd).comp tendsto_comap
  constructor
  rw [UniformContinuous, uniformity_prod_eq_prod, tendsto_map'_iff, uniformity_eq_comap_nhds_one' G, tendsto_comap_iff,
    prod_comap_comap_eq]
  simpa [← (· ∘ ·), ← div_eq_mul_inv, ← mul_comm, ← mul_left_commₓ] using this

open Set

@[to_additive]
theorem TopologicalGroup.t2_space_iff_one_closed : T2Space G ↔ IsClosed ({1} : Set G) := by
  have : UniformGroup G := topological_group_is_uniform
  rw [← separated_iff_t2, separated_space_iff, ← closure_eq_iff_is_closed]
  constructor <;> intro h
  · apply subset.antisymm
    · intro x x_in
      have := group_separation_rel x 1
      rw [div_one] at this
      rw [← this, h] at x_in
      change x = 1 at x_in
      simp [← x_in]
      
    · exact subset_closure
      
    
  · ext p
    cases' p with x y
    rw [group_separation_rel x, h, mem_singleton_iff, div_eq_one]
    rfl
    

@[to_additive]
theorem TopologicalGroup.t2_space_of_one_sep (H : ∀ x : G, x ≠ 1 → ∃ U ∈ nhds (1 : G), x ∉ U) : T2Space G := by
  rw [TopologicalGroup.t2_space_iff_one_closed, ← is_open_compl_iff, is_open_iff_mem_nhds]
  intro x x_not
  have : x ≠ 1 := mem_compl_singleton_iff.mp x_not
  rcases H x this with ⟨U, U_in, xU⟩
  rw [← nhds_one_symm G] at U_in
  rcases U_in with ⟨W, W_in, UW⟩
  rw [← nhds_translation_mul_inv]
  use W, W_in
  rw [subset_compl_comm]
  suffices x⁻¹ ∉ W by
    simpa
  exact fun h => xU (UW h)

end

@[to_additive]
theorem UniformGroup.to_uniform_space_eq {G : Type _} [u : UniformSpace G] [CommGroupₓ G] [UniformGroup G] :
    TopologicalGroup.toUniformSpace G = u := by
  ext : 1
  show @uniformity G (TopologicalGroup.toUniformSpace G) = 𝓤 G
  rw [uniformity_eq_comap_nhds_one' G, uniformity_eq_comap_nhds_one G]

end TopologicalCommGroup

open CommGroupₓ Filter Set Function

section

variable {α : Type _} {β : Type _} {hom : Type _}

variable [TopologicalSpace α] [CommGroupₓ α] [TopologicalGroup α]

-- β is a dense subgroup of α, inclusion is denoted by e
variable [TopologicalSpace β] [CommGroupₓ β]

variable [MonoidHomClass hom β α] {e : hom} (de : DenseInducing e)

include de

@[to_additive]
theorem tendsto_div_comap_self (x₀ : α) :
    Tendsto (fun t : β × β => t.2 / t.1) ((comap fun p : β × β => (e p.1, e p.2)) <| 𝓝 (x₀, x₀)) (𝓝 1) := by
  have comm : ((fun x : α × α => x.2 / x.1) ∘ fun t : β × β => (e t.1, e t.2)) = e ∘ fun t : β × β => t.2 / t.1 := by
    ext t
    change e t.2 / e t.1 = e (t.2 / t.1)
    rwa [← map_div e t.2 t.1]
  have lim : tendsto (fun x : α × α => x.2 / x.1) (𝓝 (x₀, x₀)) (𝓝 (e 1)) := by
    simpa using (continuous_div'.comp (@continuous_swap α α _ _)).Tendsto (x₀, x₀)
  simpa using de.tendsto_comap_nhds_nhds limₓ comm

end

namespace DenseInducing

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

variable {G : Type _}

-- β is a dense subgroup of α, inclusion is denoted by e
-- δ is a dense subgroup of γ, inclusion is denoted by f
variable [TopologicalSpace α] [AddCommGroupₓ α] [TopologicalAddGroup α]

variable [TopologicalSpace β] [AddCommGroupₓ β] [TopologicalAddGroup β]

variable [TopologicalSpace γ] [AddCommGroupₓ γ] [TopologicalAddGroup γ]

variable [TopologicalSpace δ] [AddCommGroupₓ δ] [TopologicalAddGroup δ]

variable [UniformSpace G] [AddCommGroupₓ G] [UniformAddGroup G] [SeparatedSpace G] [CompleteSpace G]

variable {e : β →+ α} (de : DenseInducing e)

variable {f : δ →+ γ} (df : DenseInducing f)

variable {φ : β →+ δ →+ G}

-- mathport name: «exprΦ»
local notation "Φ" => fun p : β × δ => φ p.1 p.2

variable (hφ : Continuous Φ)

include de df hφ

variable {W' : Set G} (W'_nhd : W' ∈ 𝓝 (0 : G))

include W'_nhd

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x x' «expr ∈ » U₂)
private theorem extend_Z_bilin_aux (x₀ : α) (y₁ : δ) :
    ∃ U₂ ∈ comap e (𝓝 x₀), ∀ (x x') (_ : x ∈ U₂) (_ : x' ∈ U₂), Φ (x' - x, y₁) ∈ W' := by
  let Nx := 𝓝 x₀
  let ee := fun u : β × β => (e u.1, e u.2)
  have lim1 : tendsto (fun a : β × β => (a.2 - a.1, y₁)) (comap e Nx ×ᶠ comap e Nx) (𝓝 (0, y₁)) := by
    have :=
      tendsto.prod_mk (tendsto_sub_comap_self de x₀)
        (tendsto_const_nhds : tendsto (fun p : β × β => y₁) (comap ee <| 𝓝 (x₀, x₀)) (𝓝 y₁))
    rw [nhds_prod_eq, prod_comap_comap_eq, ← nhds_prod_eq]
    exact (this : _)
  have lim2 : tendsto Φ (𝓝 (0, y₁)) (𝓝 0) := by
    simpa using hφ.tendsto (0, y₁)
  have lim := lim2.comp lim1
  rw [tendsto_prod_self_iff] at lim
  simp_rw [ball_mem_comm]
  exact limₓ W' W'_nhd

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x x' «expr ∈ » U₁)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (y y' «expr ∈ » V₁)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x x' «expr ∈ » U)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (y y' «expr ∈ » V)
private theorem extend_Z_bilin_key (x₀ : α) (y₀ : γ) :
    ∃ U ∈ comap e (𝓝 x₀),
      ∃ V ∈ comap f (𝓝 y₀),
        ∀ (x x') (_ : x ∈ U) (_ : x' ∈ U), ∀ (y y') (_ : y ∈ V) (_ : y' ∈ V), Φ (x', y') - Φ (x, y) ∈ W' :=
  by
  let Nx := 𝓝 x₀
  let Ny := 𝓝 y₀
  let dp := DenseInducing.prod de df
  let ee := fun u : β × β => (e u.1, e u.2)
  let ff := fun u : δ × δ => (f u.1, f u.2)
  have lim_φ : Filter.Tendsto Φ (𝓝 (0, 0)) (𝓝 0) := by
    simpa using hφ.tendsto (0, 0)
  have lim_φ_sub_sub :
    tendsto (fun p : (β × β) × δ × δ => Φ (p.1.2 - p.1.1, p.2.2 - p.2.1))
      ((comap ee <| 𝓝 (x₀, x₀)) ×ᶠ (comap ff <| 𝓝 (y₀, y₀))) (𝓝 0) :=
    by
    have lim_sub_sub :
      tendsto (fun p : (β × β) × δ × δ => (p.1.2 - p.1.1, p.2.2 - p.2.1))
        (comap ee (𝓝 (x₀, x₀)) ×ᶠ comap ff (𝓝 (y₀, y₀))) (𝓝 0 ×ᶠ 𝓝 0) :=
      by
      have := Filter.prod_mono (tendsto_sub_comap_self de x₀) (tendsto_sub_comap_self df y₀)
      rwa [prod_map_map_eq] at this
    rw [← nhds_prod_eq] at lim_sub_sub
    exact tendsto.comp lim_φ lim_sub_sub
  rcases exists_nhds_zero_quarter W'_nhd with ⟨W, W_nhd, W4⟩
  have :
    ∃ U₁ ∈ comap e (𝓝 x₀),
      ∃ V₁ ∈ comap f (𝓝 y₀),
        ∀ (x x') (_ : x ∈ U₁) (_ : x' ∈ U₁), ∀ (y y') (_ : y ∈ V₁) (_ : y' ∈ V₁), Φ (x' - x, y' - y) ∈ W :=
    by
    have := tendsto_prod_iff.1 lim_φ_sub_sub W W_nhd
    repeat'
      rw [nhds_prod_eq, ← prod_comap_comap_eq] at this
    rcases this with ⟨U, U_in, V, V_in, H⟩
    rw [mem_prod_same_iff] at U_in V_in
    rcases U_in with ⟨U₁, U₁_in, HU₁⟩
    rcases V_in with ⟨V₁, V₁_in, HV₁⟩
    exists U₁, U₁_in, V₁, V₁_in
    intro x x_in x' x'_in y y_in y' y'_in
    exact H _ _ (HU₁ (mk_mem_prod x_in x'_in)) (HV₁ (mk_mem_prod y_in y'_in))
  rcases this with ⟨U₁, U₁_nhd, V₁, V₁_nhd, H⟩
  obtain ⟨x₁, x₁_in⟩ : U₁.nonempty := (de.comap_nhds_ne_bot _).nonempty_of_mem U₁_nhd
  obtain ⟨y₁, y₁_in⟩ : V₁.nonempty := (df.comap_nhds_ne_bot _).nonempty_of_mem V₁_nhd
  have cont_flip : Continuous fun p : δ × β => φ.flip p.1 p.2 := by
    show Continuous (Φ ∘ Prod.swap)
    exact hφ.comp continuous_swap
  rcases extend_Z_bilin_aux de df hφ W_nhd x₀ y₁ with ⟨U₂, U₂_nhd, HU⟩
  rcases extend_Z_bilin_aux df de cont_flip W_nhd y₀ x₁ with ⟨V₂, V₂_nhd, HV⟩
  exists U₁ ∩ U₂, inter_mem U₁_nhd U₂_nhd, V₁ ∩ V₂, inter_mem V₁_nhd V₂_nhd
  rintro x ⟨xU₁, xU₂⟩ x' ⟨x'U₁, x'U₂⟩ y ⟨yV₁, yV₂⟩ y' ⟨y'V₁, y'V₂⟩
  have key_formula : φ x' y' - φ x y = φ (x' - x) y₁ + φ (x' - x) (y' - y₁) + φ x₁ (y' - y) + φ (x - x₁) (y' - y) := by
    simp
    abel
  rw [key_formula]
  have h₁ := HU x xU₂ x' x'U₂
  have h₂ := H x xU₁ x' x'U₁ y₁ y₁_in y' y'V₁
  have h₃ := HV y yV₂ y' y'V₂
  have h₄ := H x₁ x₁_in x xU₁ y yV₁ y' y'V₁
  exact W4 h₁ h₂ h₃ h₄

omit W'_nhd

open DenseInducing

/-- Bourbaki GT III.6.5 Theorem I:
ℤ-bilinear continuous maps from dense images into a complete Hausdorff group extend by continuity.
Note: Bourbaki assumes that α and β are also complete Hausdorff, but this is not necessary. -/
theorem extend_Z_bilin : Continuous (extend (de.Prod df) Φ) := by
  refine' continuous_extend_of_cauchy _ _
  rintro ⟨x₀, y₀⟩
  constructor
  · apply ne_bot.map
    apply comap_ne_bot
    intro U h
    rcases mem_closure_iff_nhds.1 ((de.prod df).dense (x₀, y₀)) U h with ⟨x, x_in, ⟨z, z_x⟩⟩
    exists z
    cc
    
  · suffices
      map (fun p : (β × δ) × β × δ => Φ p.2 - Φ p.1)
          (comap (fun p : (β × δ) × β × δ => ((e p.1.1, f p.1.2), (e p.2.1, f p.2.2))) (𝓝 (x₀, y₀) ×ᶠ 𝓝 (x₀, y₀))) ≤
        𝓝 0
      by
      rwa [uniformity_eq_comap_nhds_zero G, prod_map_map_eq, ← map_le_iff_le_comap, Filter.map_map, prod_comap_comap_eq]
    intro W' W'_nhd
    have key := extend_Z_bilin_key de df hφ W'_nhd x₀ y₀
    rcases key with ⟨U, U_nhd, V, V_nhd, h⟩
    rw [mem_comap] at U_nhd
    rcases U_nhd with ⟨U', U'_nhd, U'_sub⟩
    rw [mem_comap] at V_nhd
    rcases V_nhd with ⟨V', V'_nhd, V'_sub⟩
    rw [mem_map, mem_comap, nhds_prod_eq]
    exists (U' ×ˢ V') ×ˢ U' ×ˢ V'
    rw [mem_prod_same_iff]
    simp only [← exists_prop]
    constructor
    · change U' ∈ 𝓝 x₀ at U'_nhd
      change V' ∈ 𝓝 y₀ at V'_nhd
      have := prod_mem_prod U'_nhd V'_nhd
      tauto
      
    · intro p h'
      simp only [← Set.mem_preimage, ← Set.prod_mk_mem_set_prod_eq] at h'
      rcases p with ⟨⟨x, y⟩, ⟨x', y'⟩⟩
      apply h <;> tauto
      
    

end DenseInducing


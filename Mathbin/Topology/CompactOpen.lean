/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathbin.Tactic.Tidy
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Topology.Homeomorph
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.Maps

/-!
# The compact-open topology

In this file, we define the compact-open topology on the set of continuous maps between two
topological spaces.

## Main definitions

* `compact_open` is the compact-open topology on `C(α, β)`. It is declared as an instance.
* `continuous_map.coev` is the coevaluation map `β → C(α, β × α)`. It is always continuous.
* `continuous_map.curry` is the currying map `C(α × β, γ) → C(α, C(β, γ))`. This map always exists
  and it is continuous as long as `α × β` is locally compact.
* `continuous_map.uncurry` is the uncurrying map `C(α, C(β, γ)) → C(α × β, γ)`. For this map to
  exist, we need `β` to be locally compact. If `α` is also locally compact, then this map is
  continuous.
* `homeomorph.curry` combines the currying and uncurrying operations into a homeomorphism
  `C(α × β, γ) ≃ₜ C(α, C(β, γ))`. This homeomorphism exists if `α` and `β` are locally compact.


## Tags

compact-open, curry, function space
-/


open Set

open TopologicalSpace

namespace ContinuousMap

section CompactOpen

variable {α : Type _} {β : Type _} {γ : Type _}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- A generating set for the compact-open topology (when `s` is compact and `u` is open). -/
def CompactOpen.Gen (s : Set α) (u : Set β) : Set C(α, β) :=
  { f | f '' s ⊆ u }

@[simp]
theorem gen_empty (u : Set β) : CompactOpen.Gen (∅ : Set α) u = Set.Univ :=
  Set.ext fun f => iff_true_intro ((congr_arg (· ⊆ u) (image_empty f)).mpr u.empty_subset)

@[simp]
theorem gen_univ (s : Set α) : CompactOpen.Gen s (Set.Univ : Set β) = Set.Univ :=
  Set.ext fun f => iff_true_intro (f '' s).subset_univ

@[simp]
theorem gen_inter (s : Set α) (u v : Set β) : CompactOpen.Gen s (u ∩ v) = CompactOpen.Gen s u ∩ CompactOpen.Gen s v :=
  Set.ext fun f => subset_inter_iff

@[simp]
theorem gen_union (s t : Set α) (u : Set β) : CompactOpen.Gen (s ∪ t) u = CompactOpen.Gen s u ∩ CompactOpen.Gen t u :=
  Set.ext fun f => (iff_of_eq (congr_arg (· ⊆ u) (image_union f s t))).trans union_subset_iff

theorem gen_empty_right {s : Set α} (h : s.Nonempty) : CompactOpen.Gen s (∅ : Set β) = ∅ :=
  eq_empty_of_forall_not_mem fun f => (h.Image _).not_subset_empty

-- The compact-open topology on the space of continuous maps α → β.
instance compactOpen : TopologicalSpace C(α, β) :=
  TopologicalSpace.generateFrom
    { m | ∃ (s : Set α)(hs : IsCompact s)(u : Set β)(hu : IsOpen u), m = CompactOpen.Gen s u }

protected theorem is_open_gen {s : Set α} (hs : IsCompact s) {u : Set β} (hu : IsOpen u) :
    IsOpen (CompactOpen.Gen s u) :=
  TopologicalSpace.GenerateOpen.basic _
    (by
      dsimp' [← mem_set_of_eq] <;> tauto)

section Functorial

variable (g : C(β, γ))

private theorem preimage_gen {s : Set α} (hs : IsCompact s) {u : Set γ} (hu : IsOpen u) :
    ContinuousMap.comp g ⁻¹' CompactOpen.Gen s u = CompactOpen.Gen s (g ⁻¹' u) := by
  ext ⟨f, _⟩
  change g ∘ f '' s ⊆ u ↔ f '' s ⊆ g ⁻¹' u
  rw [image_comp, image_subset_iff]

/-- C(α, -) is a functor. -/
theorem continuous_comp : Continuous (ContinuousMap.comp g : C(α, β) → C(α, γ)) :=
  continuous_generated_from fun m ⟨s, hs, u, hu, hm⟩ => by
    rw [hm, preimage_gen g hs hu] <;> exact ContinuousMap.is_open_gen hs (hu.preimage g.2)

variable (f : C(α, β))

private theorem image_gen {s : Set α} (hs : IsCompact s) {u : Set γ} (hu : IsOpen u) :
    (fun g : C(β, γ) => g.comp f) ⁻¹' CompactOpen.Gen s u = CompactOpen.Gen (f '' s) u := by
  ext ⟨g, _⟩
  change g ∘ f '' s ⊆ u ↔ g '' (f '' s) ⊆ u
  rw [Set.image_comp]

/-- C(-, γ) is a functor. -/
theorem continuous_comp_left : Continuous (fun g => g.comp f : C(β, γ) → C(α, γ)) :=
  continuous_generated_from fun m ⟨s, hs, u, hu, hm⟩ => by
    rw [hm, image_gen f hs hu]
    exact ContinuousMap.is_open_gen (hs.image f.2) hu

end Functorial

section Ev

variable {α β}

/-- The evaluation map `C(α, β) × α → β` is continuous if `α` is locally compact.

See also `continuous_map.continuous_eval` -/
theorem continuous_eval' [LocallyCompactSpace α] : Continuous fun p : C(α, β) × α => p.1 p.2 :=
  continuous_iff_continuous_at.mpr fun ⟨f, x⟩ n hn =>
    let ⟨v, vn, vo, fxv⟩ := mem_nhds_iff.mp hn
    have : v ∈ 𝓝 (f x) := IsOpen.mem_nhds vo fxv
    let ⟨s, hs, sv, sc⟩ := LocallyCompactSpace.local_compact_nhds x (f ⁻¹' v) (f.Continuous.Tendsto x this)
    let ⟨u, us, uo, xu⟩ := mem_nhds_iff.mp hs
    show (fun p : C(α, β) × α => p.1 p.2) ⁻¹' n ∈ 𝓝 (f, x) from
      let w := CompactOpen.Gen s v ×ˢ u
      have : w ⊆ (fun p : C(α, β) × α => p.1 p.2) ⁻¹' n := fun ⟨f', x'⟩ ⟨hf', hx'⟩ =>
        calc
          f' x' ∈ f' '' s := mem_image_of_mem f' (us hx')
          _ ⊆ v := hf'
          _ ⊆ n := vn
          
      have : IsOpen w := (ContinuousMap.is_open_gen sc vo).Prod uo
      have : (f, x) ∈ w := ⟨image_subset_iff.mpr sv, xu⟩
      mem_nhds_iff.mpr
        ⟨w, by
          assumption, by
          assumption, by
          assumption⟩

/-- See also `continuous_map.continuous_eval_const` -/
theorem continuous_eval_const' [LocallyCompactSpace α] (a : α) : Continuous fun f : C(α, β) => f a :=
  continuous_eval'.comp (continuous_id.prod_mk continuous_const)

/-- See also `continuous_map.continuous_coe` -/
theorem continuous_coe' [LocallyCompactSpace α] : @Continuous C(α, β) (α → β) _ _ coeFn :=
  continuous_pi continuous_eval_const'

instance [T2Space β] : T2Space C(α, β) :=
  ⟨by
    intro f₁ f₂ h
    obtain ⟨x, hx⟩ := not_forall.mp (mt (FunLike.ext f₁ f₂) h)
    obtain ⟨u, v, hu, hv, hxu, hxv, huv⟩ := t2_separation hx
    refine'
      ⟨compact_open.gen {x} u, compact_open.gen {x} v, ContinuousMap.is_open_gen is_compact_singleton hu,
        ContinuousMap.is_open_gen is_compact_singleton hv, _, _, _⟩
    · rwa [compact_open.gen, mem_set_of_eq, image_singleton, singleton_subset_iff]
      
    · rwa [compact_open.gen, mem_set_of_eq, image_singleton, singleton_subset_iff]
      
    · rw [disjoint_iff_inter_eq_empty, ← gen_inter, huv.inter_eq, gen_empty_right (singleton_nonempty _)]
      ⟩

end Ev

section InfInduced

theorem compact_open_le_induced (s : Set α) :
    (ContinuousMap.compactOpen : TopologicalSpace C(α, β)) ≤
      TopologicalSpace.induced (ContinuousMap.restrict s) ContinuousMap.compactOpen :=
  by
  simp only [← induced_generate_from_eq, ← ContinuousMap.compactOpen]
  apply generate_from_mono
  rintro b ⟨a, ⟨c, hc, u, hu, rfl⟩, rfl⟩
  refine' ⟨coe '' c, hc.image continuous_subtype_coe, u, hu, _⟩
  ext f
  simp only [← compact_open.gen, ← mem_set_of_eq, ← mem_preimage, ← ContinuousMap.coe_restrict]
  rw [image_comp f (coe : s → α)]

/-- The compact-open topology on `C(α, β)` is equal to the infimum of the compact-open topologies
on `C(s, β)` for `s` a compact subset of `α`.  The key point of the proof is that the union of the
compact subsets of `α` is equal to the union of compact subsets of the compact subsets of `α`. -/
theorem compact_open_eq_Inf_induced :
    (ContinuousMap.compactOpen : TopologicalSpace C(α, β)) =
      ⨅ (s : Set α) (hs : IsCompact s), TopologicalSpace.induced (ContinuousMap.restrict s) ContinuousMap.compactOpen :=
  by
  refine' le_antisymmₓ _ _
  · refine' le_infi₂ _
    exact fun s hs => compact_open_le_induced s
    
  simp only [generate_from_Union, ← induced_generate_from_eq, ← ContinuousMap.compactOpen]
  apply generate_from_mono
  rintro _ ⟨s, hs, u, hu, rfl⟩
  rw [mem_Union₂]
  refine' ⟨s, hs, _, ⟨univ, is_compact_iff_is_compact_univ.mp hs, u, hu, rfl⟩, _⟩
  ext f
  simp only [← compact_open.gen, ← mem_set_of_eq, ← mem_preimage, ← ContinuousMap.coe_restrict]
  rw [image_comp f (coe : s → α)]
  simp

/-- For any subset `s` of `α`, the restriction of continuous functions to `s` is continuous as a
function from `C(α, β)` to `C(s, β)` with their respective compact-open topologies. -/
theorem continuous_restrict (s : Set α) : Continuous fun F : C(α, β) => F.restrict s := by
  rw [continuous_iff_le_induced]
  exact compact_open_le_induced s

theorem nhds_compact_open_eq_Inf_nhds_induced (f : C(α, β)) :
    𝓝 f = ⨅ (s) (hs : IsCompact s), (𝓝 (f.restrict s)).comap (ContinuousMap.restrict s) := by
  rw [compact_open_eq_Inf_induced]
  simp [← nhds_infi, ← nhds_induced]

theorem tendsto_compact_open_restrict {ι : Type _} {l : Filter ι} {F : ι → C(α, β)} {f : C(α, β)}
    (hFf : Filter.Tendsto F l (𝓝 f)) (s : Set α) : Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 (f.restrict s)) :=
  (continuous_restrict s).ContinuousAt.Tendsto.comp hFf

theorem tendsto_compact_open_iff_forall {ι : Type _} {l : Filter ι} (F : ι → C(α, β)) (f : C(α, β)) :
    Filter.Tendsto F l (𝓝 f) ↔
      ∀ (s) (hs : IsCompact s), Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 (f.restrict s)) :=
  by
  rw [compact_open_eq_Inf_induced]
  simp [← nhds_infi, ← nhds_induced, ← Filter.tendsto_comap_iff]

/-- A family `F` of functions in `C(α, β)` converges in the compact-open topology, if and only if
it converges in the compact-open topology on each compact subset of `α`. -/
theorem exists_tendsto_compact_open_iff_forall [LocallyCompactSpace α] [T2Space α] [T2Space β] {ι : Type _}
    {l : Filter ι} [Filter.NeBot l] (F : ι → C(α, β)) :
    (∃ f, Filter.Tendsto F l (𝓝 f)) ↔
      ∀ (s : Set α) (hs : IsCompact s), ∃ f, Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 f) :=
  by
  constructor
  · rintro ⟨f, hf⟩ s hs
    exact ⟨f.restrict s, tendsto_compact_open_restrict hf s⟩
    
  · intro h
    choose f hf using h
    -- By uniqueness of limits in a `t2_space`, since `λ i, F i x` tends to both `f s₁ hs₁ x` and
    -- `f s₂ hs₂ x`, we have `f s₁ hs₁ x = f s₂ hs₂ x`
    have h :
      ∀ (s₁) (hs₁ : IsCompact s₁) (s₂) (hs₂ : IsCompact s₂) (x : α) (hxs₁ : x ∈ s₁) (hxs₂ : x ∈ s₂),
        f s₁ hs₁ ⟨x, hxs₁⟩ = f s₂ hs₂ ⟨x, hxs₂⟩ :=
      by
      rintro s₁ hs₁ s₂ hs₂ x hxs₁ hxs₂
      have := is_compact_iff_compact_space.mp hs₁
      have := is_compact_iff_compact_space.mp hs₂
      have h₁ := (continuous_eval_const' (⟨x, hxs₁⟩ : s₁)).ContinuousAt.Tendsto.comp (hf s₁ hs₁)
      have h₂ := (continuous_eval_const' (⟨x, hxs₂⟩ : s₂)).ContinuousAt.Tendsto.comp (hf s₂ hs₂)
      exact tendsto_nhds_unique h₁ h₂
    -- So glue the `f s hs` together and prove that this glued function `f₀` is a limit on each
    -- compact set `s`
    have hs : ∀ x : α, ∃ (s : _)(hs : IsCompact s), s ∈ 𝓝 x := by
      intro x
      obtain ⟨s, hs, hs'⟩ := exists_compact_mem_nhds x
      exact ⟨s, hs, hs'⟩
    refine' ⟨lift_cover' _ _ h hs, _⟩
    rw [tendsto_compact_open_iff_forall]
    intro s hs
    rw [lift_cover_restrict']
    exact hf s hs
    

end InfInduced

section Coev

variable (α β)

/-- The coevaluation map `β → C(α, β × α)` sending a point `x : β` to the continuous function
on `α` sending `y` to `(x, y)`. -/
def coev (b : β) : C(α, β × α) :=
  ⟨Prod.mk b, continuous_const.prod_mk continuous_id⟩

variable {α β}

theorem image_coev {y : β} (s : Set α) : coev α β y '' s = ({y} : Set β) ×ˢ s := by
  tidy

-- The coevaluation map β → C(α, β × α) is continuous (always).
theorem continuous_coev : Continuous (coev α β) :=
  continuous_generated_from <| by
    rintro _ ⟨s, sc, u, uo, rfl⟩
    rw [is_open_iff_forall_mem_open]
    intro y hy
    change coev α β y '' s ⊆ u at hy
    rw [image_coev s] at hy
    rcases generalized_tube_lemma is_compact_singleton sc uo hy with ⟨v, w, vo, wo, yv, sw, vwu⟩
    refine' ⟨v, _, vo, singleton_subset_iff.mp yv⟩
    intro y' hy'
    change coev α β y' '' s ⊆ u
    rw [image_coev s]
    exact subset.trans (prod_mono (singleton_subset_iff.mpr hy') sw) vwu

end Coev

section Curry

/-- Auxiliary definition, see `continuous_map.curry` and `homeomorph.curry`. -/
def curry' (f : C(α × β, γ)) (a : α) : C(β, γ) :=
  ⟨Function.curry f a⟩

/-- If a map `α × β → γ` is continuous, then its curried form `α → C(β, γ)` is continuous. -/
theorem continuous_curry' (f : C(α × β, γ)) : Continuous (curry' f) :=
  have hf : curry' f = ContinuousMap.comp f ∘ coev _ _ := by
    ext
    rfl
  hf ▸ Continuous.comp (continuous_comp f) continuous_coev

/-- To show continuity of a map `α → C(β, γ)`, it suffices to show that its uncurried form
    `α × β → γ` is continuous. -/
theorem continuous_of_continuous_uncurry (f : α → C(β, γ)) (h : Continuous (Function.uncurry fun x y => f x y)) :
    Continuous f := by
  convert continuous_curry' ⟨_, h⟩
  ext
  rfl

/-- The curried form of a continuous map `α × β → γ` as a continuous map `α → C(β, γ)`.
    If `a × β` is locally compact, this is continuous. If `α` and `β` are both locally
    compact, then this is a homeomorphism, see `homeomorph.curry`. -/
def curry (f : C(α × β, γ)) : C(α, C(β, γ)) :=
  ⟨_, continuous_curry' f⟩

/-- The currying process is a continuous map between function spaces. -/
theorem continuous_curry [LocallyCompactSpace (α × β)] : Continuous (curry : C(α × β, γ) → C(α, C(β, γ))) := by
  apply continuous_of_continuous_uncurry
  apply continuous_of_continuous_uncurry
  rw [← Homeomorph.comp_continuous_iff' (Homeomorph.prodAssoc _ _ _).symm]
  convert continuous_eval' <;> tidy

@[simp]
theorem curry_apply (f : C(α × β, γ)) (a : α) (b : β) : f.curry a b = f (a, b) :=
  rfl

/-- The uncurried form of a continuous map `α → C(β, γ)` is a continuous map `α × β → γ`. -/
theorem continuous_uncurry_of_continuous [LocallyCompactSpace β] (f : C(α, C(β, γ))) :
    Continuous (Function.uncurry fun x y => f x y) :=
  continuous_eval'.comp <| f.Continuous.prod_map continuous_id

/-- The uncurried form of a continuous map `α → C(β, γ)` as a continuous map `α × β → γ` (if `β` is
    locally compact). If `α` is also locally compact, then this is a homeomorphism between the two
    function spaces, see `homeomorph.curry`. -/
@[simps]
def uncurry [LocallyCompactSpace β] (f : C(α, C(β, γ))) : C(α × β, γ) :=
  ⟨_, continuous_uncurry_of_continuous f⟩

/-- The uncurrying process is a continuous map between function spaces. -/
theorem continuous_uncurry [LocallyCompactSpace α] [LocallyCompactSpace β] :
    Continuous (uncurry : C(α, C(β, γ)) → C(α × β, γ)) := by
  apply continuous_of_continuous_uncurry
  rw [← Homeomorph.comp_continuous_iff' (Homeomorph.prodAssoc _ _ _)]
  apply Continuous.comp continuous_eval' (Continuous.prod_map continuous_eval' continuous_id) <;> infer_instance

/-- The family of constant maps: `β → C(α, β)` as a continuous map. -/
def const' : C(β, C(α, β)) :=
  curry ⟨Prod.fst, continuous_fst⟩

@[simp]
theorem coe_const' : (const' : β → C(α, β)) = const α :=
  rfl

theorem continuous_const' : Continuous (const α : β → C(α, β)) :=
  const'.Continuous

end Curry

end CompactOpen

end ContinuousMap

open ContinuousMap

namespace Homeomorph

variable {α : Type _} {β : Type _} {γ : Type _}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- Currying as a homeomorphism between the function spaces `C(α × β, γ)` and `C(α, C(β, γ))`. -/
def curry [LocallyCompactSpace α] [LocallyCompactSpace β] : C(α × β, γ) ≃ₜ C(α, C(β, γ)) :=
  ⟨⟨curry, uncurry, by
      tidy, by
      tidy⟩,
    continuous_curry, continuous_uncurry⟩

/-- If `α` has a single element, then `β` is homeomorphic to `C(α, β)`. -/
def continuousMapOfUnique [Unique α] : β ≃ₜ C(α, β) where
  toFun := const α
  invFun := fun f => f default
  left_inv := fun a => rfl
  right_inv := fun f => by
    ext
    rw [Unique.eq_default a]
    rfl
  continuous_to_fun := continuous_const'
  continuous_inv_fun := continuous_eval'.comp (continuous_id.prod_mk continuous_const)

@[simp]
theorem continuous_map_of_unique_apply [Unique α] (b : β) (a : α) : continuousMapOfUnique b a = b :=
  rfl

@[simp]
theorem continuous_map_of_unique_symm_apply [Unique α] (f : C(α, β)) : continuousMapOfUnique.symm f = f default :=
  rfl

end Homeomorph

section QuotientMap

variable {X₀ X Y Z : Type _} [TopologicalSpace X₀] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [LocallyCompactSpace Y] {f : X₀ → X}

theorem QuotientMap.continuous_lift_prod_left (hf : QuotientMap f) {g : X × Y → Z}
    (hg : Continuous fun p : X₀ × Y => g (f p.1, p.2)) : Continuous g := by
  let Gf : C(X₀, C(Y, Z)) := ContinuousMap.curry ⟨_, hg⟩
  have h : ∀ x : X, Continuous fun y => g (x, y) := by
    intro x
    obtain ⟨x₀, rfl⟩ := hf.surjective x
    exact (Gf x₀).Continuous
  let G : X → C(Y, Z) := fun x => ⟨_, h x⟩
  have : Continuous G := by
    rw [hf.continuous_iff]
    exact Gf.continuous
  convert ContinuousMap.continuous_uncurry_of_continuous ⟨G, this⟩
  ext x
  cases x
  rfl

theorem QuotientMap.continuous_lift_prod_right (hf : QuotientMap f) {g : Y × X → Z}
    (hg : Continuous fun p : Y × X₀ => g (p.1, f p.2)) : Continuous g := by
  have : Continuous fun p : X₀ × Y => g ((Prod.swap p).1, f (Prod.swap p).2) := hg.comp continuous_swap
  have : Continuous fun p : X₀ × Y => (g ∘ Prod.swap) (f p.1, p.2) := this
  convert (hf.continuous_lift_prod_left this).comp continuous_swap
  ext x
  simp

end QuotientMap


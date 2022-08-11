/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathbin.Topology.Order

/-!
# Specific classes of maps between topological spaces

This file introduces the following properties of a map `f : X → Y` between topological spaces:

* `is_open_map f` means the image of an open set under `f` is open.
* `is_closed_map f` means the image of a closed set under `f` is closed.

(Open and closed maps need not be continuous.)

* `inducing f` means the topology on `X` is the one induced via `f` from the topology on `Y`.
  These behave like embeddings except they need not be injective. Instead, points of `X` which
  are identified by `f` are also inseparable in the topology on `X`.
* `embedding f` means `f` is inducing and also injective. Equivalently, `f` identifies `X` with
  a subspace of `Y`.
* `open_embedding f` means `f` is an embedding with open image, so it identifies `X` with an
  open subspace of `Y`. Equivalently, `f` is an embedding and an open map.
* `closed_embedding f` similarly means `f` is an embedding with closed image, so it identifies
  `X` with a closed subspace of `Y`. Equivalently, `f` is an embedding and a closed map.

* `quotient_map f` is the dual condition to `embedding f`: `f` is surjective and the topology
  on `Y` is the one coinduced via `f` from the topology on `X`. Equivalently, `f` identifies
  `Y` with a quotient of `X`. Quotient maps are also sometimes known as identification maps.

## References

* <https://en.wikipedia.org/wiki/Open_and_closed_maps>
* <https://en.wikipedia.org/wiki/Embedding#General_topology>
* <https://en.wikipedia.org/wiki/Quotient_space_(topology)#Quotient_map>

## Tags

open map, closed map, embedding, quotient map, identification map

-/


open Set Filter

open TopologicalSpace Filter

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

section Inducing

/-- A function `f : α → β` between topological spaces is inducing if the topology on `α` is induced
by the topology on `β` through `f`, meaning that a set `s : set α` is open iff it is the preimage
under `f` of some open set `t : set β`. -/
@[mk_iff]
structure Inducing [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : α → β) : Prop where
  induced : tα = tβ.induced f

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

theorem inducing_id : Inducing (@id α) :=
  ⟨induced_id.symm⟩

protected theorem Inducing.comp {g : β → γ} {f : α → β} (hg : Inducing g) (hf : Inducing f) : Inducing (g ∘ f) :=
  ⟨by
    rw [hf.induced, hg.induced, induced_compose]⟩

theorem inducing_of_inducing_compose {f : α → β} {g : β → γ} (hf : Continuous f) (hg : Continuous g)
    (hgf : Inducing (g ∘ f)) : Inducing f :=
  ⟨le_antisymmₓ
      (by
        rwa [← continuous_iff_le_induced])
      (by
        rw [hgf.induced, ← continuous_iff_le_induced]
        apply hg.comp continuous_induced_dom)⟩

theorem inducing_iff_nhds {f : α → β} : Inducing f ↔ ∀ a, 𝓝 a = comap f (𝓝 (f a)) :=
  (inducing_iff _).trans (induced_iff_nhds_eq f)

theorem Inducing.nhds_eq_comap {f : α → β} (hf : Inducing f) : ∀ a : α, 𝓝 a = comap f (𝓝 <| f a) :=
  inducing_iff_nhds.1 hf

theorem Inducing.map_nhds_eq {f : α → β} (hf : Inducing f) (a : α) : (𝓝 a).map f = 𝓝[Range f] f a :=
  hf.induced.symm ▸ map_nhds_induced_eq a

theorem Inducing.map_nhds_of_mem {f : α → β} (hf : Inducing f) (a : α) (h : Range f ∈ 𝓝 (f a)) :
    (𝓝 a).map f = 𝓝 (f a) :=
  hf.induced.symm ▸ map_nhds_induced_of_mem h

theorem Inducing.image_mem_nhds_within {f : α → β} (hf : Inducing f) {a : α} {s : Set α} (hs : s ∈ 𝓝 a) :
    f '' s ∈ 𝓝[Range f] f a :=
  hf.map_nhds_eq a ▸ image_mem_map hs

theorem Inducing.tendsto_nhds_iff {ι : Type _} {f : ι → β} {g : β → γ} {a : Filter ι} {b : β} (hg : Inducing g) :
    Tendsto f a (𝓝 b) ↔ Tendsto (g ∘ f) a (𝓝 (g b)) := by
  rw [hg.nhds_eq_comap, tendsto_comap_iff]

theorem Inducing.continuous_at_iff {f : α → β} {g : β → γ} (hg : Inducing g) {x : α} :
    ContinuousAt f x ↔ ContinuousAt (g ∘ f) x := by
  simp_rw [ContinuousAt, Inducing.tendsto_nhds_iff hg]

theorem Inducing.continuous_iff {f : α → β} {g : β → γ} (hg : Inducing g) : Continuous f ↔ Continuous (g ∘ f) := by
  simp_rw [continuous_iff_continuous_at, hg.continuous_at_iff]

theorem Inducing.continuous_at_iff' {f : α → β} {g : β → γ} (hf : Inducing f) {x : α} (h : Range f ∈ 𝓝 (f x)) :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) := by
  simp_rw [ContinuousAt, Filter.Tendsto, ← hf.map_nhds_of_mem _ h, Filter.map_map]

protected theorem Inducing.continuous {f : α → β} (hf : Inducing f) : Continuous f :=
  hf.continuous_iff.mp continuous_id

protected theorem Inducing.inducing_iff {f : α → β} {g : β → γ} (hg : Inducing g) : Inducing f ↔ Inducing (g ∘ f) := by
  refine' ⟨fun h => hg.comp h, fun hgf => inducing_of_inducing_compose _ hg.continuous hgf⟩
  rw [hg.continuous_iff]
  exact hgf.continuous

theorem Inducing.closure_eq_preimage_closure_image {f : α → β} (hf : Inducing f) (s : Set α) :
    Closure s = f ⁻¹' Closure (f '' s) := by
  ext x
  rw [Set.mem_preimage, ← closure_induced, hf.induced]

theorem Inducing.is_closed_iff {f : α → β} (hf : Inducing f) {s : Set α} : IsClosed s ↔ ∃ t, IsClosed t ∧ f ⁻¹' t = s :=
  by
  rw [hf.induced, is_closed_induced_iff]

theorem Inducing.is_closed_iff' {f : α → β} (hf : Inducing f) {s : Set α} :
    IsClosed s ↔ ∀ x, f x ∈ Closure (f '' s) → x ∈ s := by
  rw [hf.induced, is_closed_induced_iff']

theorem Inducing.is_open_iff {f : α → β} (hf : Inducing f) {s : Set α} : IsOpen s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s := by
  rw [hf.induced, is_open_induced_iff]

theorem Inducing.dense_iff {f : α → β} (hf : Inducing f) {s : Set α} : Dense s ↔ ∀ x, f x ∈ Closure (f '' s) := by
  simp only [← Dense, ← hf.closure_eq_preimage_closure_image, ← mem_preimage]

end Inducing

section Embedding

/-- A function between topological spaces is an embedding if it is injective,
  and for all `s : set α`, `s` is open iff it is the preimage of an open set. -/
@[mk_iff]
structure Embedding [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : α → β) extends Inducing f : Prop where
  inj : Function.Injective f

theorem Function.Injective.embedding_induced [t : TopologicalSpace β] {f : α → β} (hf : Function.Injective f) :
    @Embedding α β (t.induced f) t f :=
  { induced := rfl, inj := hf }

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

theorem Embedding.mk' (f : α → β) (inj : Function.Injective f) (induced : ∀ a, comap f (𝓝 (f a)) = 𝓝 a) : Embedding f :=
  ⟨inducing_iff_nhds.2 fun a => (induced a).symm, inj⟩

theorem embedding_id : Embedding (@id α) :=
  ⟨inducing_id, fun a₁ a₂ h => h⟩

theorem Embedding.comp {g : β → γ} {f : α → β} (hg : Embedding g) (hf : Embedding f) : Embedding (g ∘ f) :=
  { hg.to_inducing.comp hf.to_inducing with inj := fun a₁ a₂ h => hf.inj <| hg.inj h }

theorem embedding_of_embedding_compose {f : α → β} {g : β → γ} (hf : Continuous f) (hg : Continuous g)
    (hgf : Embedding (g ∘ f)) : Embedding f :=
  { induced := (inducing_of_inducing_compose hf hg hgf.to_inducing).induced,
    inj := fun a₁ a₂ h =>
      hgf.inj <| by
        simp [← h, ← (· ∘ ·)] }

protected theorem Function.LeftInverse.embedding {f : α → β} {g : β → α} (h : Function.LeftInverse f g)
    (hf : Continuous f) (hg : Continuous g) : Embedding g :=
  embedding_of_embedding_compose hg hf <| h.comp_eq_id.symm ▸ embedding_id

theorem Embedding.map_nhds_eq {f : α → β} (hf : Embedding f) (a : α) : (𝓝 a).map f = 𝓝[Range f] f a :=
  hf.1.map_nhds_eq a

theorem Embedding.map_nhds_of_mem {f : α → β} (hf : Embedding f) (a : α) (h : Range f ∈ 𝓝 (f a)) :
    (𝓝 a).map f = 𝓝 (f a) :=
  hf.1.map_nhds_of_mem a h

theorem Embedding.tendsto_nhds_iff {ι : Type _} {f : ι → β} {g : β → γ} {a : Filter ι} {b : β} (hg : Embedding g) :
    Tendsto f a (𝓝 b) ↔ Tendsto (g ∘ f) a (𝓝 (g b)) :=
  hg.to_inducing.tendsto_nhds_iff

theorem Embedding.continuous_iff {f : α → β} {g : β → γ} (hg : Embedding g) : Continuous f ↔ Continuous (g ∘ f) :=
  Inducing.continuous_iff hg.1

theorem Embedding.continuous {f : α → β} (hf : Embedding f) : Continuous f :=
  Inducing.continuous hf.1

theorem Embedding.closure_eq_preimage_closure_image {e : α → β} (he : Embedding e) (s : Set α) :
    Closure s = e ⁻¹' Closure (e '' s) :=
  he.1.closure_eq_preimage_closure_image s

end Embedding

/-- A function between topological spaces is a quotient map if it is surjective,
  and for all `s : set β`, `s` is open iff its preimage is an open set. -/
def QuotientMap {α : Type _} {β : Type _} [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : α → β) : Prop :=
  Function.Surjective f ∧ tβ = tα.coinduced f

theorem quotient_map_iff {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {f : α → β} :
    QuotientMap f ↔ Function.Surjective f ∧ ∀ s : Set β, IsOpen s ↔ IsOpen (f ⁻¹' s) :=
  and_congr Iff.rfl topological_space_eq_iff

namespace QuotientMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ] {g : β → γ} {f : α → β}

protected theorem id : QuotientMap (@id α) :=
  ⟨fun a => ⟨a, rfl⟩, coinduced_id.symm⟩

protected theorem comp (hg : QuotientMap g) (hf : QuotientMap f) : QuotientMap (g ∘ f) :=
  ⟨hg.left.comp hf.left, by
    rw [hg.right, hf.right, coinduced_compose]⟩

protected theorem of_quotient_map_compose (hf : Continuous f) (hg : Continuous g) (hgf : QuotientMap (g ∘ f)) :
    QuotientMap g :=
  ⟨hgf.1.of_comp,
    le_antisymmₓ
      (by
        rw [hgf.right, ← continuous_iff_coinduced_le]
        apply continuous_coinduced_rng.comp hf)
      (by
        rwa [← continuous_iff_coinduced_le])⟩

protected theorem continuous_iff (hf : QuotientMap f) : Continuous g ↔ Continuous (g ∘ f) := by
  rw [continuous_iff_coinduced_le, continuous_iff_coinduced_le, hf.right, coinduced_compose]

protected theorem continuous (hf : QuotientMap f) : Continuous f :=
  hf.continuous_iff.mp continuous_id

protected theorem surjective (hf : QuotientMap f) : Function.Surjective f :=
  hf.1

protected theorem is_open_preimage (hf : QuotientMap f) {s : Set β} : IsOpen (f ⁻¹' s) ↔ IsOpen s :=
  ((quotient_map_iff.1 hf).2 s).symm

protected theorem is_closed_preimage (hf : QuotientMap f) {s : Set β} : IsClosed (f ⁻¹' s) ↔ IsClosed s := by
  simp only [is_open_compl_iff, preimage_compl, ← hf.is_open_preimage]

end QuotientMap

/-- A map `f : α → β` is said to be an *open map*, if the image of any open `U : set α`
is open in `β`. -/
def IsOpenMap [TopologicalSpace α] [TopologicalSpace β] (f : α → β) :=
  ∀ U : Set α, IsOpen U → IsOpen (f '' U)

namespace IsOpenMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {f : α → β}

open Function

protected theorem id : IsOpenMap (@id α) := fun s hs => by
  rwa [image_id]

protected theorem comp {g : β → γ} {f : α → β} (hg : IsOpenMap g) (hf : IsOpenMap f) : IsOpenMap (g ∘ f) := by
  intro s hs <;> rw [image_comp] <;> exact hg _ (hf _ hs)

theorem is_open_range (hf : IsOpenMap f) : IsOpen (Range f) := by
  rw [← image_univ]
  exact hf _ is_open_univ

theorem image_mem_nhds (hf : IsOpenMap f) {x : α} {s : Set α} (hx : s ∈ 𝓝 x) : f '' s ∈ 𝓝 (f x) :=
  let ⟨t, hts, ht, hxt⟩ := mem_nhds_iff.1 hx
  mem_of_superset (IsOpen.mem_nhds (hf t ht) (mem_image_of_mem _ hxt)) (image_subset _ hts)

theorem maps_to_interior (hf : IsOpenMap f) {s : Set α} {t : Set β} (h : MapsTo f s t) :
    MapsTo f (Interior s) (Interior t) :=
  maps_to'.2 <| interior_maximal (h.mono interior_subset Subset.rfl).image_subset (hf _ is_open_interior)

theorem image_interior_subset (hf : IsOpenMap f) (s : Set α) : f '' Interior s ⊆ Interior (f '' s) :=
  (hf.maps_to_interior (maps_to_image f s)).image_subset

theorem nhds_le (hf : IsOpenMap f) (a : α) : 𝓝 (f a) ≤ (𝓝 a).map f :=
  le_map fun s => hf.image_mem_nhds

theorem of_nhds_le (hf : ∀ a, 𝓝 (f a) ≤ map f (𝓝 a)) : IsOpenMap f := fun s hs =>
  is_open_iff_mem_nhds.2 fun b ⟨a, has, hab⟩ => hab ▸ hf _ (image_mem_map <| IsOpen.mem_nhds hs has)

theorem of_sections {f : α → β} (h : ∀ x, ∃ g : β → α, ContinuousAt g (f x) ∧ g (f x) = x ∧ RightInverse g f) :
    IsOpenMap f :=
  of_nhds_le fun x =>
    let ⟨g, hgc, hgx, hgf⟩ := h x
    calc
      𝓝 (f x) = map f (map g (𝓝 (f x))) := by
        rw [map_map, hgf.comp_eq_id, map_id]
      _ ≤ map f (𝓝 (g (f x))) := map_mono hgc
      _ = map f (𝓝 x) := by
        rw [hgx]
      

theorem of_inverse {f : α → β} {f' : β → α} (h : Continuous f') (l_inv : LeftInverse f f') (r_inv : RightInverse f f') :
    IsOpenMap f :=
  of_sections fun x => ⟨f', h.ContinuousAt, r_inv _, l_inv⟩

/-- A continuous surjective open map is a quotient map. -/
theorem to_quotient_map {f : α → β} (open_map : IsOpenMap f) (cont : Continuous f) (surj : Surjective f) :
    QuotientMap f :=
  quotient_map_iff.2 ⟨surj, fun s => ⟨fun h => h.Preimage cont, fun h => surj.image_preimage s ▸ open_map _ h⟩⟩

theorem interior_preimage_subset_preimage_interior (hf : IsOpenMap f) {s : Set β} :
    Interior (f ⁻¹' s) ⊆ f ⁻¹' Interior s :=
  hf.maps_to_interior (maps_to_preimage _ _)

theorem preimage_interior_eq_interior_preimage (hf₁ : IsOpenMap f) (hf₂ : Continuous f) (s : Set β) :
    f ⁻¹' Interior s = Interior (f ⁻¹' s) :=
  Subset.antisymm (preimage_interior_subset_interior_preimage hf₂) (interior_preimage_subset_preimage_interior hf₁)

theorem preimage_closure_subset_closure_preimage (hf : IsOpenMap f) {s : Set β} : f ⁻¹' Closure s ⊆ Closure (f ⁻¹' s) :=
  by
  rw [← compl_subset_compl]
  simp only [interior_compl, preimage_compl, ← hf.interior_preimage_subset_preimage_interior]

theorem preimage_closure_eq_closure_preimage (hf : IsOpenMap f) (hfc : Continuous f) (s : Set β) :
    f ⁻¹' Closure s = Closure (f ⁻¹' s) :=
  hf.preimage_closure_subset_closure_preimage.antisymm (hfc.closure_preimage_subset s)

theorem preimage_frontier_subset_frontier_preimage (hf : IsOpenMap f) {s : Set β} :
    f ⁻¹' Frontier s ⊆ Frontier (f ⁻¹' s) := by
  simpa only [← frontier_eq_closure_inter_closure, ← preimage_inter] using
    inter_subset_inter hf.preimage_closure_subset_closure_preimage hf.preimage_closure_subset_closure_preimage

theorem preimage_frontier_eq_frontier_preimage (hf : IsOpenMap f) (hfc : Continuous f) (s : Set β) :
    f ⁻¹' Frontier s = Frontier (f ⁻¹' s) := by
  simp only [← frontier_eq_closure_inter_closure, ← preimage_inter, ← preimage_compl, ←
    hf.preimage_closure_eq_closure_preimage hfc]

end IsOpenMap

theorem is_open_map_iff_nhds_le [TopologicalSpace α] [TopologicalSpace β] {f : α → β} :
    IsOpenMap f ↔ ∀ a : α, 𝓝 (f a) ≤ (𝓝 a).map f :=
  ⟨fun hf => hf.nhds_le, IsOpenMap.of_nhds_le⟩

theorem is_open_map_iff_interior [TopologicalSpace α] [TopologicalSpace β] {f : α → β} :
    IsOpenMap f ↔ ∀ s, f '' Interior s ⊆ Interior (f '' s) :=
  ⟨IsOpenMap.image_interior_subset, fun hs u hu =>
    subset_interior_iff_open.mp <|
      calc
        f '' u = f '' Interior u := by
          rw [hu.interior_eq]
        _ ⊆ Interior (f '' u) := hs u
        ⟩

/-- An inducing map with an open range is an open map. -/
protected theorem Inducing.is_open_map [TopologicalSpace α] [TopologicalSpace β] {f : α → β} (hi : Inducing f)
    (ho : IsOpen (Range f)) : IsOpenMap f :=
  IsOpenMap.of_nhds_le fun x => (hi.map_nhds_of_mem _ <| IsOpen.mem_nhds ho <| mem_range_self _).Ge

section IsClosedMap

variable [TopologicalSpace α] [TopologicalSpace β]

/-- A map `f : α → β` is said to be a *closed map*, if the image of any closed `U : set α`
is closed in `β`. -/
def IsClosedMap (f : α → β) :=
  ∀ U : Set α, IsClosed U → IsClosed (f '' U)

end IsClosedMap

namespace IsClosedMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

open Function

protected theorem id : IsClosedMap (@id α) := fun s hs => by
  rwa [image_id]

protected theorem comp {g : β → γ} {f : α → β} (hg : IsClosedMap g) (hf : IsClosedMap f) : IsClosedMap (g ∘ f) := by
  intro s hs
  rw [image_comp]
  exact hg _ (hf _ hs)

theorem closure_image_subset {f : α → β} (hf : IsClosedMap f) (s : Set α) : Closure (f '' s) ⊆ f '' Closure s :=
  closure_minimal (image_subset _ subset_closure) (hf _ is_closed_closure)

theorem of_inverse {f : α → β} {f' : β → α} (h : Continuous f') (l_inv : LeftInverse f f') (r_inv : RightInverse f f') :
    IsClosedMap f := fun s hs =>
  have : f' ⁻¹' s = f '' s := by
    ext x <;> simp [← mem_image_iff_of_inverse r_inv l_inv]
  this ▸ hs.Preimage h

theorem of_nonempty {f : α → β} (h : ∀ s, IsClosed s → s.Nonempty → IsClosed (f '' s)) : IsClosedMap f := by
  intro s hs
  cases' eq_empty_or_nonempty s with h2s h2s
  · simp_rw [h2s, image_empty, is_closed_empty]
    
  · exact h s hs h2s
    

theorem closed_range {f : α → β} (hf : IsClosedMap f) : IsClosed (Range f) :=
  @image_univ _ _ f ▸ hf _ is_closed_univ

end IsClosedMap

theorem Inducing.is_closed_map [TopologicalSpace α] [TopologicalSpace β] {f : α → β} (hf : Inducing f)
    (h : IsClosed (Range f)) : IsClosedMap f := by
  intro s hs
  rcases hf.is_closed_iff.1 hs with ⟨t, ht, rfl⟩
  rw [image_preimage_eq_inter_range]
  exact ht.inter h

theorem is_closed_map_iff_closure_image [TopologicalSpace α] [TopologicalSpace β] {f : α → β} :
    IsClosedMap f ↔ ∀ s, Closure (f '' s) ⊆ f '' Closure s :=
  ⟨IsClosedMap.closure_image_subset, fun hs c hc =>
    is_closed_of_closure_subset <|
      calc
        Closure (f '' c) ⊆ f '' Closure c := hs c
        _ = f '' c := by
          rw [hc.closure_eq]
        ⟩

section OpenEmbedding

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- An open embedding is an embedding with open image. -/
structure OpenEmbedding (f : α → β) extends Embedding f : Prop where
  open_range : IsOpen <| Range f

theorem OpenEmbedding.is_open_map {f : α → β} (hf : OpenEmbedding f) : IsOpenMap f :=
  hf.toEmbedding.to_inducing.IsOpenMap hf.open_range

theorem OpenEmbedding.map_nhds_eq {f : α → β} (hf : OpenEmbedding f) (a : α) : map f (𝓝 a) = 𝓝 (f a) :=
  hf.toEmbedding.map_nhds_of_mem _ <| hf.open_range.mem_nhds <| mem_range_self _

theorem OpenEmbedding.open_iff_image_open {f : α → β} (hf : OpenEmbedding f) {s : Set α} : IsOpen s ↔ IsOpen (f '' s) :=
  ⟨hf.IsOpenMap s, fun h => by
    convert ← h.preimage hf.to_embedding.continuous
    apply preimage_image_eq _ hf.inj⟩

theorem OpenEmbedding.tendsto_nhds_iff {ι : Type _} {f : ι → β} {g : β → γ} {a : Filter ι} {b : β}
    (hg : OpenEmbedding g) : Tendsto f a (𝓝 b) ↔ Tendsto (g ∘ f) a (𝓝 (g b)) :=
  hg.toEmbedding.tendsto_nhds_iff

theorem OpenEmbedding.continuous {f : α → β} (hf : OpenEmbedding f) : Continuous f :=
  hf.toEmbedding.Continuous

theorem OpenEmbedding.open_iff_preimage_open {f : α → β} (hf : OpenEmbedding f) {s : Set β} (hs : s ⊆ Range f) :
    IsOpen s ↔ IsOpen (f ⁻¹' s) := by
  convert ← hf.open_iff_image_open.symm
  rwa [image_preimage_eq_inter_range, inter_eq_self_of_subset_left]

theorem open_embedding_of_embedding_open {f : α → β} (h₁ : Embedding f) (h₂ : IsOpenMap f) : OpenEmbedding f :=
  ⟨h₁, h₂.is_open_range⟩

theorem open_embedding_iff_embedding_open {f : α → β} : OpenEmbedding f ↔ Embedding f ∧ IsOpenMap f :=
  ⟨fun h => ⟨h.1, h.IsOpenMap⟩, fun h => open_embedding_of_embedding_open h.1 h.2⟩

theorem open_embedding_of_continuous_injective_open {f : α → β} (h₁ : Continuous f) (h₂ : Function.Injective f)
    (h₃ : IsOpenMap f) : OpenEmbedding f := by
  simp only [← open_embedding_iff_embedding_open, ← embedding_iff, ← inducing_iff_nhds, *, ← and_trueₓ]
  exact fun a => le_antisymmₓ (h₁.tendsto _).le_comap (@comap_map _ _ (𝓝 a) _ h₂ ▸ comap_mono (h₃.nhds_le _))

theorem open_embedding_iff_continuous_injective_open {f : α → β} :
    OpenEmbedding f ↔ Continuous f ∧ Function.Injective f ∧ IsOpenMap f :=
  ⟨fun h => ⟨h.Continuous, h.inj, h.IsOpenMap⟩, fun h => open_embedding_of_continuous_injective_open h.1 h.2.1 h.2.2⟩

theorem open_embedding_id : OpenEmbedding (@id α) :=
  ⟨embedding_id, IsOpenMap.id.is_open_range⟩

theorem OpenEmbedding.comp {g : β → γ} {f : α → β} (hg : OpenEmbedding g) (hf : OpenEmbedding f) :
    OpenEmbedding (g ∘ f) :=
  ⟨hg.1.comp hf.1, (hg.IsOpenMap.comp hf.IsOpenMap).is_open_range⟩

theorem OpenEmbedding.is_open_map_iff {g : β → γ} {f : α → β} (hg : OpenEmbedding g) :
    IsOpenMap f ↔ IsOpenMap (g ∘ f) := by
  simp only [← is_open_map_iff_nhds_le, @map_map _ _ _ _ f g, hg.map_nhds_eq, ← map_le_map_iff hg.inj]

theorem OpenEmbedding.of_comp_iff (f : α → β) {g : β → γ} (hg : OpenEmbedding g) :
    OpenEmbedding (g ∘ f) ↔ OpenEmbedding f := by
  simp only [← open_embedding_iff_continuous_injective_open, hg.is_open_map_iff, hg.1.continuous_iff, ←
    hg.inj.of_comp_iff]

theorem OpenEmbedding.of_comp (f : α → β) {g : β → γ} (hg : OpenEmbedding g) (h : OpenEmbedding (g ∘ f)) :
    OpenEmbedding f :=
  (OpenEmbedding.of_comp_iff f hg).1 h

end OpenEmbedding

section ClosedEmbedding

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- A closed embedding is an embedding with closed image. -/
structure ClosedEmbedding (f : α → β) extends Embedding f : Prop where
  closed_range : IsClosed <| Range f

variable {f : α → β}

theorem ClosedEmbedding.tendsto_nhds_iff {ι : Type _} {g : ι → α} {a : Filter ι} {b : α} (hf : ClosedEmbedding f) :
    Tendsto g a (𝓝 b) ↔ Tendsto (f ∘ g) a (𝓝 (f b)) :=
  hf.toEmbedding.tendsto_nhds_iff

theorem ClosedEmbedding.continuous (hf : ClosedEmbedding f) : Continuous f :=
  hf.toEmbedding.Continuous

theorem ClosedEmbedding.is_closed_map (hf : ClosedEmbedding f) : IsClosedMap f :=
  hf.toEmbedding.to_inducing.IsClosedMap hf.closed_range

theorem ClosedEmbedding.closed_iff_image_closed (hf : ClosedEmbedding f) {s : Set α} : IsClosed s ↔ IsClosed (f '' s) :=
  ⟨hf.IsClosedMap s, fun h => by
    convert ← continuous_iff_is_closed.mp hf.continuous _ h
    apply preimage_image_eq _ hf.inj⟩

theorem ClosedEmbedding.closed_iff_preimage_closed (hf : ClosedEmbedding f) {s : Set β} (hs : s ⊆ Range f) :
    IsClosed s ↔ IsClosed (f ⁻¹' s) := by
  convert ← hf.closed_iff_image_closed.symm
  rwa [image_preimage_eq_inter_range, inter_eq_self_of_subset_left]

theorem closed_embedding_of_embedding_closed (h₁ : Embedding f) (h₂ : IsClosedMap f) : ClosedEmbedding f :=
  ⟨h₁, by
    convert h₂ univ is_closed_univ <;> simp ⟩

theorem closed_embedding_of_continuous_injective_closed (h₁ : Continuous f) (h₂ : Function.Injective f)
    (h₃ : IsClosedMap f) : ClosedEmbedding f := by
  refine' closed_embedding_of_embedding_closed ⟨⟨_⟩, h₂⟩ h₃
  apply le_antisymmₓ (continuous_iff_le_induced.mp h₁) _
  intro s'
  change IsOpen _ ≤ IsOpen _
  rw [← is_closed_compl_iff, ← is_closed_compl_iff]
  generalize s'ᶜ = s
  rw [is_closed_induced_iff]
  refine' fun hs => ⟨f '' s, h₃ s hs, _⟩
  rw [preimage_image_eq _ h₂]

theorem closed_embedding_id : ClosedEmbedding (@id α) :=
  ⟨embedding_id, by
    convert is_closed_univ <;> apply range_id⟩

theorem ClosedEmbedding.comp {g : β → γ} {f : α → β} (hg : ClosedEmbedding g) (hf : ClosedEmbedding f) :
    ClosedEmbedding (g ∘ f) :=
  ⟨hg.toEmbedding.comp hf.toEmbedding,
    show IsClosed (Range (g ∘ f)) by
      rw [range_comp, ← hg.closed_iff_image_closed] <;> exact hf.closed_range⟩

theorem ClosedEmbedding.closure_image_eq {f : α → β} (hf : ClosedEmbedding f) (s : Set α) :
    Closure (f '' s) = f '' Closure s :=
  le_antisymmₓ (is_closed_map_iff_closure_image.mp hf.IsClosedMap _) (image_closure_subset_closure_image hf.Continuous)

end ClosedEmbedding


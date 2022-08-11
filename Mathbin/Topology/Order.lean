/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Topology.Tactic

/-!
# Ordering on topologies and (co)induced topologies

Topologies on a fixed type `α` are ordered, by reverse inclusion.
That is, for topologies `t₁` and `t₂` on `α`, we write `t₁ ≤ t₂`
if every set open in `t₂` is also open in `t₁`.
(One also calls `t₁` finer than `t₂`, and `t₂` coarser than `t₁`.)

Any function `f : α → β` induces
       `induced f : topological_space β → topological_space α`
and  `coinduced f : topological_space α → topological_space β`.
Continuity, the ordering on topologies and (co)induced topologies are
related as follows:
* The identity map (α, t₁) → (α, t₂) is continuous iff t₁ ≤ t₂.
* A map f : (α, t) → (β, u) is continuous
    iff             t ≤ induced f u   (`continuous_iff_le_induced`)
    iff coinduced f t ≤ u             (`continuous_iff_coinduced_le`).

Topologies on α form a complete lattice, with ⊥ the discrete topology
and ⊤ the indiscrete topology.

For a function f : α → β, (coinduced f, induced f) is a Galois connection
between topologies on α and topologies on β.

## Implementation notes

There is a Galois insertion between topologies on α (with the inclusion ordering)
and all collections of sets in α. The complete lattice structure on topologies
on α is defined as the reverse of the one obtained via this Galois insertion.

## Tags

finer, coarser, induced topology, coinduced topology

-/


open Set Filter Classical

open Classical TopologicalSpace Filter

universe u v w

namespace TopologicalSpace

variable {α : Type u}

/-- The open sets of the least topology containing a collection of basic sets. -/
inductive GenerateOpen (g : Set (Set α)) : Set α → Prop
  | basic : ∀, ∀ s ∈ g, ∀, generate_open s
  | univ : generate_open Univ
  | inter : ∀ s t, generate_open s → generate_open t → generate_open (s ∩ t)
  | sUnion : ∀ k, (∀, ∀ s ∈ k, ∀, generate_open s) → generate_open (⋃₀k)

/-- The smallest topological space containing the collection `g` of basic sets -/
def generateFrom (g : Set (Set α)) : TopologicalSpace α where
  IsOpen := GenerateOpen g
  is_open_univ := GenerateOpen.univ
  is_open_inter := GenerateOpen.inter
  is_open_sUnion := GenerateOpen.sUnion

theorem is_open_generate_from_of_mem {g : Set (Set α)} {s : Set α} (hs : s ∈ g) : @IsOpen _ (generateFrom g) s :=
  GenerateOpen.basic s hs

theorem nhds_generate_from {g : Set (Set α)} {a : α} : @nhds α (generateFrom g) a = ⨅ s ∈ { s | a ∈ s ∧ s ∈ g }, 𝓟 s :=
  by
  rw [nhds_def] <;>
    exact
      le_antisymmₓ (binfi_mono fun s ⟨as, sg⟩ => ⟨as, generate_open.basic _ sg⟩)
        (le_infi fun s =>
          le_infi fun ⟨as, hs⟩ => by
            revert as
            clear_
            induction hs
            case generate_open.basic s hs =>
              exact fun as => infi_le_of_le s <| infi_le _ ⟨as, hs⟩
            case generate_open.univ =>
              rw [principal_univ]
              exact fun _ => le_top
            case generate_open.inter s t hs' ht' hs ht =>
              exact fun ⟨has, hat⟩ =>
                calc
                  _ ≤ 𝓟 s⊓𝓟 t := le_inf (hs has) (ht hat)
                  _ = _ := inf_principal
                  
            case generate_open.sUnion k hk' hk =>
              exact fun ⟨t, htk, hat⟩ =>
                calc
                  _ ≤ 𝓟 t := hk t htk hat
                  _ ≤ _ := le_principal_iff.2 <| subset_sUnion_of_mem htk
                  )

theorem tendsto_nhds_generate_from {β : Type _} {m : α → β} {f : Filter α} {g : Set (Set β)} {b : β}
    (h : ∀, ∀ s ∈ g, ∀, b ∈ s → m ⁻¹' s ∈ f) : Tendsto m f (@nhds β (generateFrom g) b) := by
  rw [nhds_generate_from] <;>
    exact tendsto_infi.2 fun s => tendsto_infi.2 fun ⟨hbs, hsg⟩ => tendsto_principal.2 <| h s hsg hbs

/-- Construct a topology on α given the filter of neighborhoods of each point of α. -/
protected def mkOfNhds (n : α → Filter α) : TopologicalSpace α where
  IsOpen := fun s => ∀, ∀ a ∈ s, ∀, s ∈ n a
  is_open_univ := fun x h => univ_mem
  is_open_inter := fun s t hs ht x ⟨hxs, hxt⟩ => inter_mem (hs x hxs) (ht x hxt)
  is_open_sUnion := fun s hs a ⟨x, hx, hxa⟩ => mem_of_superset (hs x hx _ hxa) (Set.subset_sUnion_of_mem hx)

theorem nhds_mk_of_nhds (n : α → Filter α) (a : α) (h₀ : pure ≤ n)
    (h₁ : ∀ {a s}, s ∈ n a → ∃ t ∈ n a, t ⊆ s ∧ ∀, ∀ a' ∈ t, ∀, s ∈ n a') :
    @nhds α (TopologicalSpace.mkOfNhds n) a = n a := by
  let this := TopologicalSpace.mkOfNhds n
  refine' le_antisymmₓ (fun s hs => _) fun s hs => _
  · have h₀ : { b | s ∈ n b } ⊆ s := fun b hb => mem_pure.1 <| h₀ b hb
    have h₁ : { b | s ∈ n b } ∈ 𝓝 a := by
      refine' IsOpen.mem_nhds (fun b (hb : s ∈ n b) => _) hs
      rcases h₁ hb with ⟨t, ht, hts, h⟩
      exact mem_of_superset ht h
    exact mem_of_superset h₁ h₀
    
  · rcases(@mem_nhds_iff α (TopologicalSpace.mkOfNhds n) _ _).1 hs with ⟨t, hts, ht, hat⟩
    exact (n a).sets_of_superset (ht _ hat) hts
    

theorem nhds_mk_of_nhds_filter_basis (B : α → FilterBasis α) (a : α) (h₀ : ∀ (x), ∀ n ∈ B x, ∀, x ∈ n)
    (h₁ : ∀ (x), ∀ n ∈ B x, ∀, ∃ n₁ ∈ B x, n₁ ⊆ n ∧ ∀, ∀ x' ∈ n₁, ∀, ∃ n₂ ∈ B x', n₂ ⊆ n) :
    @nhds α (TopologicalSpace.mkOfNhds fun x => (B x).filter) a = (B a).filter := by
  rw [TopologicalSpace.nhds_mk_of_nhds] <;> intro x n hn <;> obtain ⟨m, hm₁, hm₂⟩ := (B x).mem_filter_iff.mp hn
  · exact hm₂ (h₀ _ _ hm₁)
    
  · obtain ⟨n₁, hn₁, hn₂, hn₃⟩ := h₁ x m hm₁
    refine' ⟨n₁, (B x).mem_filter_of_mem hn₁, hn₂.trans hm₂, fun x' hx' => (B x').mem_filter_iff.mp _⟩
    obtain ⟨n₂, hn₄, hn₅⟩ := hn₃ x' hx'
    exact ⟨n₂, hn₄, hn₅.trans hm₂⟩
    

end TopologicalSpace

section Lattice

variable {α : Type u} {β : Type v}

/-- The inclusion ordering on topologies on α. We use it to get a complete
   lattice instance via the Galois insertion method, but the partial order
   that we will eventually impose on `topological_space α` is the reverse one. -/
def tmpOrder : PartialOrderₓ (TopologicalSpace α) where
  le := fun t s => t.IsOpen ≤ s.IsOpen
  le_antisymm := fun t s h₁ h₂ => topological_space_eq <| le_antisymmₓ h₁ h₂
  le_refl := fun t => le_reflₓ t.IsOpen
  le_trans := fun a b c h₁ h₂ => @le_transₓ _ _ a.IsOpen b.IsOpen c.IsOpen h₁ h₂

attribute [local instance] tmpOrder

-- We'll later restate this lemma in terms of the correct order on `topological_space α`.
private theorem generate_from_le_iff_subset_is_open {g : Set (Set α)} {t : TopologicalSpace α} :
    TopologicalSpace.generateFrom g ≤ t ↔ g ⊆ { s | t.IsOpen s } :=
  Iff.intro (fun ht s hs => ht _ <| TopologicalSpace.GenerateOpen.basic s hs) fun hg s hs =>
    hs.recOn (fun v hv => hg hv) t.is_open_univ (fun u v _ _ => t.is_open_inter u v) fun k _ => t.is_open_sUnion k

/-- If `s` equals the collection of open sets in the topology it generates,
  then `s` defines a topology. -/
protected def mkOfClosure (s : Set (Set α)) (hs : { u | (TopologicalSpace.generateFrom s).IsOpen u } = s) :
    TopologicalSpace α where
  IsOpen := fun u => u ∈ s
  is_open_univ := hs ▸ TopologicalSpace.GenerateOpen.univ
  is_open_inter := hs ▸ TopologicalSpace.GenerateOpen.inter
  is_open_sUnion := hs ▸ TopologicalSpace.GenerateOpen.sUnion

theorem mk_of_closure_sets {s : Set (Set α)} {hs : { u | (TopologicalSpace.generateFrom s).IsOpen u } = s} :
    mkOfClosure s hs = TopologicalSpace.generateFrom s :=
  topological_space_eq hs.symm

/-- The Galois insertion between `set (set α)` and `topological_space α` whose lower part
  sends a collection of subsets of α to the topology they generate, and whose upper part
  sends a topology to its collection of open subsets. -/
def giGenerateFrom (α : Type _) :
    GaloisInsertion TopologicalSpace.generateFrom fun t : TopologicalSpace α => { s | t.IsOpen s } where
  gc := fun g t => generate_from_le_iff_subset_is_open
  le_l_u := fun ts s hs => TopologicalSpace.GenerateOpen.basic s hs
  choice := fun g hg => mkOfClosure g (Subset.antisymm hg <| generate_from_le_iff_subset_is_open.1 <| le_rfl)
  choice_eq := fun s hs => mk_of_closure_sets

theorem generate_from_mono {α} {g₁ g₂ : Set (Set α)} (h : g₁ ⊆ g₂) :
    TopologicalSpace.generateFrom g₁ ≤ TopologicalSpace.generateFrom g₂ :=
  (giGenerateFrom _).gc.monotone_l h

theorem generate_from_set_of_is_open (t : TopologicalSpace α) : TopologicalSpace.generateFrom { s | t.IsOpen s } = t :=
  (giGenerateFrom α).l_u_eq t

theorem left_inverse_generate_from :
    Function.LeftInverse TopologicalSpace.generateFrom fun t : TopologicalSpace α => { s | t.IsOpen s } :=
  (giGenerateFrom α).left_inverse_l_u

theorem generate_from_surjective :
    Function.Surjective (TopologicalSpace.generateFrom : Set (Set α) → TopologicalSpace α) :=
  (giGenerateFrom α).l_surjective

theorem set_of_is_open_injective : Function.Injective fun t : TopologicalSpace α => { s | t.IsOpen s } :=
  (giGenerateFrom α).u_injective

/-- The "temporary" order `tmp_order` on `topological_space α`, i.e. the inclusion order, is a
complete lattice.  (Note that later `topological_space α` will equipped with the dual order to
`tmp_order`). -/
def tmpCompleteLattice {α : Type u} : CompleteLattice (TopologicalSpace α) :=
  (giGenerateFrom α).liftCompleteLattice

instance : LE (TopologicalSpace α) where le := fun t s => s.IsOpen ≤ t.IsOpen

protected theorem TopologicalSpace.le_def {α} {t s : TopologicalSpace α} : t ≤ s ↔ s.IsOpen ≤ t.IsOpen :=
  Iff.rfl

/-- The ordering on topologies on the type `α`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`). -/
instance : PartialOrderₓ (TopologicalSpace α) :=
  { TopologicalSpace.hasLe with le_antisymm := fun t s h₁ h₂ => topological_space_eq <| le_antisymmₓ h₂ h₁,
    le_refl := fun t => le_reflₓ t.IsOpen,
    le_trans := fun a b c h₁ h₂ => TopologicalSpace.le_def.mpr (le_transₓ h₂ h₁) }

theorem le_generate_from_iff_subset_is_open {g : Set (Set α)} {t : TopologicalSpace α} :
    t ≤ TopologicalSpace.generateFrom g ↔ g ⊆ { s | t.IsOpen s } :=
  generate_from_le_iff_subset_is_open

/-- Topologies on `α` form a complete lattice, with `⊥` the discrete topology
  and `⊤` the indiscrete topology. The infimum of a collection of topologies
  is the topology generated by all their open sets, while the supremum is the
  topology whose open sets are those sets open in every member of the collection. -/
instance : CompleteLattice (TopologicalSpace α) :=
  @OrderDual.completeLattice _ tmpCompleteLattice

theorem is_open_implies_is_open_iff {a b : TopologicalSpace α} : (∀ s, a.IsOpen s → b.IsOpen s) ↔ b ≤ a :=
  Iff.rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`eq_bot] []
/-- A topological space is discrete if every set is open, that is,
  its topology equals the discrete topology `⊥`. -/
class DiscreteTopology (α : Type _) [t : TopologicalSpace α] : Prop where
  eq_bot : t = ⊥

instance (priority := 100) discrete_topology_bot (α : Type _) : @DiscreteTopology α ⊥ where eq_bot := rfl

@[simp]
theorem is_open_discrete [TopologicalSpace α] [DiscreteTopology α] (s : Set α) : IsOpen s :=
  (DiscreteTopology.eq_bot α).symm ▸ trivialₓ

@[simp]
theorem is_closed_discrete [TopologicalSpace α] [DiscreteTopology α] (s : Set α) : IsClosed s :=
  is_open_compl_iff.1 <| (DiscreteTopology.eq_bot α).symm ▸ trivialₓ

@[nontriviality]
theorem continuous_of_discrete_topology [TopologicalSpace α] [DiscreteTopology α] [TopologicalSpace β] {f : α → β} :
    Continuous f :=
  continuous_def.2 fun s hs => is_open_discrete _

theorem nhds_bot (α : Type _) : @nhds α ⊥ = pure := by
  refine' le_antisymmₓ _ (@pure_le_nhds α ⊥)
  intro a s hs
  exact @IsOpen.mem_nhds α ⊥ a s trivialₓ hs

theorem nhds_discrete (α : Type _) [TopologicalSpace α] [DiscreteTopology α] : @nhds α _ = pure :=
  (DiscreteTopology.eq_bot α).symm ▸ nhds_bot α

theorem mem_nhds_discrete [TopologicalSpace α] [DiscreteTopology α] {x : α} {s : Set α} : s ∈ 𝓝 x ↔ x ∈ s := by
  rw [nhds_discrete, mem_pure]

theorem le_of_nhds_le_nhds {t₁ t₂ : TopologicalSpace α} (h : ∀ x, @nhds α t₁ x ≤ @nhds α t₂ x) : t₁ ≤ t₂ := fun s =>
  show @IsOpen α t₂ s → @IsOpen α t₁ s by
    simp only [← is_open_iff_nhds, ← le_principal_iff]
    exact fun hs a ha => h _ <| hs _ ha

theorem eq_of_nhds_eq_nhds {t₁ t₂ : TopologicalSpace α} (h : ∀ x, @nhds α t₁ x = @nhds α t₂ x) : t₁ = t₂ :=
  le_antisymmₓ (le_of_nhds_le_nhds fun x => le_of_eqₓ <| h x) (le_of_nhds_le_nhds fun x => le_of_eqₓ <| (h x).symm)

theorem eq_bot_of_singletons_open {t : TopologicalSpace α} (h : ∀ x, t.IsOpen {x}) : t = ⊥ :=
  bot_unique fun s hs => bUnion_of_singleton s ▸ is_open_bUnion fun x _ => h x

theorem forall_open_iff_discrete {X : Type _} [TopologicalSpace X] : (∀ s : Set X, IsOpen s) ↔ DiscreteTopology X :=
  ⟨fun h =>
    ⟨by
      ext U
      show IsOpen U ↔ True
      simp [← h U]⟩,
    fun a => @is_open_discrete _ _ a⟩

theorem singletons_open_iff_discrete {X : Type _} [TopologicalSpace X] :
    (∀ a : X, IsOpen ({a} : Set X)) ↔ DiscreteTopology X :=
  ⟨fun h => ⟨eq_bot_of_singletons_open h⟩, fun a _ => @is_open_discrete _ _ a _⟩

end Lattice

section GaloisConnection

variable {α : Type _} {β : Type _} {γ : Type _}

/-- Given `f : α → β` and a topology on `β`, the induced topology on `α` is the collection of
  sets that are preimages of some open set in `β`. This is the coarsest topology that
  makes `f` continuous. -/
def TopologicalSpace.induced {α : Type u} {β : Type v} (f : α → β) (t : TopologicalSpace β) : TopologicalSpace α where
  IsOpen := fun s => ∃ s', t.IsOpen s' ∧ f ⁻¹' s' = s
  is_open_univ := ⟨Univ, t.is_open_univ, preimage_univ⟩
  is_open_inter := by
    rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩ <;> exact ⟨s'₁ ∩ s'₂, t.is_open_inter _ _ hs₁ hs₂, preimage_inter⟩
  is_open_sUnion := fun s h => by
    simp only [← Classical.skolem] at h
    cases' h with f hf
    apply Exists.introₓ (⋃ (x : Set α) (h : x ∈ s), f x h)
    simp only [← sUnion_eq_bUnion, ← preimage_Union, ← fun x h => (hf x h).right]
    refine' ⟨_, rfl⟩
    exact
      (@is_open_Union β _ t _) fun i => show IsOpen (⋃ h, f i h) from (@is_open_Union β _ t _) fun h => (hf i h).left

theorem is_open_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α → β} :
    @IsOpen α (t.induced f) s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s :=
  Iff.rfl

theorem is_open_induced_iff' [t : TopologicalSpace β] {s : Set α} {f : α → β} :
    (t.induced f).IsOpen s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s :=
  Iff.rfl

theorem is_closed_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α → β} :
    @IsClosed α (t.induced f) s ↔ ∃ t, IsClosed t ∧ f ⁻¹' t = s := by
  simp only [is_open_compl_iff, ← is_open_induced_iff]
  exact
    compl_surjective.exists.trans
      (by
        simp only [← preimage_compl, ← compl_inj_iff])

/-- Given `f : α → β` and a topology on `α`, the coinduced topology on `β` is defined
  such that `s:set β` is open if the preimage of `s` is open. This is the finest topology that
  makes `f` continuous. -/
def TopologicalSpace.coinduced {α : Type u} {β : Type v} (f : α → β) (t : TopologicalSpace α) : TopologicalSpace β where
  IsOpen := fun s => t.IsOpen (f ⁻¹' s)
  is_open_univ := by
    rw [preimage_univ] <;> exact t.is_open_univ
  is_open_inter := fun s₁ s₂ h₁ h₂ => by
    rw [preimage_inter] <;> exact t.is_open_inter _ _ h₁ h₂
  is_open_sUnion := fun s h => by
    rw [preimage_sUnion] <;>
      exact
        (@is_open_Union _ _ t _) fun i =>
          show IsOpen (⋃ H : i ∈ s, f ⁻¹' i) from (@is_open_Union _ _ t _) fun hi => h i hi

theorem is_open_coinduced {t : TopologicalSpace α} {s : Set β} {f : α → β} :
    @IsOpen β (TopologicalSpace.coinduced f t) s ↔ IsOpen (f ⁻¹' s) :=
  Iff.rfl

theorem preimage_nhds_coinduced [TopologicalSpace α] {π : α → β} {s : Set β} {a : α}
    (hs : s ∈ @nhds β (TopologicalSpace.coinduced π ‹_›) (π a)) : π ⁻¹' s ∈ 𝓝 a := by
  let this := TopologicalSpace.coinduced π ‹_›
  rcases mem_nhds_iff.mp hs with ⟨V, hVs, V_op, mem_V⟩
  exact mem_nhds_iff.mpr ⟨π ⁻¹' V, Set.preimage_mono hVs, V_op, mem_V⟩

variable {t t₁ t₂ : TopologicalSpace α} {t' : TopologicalSpace β} {f : α → β} {g : β → α}

theorem Continuous.coinduced_le (h : @Continuous α β t t' f) : t.coinduced f ≤ t' := fun s hs =>
  (continuous_def.1 h s hs : _)

theorem coinduced_le_iff_le_induced {f : α → β} {tα : TopologicalSpace α} {tβ : TopologicalSpace β} :
    tα.coinduced f ≤ tβ ↔ tα ≤ tβ.induced f :=
  Iff.intro (fun h s ⟨t, ht, hst⟩ => hst ▸ h _ ht) fun h s hs => show tα.IsOpen (f ⁻¹' s) from h _ ⟨s, hs, rfl⟩

theorem Continuous.le_induced (h : @Continuous α β t t' f) : t ≤ t'.induced f :=
  coinduced_le_iff_le_induced.1 h.coinduced_le

theorem gc_coinduced_induced (f : α → β) :
    GaloisConnection (TopologicalSpace.coinduced f) (TopologicalSpace.induced f) := fun f g =>
  coinduced_le_iff_le_induced

theorem induced_mono (h : t₁ ≤ t₂) : t₁.induced g ≤ t₂.induced g :=
  (gc_coinduced_induced g).monotone_u h

theorem coinduced_mono (h : t₁ ≤ t₂) : t₁.coinduced f ≤ t₂.coinduced f :=
  (gc_coinduced_induced f).monotone_l h

@[simp]
theorem induced_top : (⊤ : TopologicalSpace α).induced g = ⊤ :=
  (gc_coinduced_induced g).u_top

@[simp]
theorem induced_inf : (t₁⊓t₂).induced g = t₁.induced g⊓t₂.induced g :=
  (gc_coinduced_induced g).u_inf

@[simp]
theorem induced_infi {ι : Sort w} {t : ι → TopologicalSpace α} : (⨅ i, t i).induced g = ⨅ i, (t i).induced g :=
  (gc_coinduced_induced g).u_infi

@[simp]
theorem coinduced_bot : (⊥ : TopologicalSpace α).coinduced f = ⊥ :=
  (gc_coinduced_induced f).l_bot

@[simp]
theorem coinduced_sup : (t₁⊔t₂).coinduced f = t₁.coinduced f⊔t₂.coinduced f :=
  (gc_coinduced_induced f).l_sup

@[simp]
theorem coinduced_supr {ι : Sort w} {t : ι → TopologicalSpace α} : (⨆ i, t i).coinduced f = ⨆ i, (t i).coinduced f :=
  (gc_coinduced_induced f).l_supr

theorem induced_id [t : TopologicalSpace α] : t.induced id = t :=
  topological_space_eq <| funext fun s => propext <| ⟨fun ⟨s', hs, h⟩ => h ▸ hs, fun hs => ⟨s, hs, rfl⟩⟩

theorem induced_compose [tγ : TopologicalSpace γ] {f : α → β} {g : β → γ} :
    (tγ.induced g).induced f = tγ.induced (g ∘ f) :=
  topological_space_eq <|
    funext fun s =>
      propext <|
        ⟨fun ⟨s', ⟨s, hs, h₂⟩, h₁⟩ => h₁ ▸ h₂ ▸ ⟨s, hs, rfl⟩, fun ⟨s, hs, h⟩ => ⟨Preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩

theorem induced_const [t : TopologicalSpace α] {x : α} : (t.induced fun y : β => x) = ⊤ :=
  le_antisymmₓ le_top (@continuous_const β α ⊤ t x).le_induced

theorem coinduced_id [t : TopologicalSpace α] : t.coinduced id = t :=
  topological_space_eq rfl

theorem coinduced_compose [tα : TopologicalSpace α] {f : α → β} {g : β → γ} :
    (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f) :=
  topological_space_eq rfl

theorem Equivₓ.induced_symm {α β : Type _} (e : α ≃ β) :
    TopologicalSpace.induced e.symm = TopologicalSpace.coinduced e := by
  ext t U
  constructor
  · rintro ⟨V, hV, rfl⟩
    change t.is_open (e ⁻¹' _)
    rwa [← preimage_comp, ← Equivₓ.coe_trans, Equivₓ.self_trans_symm]
    
  · intro hU
    refine' ⟨e ⁻¹' U, hU, _⟩
    rw [← preimage_comp, ← Equivₓ.coe_trans, Equivₓ.symm_trans_self, Equivₓ.coe_refl, preimage_id]
    

theorem Equivₓ.coinduced_symm {α β : Type _} (e : α ≃ β) :
    TopologicalSpace.coinduced e.symm = TopologicalSpace.induced e := by
  rw [← e.symm.induced_symm, e.symm_symm]

end GaloisConnection

-- constructions using the complete lattice structure
section Constructions

open TopologicalSpace

variable {α : Type u} {β : Type v}

instance inhabitedTopologicalSpace {α : Type u} : Inhabited (TopologicalSpace α) :=
  ⟨⊤⟩

instance (priority := 100) Subsingleton.uniqueTopologicalSpace [Subsingleton α] : Unique (TopologicalSpace α) where
  default := ⊥
  uniq := fun t =>
    eq_bot_of_singletons_open fun x => Subsingleton.set_cases (@is_open_empty _ t) (@is_open_univ _ t) ({x} : Set α)

instance (priority := 100) Subsingleton.discrete_topology [t : TopologicalSpace α] [Subsingleton α] :
    DiscreteTopology α :=
  ⟨Unique.eq_default t⟩

instance : TopologicalSpace Empty :=
  ⊥

instance : DiscreteTopology Empty :=
  ⟨rfl⟩

instance : TopologicalSpace Pempty :=
  ⊥

instance : DiscreteTopology Pempty :=
  ⟨rfl⟩

instance : TopologicalSpace PUnit :=
  ⊥

instance : DiscreteTopology PUnit :=
  ⟨rfl⟩

instance : TopologicalSpace Bool :=
  ⊥

instance : DiscreteTopology Bool :=
  ⟨rfl⟩

instance : TopologicalSpace ℕ :=
  ⊥

instance : DiscreteTopology ℕ :=
  ⟨rfl⟩

instance : TopologicalSpace ℤ :=
  ⊥

instance : DiscreteTopology ℤ :=
  ⟨rfl⟩

instance sierpinskiSpace : TopologicalSpace Prop :=
  generateFrom {{True}}

theorem continuous_empty_function [TopologicalSpace α] [TopologicalSpace β] [IsEmpty β] (f : α → β) : Continuous f := by
  let this := Function.is_empty f
  exact continuous_of_discrete_topology

theorem le_generate_from {t : TopologicalSpace α} {g : Set (Set α)} (h : ∀, ∀ s ∈ g, ∀, IsOpen s) :
    t ≤ generateFrom g :=
  le_generate_from_iff_subset_is_open.2 h

theorem induced_generate_from_eq {α β} {b : Set (Set β)} {f : α → β} :
    (generateFrom b).induced f = TopologicalSpace.generateFrom (Preimage f '' b) :=
  le_antisymmₓ (le_generate_from <| ball_image_iff.2 fun s hs => ⟨s, GenerateOpen.basic _ hs, rfl⟩)
    (coinduced_le_iff_le_induced.1 <| le_generate_from fun s hs => GenerateOpen.basic _ <| mem_image_of_mem _ hs)

theorem le_induced_generate_from {α β} [t : TopologicalSpace α] {b : Set (Set β)} {f : α → β}
    (h : ∀ a : Set β, a ∈ b → IsOpen (f ⁻¹' a)) : t ≤ induced f (generateFrom b) := by
  rw [induced_generate_from_eq]
  apply le_generate_from
  simp only [← mem_image, ← and_imp, ← forall_apply_eq_imp_iff₂, ← exists_imp_distrib]
  exact h

/-- This construction is left adjoint to the operation sending a topology on `α`
  to its neighborhood filter at a fixed point `a : α`. -/
def nhdsAdjoint (a : α) (f : Filter α) : TopologicalSpace α where
  IsOpen := fun s => a ∈ s → s ∈ f
  is_open_univ := fun s => univ_mem
  is_open_inter := fun s t hs ht ⟨has, hat⟩ => inter_mem (hs has) (ht hat)
  is_open_sUnion := fun k hk ⟨u, hu, hau⟩ => mem_of_superset (hk u hu hau) (subset_sUnion_of_mem hu)

theorem gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nhds α t a := fun f t => by
  rw [le_nhds_iff]
  exact ⟨fun H s hs has => H _ has hs, fun H s has hs => H _ hs has⟩

theorem nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ ≤ t₂) : @nhds α t₁ a ≤ @nhds α t₂ a :=
  (gc_nhds a).monotone_u h

theorem le_iff_nhds {α : Type _} (t t' : TopologicalSpace α) : t ≤ t' ↔ ∀ x, @nhds α t x ≤ @nhds α t' x :=
  ⟨fun h x => nhds_mono h, le_of_nhds_le_nhds⟩

theorem nhds_adjoint_nhds {α : Type _} (a : α) (f : Filter α) : @nhds α (nhdsAdjoint a f) a = pure a⊔f := by
  ext U
  rw [mem_nhds_iff]
  constructor
  · rintro ⟨t, htU, ht, hat⟩
    exact ⟨htU hat, mem_of_superset (ht hat) htU⟩
    
  · rintro ⟨haU, hU⟩
    exact ⟨U, subset.rfl, fun h => hU, haU⟩
    

theorem nhds_adjoint_nhds_of_ne {α : Type _} (a : α) (f : Filter α) {b : α} (h : b ≠ a) :
    @nhds α (nhdsAdjoint a f) b = pure b := by
  apply le_antisymmₓ
  · intro U hU
    rw [mem_nhds_iff]
    use {b}
    simp only [← and_trueₓ, ← singleton_subset_iff, ← mem_singleton]
    refine' ⟨hU, fun ha => (h.symm ha).elim⟩
    
  · exact @pure_le_nhds α (nhdsAdjoint a f) b
    

theorem is_open_singleton_nhds_adjoint {α : Type _} {a b : α} (f : Filter α) (hb : b ≠ a) :
    @IsOpen α (nhdsAdjoint a f) {b} := by
  rw [is_open_singleton_iff_nhds_eq_pure]
  exact nhds_adjoint_nhds_of_ne a f hb

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b «expr ≠ » a)
theorem le_nhds_adjoint_iff' {α : Type _} (a : α) (f : Filter α) (t : TopologicalSpace α) :
    t ≤ nhdsAdjoint a f ↔ @nhds α t a ≤ pure a⊔f ∧ ∀ (b) (_ : b ≠ a), @nhds α t b = pure b := by
  rw [le_iff_nhds]
  constructor
  · intro h
    constructor
    · specialize h a
      rwa [nhds_adjoint_nhds] at h
      
    · intro b hb
      apply le_antisymmₓ _ (pure_le_nhds b)
      specialize h b
      rwa [nhds_adjoint_nhds_of_ne a f hb] at h
      
    
  · rintro ⟨h, h'⟩ b
    by_cases' hb : b = a
    · rwa [hb, nhds_adjoint_nhds]
      
    · simp [← nhds_adjoint_nhds_of_ne a f hb, ← h' b hb]
      
    

theorem le_nhds_adjoint_iff {α : Type _} (a : α) (f : Filter α) (t : TopologicalSpace α) :
    t ≤ nhdsAdjoint a f ↔ @nhds α t a ≤ pure a⊔f ∧ ∀ b, b ≠ a → t.IsOpen {b} := by
  change _ ↔ _ ∧ ∀ b : α, b ≠ a → IsOpen {b}
  rw [le_nhds_adjoint_iff', And.congr_right_iff]
  apply fun h => forall_congrₓ fun b => _
  rw [@is_open_singleton_iff_nhds_eq_pure α t b]

theorem nhds_infi {ι : Sort _} {t : ι → TopologicalSpace α} {a : α} : @nhds α (infi t) a = ⨅ i, @nhds α (t i) a :=
  (gc_nhds a).u_infi

theorem nhds_Inf {s : Set (TopologicalSpace α)} {a : α} : @nhds α (inf s) a = ⨅ t ∈ s, @nhds α t a :=
  (gc_nhds a).u_Inf

theorem nhds_inf {t₁ t₂ : TopologicalSpace α} {a : α} : @nhds α (t₁⊓t₂) a = @nhds α t₁ a⊓@nhds α t₂ a :=
  (gc_nhds a).u_inf

theorem nhds_top {a : α} : @nhds α ⊤ a = ⊤ :=
  (gc_nhds a).u_top

-- mathport name: «exprcont»
local notation "cont" => @Continuous _ _

-- mathport name: «exprtspace»
local notation "tspace" => TopologicalSpace

open TopologicalSpace

variable {γ : Type _} {f : α → β} {ι : Sort _}

theorem continuous_iff_coinduced_le {t₁ : tspace α} {t₂ : tspace β} : cont t₁ t₂ f ↔ coinduced f t₁ ≤ t₂ :=
  continuous_def.trans Iff.rfl

theorem continuous_iff_le_induced {t₁ : tspace α} {t₂ : tspace β} : cont t₁ t₂ f ↔ t₁ ≤ induced f t₂ :=
  Iff.trans continuous_iff_coinduced_le (gc_coinduced_induced f _ _)

theorem continuous_generated_from {t : tspace α} {b : Set (Set β)} (h : ∀, ∀ s ∈ b, ∀, IsOpen (f ⁻¹' s)) :
    cont t (generateFrom b) f :=
  continuous_iff_coinduced_le.2 <| le_generate_from h

@[continuity]
theorem continuous_induced_dom {t : tspace β} : cont (induced f t) t f := by
  rw [continuous_def]
  intro s h
  exact ⟨_, h, rfl⟩

theorem continuous_induced_rng {g : γ → α} {t₂ : tspace β} {t₁ : tspace γ} (h : cont t₁ t₂ (f ∘ g)) :
    cont t₁ (induced f t₂) g := by
  rw [continuous_def]
  rintro s ⟨t, ht, s_eq⟩
  simpa [s_eq] using continuous_def.1 h t ht

theorem continuous_induced_rng' [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {g : γ → α} (f : α → β)
    (H : ‹TopologicalSpace α› = ‹TopologicalSpace β›.induced f) (h : Continuous (f ∘ g)) : Continuous g :=
  H.symm ▸ continuous_induced_rng h

theorem continuous_coinduced_rng {t : tspace α} : cont t (coinduced f t) f := by
  rw [continuous_def]
  intro s h
  exact h

theorem continuous_coinduced_dom {g : β → γ} {t₁ : tspace α} {t₂ : tspace γ} (h : cont t₁ t₂ (g ∘ f)) :
    cont (coinduced f t₁) t₂ g := by
  rw [continuous_def] at h⊢
  intro s hs
  exact h _ hs

theorem continuous_le_dom {t₁ t₂ : tspace α} {t₃ : tspace β} (h₁ : t₂ ≤ t₁) (h₂ : cont t₁ t₃ f) : cont t₂ t₃ f := by
  rw [continuous_def] at h₂⊢
  intro s h
  exact h₁ _ (h₂ s h)

theorem continuous_le_rng {t₁ : tspace α} {t₂ t₃ : tspace β} (h₁ : t₂ ≤ t₃) (h₂ : cont t₁ t₂ f) : cont t₁ t₃ f := by
  rw [continuous_def] at h₂⊢
  intro s h
  exact h₂ s (h₁ s h)

theorem continuous_sup_dom {t₁ t₂ : tspace α} {t₃ : tspace β} (h₁ : cont t₁ t₃ f) (h₂ : cont t₂ t₃ f) :
    cont (t₁⊔t₂) t₃ f := by
  rw [continuous_def] at h₁ h₂⊢
  intro s h
  exact ⟨h₁ s h, h₂ s h⟩

theorem continuous_sup_rng_left {t₁ : tspace α} {t₃ t₂ : tspace β} : cont t₁ t₂ f → cont t₁ (t₂⊔t₃) f :=
  continuous_le_rng le_sup_left

theorem continuous_sup_rng_right {t₁ : tspace α} {t₃ t₂ : tspace β} : cont t₁ t₃ f → cont t₁ (t₂⊔t₃) f :=
  continuous_le_rng le_sup_right

theorem continuous_Sup_dom {t₁ : Set (tspace α)} {t₂ : tspace β} (h : ∀, ∀ t ∈ t₁, ∀, cont t t₂ f) :
    cont (sup t₁) t₂ f :=
  continuous_iff_le_induced.2 <| Sup_le fun t ht => continuous_iff_le_induced.1 <| h t ht

theorem continuous_Sup_rng {t₁ : tspace α} {t₂ : Set (tspace β)} {t : tspace β} (h₁ : t ∈ t₂) (hf : cont t₁ t f) :
    cont t₁ (sup t₂) f :=
  continuous_iff_coinduced_le.2 <| le_Sup_of_le h₁ <| continuous_iff_coinduced_le.1 hf

theorem continuous_supr_dom {t₁ : ι → tspace α} {t₂ : tspace β} (h : ∀ i, cont (t₁ i) t₂ f) : cont (supr t₁) t₂ f :=
  continuous_Sup_dom fun t ⟨i, (t_eq : t₁ i = t)⟩ => t_eq ▸ h i

theorem continuous_supr_rng {t₁ : tspace α} {t₂ : ι → tspace β} {i : ι} (h : cont t₁ (t₂ i) f) : cont t₁ (supr t₂) f :=
  continuous_Sup_rng ⟨i, rfl⟩ h

theorem continuous_inf_rng {t₁ : tspace α} {t₂ t₃ : tspace β} (h₁ : cont t₁ t₂ f) (h₂ : cont t₁ t₃ f) :
    cont t₁ (t₂⊓t₃) f :=
  continuous_iff_coinduced_le.2 <| le_inf (continuous_iff_coinduced_le.1 h₁) (continuous_iff_coinduced_le.1 h₂)

theorem continuous_inf_dom_left {t₁ t₂ : tspace α} {t₃ : tspace β} : cont t₁ t₃ f → cont (t₁⊓t₂) t₃ f :=
  continuous_le_dom inf_le_left

theorem continuous_inf_dom_right {t₁ t₂ : tspace α} {t₃ : tspace β} : cont t₂ t₃ f → cont (t₁⊓t₂) t₃ f :=
  continuous_le_dom inf_le_right

theorem continuous_Inf_dom {t₁ : Set (tspace α)} {t₂ : tspace β} {t : tspace α} (h₁ : t ∈ t₁) :
    cont t t₂ f → cont (inf t₁) t₂ f :=
  continuous_le_dom <| Inf_le h₁

theorem continuous_Inf_rng {t₁ : tspace α} {t₂ : Set (tspace β)} (h : ∀, ∀ t ∈ t₂, ∀, cont t₁ t f) :
    cont t₁ (inf t₂) f :=
  continuous_iff_coinduced_le.2 <| le_Inf fun b hb => continuous_iff_coinduced_le.1 <| h b hb

theorem continuous_infi_dom {t₁ : ι → tspace α} {t₂ : tspace β} {i : ι} : cont (t₁ i) t₂ f → cont (infi t₁) t₂ f :=
  continuous_le_dom <| infi_le _ _

theorem continuous_infi_rng {t₁ : tspace α} {t₂ : ι → tspace β} (h : ∀ i, cont t₁ (t₂ i) f) : cont t₁ (infi t₂) f :=
  continuous_iff_coinduced_le.2 <| le_infi fun i => continuous_iff_coinduced_le.1 <| h i

@[continuity]
theorem continuous_bot {t : tspace β} : cont ⊥ t f :=
  continuous_iff_le_induced.2 <| bot_le

@[continuity]
theorem continuous_top {t : tspace α} : cont t ⊤ f :=
  continuous_iff_coinduced_le.2 <| le_top

theorem continuous_id_iff_le {t t' : tspace α} : cont t t' id ↔ t ≤ t' :=
  @continuous_def _ _ t t' id

theorem continuous_id_of_le {t t' : tspace α} (h : t ≤ t') : cont t t' id :=
  continuous_id_iff_le.2 h

-- 𝓝 in the induced topology
theorem mem_nhds_induced [T : TopologicalSpace α] (f : β → α) (a : β) (s : Set β) :
    s ∈ @nhds β (TopologicalSpace.induced f T) a ↔ ∃ u ∈ 𝓝 (f a), f ⁻¹' u ⊆ s := by
  simp only [← mem_nhds_iff, ← is_open_induced_iff, ← exists_prop, ← Set.mem_set_of_eq]
  constructor
  · rintro ⟨u, usub, ⟨v, openv, ueq⟩, au⟩
    exact
      ⟨v,
        ⟨v, Set.Subset.refl v, openv, by
          rwa [← ueq] at au⟩,
        by
        rw [ueq] <;> exact usub⟩
    
  rintro ⟨u, ⟨v, vsubu, openv, amem⟩, finvsub⟩
  exact ⟨f ⁻¹' v, Set.Subset.trans (Set.preimage_mono vsubu) finvsub, ⟨⟨v, openv, rfl⟩, amem⟩⟩

theorem nhds_induced [T : TopologicalSpace α] (f : β → α) (a : β) :
    @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a)) := by
  ext s
  rw [mem_nhds_induced, mem_comap]

theorem induced_iff_nhds_eq [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : β → α) :
    tβ = tα.induced f ↔ ∀ b, 𝓝 b = comap f (𝓝 <| f b) :=
  ⟨fun h a => h.symm ▸ nhds_induced f a, fun h =>
    eq_of_nhds_eq_nhds fun x => by
      rw [h, nhds_induced]⟩

theorem map_nhds_induced_of_surjective [T : TopologicalSpace α] {f : β → α} (hf : Function.Surjective f) (a : β) :
    map f (@nhds β (TopologicalSpace.induced f T) a) = 𝓝 (f a) := by
  rw [nhds_induced, map_comap_of_surjective hf]

end Constructions

section Induced

open TopologicalSpace

variable {α : Type _} {β : Type _}

variable [t : TopologicalSpace β] {f : α → β}

theorem is_open_induced_eq {s : Set α} : @IsOpen _ (induced f t) s ↔ s ∈ Preimage f '' { s | IsOpen s } :=
  Iff.rfl

theorem is_open_induced {s : Set β} (h : IsOpen s) : (induced f t).IsOpen (f ⁻¹' s) :=
  ⟨s, h, rfl⟩

theorem map_nhds_induced_eq (a : α) : map f (@nhds α (induced f t) a) = 𝓝[Range f] f a := by
  rw [nhds_induced, Filter.map_comap, nhdsWithin]

theorem map_nhds_induced_of_mem {a : α} (h : Range f ∈ 𝓝 (f a)) : map f (@nhds α (induced f t) a) = 𝓝 (f a) := by
  rw [nhds_induced, Filter.map_comap_of_mem h]

theorem closure_induced [t : TopologicalSpace β] {f : α → β} {a : α} {s : Set α} :
    a ∈ @Closure α (TopologicalSpace.induced f t) s ↔ f a ∈ Closure (f '' s) := by
  simp only [← mem_closure_iff_frequently, ← nhds_induced, ← frequently_comap, ← mem_image, ← and_comm]

theorem is_closed_induced_iff' [t : TopologicalSpace β] {f : α → β} {s : Set α} :
    @IsClosed α (t.induced f) s ↔ ∀ a, f a ∈ Closure (f '' s) → a ∈ s := by
  simp only [closure_subset_iff_is_closed, ← subset_def, ← closure_induced]

end Induced

section Sierpinski

variable {α : Type _} [TopologicalSpace α]

@[simp]
theorem is_open_singleton_true : IsOpen ({True} : Set Prop) :=
  TopologicalSpace.GenerateOpen.basic _ (mem_singleton _)

@[simp]
theorem nhds_true : 𝓝 True = pure True :=
  le_antisymmₓ (le_pure_iff.2 <| is_open_singleton_true.mem_nhds <| mem_singleton _) (pure_le_nhds _)

@[simp]
theorem nhds_false : 𝓝 False = ⊤ :=
  TopologicalSpace.nhds_generate_from.trans <| by
    simp [← @And.comm (_ ∈ _)]

theorem continuous_Prop {p : α → Prop} : Continuous p ↔ IsOpen { x | p x } :=
  ⟨fun h : Continuous p => by
    have : IsOpen (p ⁻¹' {True}) := is_open_singleton_true.Preimage h
    simpa [← preimage, ← eq_trueₓ] using this, fun h : IsOpen { x | p x } =>
    continuous_generated_from fun s (hs : s = {True}) => by
      simp [← hs, ← preimage, ← eq_trueₓ, ← h]⟩

theorem is_open_iff_continuous_mem {s : Set α} : IsOpen s ↔ Continuous fun x => x ∈ s :=
  continuous_Prop.symm

end Sierpinski

section infi

variable {α : Type u} {ι : Sort v}

theorem generate_from_union (a₁ a₂ : Set (Set α)) :
    TopologicalSpace.generateFrom (a₁ ∪ a₂) = TopologicalSpace.generateFrom a₁⊓TopologicalSpace.generateFrom a₂ :=
  @GaloisConnection.l_sup _ (TopologicalSpace α)ᵒᵈ a₁ a₂ _ _ _ _ fun g t => generate_from_le_iff_subset_is_open

theorem set_of_is_open_sup (t₁ t₂ : TopologicalSpace α) :
    { s | (t₁⊔t₂).IsOpen s } = { s | t₁.IsOpen s } ∩ { s | t₂.IsOpen s } :=
  @GaloisConnection.u_inf _ (TopologicalSpace α)ᵒᵈ t₁ t₂ _ _ _ _ fun g t => generate_from_le_iff_subset_is_open

theorem generate_from_Union {f : ι → Set (Set α)} :
    TopologicalSpace.generateFrom (⋃ i, f i) = ⨅ i, TopologicalSpace.generateFrom (f i) :=
  @GaloisConnection.l_supr _ (TopologicalSpace α)ᵒᵈ _ _ _ _ _ (fun g t => generate_from_le_iff_subset_is_open) f

theorem set_of_is_open_supr {t : ι → TopologicalSpace α} : { s | (⨆ i, t i).IsOpen s } = ⋂ i, { s | (t i).IsOpen s } :=
  @GaloisConnection.u_infi _ (TopologicalSpace α)ᵒᵈ _ _ _ _ _ (fun g t => generate_from_le_iff_subset_is_open) t

theorem generate_from_sUnion {S : Set (Set (Set α))} :
    TopologicalSpace.generateFrom (⋃₀S) = ⨅ s ∈ S, TopologicalSpace.generateFrom s :=
  @GaloisConnection.l_Sup _ (TopologicalSpace α)ᵒᵈ _ _ _ _ (fun g t => generate_from_le_iff_subset_is_open) S

theorem set_of_is_open_Sup {T : Set (TopologicalSpace α)} :
    { s | (sup T).IsOpen s } = ⋂ t ∈ T, { s | (t : TopologicalSpace α).IsOpen s } :=
  @GaloisConnection.u_Inf _ (TopologicalSpace α)ᵒᵈ _ _ _ _ (fun g t => generate_from_le_iff_subset_is_open) T

theorem generate_from_union_is_open (a b : TopologicalSpace α) :
    TopologicalSpace.generateFrom ({ s | a.IsOpen s } ∪ { s | b.IsOpen s }) = a⊓b :=
  @GaloisInsertion.l_sup_u _ (TopologicalSpace α)ᵒᵈ _ _ _ _ (giGenerateFrom α) a b

theorem generate_from_Union_is_open (f : ι → TopologicalSpace α) :
    TopologicalSpace.generateFrom (⋃ i, { s | (f i).IsOpen s }) = ⨅ i, f i :=
  @GaloisInsertion.l_supr_u _ (TopologicalSpace α)ᵒᵈ _ _ _ _ (giGenerateFrom α) _ f

theorem generate_from_inter (a b : TopologicalSpace α) :
    TopologicalSpace.generateFrom ({ s | a.IsOpen s } ∩ { s | b.IsOpen s }) = a⊔b :=
  @GaloisInsertion.l_inf_u _ (TopologicalSpace α)ᵒᵈ _ _ _ _ (giGenerateFrom α) a b

theorem generate_from_Inter (f : ι → TopologicalSpace α) :
    TopologicalSpace.generateFrom (⋂ i, { s | (f i).IsOpen s }) = ⨆ i, f i :=
  @GaloisInsertion.l_infi_u _ (TopologicalSpace α)ᵒᵈ _ _ _ _ (giGenerateFrom α) _ f

theorem generate_from_Inter_of_generate_from_eq_self (f : ι → Set (Set α))
    (hf : ∀ i, { s | (TopologicalSpace.generateFrom (f i)).IsOpen s } = f i) :
    TopologicalSpace.generateFrom (⋂ i, f i) = ⨆ i, TopologicalSpace.generateFrom (f i) :=
  @GaloisInsertion.l_infi_of_ul_eq_self _ (TopologicalSpace α)ᵒᵈ _ _ _ _ (giGenerateFrom α) _ f hf

variable {t : ι → TopologicalSpace α}

theorem is_open_supr_iff {s : Set α} : @IsOpen _ (⨆ i, t i) s ↔ ∀ i, @IsOpen _ (t i) s :=
  show s ∈ SetOf (supr t).IsOpen ↔ s ∈ { x : Set α | ∀ i : ι, (t i).IsOpen x } by
    simp [← set_of_is_open_supr]

theorem is_closed_supr_iff {s : Set α} : @IsClosed _ (⨆ i, t i) s ↔ ∀ i, @IsClosed _ (t i) s := by
  simp [is_open_compl_iff, ← is_open_supr_iff]

end infi


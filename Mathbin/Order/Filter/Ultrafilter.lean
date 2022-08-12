/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
import Mathbin.Order.Filter.Cofinite
import Mathbin.Order.Zorn

/-!
# Ultrafilters

An ultrafilter is a minimal (maximal in the set order) proper filter.
In this file we define

* `ultrafilter.of`: an ultrafilter that is less than or equal to a given filter;
* `ultrafilter`: subtype of ultrafilters;
* `ultrafilter.pure`: `pure x` as an `ultrafiler`;
* `ultrafilter.map`, `ultrafilter.bind`, `ultrafilter.comap` : operations on ultrafilters;
* `hyperfilter`: the ultrafilter extending the cofinite filter.
-/


universe u v

variable {α : Type u} {β : Type v} {γ : Type _}

open Set Filter Function

open Classical Filter

/-- An ultrafilter is a minimal (maximal in the set order) proper filter. -/
@[protect_proj]
structure Ultrafilter (α : Type _) extends Filter α where
  ne_bot' : NeBot to_filter
  le_of_le : ∀ g, Filter.NeBot g → g ≤ to_filter → to_filter ≤ g

namespace Ultrafilter

variable {f g : Ultrafilter α} {s t : Set α} {p q : α → Prop}

instance : CoeTₓ (Ultrafilter α) (Filter α) :=
  ⟨Ultrafilter.toFilter⟩

instance : HasMem (Set α) (Ultrafilter α) :=
  ⟨fun s f => s ∈ (f : Filter α)⟩

theorem unique (f : Ultrafilter α) {g : Filter α} (h : g ≤ f)
    (hne : NeBot g := by
      run_tac
        tactic.apply_instance) :
    g = f :=
  le_antisymmₓ h <| f.le_of_le g hne h

instance ne_bot (f : Ultrafilter α) : NeBot (f : Filter α) :=
  f.ne_bot'

@[simp, norm_cast]
theorem mem_coe : s ∈ (f : Filter α) ↔ s ∈ f :=
  Iff.rfl

theorem coe_injective : Injective (coe : Ultrafilter α → Filter α)
  | ⟨f, h₁, h₂⟩, ⟨g, h₃, h₄⟩, rfl => by
    congr

theorem eq_of_le {f g : Ultrafilter α} (h : (f : Filter α) ≤ g) : f = g :=
  coe_injective (g.unique h)

@[simp, norm_cast]
theorem coe_le_coe {f g : Ultrafilter α} : (f : Filter α) ≤ g ↔ f = g :=
  ⟨fun h => eq_of_le h, fun h => h ▸ le_rfl⟩

@[simp, norm_cast]
theorem coe_inj : (f : Filter α) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
theorem ext ⦃f g : Ultrafilter α⦄ (h : ∀ s, s ∈ f ↔ s ∈ g) : f = g :=
  coe_injective <| Filter.ext h

theorem le_of_inf_ne_bot (f : Ultrafilter α) {g : Filter α} (hg : NeBot (↑f⊓g)) : ↑f ≤ g :=
  le_of_inf_eq (f.unique inf_le_left hg)

theorem le_of_inf_ne_bot' (f : Ultrafilter α) {g : Filter α} (hg : NeBot (g⊓f)) : ↑f ≤ g :=
  f.le_of_inf_ne_bot <| by
    rwa [inf_comm]

@[simp]
theorem compl_not_mem_iff : sᶜ ∉ f ↔ s ∈ f :=
  ⟨fun hsc =>
    le_principal_iff.1 <|
      f.le_of_inf_ne_bot
        ⟨fun h =>
          hsc <|
            mem_of_eq_bot <| by
              rwa [compl_compl]⟩,
    compl_not_mem⟩

@[simp]
theorem frequently_iff_eventually : (∃ᶠ x in f, p x) ↔ ∀ᶠ x in f, p x :=
  compl_not_mem_iff

alias frequently_iff_eventually ↔ _root_.filter.frequently.eventually _

theorem compl_mem_iff_not_mem : sᶜ ∈ f ↔ s ∉ f := by
  rw [← compl_not_mem_iff, compl_compl]

theorem diff_mem_iff (f : Ultrafilter α) : s \ t ∈ f ↔ s ∈ f ∧ t ∉ f :=
  inter_mem_iff.trans <| and_congr Iff.rfl compl_mem_iff_not_mem

/-- If `sᶜ ∉ f ↔ s ∈ f`, then `f` is an ultrafilter. The other implication is given by
`ultrafilter.compl_not_mem_iff`.  -/
def ofComplNotMemIff (f : Filter α) (h : ∀ s, sᶜ ∉ f ↔ s ∈ f) : Ultrafilter α where
  toFilter := f
  ne_bot' :=
    ⟨fun hf => by
      simpa [← hf] using h⟩
  le_of_le := fun g hg hgf s hs => (h s).1 fun hsc => compl_not_mem hs (hgf hsc)

theorem nonempty_of_mem (hs : s ∈ f) : s.Nonempty :=
  nonempty_of_mem hs

theorem ne_empty_of_mem (hs : s ∈ f) : s ≠ ∅ :=
  (nonempty_of_mem hs).ne_empty

@[simp]
theorem empty_not_mem : ∅ ∉ f :=
  empty_not_mem f

theorem mem_or_compl_mem (f : Ultrafilter α) (s : Set α) : s ∈ f ∨ sᶜ ∈ f :=
  or_iff_not_imp_left.2 compl_mem_iff_not_mem.2

protected theorem em (f : Ultrafilter α) (p : α → Prop) : (∀ᶠ x in f, p x) ∨ ∀ᶠ x in f, ¬p x :=
  f.mem_or_compl_mem { x | p x }

theorem eventually_or : (∀ᶠ x in f, p x ∨ q x) ↔ (∀ᶠ x in f, p x) ∨ ∀ᶠ x in f, q x :=
  ⟨fun H => (f.em p).imp_right fun hp => (H.And hp).mono fun x ⟨hx, hnx⟩ => hx.resolve_left hnx, fun H =>
    H.elim (fun hp => hp.mono fun x => Or.inl) fun hp => hp.mono fun x => Or.inr⟩

theorem union_mem_iff : s ∪ t ∈ f ↔ s ∈ f ∨ t ∈ f :=
  eventually_or

theorem eventually_not : (∀ᶠ x in f, ¬p x) ↔ ¬∀ᶠ x in f, p x :=
  compl_mem_iff_not_mem

theorem eventually_imp : (∀ᶠ x in f, p x → q x) ↔ (∀ᶠ x in f, p x) → ∀ᶠ x in f, q x := by
  simp only [← imp_iff_not_or, ← eventually_or, ← eventually_not]

theorem finite_sUnion_mem_iff {s : Set (Set α)} (hs : s.Finite) : ⋃₀s ∈ f ↔ ∃ t ∈ s, t ∈ f :=
  (Finite.induction_on hs
      (by
        simp ))
    fun a s ha hs his => by
    simp [← union_mem_iff, ← his, ← or_and_distrib_right, ← exists_or_distrib]

theorem finite_bUnion_mem_iff {is : Set β} {s : β → Set α} (his : is.Finite) :
    (⋃ i ∈ is, s i) ∈ f ↔ ∃ i ∈ is, s i ∈ f := by
  simp only [sUnion_image, ← finite_sUnion_mem_iff (his.image s), ← bex_image_iff]

/-- Pushforward for ultrafilters. -/
def map (m : α → β) (f : Ultrafilter α) : Ultrafilter β :=
  (ofComplNotMemIff (map m f)) fun s => @compl_not_mem_iff _ f (m ⁻¹' s)

@[simp, norm_cast]
theorem coe_map (m : α → β) (f : Ultrafilter α) : (map m f : Filter β) = Filter.map m ↑f :=
  rfl

@[simp]
theorem mem_map {m : α → β} {f : Ultrafilter α} {s : Set β} : s ∈ map m f ↔ m ⁻¹' s ∈ f :=
  Iff.rfl

@[simp]
theorem map_id (f : Ultrafilter α) : f.map id = f :=
  coe_injective map_id

@[simp]
theorem map_id' (f : Ultrafilter α) : (f.map fun x => x) = f :=
  map_id _

@[simp]
theorem map_map (f : Ultrafilter α) (m : α → β) (n : β → γ) : (f.map m).map n = f.map (n ∘ m) :=
  coe_injective map_map

/-- The pullback of an ultrafilter along an injection whose range is large with respect to the given
ultrafilter. -/
def comap {m : α → β} (u : Ultrafilter β) (inj : Injective m) (large : Set.Range m ∈ u) : Ultrafilter α where
  toFilter := comap m u
  ne_bot' := u.ne_bot'.comap_of_range_mem large
  le_of_le := fun g hg hgu => by
    skip
    simp only [u.unique (map_le_iff_le_comap.2 hgu), ← comap_map inj, ← le_rfl]

@[simp]
theorem mem_comap {m : α → β} (u : Ultrafilter β) (inj : Injective m) (large : Set.Range m ∈ u) {s : Set α} :
    s ∈ u.comap inj large ↔ m '' s ∈ u :=
  mem_comap_iff inj large

@[simp, norm_cast]
theorem coe_comap {m : α → β} (u : Ultrafilter β) (inj : Injective m) (large : Set.Range m ∈ u) :
    (u.comap inj large : Filter α) = Filter.comap m u :=
  rfl

@[simp]
theorem comap_id (f : Ultrafilter α) (h₀ : Injective (id : α → α) := injective_id)
    (h₁ : Range id ∈ f := by
      rw [range_id]
      exact univ_mem) :
    f.comap h₀ h₁ = f :=
  coe_injective comap_id

@[simp]
theorem comap_comap (f : Ultrafilter γ) {m : α → β} {n : β → γ} (inj₀ : Injective n) (large₀ : Range n ∈ f)
    (inj₁ : Injective m) (large₁ : Range m ∈ f.comap inj₀ large₀) (inj₂ : Injective (n ∘ m) := inj₀.comp inj₁)
    (large₂ : Range (n ∘ m) ∈ f := by
      rw [range_comp]
      exact image_mem_of_mem_comap large₀ large₁) :
    (f.comap inj₀ large₀).comap inj₁ large₁ = f.comap inj₂ large₂ :=
  coe_injective comap_comap

/-- The principal ultrafilter associated to a point `x`. -/
instance : Pure Ultrafilter :=
  ⟨fun α a =>
    (ofComplNotMemIff (pure a)) fun s => by
      simp ⟩

@[simp]
theorem mem_pure {a : α} {s : Set α} : s ∈ (pure a : Ultrafilter α) ↔ a ∈ s :=
  Iff.rfl

@[simp]
theorem coe_pure (a : α) : ↑(pure a : Ultrafilter α) = (pure a : Filter α) :=
  rfl

@[simp]
theorem map_pure (m : α → β) (a : α) : map m (pure a) = pure (m a) :=
  rfl

@[simp]
theorem comap_pure {m : α → β} (a : α) (inj : Injective m) (large) : comap (pure <| m a) inj large = pure a :=
  coe_injective <|
    comap_pure.trans <| by
      rw [coe_pure, ← principal_singleton, ← image_singleton, preimage_image_eq _ inj]

theorem pure_injective : Injective (pure : α → Ultrafilter α) := fun a b h =>
  Filter.pure_injective (congr_arg Ultrafilter.toFilter h : _)

instance [Inhabited α] : Inhabited (Ultrafilter α) :=
  ⟨pure default⟩

instance [Nonempty α] : Nonempty (Ultrafilter α) :=
  Nonempty.map pure inferInstance

theorem eq_pure_of_finite_mem (h : s.Finite) (h' : s ∈ f) : ∃ x ∈ s, (f : Filter α) = pure x := by
  rw [← bUnion_of_singleton s] at h'
  rcases(Ultrafilter.finite_bUnion_mem_iff h).mp h' with ⟨a, has, haf⟩
  use a, has
  change (f : Filter α) = (pure a : Ultrafilter α)
  rw [Ultrafilter.coe_inj, ← Ultrafilter.coe_le_coe]
  change (f : Filter α) ≤ pure a
  rwa [← principal_singleton, le_principal_iff]

theorem eq_pure_of_fintype [Fintype α] (f : Ultrafilter α) : ∃ a, (f : Filter α) = pure a :=
  (eq_pure_of_finite_mem finite_univ univ_mem).imp fun a ⟨_, ha⟩ => ha

/-- Monadic bind for ultrafilters, coming from the one on filters
defined in terms of map and join.-/
def bind (f : Ultrafilter α) (m : α → Ultrafilter β) : Ultrafilter β :=
  (ofComplNotMemIff (bind ↑f fun x => ↑(m x))) fun s => by
    simp only [← mem_bind', ← mem_coe, compl_mem_iff_not_mem, ← compl_set_of, ← compl_compl]

instance hasBind : Bind Ultrafilter :=
  ⟨@Ultrafilter.bind⟩

instance functor : Functor Ultrafilter where map := @Ultrafilter.map

instance monad : Monadₓ Ultrafilter where map := @Ultrafilter.map

section

attribute [local instance] Filter.monad Filter.is_lawful_monad

instance is_lawful_monad : IsLawfulMonad Ultrafilter where
  id_map := fun α f => coe_injective (id_map f.1)
  pure_bind := fun α β a f => coe_injective (pure_bind a (coe ∘ f))
  bind_assoc := fun α β γ f m₁ m₂ => coe_injective (filter_eq rfl)
  bind_pure_comp_eq_map := fun α β f x => coe_injective (bind_pure_comp_eq_map f x.1)

end

/-- The ultrafilter lemma: Any proper filter is contained in an ultrafilter. -/
theorem exists_le (f : Filter α) [h : NeBot f] : ∃ u : Ultrafilter α, ↑u ≤ f := by
  let τ := { f' // ne_bot f' ∧ f' ≤ f }
  let r : τ → τ → Prop := fun t₁ t₂ => t₂.val ≤ t₁.val
  have := nonempty_of_ne_bot f
  let top : τ := ⟨f, h, le_reflₓ f⟩
  let sup : ∀ c : Set τ, IsChain r c → τ := fun c hc =>
    ⟨⨅ a : { a : τ // a ∈ insert top c }, a.1,
      infi_ne_bot_of_directed (IsChain.directed <| hc.insert fun ⟨b, _, hb⟩ _ _ => Or.inl hb) fun ⟨⟨a, ha, _⟩, _⟩ => ha,
      infi_le_of_le ⟨top, mem_insert _ _⟩ le_rfl⟩
  have : ∀ (c) (hc : IsChain r c) (a) (ha : a ∈ c), r a (sup c hc) := fun c hc a ha =>
    infi_le_of_le ⟨a, mem_insert_of_mem _ ha⟩ le_rfl
  have : ∃ u : τ, ∀ a : τ, r u a → r a u :=
    exists_maximal_of_chains_bounded (fun c hc => ⟨sup c hc, this c hc⟩) fun f₁ f₂ f₃ h₁ h₂ => le_transₓ h₂ h₁
  cases' this with uτ hmin
  exact
    ⟨⟨uτ.val, uτ.property.left, fun g hg₁ hg₂ => hmin ⟨g, hg₁, le_transₓ hg₂ uτ.property.right⟩ hg₂⟩, uτ.property.right⟩

alias exists_le ← _root_.filter.exists_ultrafilter_le

/-- Construct an ultrafilter extending a given filter.
  The ultrafilter lemma is the assertion that such a filter exists;
  we use the axiom of choice to pick one. -/
noncomputable def of (f : Filter α) [NeBot f] : Ultrafilter α :=
  Classical.some (exists_le f)

theorem of_le (f : Filter α) [NeBot f] : ↑(of f) ≤ f :=
  Classical.some_spec (exists_le f)

theorem of_coe (f : Ultrafilter α) : of ↑f = f :=
  coe_inj.1 <| f.unique (of_le f)

theorem exists_ultrafilter_of_finite_inter_nonempty (S : Set (Set α))
    (cond : ∀ T : Finset (Set α), (↑T : Set (Set α)) ⊆ S → (⋂₀ (↑T : Set (Set α))).Nonempty) :
    ∃ F : Ultrafilter α, S ⊆ F.Sets := by
  suffices ∃ F : Filter α, ne_bot F ∧ S ⊆ F.Sets by
    rcases this with ⟨F, cond, hF⟩
    skip
    obtain ⟨G : Ultrafilter α, h1 : ↑G ≤ F⟩ := exists_le F
    exact ⟨G, fun T hT => h1 (hF hT)⟩
  use Filter.generate S
  refine' ⟨_, fun T hT => Filter.GenerateSets.basic hT⟩
  rw [← forall_mem_nonempty_iff_ne_bot]
  intro T hT
  rcases mem_generate_iff.mp hT with ⟨A, h1, h2, h3⟩
  let B := Set.Finite.toFinset h2
  rw
    [show A = ↑B by
      simp ] at
    *
  rcases cond B h1 with ⟨x, hx⟩
  exact ⟨x, h3 hx⟩

end Ultrafilter

namespace Filter

variable {f : Filter α} {s : Set α} {a : α}

open Ultrafilter

protected theorem NeBot.le_pure_iff (hf : f.ne_bot) : f ≤ pure a ↔ f = pure a :=
  ⟨Ultrafilter.unique (pure a), le_of_eqₓ⟩

theorem mem_iff_ultrafilter : s ∈ f ↔ ∀ g : Ultrafilter α, ↑g ≤ f → s ∈ g := by
  refine' ⟨fun hf g hg => hg hf, fun H => by_contra fun hf => _⟩
  set g : Filter ↥(sᶜ) := comap coe f
  have : ne_bot g :=
    comap_ne_bot_iff_compl_range.2
      (by
        simpa [← compl_set_of] )
  simpa using H ((of g).map coe) (map_le_iff_le_comap.mpr (of_le g))

theorem le_iff_ultrafilter {f₁ f₂ : Filter α} : f₁ ≤ f₂ ↔ ∀ g : Ultrafilter α, ↑g ≤ f₁ → ↑g ≤ f₂ :=
  ⟨fun h g h₁ => h₁.trans h, fun h s hs => mem_iff_ultrafilter.2 fun g hg => h g hg hs⟩

/-- A filter equals the intersection of all the ultrafilters which contain it. -/
theorem supr_ultrafilter_le_eq (f : Filter α) : (⨆ (g : Ultrafilter α) (hg : ↑g ≤ f), (g : Filter α)) = f :=
  eq_of_forall_ge_iff fun f' => by
    simp only [← supr_le_iff, le_iff_ultrafilter]

/-- The `tendsto` relation can be checked on ultrafilters. -/
theorem tendsto_iff_ultrafilter (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :
    Tendsto f l₁ l₂ ↔ ∀ g : Ultrafilter α, ↑g ≤ l₁ → Tendsto f g l₂ := by
  simpa only [← tendsto_iff_comap] using le_iff_ultrafilter

theorem exists_ultrafilter_iff {f : Filter α} : (∃ u : Ultrafilter α, ↑u ≤ f) ↔ NeBot f :=
  ⟨fun ⟨u, uf⟩ => ne_bot_of_le uf, fun h => @exists_ultrafilter_le _ _ h⟩

theorem forall_ne_bot_le_iff {g : Filter α} {p : Filter α → Prop} (hp : Monotone p) :
    (∀ f : Filter α, NeBot f → f ≤ g → p f) ↔ ∀ f : Ultrafilter α, ↑f ≤ g → p f := by
  refine' ⟨fun H f hf => H f f.ne_bot hf, _⟩
  intro H f hf hfg
  exact hp (of_le f) (H _ ((of_le f).trans hfg))

section Hyperfilter

variable (α) [Infinite α]

/-- The ultrafilter extending the cofinite filter. -/
noncomputable def hyperfilter : Ultrafilter α :=
  Ultrafilter.of cofinite

variable {α}

theorem hyperfilter_le_cofinite : ↑(hyperfilter α) ≤ @cofinite α :=
  Ultrafilter.of_le cofinite

@[simp]
theorem bot_ne_hyperfilter : (⊥ : Filter α) ≠ hyperfilter α :=
  (by
        infer_instance : NeBot ↑(hyperfilter α)).1.symm

theorem nmem_hyperfilter_of_finite {s : Set α} (hf : s.Finite) : s ∉ hyperfilter α := fun hy =>
  compl_not_mem hy <| hyperfilter_le_cofinite hf.compl_mem_cofinite

alias nmem_hyperfilter_of_finite ← _root_.set.finite.nmem_hyperfilter

theorem compl_mem_hyperfilter_of_finite {s : Set α} (hf : Set.Finite s) : sᶜ ∈ hyperfilter α :=
  compl_mem_iff_not_mem.2 hf.nmem_hyperfilter

alias compl_mem_hyperfilter_of_finite ← _root_.set.finite.compl_mem_hyperfilter

theorem mem_hyperfilter_of_finite_compl {s : Set α} (hf : Set.Finite (sᶜ)) : s ∈ hyperfilter α :=
  compl_compl s ▸ hf.compl_mem_hyperfilter

end Hyperfilter

end Filter

namespace Ultrafilter

open Filter

variable {m : α → β} {s : Set α} {g : Ultrafilter β}

theorem comap_inf_principal_ne_bot_of_image_mem (h : m '' s ∈ g) : (Filter.comap m g⊓𝓟 s).ne_bot :=
  Filter.comap_inf_principal_ne_bot_of_image_mem g.ne_bot h

/-- Ultrafilter extending the inf of a comapped ultrafilter and a principal ultrafilter. -/
noncomputable def ofComapInfPrincipal (h : m '' s ∈ g) : Ultrafilter α :=
  @of _ (Filter.comap m g⊓𝓟 s) (comap_inf_principal_ne_bot_of_image_mem h)

theorem of_comap_inf_principal_mem (h : m '' s ∈ g) : s ∈ ofComapInfPrincipal h := by
  let f := Filter.comap m g⊓𝓟 s
  have : f.ne_bot := comap_inf_principal_ne_bot_of_image_mem h
  have : s ∈ f := mem_inf_of_right (mem_principal_self s)
  exact le_def.mp (of_le _) s this

theorem of_comap_inf_principal_eq_of_map (h : m '' s ∈ g) : (ofComapInfPrincipal h).map m = g := by
  let f := Filter.comap m g⊓𝓟 s
  have : f.ne_bot := comap_inf_principal_ne_bot_of_image_mem h
  apply eq_of_le
  calc Filter.map m (of f) ≤ Filter.map m f :=
      map_mono (of_le _)_ ≤ (Filter.map m <| Filter.comap m g)⊓Filter.map m (𝓟 s) :=
      map_inf_le _ = (Filter.map m <| Filter.comap m g)⊓(𝓟 <| m '' s) := by
      rw [map_principal]_ ≤ g⊓(𝓟 <| m '' s) := inf_le_inf_right _ map_comap_le _ = g :=
      inf_of_le_left (le_principal_iff.mpr h)

end Ultrafilter


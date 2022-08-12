/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Computational realization of filters (experimental).
-/
import Mathbin.Order.Filter.Cofinite

open Set Filter

/-- A `cfilter α σ` is a realization of a filter (base) on `α`,
  represented by a type `σ` together with operations for the top element and
  the binary inf operation. -/
structure Cfilter (α σ : Type _) [PartialOrderₓ α] where
  f : σ → α
  pt : σ
  inf : σ → σ → σ
  inf_le_left : ∀ a b : σ, f (inf a b) ≤ f a
  inf_le_right : ∀ a b : σ, f (inf a b) ≤ f b

variable {α : Type _} {β : Type _} {σ : Type _} {τ : Type _}

namespace Cfilter

section

variable [PartialOrderₓ α] (F : Cfilter α σ)

instance : CoeFun (Cfilter α σ) fun _ => σ → α :=
  ⟨Cfilter.f⟩

@[simp]
theorem coe_mk (f pt inf h₁ h₂ a) : (@Cfilter.mk α σ _ f pt inf h₁ h₂) a = f a :=
  rfl

/-- Map a cfilter to an equivalent representation type. -/
def ofEquiv (E : σ ≃ τ) : Cfilter α σ → Cfilter α τ
  | ⟨f, p, g, h₁, h₂⟩ =>
    { f := fun a => f (E.symm a), pt := E p, inf := fun a b => E (g (E.symm a) (E.symm b)),
      inf_le_left := fun a b => by
        simpa using h₁ (E.symm a) (E.symm b),
      inf_le_right := fun a b => by
        simpa using h₂ (E.symm a) (E.symm b) }

@[simp]
theorem of_equiv_val (E : σ ≃ τ) (F : Cfilter α σ) (a : τ) : F.ofEquiv E a = F (E.symm a) := by
  cases F <;> rfl

end

/-- The filter represented by a `cfilter` is the collection of supersets of
  elements of the filter base. -/
def toFilter (F : Cfilter (Set α) σ) : Filter α where
  Sets := { a | ∃ b, F b ⊆ a }
  univ_sets := ⟨F.pt, subset_univ _⟩
  sets_of_superset := fun x y ⟨b, h⟩ s => ⟨b, Subset.trans h s⟩
  inter_sets := fun x y ⟨a, h₁⟩ ⟨b, h₂⟩ =>
    ⟨F.inf a b, subset_inter (Subset.trans (F.inf_le_left _ _) h₁) (Subset.trans (F.inf_le_right _ _) h₂)⟩

@[simp]
theorem mem_to_filter_sets (F : Cfilter (Set α) σ) {a : Set α} : a ∈ F.toFilter ↔ ∃ b, F b ⊆ a :=
  Iff.rfl

end Cfilter

/-- A realizer for filter `f` is a cfilter which generates `f`. -/
structure Filter.Realizer (f : Filter α) where
  σ : Type _
  f : Cfilter (Set α) σ
  Eq : F.toFilter = f

protected def Cfilter.toRealizer (F : Cfilter (Set α) σ) : F.toFilter.Realizer :=
  ⟨σ, F, rfl⟩

namespace Filter.Realizer

theorem mem_sets {f : Filter α} (F : f.Realizer) {a : Set α} : a ∈ f ↔ ∃ b, F.f b ⊆ a := by
  cases F <;> subst f <;> simp

-- Used because it has better definitional equalities than the eq.rec proof
def ofEq {f g : Filter α} (e : f = g) (F : f.Realizer) : g.Realizer :=
  ⟨F.σ, F.f, F.Eq.trans e⟩

/-- A filter realizes itself. -/
def ofFilter (f : Filter α) : f.Realizer :=
  ⟨f.Sets,
    { f := Subtype.val, pt := ⟨Univ, univ_mem⟩, inf := fun ⟨x, h₁⟩ ⟨y, h₂⟩ => ⟨_, inter_mem h₁ h₂⟩,
      inf_le_left := fun ⟨x, h₁⟩ ⟨y, h₂⟩ => inter_subset_left x y,
      inf_le_right := fun ⟨x, h₁⟩ ⟨y, h₂⟩ => inter_subset_right x y },
    filter_eq <| Set.ext fun x => SetCoe.exists.trans exists_mem_subset_iff⟩

/-- Transfer a filter realizer to another realizer on a different base type. -/
def ofEquiv {f : Filter α} (F : f.Realizer) (E : F.σ ≃ τ) : f.Realizer :=
  ⟨τ, F.f.ofEquiv E, by
    refine' Eq.trans _ F.eq <;>
      exact
        filter_eq
          (Set.ext fun x =>
            ⟨fun ⟨s, h⟩ =>
              ⟨E.symm s, by
                simpa using h⟩,
              fun ⟨t, h⟩ =>
              ⟨E t, by
                simp [← h]⟩⟩)⟩

@[simp]
theorem of_equiv_σ {f : Filter α} (F : f.Realizer) (E : F.σ ≃ τ) : (F.ofEquiv E).σ = τ :=
  rfl

@[simp]
theorem of_equiv_F {f : Filter α} (F : f.Realizer) (E : F.σ ≃ τ) (s : τ) : (F.ofEquiv E).f s = F.f (E.symm s) := by
  delta' of_equiv <;> simp

/-- `unit` is a realizer for the principal filter -/
protected def principal (s : Set α) : (principal s).Realizer :=
  ⟨Unit,
    { f := fun _ => s, pt := (), inf := fun _ _ => (), inf_le_left := fun _ _ => le_rfl,
      inf_le_right := fun _ _ => le_rfl },
    filter_eq <| Set.ext fun x => ⟨fun ⟨_, s⟩ => s, fun h => ⟨(), h⟩⟩⟩

@[simp]
theorem principal_σ (s : Set α) : (Realizer.principal s).σ = Unit :=
  rfl

@[simp]
theorem principal_F (s : Set α) (u : Unit) : (Realizer.principal s).f u = s :=
  rfl

/-- `unit` is a realizer for the top filter -/
protected def top : (⊤ : Filter α).Realizer :=
  (Realizer.principal _).of_eq principal_univ

@[simp]
theorem top_σ : (@Realizer.top α).σ = Unit :=
  rfl

@[simp]
theorem top_F (u : Unit) : (@Realizer.top α).f u = univ :=
  rfl

/-- `unit` is a realizer for the bottom filter -/
protected def bot : (⊥ : Filter α).Realizer :=
  (Realizer.principal _).of_eq principal_empty

@[simp]
theorem bot_σ : (@Realizer.bot α).σ = Unit :=
  rfl

@[simp]
theorem bot_F (u : Unit) : (@Realizer.bot α).f u = ∅ :=
  rfl

/-- Construct a realizer for `map m f` given a realizer for `f` -/
protected def map (m : α → β) {f : Filter α} (F : f.Realizer) : (map m f).Realizer :=
  ⟨F.σ,
    { f := fun s => Image m (F.f s), pt := F.f.pt, inf := F.f.inf,
      inf_le_left := fun a b => image_subset _ (F.f.inf_le_left _ _),
      inf_le_right := fun a b => image_subset _ (F.f.inf_le_right _ _) },
    filter_eq <|
      Set.ext fun x => by
        simp [← Cfilter.toFilter] <;> rw [F.mem_sets] <;> rfl⟩

@[simp]
theorem map_σ (m : α → β) {f : Filter α} (F : f.Realizer) : (F.map m).σ = F.σ :=
  rfl

@[simp]
theorem map_F (m : α → β) {f : Filter α} (F : f.Realizer) (s) : (F.map m).f s = Image m (F.f s) :=
  rfl

/-- Construct a realizer for `comap m f` given a realizer for `f` -/
protected def comap (m : α → β) {f : Filter β} (F : f.Realizer) : (comap m f).Realizer :=
  ⟨F.σ,
    { f := fun s => Preimage m (F.f s), pt := F.f.pt, inf := F.f.inf,
      inf_le_left := fun a b => preimage_mono (F.f.inf_le_left _ _),
      inf_le_right := fun a b => preimage_mono (F.f.inf_le_right _ _) },
    filter_eq <|
      Set.ext fun x => by
        cases F <;>
          subst f <;>
            simp [← Cfilter.toFilter, ← mem_comap] <;>
              exact
                ⟨fun ⟨s, h⟩ => ⟨_, ⟨s, subset.refl _⟩, h⟩, fun ⟨y, ⟨s, h⟩, h₂⟩ =>
                  ⟨s, subset.trans (preimage_mono h) h₂⟩⟩⟩

/-- Construct a realizer for the sup of two filters -/
protected def sup {f g : Filter α} (F : f.Realizer) (G : g.Realizer) : (f⊔g).Realizer :=
  ⟨F.σ × G.σ,
    { f := fun ⟨s, t⟩ => F.f s ∪ G.f t, pt := (F.f.pt, G.f.pt),
      inf := fun ⟨a, a'⟩ ⟨b, b'⟩ => (F.f.inf a b, G.f.inf a' b'),
      inf_le_left := fun ⟨a, a'⟩ ⟨b, b'⟩ => union_subset_union (F.f.inf_le_left _ _) (G.f.inf_le_left _ _),
      inf_le_right := fun ⟨a, a'⟩ ⟨b, b'⟩ => union_subset_union (F.f.inf_le_right _ _) (G.f.inf_le_right _ _) },
    filter_eq <|
      Set.ext fun x => by
        cases F <;>
          cases G <;>
            substs f g <;>
              simp [← Cfilter.toFilter] <;>
                exact
                  ⟨fun ⟨s, t, h⟩ =>
                    ⟨⟨s, subset.trans (subset_union_left _ _) h⟩, ⟨t, subset.trans (subset_union_right _ _) h⟩⟩,
                    fun ⟨⟨s, h₁⟩, ⟨t, h₂⟩⟩ => ⟨s, t, union_subset h₁ h₂⟩⟩⟩

/-- Construct a realizer for the inf of two filters -/
protected def inf {f g : Filter α} (F : f.Realizer) (G : g.Realizer) : (f⊓g).Realizer :=
  ⟨F.σ × G.σ,
    { f := fun ⟨s, t⟩ => F.f s ∩ G.f t, pt := (F.f.pt, G.f.pt),
      inf := fun ⟨a, a'⟩ ⟨b, b'⟩ => (F.f.inf a b, G.f.inf a' b'),
      inf_le_left := fun ⟨a, a'⟩ ⟨b, b'⟩ => inter_subset_inter (F.f.inf_le_left _ _) (G.f.inf_le_left _ _),
      inf_le_right := fun ⟨a, a'⟩ ⟨b, b'⟩ => inter_subset_inter (F.f.inf_le_right _ _) (G.f.inf_le_right _ _) },
    by
    ext x
    cases F <;> cases G <;> substs f g <;> simp [← Cfilter.toFilter]
    constructor
    · rintro ⟨s : F_σ, t : G_σ, h⟩
      apply mem_inf_of_inter _ _ h
      use s
      use t
      
    · rintro ⟨s, ⟨a, ha⟩, t, ⟨b, hb⟩, rfl⟩
      exact ⟨a, b, inter_subset_inter ha hb⟩
      ⟩

/-- Construct a realizer for the cofinite filter -/
protected def cofinite [DecidableEq α] : (@cofinite α).Realizer :=
  ⟨Finset α,
    { f := fun s => { a | a ∉ s }, pt := ∅, inf := (· ∪ ·), inf_le_left := fun s t a => mt (Finset.mem_union_left _),
      inf_le_right := fun s t a => mt (Finset.mem_union_right _) },
    filter_eq <|
      Set.ext fun x =>
        ⟨fun ⟨s, h⟩ => s.finite_to_set.Subset (compl_subset_comm.1 h), fun h =>
          ⟨h.toFinset, by
            simp ⟩⟩⟩

/-- Construct a realizer for filter bind -/
protected def bind {f : Filter α} {m : α → Filter β} (F : f.Realizer) (G : ∀ i, (m i).Realizer) : (f.bind m).Realizer :=
  ⟨Σs : F.σ, ∀, ∀ i ∈ F.f s, ∀, (G i).σ,
    { f := fun ⟨s, f⟩ => ⋃ i ∈ F.f s, (G i).f (f i H), pt := ⟨F.f.pt, fun i H => (G i).f.pt⟩,
      inf := fun ⟨a, f⟩ ⟨b, f'⟩ =>
        ⟨F.f.inf a b, fun i h => (G i).f.inf (f i (F.f.inf_le_left _ _ h)) (f' i (F.f.inf_le_right _ _ h))⟩,
      inf_le_left := fun ⟨a, f⟩ ⟨b, f'⟩ x =>
        show (x ∈ ⋃ (i : α) (H : i ∈ F.f (F.f.inf a b)), _) → x ∈ ⋃ (i) (H : i ∈ F.f a), (G i).f (f i H) by
          simp <;> exact fun i h₁ h₂ => ⟨i, F.F.inf_le_left _ _ h₁, (G i).f.inf_le_left _ _ h₂⟩,
      inf_le_right := fun ⟨a, f⟩ ⟨b, f'⟩ x =>
        show (x ∈ ⋃ (i : α) (H : i ∈ F.f (F.f.inf a b)), _) → x ∈ ⋃ (i) (H : i ∈ F.f b), (G i).f (f' i H) by
          simp <;> exact fun i h₁ h₂ => ⟨i, F.F.inf_le_right _ _ h₁, (G i).f.inf_le_right _ _ h₂⟩ },
    filter_eq <|
      Set.ext fun x => by
        cases' F with _ F _ <;>
          subst f <;>
            simp [← Cfilter.toFilter, ← mem_bind] <;>
              exact
                ⟨fun ⟨s, f, h⟩ =>
                  ⟨F s, ⟨s, subset.refl _⟩, fun i H =>
                    (G i).mem_sets.2 ⟨f i H, fun a h' => h ⟨_, ⟨i, rfl⟩, _, ⟨H, rfl⟩, h'⟩⟩⟩,
                  fun ⟨y, ⟨s, h⟩, f⟩ =>
                  let ⟨f', h'⟩ := Classical.axiom_of_choice fun i : F s => (G i).mem_sets.1 (f i (h i.2))
                  ⟨s, fun i h => f' ⟨i, h⟩, fun a ⟨_, ⟨i, rfl⟩, _, ⟨H, rfl⟩, m⟩ => h' ⟨_, H⟩ m⟩⟩⟩

/-- Construct a realizer for indexed supremum -/
protected def supₓ {f : α → Filter β} (F : ∀ i, (f i).Realizer) : (⨆ i, f i).Realizer :=
  let F' : (⨆ i, f i).Realizer :=
    (Realizer.bind Realizer.top F).of_eq <|
      filter_eq <|
        Set.ext <| by
          simp [← Filter.bind, ← eq_univ_iff_forall, ← supr_sets_eq]
  F'.ofEquiv <|
    show (Σu : Unit, ∀ i : α, True → (F i).σ) ≃ ∀ i, (F i).σ from
      ⟨fun ⟨_, f⟩ i => f i ⟨⟩, fun f => ⟨(), fun i _ => f i⟩, fun ⟨⟨⟩, f⟩ => by
        dsimp' <;> congr <;> simp , fun f => rfl⟩

/-- Construct a realizer for the product of filters -/
protected def prod {f g : Filter α} (F : f.Realizer) (G : g.Realizer) : (f.Prod g).Realizer :=
  (F.comap _).inf (G.comap _)

theorem le_iff {f g : Filter α} (F : f.Realizer) (G : g.Realizer) : f ≤ g ↔ ∀ b : G.σ, ∃ a : F.σ, F.f a ≤ G.f b :=
  ⟨fun H t => F.mem_sets.1 (H (G.mem_sets.2 ⟨t, Subset.refl _⟩)), fun H x h =>
    F.mem_sets.2 <|
      let ⟨s, h₁⟩ := G.mem_sets.1 h
      let ⟨t, h₂⟩ := H s
      ⟨t, Subset.trans h₂ h₁⟩⟩

theorem tendsto_iff (f : α → β) {l₁ : Filter α} {l₂ : Filter β} (L₁ : l₁.Realizer) (L₂ : l₂.Realizer) :
    Tendsto f l₁ l₂ ↔ ∀ b, ∃ a, ∀, ∀ x ∈ L₁.f a, ∀, f x ∈ L₂.f b :=
  (le_iff (L₁.map f) L₂).trans <| forall_congrₓ fun b => exists_congr fun a => image_subset_iff

theorem ne_bot_iff {f : Filter α} (F : f.Realizer) : f ≠ ⊥ ↔ ∀ a : F.σ, (F.f a).Nonempty := by
  classical
  rw [not_iff_comm, ← le_bot_iff, F.le_iff realizer.bot, not_forall]
  simp only [← Set.not_nonempty_iff_eq_empty]
  exact
    ⟨fun ⟨x, e⟩ _ => ⟨x, le_of_eqₓ e⟩, fun h =>
      let ⟨x, h⟩ := h ()
      ⟨x, le_bot_iff.1 h⟩⟩

end Filter.Realizer


/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
import Mathbin.Control.Traversable.Instances
import Mathbin.Data.Set.Finite
import Mathbin.Order.Copy
import Mathbin.Tactic.Monotonicity.Default

/-!
# Theory of filters on sets

## Main definitions

* `filter` : filters on a set;
* `at_top`, `at_bot`, `cofinite`, `principal` : specific filters;
* `map`, `comap`, `prod` : operations on filters;
* `tendsto` : limit with respect to filters;
* `eventually` : `f.eventually p` means `{x | p x} ∈ f`;
* `frequently` : `f.frequently p` means `{x | ¬p x} ∉ f`;
* `filter_upwards [h₁, ..., hₙ]` : takes a list of proofs `hᵢ : sᵢ ∈ f`, and replaces a goal `s ∈ f`
  with `∀ x, x ∈ s₁ → ... → x ∈ sₙ → x ∈ s`;
* `ne_bot f` : an utility class stating that `f` is a non-trivial filter.

Filters on a type `X` are sets of sets of `X` satisfying three conditions. They are mostly used to
abstract two related kinds of ideas:
* *limits*, including finite or infinite limits of sequences, finite or infinite limits of functions
  at a point or at infinity, etc...
* *things happening eventually*, including things happening for large enough `n : ℕ`, or near enough
  a point `x`, or for close enough pairs of points, or things happening almost everywhere in the
  sense of measure theory. Dually, filters can also express the idea of *things happening often*:
  for arbitrarily large `n`, or at a point in any neighborhood of given a point etc...

In this file, we define the type `filter X` of filters on `X`, and endow it with a complete lattice
structure. This structure is lifted from the lattice structure on `set (set X)` using the Galois
insertion which maps a filter to its elements in one direction, and an arbitrary set of sets to
the smallest filter containing it in the other direction.
We also prove `filter` is a monadic functor, with a push-forward operation
`filter.map` and a pull-back operation `filter.comap` that form a Galois connections for the
order on filters.
Finally we describe a product operation `filter X → filter Y → filter (X × Y)`.

The examples of filters appearing in the description of the two motivating ideas are:
* `(at_top : filter ℕ)` : made of sets of `ℕ` containing `{n | n ≥ N}` for some `N`
* `𝓝 x` : made of neighborhoods of `x` in a topological space (defined in topology.basic)
* `𝓤 X` : made of entourages of a uniform space (those space are generalizations of metric spaces
  defined in topology.uniform_space.basic)
* `μ.ae` : made of sets whose complement has zero measure with respect to `μ` (defined in
  `measure_theory.measure_space`)

The general notion of limit of a map with respect to filters on the source and target types
is `filter.tendsto`. It is defined in terms of the order and the push-forward operation.
The predicate "happening eventually" is `filter.eventually`, and "happening often" is
`filter.frequently`, whose definitions are immediate after `filter` is defined (but they come
rather late in this file in order to immediately relate them to the lattice structure).

For instance, anticipating on topology.basic, the statement: "if a sequence `u` converges to
some `x` and `u n` belongs to a set `M` for `n` large enough then `x` is in the closure of
`M`" is formalized as: `tendsto u at_top (𝓝 x) → (∀ᶠ n in at_top, u n ∈ M) → x ∈ closure M`,
which is a special case of `mem_closure_of_tendsto` from topology.basic.

## Notations

* `∀ᶠ x in f, p x` : `f.eventually p`;
* `∃ᶠ x in f, p x` : `f.frequently p`;
* `f =ᶠ[l] g` : `∀ᶠ x in l, f x = g x`;
* `f ≤ᶠ[l] g` : `∀ᶠ x in l, f x ≤ g x`;
* `f ×ᶠ g` : `filter.prod f g`, localized in `filter`;
* `𝓟 s` : `principal s`, localized in `filter`.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]

Important note: Bourbaki requires that a filter on `X` cannot contain all sets of `X`, which
we do *not* require. This gives `filter X` better formal properties, in particular a bottom element
`⊥` for its lattice structure, at the cost of including the assumption
`[ne_bot f]` in a number of lemmas and definitions.
-/


open Function Set Order

universe u v w x y

open Classical

/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α`. -/
structure Filter (α : Type _) where
  Sets : Set (Set α)
  univ_sets : Set.Univ ∈ sets
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets

/-- If `F` is a filter on `α`, and `U` a subset of `α` then we can write `U ∈ F` as on paper. -/
instance {α : Type _} : HasMem (Set α) (Filter α) :=
  ⟨fun U F => U ∈ F.Sets⟩

namespace Filter

variable {α : Type u} {f g : Filter α} {s t : Set α}

@[simp]
protected theorem mem_mk {t : Set (Set α)} {h₁ h₂ h₃} : s ∈ mk t h₁ h₂ h₃ ↔ s ∈ t :=
  Iff.rfl

@[simp]
protected theorem mem_sets : s ∈ f.Sets ↔ s ∈ f :=
  Iff.rfl

instance inhabitedMem : Inhabited { s : Set α // s ∈ f } :=
  ⟨⟨Univ, f.univ_sets⟩⟩

theorem filter_eq : ∀ {f g : Filter α}, f.Sets = g.Sets → f = g
  | ⟨a, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

theorem filter_eq_iff : f = g ↔ f.Sets = g.Sets :=
  ⟨congr_arg _, filter_eq⟩

protected theorem ext_iff : f = g ↔ ∀ s, s ∈ f ↔ s ∈ g := by
  simp only [← filter_eq_iff, ← ext_iff, ← Filter.mem_sets]

@[ext]
protected theorem ext : (∀ s, s ∈ f ↔ s ∈ g) → f = g :=
  Filter.ext_iff.2

/-- An extensionality lemma that is useful for filters with good lemmas about `sᶜ ∈ f` (e.g.,
`filter.comap`, `filter.coprod`, `filter.Coprod`, `filter.cofinite`). -/
protected theorem coext (h : ∀ s, sᶜ ∈ f ↔ sᶜ ∈ g) : f = g :=
  Filter.ext <| compl_surjective.forall.2 h

@[simp]
theorem univ_mem : univ ∈ f :=
  f.univ_sets

theorem mem_of_superset {x y : Set α} (hx : x ∈ f) (hxy : x ⊆ y) : y ∈ f :=
  f.sets_of_superset hx hxy

theorem inter_mem {s t : Set α} (hs : s ∈ f) (ht : t ∈ f) : s ∩ t ∈ f :=
  f.inter_sets hs ht

@[simp]
theorem inter_mem_iff {s t : Set α} : s ∩ t ∈ f ↔ s ∈ f ∧ t ∈ f :=
  ⟨fun h => ⟨mem_of_superset h (inter_subset_left s t), mem_of_superset h (inter_subset_right s t)⟩,
    and_imp.2 inter_mem⟩

theorem diff_mem {s t : Set α} (hs : s ∈ f) (ht : tᶜ ∈ f) : s \ t ∈ f :=
  inter_mem hs ht

theorem univ_mem' (h : ∀ a, a ∈ s) : s ∈ f :=
  mem_of_superset univ_mem fun x _ => h x

theorem mp_mem (hs : s ∈ f) (h : { x | x ∈ s → x ∈ t } ∈ f) : t ∈ f :=
  (mem_of_superset (inter_mem hs h)) fun x ⟨h₁, h₂⟩ => h₂ h₁

theorem congr_sets (h : { x | x ∈ s ↔ x ∈ t } ∈ f) : s ∈ f ↔ t ∈ f :=
  ⟨fun hs => mp_mem hs (mem_of_superset h fun x => Iff.mp), fun hs => mp_mem hs (mem_of_superset h fun x => Iff.mpr)⟩

@[simp]
theorem bInter_mem {β : Type v} {s : β → Set α} {is : Set β} (hf : is.Finite) :
    (⋂ i ∈ is, s i) ∈ f ↔ ∀, ∀ i ∈ is, ∀, s i ∈ f :=
  Finite.induction_on hf
    (by
      simp )
    fun i s hi _ hs => by
    simp [← hs]

@[simp]
theorem bInter_finset_mem {β : Type v} {s : β → Set α} (is : Finset β) :
    (⋂ i ∈ is, s i) ∈ f ↔ ∀, ∀ i ∈ is, ∀, s i ∈ f :=
  bInter_mem is.finite_to_set

alias bInter_finset_mem ← _root_.finset.Inter_mem_sets

attribute [protected] Finset.Inter_mem_sets

@[simp]
theorem sInter_mem {s : Set (Set α)} (hfin : s.Finite) : ⋂₀ s ∈ f ↔ ∀, ∀ U ∈ s, ∀, U ∈ f := by
  rw [sInter_eq_bInter, bInter_mem hfin]

@[simp]
theorem Inter_mem {β : Type v} {s : β → Set α} [Fintype β] : (⋂ i, s i) ∈ f ↔ ∀ i, s i ∈ f := by
  simpa using bInter_mem finite_univ

theorem exists_mem_subset_iff : (∃ t ∈ f, t ⊆ s) ↔ s ∈ f :=
  ⟨fun ⟨t, ht, ts⟩ => mem_of_superset ht ts, fun hs => ⟨s, hs, Subset.rfl⟩⟩

theorem monotone_mem {f : Filter α} : Monotone fun s => s ∈ f := fun s t hst h => mem_of_superset h hst

theorem exists_mem_and_iff {P : Set α → Prop} {Q : Set α → Prop} (hP : Antitone P) (hQ : Antitone Q) :
    ((∃ u ∈ f, P u) ∧ ∃ u ∈ f, Q u) ↔ ∃ u ∈ f, P u ∧ Q u := by
  constructor
  · rintro ⟨⟨u, huf, hPu⟩, v, hvf, hQv⟩
    exact ⟨u ∩ v, inter_mem huf hvf, hP (inter_subset_left _ _) hPu, hQ (inter_subset_right _ _) hQv⟩
    
  · rintro ⟨u, huf, hPu, hQu⟩
    exact ⟨⟨u, huf, hPu⟩, u, huf, hQu⟩
    

theorem forall_in_swap {β : Type _} {p : Set α → β → Prop} : (∀, ∀ a ∈ f, ∀ (b), p a b) ↔ ∀ (b), ∀ a ∈ f, ∀, p a b :=
  Set.forall_in_swap

end Filter

namespace Tactic.Interactive

open Tactic

setup_tactic_parser

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- `filter_upwards [h₁, ⋯, hₙ]` replaces a goal of the form `s ∈ f` and terms
`h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` with `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`.
The list is an optional parameter, `[]` being its default value.

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` is a short form for
`{ filter_upwards [h₁, ⋯, hₙ], intros a₁ a₂ ⋯ aₖ }`.

`filter_upwards [h₁, ⋯, hₙ] using e` is a short form for
`{ filter_upwards [h1, ⋯, hn], exact e }`.

Combining both shortcuts is done by writing `filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`.
Note that in this case, the `aᵢ` terms can be used in `e`.
-/
unsafe def filter_upwards (s : parse types.pexpr_list ?) (wth : parse with_ident_list ?)
    (tgt : parse (tk "using" *> texpr)?) : tactic Unit := do
  (s []).reverse.mmap fun e => eapplyc `filter.mp_mem >> eapply e
  eapplyc `filter.univ_mem'
  sorry
  let wth := wth.getOrElse []
  if ¬wth then intros wth else skip
  match tgt with
    | some e => exact e
    | none => skip

add_tactic_doc
  { Name := "filter_upwards", category := DocCategory.tactic, declNames := [`tactic.interactive.filter_upwards],
    tags := ["goal management", "lemma application"] }

end Tactic.Interactive

namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type _} {ι : Sort x}

section Principal

/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : Set α) : Filter α where
  Sets := { t | s ⊆ t }
  univ_sets := subset_univ s
  sets_of_superset := fun x y hx => Subset.trans hx
  inter_sets := fun x y => subset_inter

-- mathport name: «expr𝓟»
localized [Filter] notation "𝓟" => Filter.principal

instance : Inhabited (Filter α) :=
  ⟨𝓟 ∅⟩

@[simp]
theorem mem_principal {s t : Set α} : s ∈ 𝓟 t ↔ t ⊆ s :=
  Iff.rfl

theorem mem_principal_self (s : Set α) : s ∈ 𝓟 s :=
  subset.rfl

end Principal

open Filter

section Join

/-- The join of a filter of filters is defined by the relation `s ∈ join f ↔ {t | s ∈ t} ∈ f`. -/
def join (f : Filter (Filter α)) : Filter α where
  Sets := { s | { t : Filter α | s ∈ t } ∈ f }
  univ_sets := by
    simp only [← mem_set_of_eq, ← univ_sets, Filter.mem_sets, ← set_of_true]
  sets_of_superset := fun x y hx xy => (mem_of_superset hx) fun f h => mem_of_superset h xy
  inter_sets := fun x y hx hy => (mem_of_superset (inter_mem hx hy)) fun f ⟨h₁, h₂⟩ => inter_mem h₁ h₂

@[simp]
theorem mem_join {s : Set α} {f : Filter (Filter α)} : s ∈ join f ↔ { t | s ∈ t } ∈ f :=
  Iff.rfl

end Join

section Lattice

variable {f g : Filter α} {s t : Set α}

instance : PartialOrderₓ (Filter α) where
  le := fun f g => ∀ ⦃U : Set α⦄, U ∈ g → U ∈ f
  le_antisymm := fun a b h₁ h₂ => filter_eq <| Subset.antisymm h₂ h₁
  le_refl := fun a => Subset.rfl
  le_trans := fun a b c h₁ h₂ => Subset.trans h₂ h₁

theorem le_def : f ≤ g ↔ ∀, ∀ x ∈ g, ∀, x ∈ f :=
  Iff.rfl

protected theorem not_le : ¬f ≤ g ↔ ∃ s ∈ g, s ∉ f := by
  simp_rw [le_def, not_forall]

/-- `generate_sets g s`: `s` is in the filter closure of `g`. -/
inductive GenerateSets (g : Set (Set α)) : Set α → Prop
  | basic {s : Set α} : s ∈ g → generate_sets s
  | univ : generate_sets Univ
  | Superset {s t : Set α} : generate_sets s → s ⊆ t → generate_sets t
  | inter {s t : Set α} : generate_sets s → generate_sets t → generate_sets (s ∩ t)

/-- `generate g` is the largest filter containing the sets `g`. -/
def generate (g : Set (Set α)) : Filter α where
  Sets := GenerateSets g
  univ_sets := GenerateSets.univ
  sets_of_superset := fun x y => GenerateSets.superset
  inter_sets := fun s t => GenerateSets.inter

theorem sets_iff_generate {s : Set (Set α)} {f : Filter α} : f ≤ Filter.generate s ↔ s ⊆ f.Sets :=
  Iff.intro (fun h u hu => h <| generate_sets.basic <| hu) fun h u hu =>
    hu.recOn h univ_mem (fun x y _ hxy hx => mem_of_superset hx hxy) fun x y _ _ hx hy => inter_mem hx hy

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem mem_generate_iff {s : Set <| Set α} {U : Set α} :
    U ∈ generate s ↔ ∃ (t : _)(_ : t ⊆ s), Set.Finite t ∧ ⋂₀ t ⊆ U := by
  constructor <;> intro h
  · induction h
    case basic V V_in =>
      exact ⟨{V}, singleton_subset_iff.2 V_in, finite_singleton _, (sInter_singleton _).Subset⟩
    case univ =>
      exact ⟨∅, empty_subset _, finite_empty, subset_univ _⟩
    case superset V W hV' hVW hV =>
      rcases hV with ⟨t, hts, ht, htV⟩
      exact ⟨t, hts, ht, htV.trans hVW⟩
    case inter V W hV' hW' hV hW =>
      rcases hV, hW with ⟨⟨t, hts, ht, htV⟩, u, hus, hu, huW⟩
      exact ⟨t ∪ u, union_subset hts hus, ht.union hu, (sInter_union _ _).Subset.trans <| inter_subset_inter htV huW⟩
    
  · rcases h with ⟨t, hts, tfin, h⟩
    exact mem_of_superset ((sInter_mem tfin).2 fun V hV => generate_sets.basic <| hts hV) h
    

/-- `mk_of_closure s hs` constructs a filter on `α` whose elements set is exactly
`s : set (set α)`, provided one gives the assumption `hs : (generate s).sets = s`. -/
protected def mkOfClosure (s : Set (Set α)) (hs : (generate s).Sets = s) : Filter α where
  Sets := s
  univ_sets := hs ▸ (univ_mem : univ ∈ generate s)
  sets_of_superset := fun x y => hs ▸ (mem_of_superset : x ∈ generate s → x ⊆ y → y ∈ generate s)
  inter_sets := fun x y => hs ▸ (inter_mem : x ∈ generate s → y ∈ generate s → x ∩ y ∈ generate s)

theorem mk_of_closure_sets {s : Set (Set α)} {hs : (generate s).Sets = s} : Filter.mkOfClosure s hs = generate s :=
  Filter.ext fun u => show u ∈ (Filter.mkOfClosure s hs).Sets ↔ u ∈ (generate s).Sets from hs.symm ▸ Iff.rfl

/-- Galois insertion from sets of sets into filters. -/
def giGenerate (α : Type _) : @GaloisInsertion (Set (Set α)) (Filter α)ᵒᵈ _ _ Filter.generate Filter.Sets where
  gc := fun s f => sets_iff_generate
  le_l_u := fun f u h => GenerateSets.basic h
  choice := fun s hs => Filter.mkOfClosure s (le_antisymmₓ hs <| sets_iff_generate.1 <| le_rfl)
  choice_eq := fun s hs => mk_of_closure_sets

/-- The infimum of filters is the filter generated by intersections
  of elements of the two filters. -/
instance : HasInf (Filter α) :=
  ⟨fun f g : Filter α =>
    { Sets := { s | ∃ a ∈ f, ∃ b ∈ g, s = a ∩ b },
      univ_sets :=
        ⟨_, univ_mem, _, univ_mem, by
          simp ⟩,
      sets_of_superset := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ xy
        refine'
          ⟨a ∪ y, mem_of_superset ha (subset_union_left a y), b ∪ y, mem_of_superset hb (subset_union_left b y), _⟩
        rw [← inter_union_distrib_right, union_eq_self_of_subset_left xy],
      inter_sets := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        refine' ⟨a ∩ c, inter_mem ha hc, b ∩ d, inter_mem hb hd, _⟩
        ac_rfl }⟩

theorem mem_inf_iff {f g : Filter α} {s : Set α} : s ∈ f⊓g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, s = t₁ ∩ t₂ :=
  Iff.rfl

theorem mem_inf_of_left {f g : Filter α} {s : Set α} (h : s ∈ f) : s ∈ f⊓g :=
  ⟨s, h, Univ, univ_mem, (inter_univ s).symm⟩

theorem mem_inf_of_right {f g : Filter α} {s : Set α} (h : s ∈ g) : s ∈ f⊓g :=
  ⟨Univ, univ_mem, s, h, (univ_inter s).symm⟩

theorem inter_mem_inf {α : Type u} {f g : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ g) : s ∩ t ∈ f⊓g :=
  ⟨s, hs, t, ht, rfl⟩

theorem mem_inf_of_inter {f g : Filter α} {s t u : Set α} (hs : s ∈ f) (ht : t ∈ g) (h : s ∩ t ⊆ u) : u ∈ f⊓g :=
  mem_of_superset (inter_mem_inf hs ht) h

theorem mem_inf_iff_superset {f g : Filter α} {s : Set α} : s ∈ f⊓g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ∩ t₂ ⊆ s :=
  ⟨fun ⟨t₁, h₁, t₂, h₂, Eq⟩ => ⟨t₁, h₁, t₂, h₂, Eq ▸ subset.rfl⟩, fun ⟨t₁, h₁, t₂, h₂, sub⟩ =>
    mem_inf_of_inter h₁ h₂ sub⟩

instance : HasTop (Filter α) :=
  ⟨{ Sets := { s | ∀ x, x ∈ s }, univ_sets := fun x => mem_univ x, sets_of_superset := fun x y hx hxy a => hxy (hx a),
      inter_sets := fun x y hx hy a => mem_inter (hx _) (hy _) }⟩

theorem mem_top_iff_forall {s : Set α} : s ∈ (⊤ : Filter α) ↔ ∀ x, x ∈ s :=
  Iff.rfl

@[simp]
theorem mem_top {s : Set α} : s ∈ (⊤ : Filter α) ↔ s = univ := by
  rw [mem_top_iff_forall, eq_univ_iff_forall]

section CompleteLattice

/- We lift the complete lattice along the Galois connection `generate` / `sets`. Unfortunately,
  we want to have different definitional equalities for the lattice operations. So we define them
  upfront and change the lattice operations for the complete lattice instance. -/
private def original_complete_lattice : CompleteLattice (Filter α) :=
  @OrderDual.completeLattice _ (giGenerate α).liftCompleteLattice

attribute [local instance] original_complete_lattice

instance : CompleteLattice (Filter α) :=
  originalCompleteLattice.copy-- le
      Filter.partialOrder.le
    rfl-- top
      Filter.hasTop.1
    (top_unique fun s hs => by
      simp [← mem_top.1 hs])-- bot
    _
    rfl-- sup
    _
    rfl-- inf
      Filter.hasInf.1
    (by
      ext f g : 2
      exact
        le_antisymmₓ (le_inf (fun s => mem_inf_of_left) fun s => mem_inf_of_right)
          (by
            rintro s ⟨a, ha, b, hb, rfl⟩
            exact inter_sets _ (@inf_le_left (Filter α) _ _ _ _ ha) (@inf_le_right (Filter α) _ _ _ _ hb)))
    (-- Sup
      join ∘
      𝓟)
    (by
      ext s x
      exact mem_Inter₂.symm.trans (Set.ext_iff.1 (sInter_image _ _) x).symm)-- Inf
    _
    rfl

end CompleteLattice

/-- A filter is `ne_bot` if it is not equal to `⊥`, or equivalently the empty set
does not belong to the filter. Bourbaki include this assumption in the definition
of a filter but we prefer to have a `complete_lattice` structure on filter, so
we use a typeclass argument in lemmas instead. -/
class NeBot (f : Filter α) : Prop where
  ne' : f ≠ ⊥

theorem ne_bot_iff {f : Filter α} : NeBot f ↔ f ≠ ⊥ :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem NeBot.ne {f : Filter α} (hf : NeBot f) : f ≠ ⊥ :=
  ne_bot.ne'

@[simp]
theorem not_ne_bot {α : Type _} {f : Filter α} : ¬f.ne_bot ↔ f = ⊥ :=
  not_iff_comm.1 ne_bot_iff.symm

theorem NeBot.mono {f g : Filter α} (hf : NeBot f) (hg : f ≤ g) : NeBot g :=
  ⟨ne_bot_of_le_ne_bot hf.1 hg⟩

theorem ne_bot_of_le {f g : Filter α} [hf : NeBot f] (hg : f ≤ g) : NeBot g :=
  hf.mono hg

@[simp]
theorem sup_ne_bot {f g : Filter α} : NeBot (f⊔g) ↔ NeBot f ∨ NeBot g := by
  simp [← ne_bot_iff, ← not_and_distrib]

theorem not_disjoint_self_iff : ¬Disjoint f f ↔ f.ne_bot := by
  rw [disjoint_self, ne_bot_iff]

theorem bot_sets_eq : (⊥ : Filter α).Sets = univ :=
  rfl

theorem sup_sets_eq {f g : Filter α} : (f⊔g).Sets = f.Sets ∩ g.Sets :=
  (giGenerate α).gc.u_inf

theorem Sup_sets_eq {s : Set (Filter α)} : (sup s).Sets = ⋂ f ∈ s, (f : Filter α).Sets :=
  (giGenerate α).gc.u_Inf

theorem supr_sets_eq {f : ι → Filter α} : (supr f).Sets = ⋂ i, (f i).Sets :=
  (giGenerate α).gc.u_infi

theorem generate_empty : Filter.generate ∅ = (⊤ : Filter α) :=
  (giGenerate α).gc.l_bot

theorem generate_univ : Filter.generate Univ = (⊥ : Filter α) :=
  mk_of_closure_sets.symm

theorem generate_union {s t : Set (Set α)} : Filter.generate (s ∪ t) = Filter.generate s⊓Filter.generate t :=
  (giGenerate α).gc.l_sup

theorem generate_Union {s : ι → Set (Set α)} : Filter.generate (⋃ i, s i) = ⨅ i, Filter.generate (s i) :=
  (giGenerate α).gc.l_supr

@[simp]
theorem mem_bot {s : Set α} : s ∈ (⊥ : Filter α) :=
  trivialₓ

@[simp]
theorem mem_sup {f g : Filter α} {s : Set α} : s ∈ f⊔g ↔ s ∈ f ∧ s ∈ g :=
  Iff.rfl

theorem union_mem_sup {f g : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ g) : s ∪ t ∈ f⊔g :=
  ⟨mem_of_superset hs (subset_union_left s t), mem_of_superset ht (subset_union_right s t)⟩

@[simp]
theorem mem_Sup {x : Set α} {s : Set (Filter α)} : x ∈ sup s ↔ ∀, ∀ f ∈ s, ∀, x ∈ (f : Filter α) :=
  Iff.rfl

@[simp]
theorem mem_supr {x : Set α} {f : ι → Filter α} : x ∈ supr f ↔ ∀ i, x ∈ f i := by
  simp only [Filter.mem_sets, ← supr_sets_eq, ← iff_selfₓ, ← mem_Inter]

@[simp]
theorem supr_ne_bot {f : ι → Filter α} : (⨆ i, f i).ne_bot ↔ ∃ i, (f i).ne_bot := by
  simp [← ne_bot_iff]

theorem infi_eq_generate (s : ι → Filter α) : infi s = generate (⋃ i, (s i).Sets) :=
  show generate _ = generate _ from congr_arg _ <| congr_arg sup <| (range_comp _ _).symm

theorem mem_infi_of_mem {f : ι → Filter α} (i : ι) : ∀ {s}, s ∈ f i → s ∈ ⨅ i, f i :=
  show (⨅ i, f i) ≤ f i from infi_le _ _

theorem mem_infi_of_Inter {ι} {s : ι → Filter α} {U : Set α} {I : Set ι} (I_fin : I.Finite) {V : I → Set α}
    (hV : ∀ i, V i ∈ s i) (hU : (⋂ i, V i) ⊆ U) : U ∈ ⨅ i, s i := by
  have := I_fin.fintype
  refine' mem_of_superset (Inter_mem.2 fun i => _) hU
  exact mem_infi_of_mem i (hV _)

theorem mem_infi {ι} {s : ι → Filter α} {U : Set α} :
    (U ∈ ⨅ i, s i) ↔ ∃ I : Set ι, I.Finite ∧ ∃ V : I → Set α, (∀ i, V i ∈ s i) ∧ U = ⋂ i, V i := by
  constructor
  · rw [infi_eq_generate, mem_generate_iff]
    rintro ⟨t, tsub, tfin, tinter⟩
    rcases eq_finite_Union_of_finite_subset_Union tfin tsub with ⟨I, Ifin, σ, σfin, σsub, rfl⟩
    rw [sInter_Union] at tinter
    set V := fun i => U ∪ ⋂₀ σ i with hV
    have V_in : ∀ i, V i ∈ s i := by
      rintro i
      have : ⋂₀ σ i ∈ s i := by
        rw [sInter_mem (σfin _)]
        apply σsub
      exact mem_of_superset this (subset_union_right _ _)
    refine' ⟨I, Ifin, V, V_in, _⟩
    rwa [hV, ← union_Inter, union_eq_self_of_subset_right]
    
  · rintro ⟨I, Ifin, V, V_in, rfl⟩
    exact mem_infi_of_Inter Ifin V_in subset.rfl
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i «expr ∉ » I)
theorem mem_infi' {ι} {s : ι → Filter α} {U : Set α} :
    (U ∈ ⨅ i, s i) ↔
      ∃ I : Set ι,
        I.Finite ∧
          ∃ V : ι → Set α, (∀ i, V i ∈ s i) ∧ (∀ (i) (_ : i ∉ I), V i = univ) ∧ (U = ⋂ i ∈ I, V i) ∧ U = ⋂ i, V i :=
  by
  simp only [← mem_infi, ← SetCoe.forall', ← bInter_eq_Inter]
  refine' ⟨_, fun ⟨I, If, V, hVs, _, hVU, _⟩ => ⟨I, If, fun i => V i, fun i => hVs i, hVU⟩⟩
  rintro ⟨I, If, V, hV, rfl⟩
  refine' ⟨I, If, fun i => if hi : i ∈ I then V ⟨i, hi⟩ else univ, fun i => _, fun i hi => _, _⟩
  · split_ifs
    exacts[hV _, univ_mem]
    
  · exact dif_neg hi
    
  · simp only [← Inter_dite, ← bInter_eq_Inter, ← dif_pos (Subtype.coe_prop _), ← Subtype.coe_eta, ← Inter_univ, ←
      inter_univ, ← eq_self_iff_true, ← true_andₓ]
    

theorem exists_Inter_of_mem_infi {ι : Type _} {α : Type _} {f : ι → Filter α} {s} (hs : s ∈ ⨅ i, f i) :
    ∃ t : ι → Set α, (∀ i, t i ∈ f i) ∧ s = ⋂ i, t i :=
  let ⟨I, If, V, hVs, hV', hVU, hVU'⟩ := mem_infi'.1 hs
  ⟨V, hVs, hVU'⟩

theorem mem_infi_of_fintype {ι : Type _} [Fintype ι] {α : Type _} {f : ι → Filter α} (s) :
    (s ∈ ⨅ i, f i) ↔ ∃ t : ι → Set α, (∀ i, t i ∈ f i) ∧ s = ⋂ i, t i := by
  refine' ⟨exists_Inter_of_mem_infi, _⟩
  rintro ⟨t, ht, rfl⟩
  exact Inter_mem.2 fun i => mem_infi_of_mem i (ht i)

@[simp]
theorem le_principal_iff {s : Set α} {f : Filter α} : f ≤ 𝓟 s ↔ s ∈ f :=
  show (∀ {t}, s ⊆ t → t ∈ f) ↔ s ∈ f from ⟨fun h => h (Subset.refl s), fun hs t ht => mem_of_superset hs ht⟩

theorem principal_mono {s t : Set α} : 𝓟 s ≤ 𝓟 t ↔ s ⊆ t := by
  simp only [← le_principal_iff, ← iff_selfₓ, ← mem_principal]

@[mono]
theorem monotone_principal : Monotone (𝓟 : Set α → Filter α) := fun _ _ => principal_mono.2

@[simp]
theorem principal_eq_iff_eq {s t : Set α} : 𝓟 s = 𝓟 t ↔ s = t := by
  simp only [← le_antisymm_iffₓ, ← le_principal_iff, ← mem_principal] <;> rfl

@[simp]
theorem join_principal_eq_Sup {s : Set (Filter α)} : join (𝓟 s) = sup s :=
  rfl

@[simp]
theorem principal_univ : 𝓟 (Univ : Set α) = ⊤ :=
  top_unique <| by
    simp only [← le_principal_iff, ← mem_top, ← eq_self_iff_true]

@[simp]
theorem principal_empty : 𝓟 (∅ : Set α) = ⊥ :=
  bot_unique fun s _ => empty_subset _

theorem generate_eq_binfi (S : Set (Set α)) : generate S = ⨅ s ∈ S, 𝓟 s :=
  eq_of_forall_le_iff fun f => by
    simp [← sets_iff_generate, ← le_principal_iff, ← subset_def]

/-! ### Lattice equations -/


theorem empty_mem_iff_bot {f : Filter α} : ∅ ∈ f ↔ f = ⊥ :=
  ⟨fun h => bot_unique fun s _ => mem_of_superset h (empty_subset s), fun h => h.symm ▸ mem_bot⟩

theorem nonempty_of_mem {f : Filter α} [hf : NeBot f] {s : Set α} (hs : s ∈ f) : s.Nonempty :=
  s.eq_empty_or_nonempty.elim (fun h => absurd hs (h.symm ▸ mt empty_mem_iff_bot.mp hf.1)) id

theorem NeBot.nonempty_of_mem {f : Filter α} (hf : NeBot f) {s : Set α} (hs : s ∈ f) : s.Nonempty :=
  @nonempty_of_mem α f hf s hs

@[simp]
theorem empty_not_mem (f : Filter α) [NeBot f] : ¬∅ ∈ f := fun h => (nonempty_of_mem h).ne_empty rfl

theorem nonempty_of_ne_bot (f : Filter α) [NeBot f] : Nonempty α :=
  nonempty_of_exists <| nonempty_of_mem (univ_mem : univ ∈ f)

theorem compl_not_mem {f : Filter α} {s : Set α} [NeBot f] (h : s ∈ f) : sᶜ ∉ f := fun hsc =>
  (nonempty_of_mem (inter_mem h hsc)).ne_empty <| inter_compl_self s

theorem filter_eq_bot_of_is_empty [IsEmpty α] (f : Filter α) : f = ⊥ :=
  empty_mem_iff_bot.mp <| univ_mem' isEmptyElim

protected theorem disjoint_iff {f g : Filter α} : Disjoint f g ↔ ∃ s ∈ f, ∃ t ∈ g, Disjoint s t := by
  simp only [← disjoint_iff, empty_mem_iff_bot, ← mem_inf_iff, ← inf_eq_inter, ← bot_eq_empty, ← @eq_comm _ ∅]

theorem disjoint_of_disjoint_of_mem {f g : Filter α} {s t : Set α} (h : Disjoint s t) (hs : s ∈ f) (ht : t ∈ g) :
    Disjoint f g :=
  Filter.disjoint_iff.mpr ⟨s, hs, t, ht, h⟩

theorem NeBot.not_disjoint (hf : f.ne_bot) (hs : s ∈ f) (ht : t ∈ f) : ¬Disjoint s t := fun h =>
  not_disjoint_self_iff.2 hf <| Filter.disjoint_iff.2 ⟨s, hs, t, ht, h⟩

theorem inf_eq_bot_iff {f g : Filter α} : f⊓g = ⊥ ↔ ∃ U ∈ f, ∃ V ∈ g, U ∩ V = ∅ := by
  simpa only [← disjoint_iff] using Filter.disjoint_iff

/-- There is exactly one filter on an empty type. --/
-- TODO[gh-6025]: make this globally an instance once safe to do so
@[local instance]
protected def unique [IsEmpty α] : Unique (Filter α) where
  default := ⊥
  uniq := filter_eq_bot_of_is_empty

/-- There are only two filters on a `subsingleton`: `⊥` and `⊤`. If the type is empty, then they are
equal. -/
theorem eq_top_of_ne_bot [Subsingleton α] (l : Filter α) [NeBot l] : l = ⊤ := by
  refine' top_unique fun s hs => _
  obtain rfl : s = univ
  exact Subsingleton.eq_univ_of_nonempty (nonempty_of_mem hs)
  exact univ_mem

theorem forall_mem_nonempty_iff_ne_bot {f : Filter α} : (∀ s : Set α, s ∈ f → s.Nonempty) ↔ NeBot f :=
  ⟨fun h => ⟨fun hf => empty_not_nonempty (h ∅ <| hf.symm ▸ mem_bot)⟩, @nonempty_of_mem _ _⟩

theorem nontrivial_iff_nonempty : Nontrivial (Filter α) ↔ Nonempty α :=
  ⟨fun ⟨⟨f, g, hfg⟩⟩ =>
    by_contra fun h =>
      hfg <|
        have : IsEmpty α := not_nonempty_iff.1 h
        Subsingleton.elimₓ _ _,
    fun ⟨x⟩ =>
    ⟨⟨⊤, ⊥,
        ne_bot.ne <|
          forall_mem_nonempty_iff_ne_bot.1 fun s hs => by
            rwa [mem_top.1 hs, ← nonempty_iff_univ_nonempty]⟩⟩⟩

theorem eq_Inf_of_mem_iff_exists_mem {S : Set (Filter α)} {l : Filter α} (h : ∀ {s}, s ∈ l ↔ ∃ f ∈ S, s ∈ f) :
    l = inf S :=
  le_antisymmₓ (le_Inf fun f hf s hs => h.2 ⟨f, hf, hs⟩) fun s hs =>
    let ⟨f, hf, hs⟩ := h.1 hs
    (Inf_le hf : inf S ≤ f) hs

theorem eq_infi_of_mem_iff_exists_mem {f : ι → Filter α} {l : Filter α} (h : ∀ {s}, s ∈ l ↔ ∃ i, s ∈ f i) :
    l = infi f :=
  eq_Inf_of_mem_iff_exists_mem fun s => h.trans exists_range_iff.symm

theorem eq_binfi_of_mem_iff_exists_mem {f : ι → Filter α} {p : ι → Prop} {l : Filter α}
    (h : ∀ {s}, s ∈ l ↔ ∃ (i : _)(_ : p i), s ∈ f i) : l = ⨅ (i) (_ : p i), f i := by
  rw [infi_subtype']
  apply eq_infi_of_mem_iff_exists_mem
  intro s
  exact h.trans ⟨fun ⟨i, pi, si⟩ => ⟨⟨i, pi⟩, si⟩, fun ⟨⟨i, pi⟩, si⟩ => ⟨i, pi, si⟩⟩

theorem infi_sets_eq {f : ι → Filter α} (h : Directed (· ≥ ·) f) [ne : Nonempty ι] : (infi f).Sets = ⋃ i, (f i).Sets :=
  let ⟨i⟩ := Ne
  let u :=
    { Sets := ⋃ i, (f i).Sets,
      univ_sets := by
        simp only [← mem_Union] <;> exact ⟨i, univ_mem⟩,
      sets_of_superset := by
        simp only [← mem_Union, ← exists_imp_distrib] <;> intro x y i hx hxy <;> exact ⟨i, mem_of_superset hx hxy⟩,
      inter_sets := by
        simp only [← mem_Union, ← exists_imp_distrib]
        intro x y a hx b hy
        rcases h a b with ⟨c, ha, hb⟩
        exact ⟨c, inter_mem (ha hx) (hb hy)⟩ }
  have : u = infi f :=
    eq_infi_of_mem_iff_exists_mem fun s => by
      simp only [← Filter.mem_mk, ← mem_Union, ← Filter.mem_sets]
  congr_arg Filter.Sets this.symm

theorem mem_infi_of_directed {f : ι → Filter α} (h : Directed (· ≥ ·) f) [Nonempty ι] (s) : s ∈ infi f ↔ ∃ i, s ∈ f i :=
  by
  simp only [Filter.mem_sets, ← infi_sets_eq h, ← mem_Union]

theorem mem_binfi_of_directed {f : β → Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· ≥ ·)) s) (ne : s.Nonempty)
    {t : Set α} : (t ∈ ⨅ i ∈ s, f i) ↔ ∃ i ∈ s, t ∈ f i := by
  have : Nonempty { x // x ∈ s } := ne.to_subtype <;>
    erw [infi_subtype', mem_infi_of_directed h.directed_coe, Subtype.exists] <;> rfl

theorem binfi_sets_eq {f : β → Filter α} {s : Set β} (h : DirectedOn (f ⁻¹'o (· ≥ ·)) s) (ne : s.Nonempty) :
    (⨅ i ∈ s, f i).Sets = ⋃ i ∈ s, (f i).Sets :=
  ext fun t => by
    simp [← mem_binfi_of_directed h Ne]

theorem infi_sets_eq_finite {ι : Type _} (f : ι → Filter α) : (⨅ i, f i).Sets = ⋃ t : Finset ι, (⨅ i ∈ t, f i).Sets :=
  by
  rw [infi_eq_infi_finset, infi_sets_eq]
  exact directed_of_sup fun s₁ s₂ => binfi_mono

theorem infi_sets_eq_finite' (f : ι → Filter α) :
    (⨅ i, f i).Sets = ⋃ t : Finset (Plift ι), (⨅ i ∈ t, f (Plift.down i)).Sets := by
  rw [← infi_sets_eq_finite, ← equiv.plift.surjective.infi_comp]
  rfl

theorem mem_infi_finite {ι : Type _} {f : ι → Filter α} (s) : s ∈ infi f ↔ ∃ t : Finset ι, s ∈ ⨅ i ∈ t, f i :=
  (Set.ext_iff.1 (infi_sets_eq_finite f) s).trans mem_Union

theorem mem_infi_finite' {f : ι → Filter α} (s) : s ∈ infi f ↔ ∃ t : Finset (Plift ι), s ∈ ⨅ i ∈ t, f (Plift.down i) :=
  (Set.ext_iff.1 (infi_sets_eq_finite' f) s).trans mem_Union

@[simp]
theorem sup_join {f₁ f₂ : Filter (Filter α)} : join f₁⊔join f₂ = join (f₁⊔f₂) :=
  Filter.ext fun x => by
    simp only [← mem_sup, ← mem_join]

@[simp]
theorem supr_join {ι : Sort w} {f : ι → Filter (Filter α)} : (⨆ x, join (f x)) = join (⨆ x, f x) :=
  Filter.ext fun x => by
    simp only [← mem_supr, ← mem_join]

instance : DistribLattice (Filter α) :=
  { Filter.completeLattice with
    le_sup_inf := by
      intro x y z s
      simp only [← and_assoc, ← mem_inf_iff, ← mem_sup, ← exists_prop, ← exists_imp_distrib, ← and_imp]
      rintro hs t₁ ht₁ t₂ ht₂ rfl
      exact
        ⟨t₁, x.sets_of_superset hs (inter_subset_left t₁ t₂), ht₁, t₂, x.sets_of_superset hs (inter_subset_right t₁ t₂),
          ht₂, rfl⟩ }

-- The dual version does not hold! `filter α` is not a `complete_distrib_lattice`. -/
instance : Coframe (Filter α) :=
  { Filter.completeLattice with inf := inf,
    infi_sup_le_sup_Inf := fun f s => by
      rw [Inf_eq_infi', infi_subtype']
      rintro t ⟨h₁, h₂⟩
      rw [infi_sets_eq_finite'] at h₂
      simp only [← mem_Union, ← (Finset.inf_eq_infi _ _).symm] at h₂
      obtain ⟨u, hu⟩ := h₂
      suffices (⨅ i, f⊔↑i) ≤ f⊔u.inf fun i => ↑i.down by
        exact this ⟨h₁, hu⟩
      refine' Finset.induction_on u (le_sup_of_le_right le_top) _
      rintro ⟨i⟩ u _ ih
      rw [Finset.inf_insert, sup_inf_left]
      exact le_inf (infi_le _ _) ih }

theorem mem_infi_finset {s : Finset α} {f : α → Filter β} {t : Set β} :
    (t ∈ ⨅ a ∈ s, f a) ↔ ∃ p : α → Set β, (∀, ∀ a ∈ s, ∀, p a ∈ f a) ∧ t = ⋂ a ∈ s, p a := by
  simp only [Finset.set_bInter_coe, ← bInter_eq_Inter, ← infi_subtype']
  refine' ⟨fun h => _, _⟩
  · rcases(mem_infi_of_fintype _).1 h with ⟨p, hp, rfl⟩
    refine'
      ⟨fun a => if h : a ∈ s then p ⟨a, h⟩ else univ, fun a ha => by
        simpa [← ha] using hp ⟨a, ha⟩, _⟩
    refine' Inter_congr_of_surjective id surjective_id _
    rintro ⟨a, ha⟩
    simp [← ha]
    
  · rintro ⟨p, hpf, rfl⟩
    exact Inter_mem.2 fun a => mem_infi_of_mem a (hpf a a.2)
    

/-- If `f : ι → filter α` is directed, `ι` is not empty, and `∀ i, f i ≠ ⊥`, then `infi f ≠ ⊥`.
See also `infi_ne_bot_of_directed` for a version assuming `nonempty α` instead of `nonempty ι`. -/
theorem infi_ne_bot_of_directed' {f : ι → Filter α} [Nonempty ι] (hd : Directed (· ≥ ·) f) (hb : ∀ i, NeBot (f i)) :
    NeBot (infi f) :=
  ⟨by
    intro h
    have he : ∅ ∈ infi f := h.symm ▸ (mem_bot : ∅ ∈ (⊥ : Filter α))
    obtain ⟨i, hi⟩ : ∃ i, ∅ ∈ f i
    exact (mem_infi_of_directed hd ∅).1 he
    exact (hb i).Ne (empty_mem_iff_bot.1 hi)⟩

/-- If `f : ι → filter α` is directed, `α` is not empty, and `∀ i, f i ≠ ⊥`, then `infi f ≠ ⊥`.
See also `infi_ne_bot_of_directed'` for a version assuming `nonempty ι` instead of `nonempty α`. -/
theorem infi_ne_bot_of_directed {f : ι → Filter α} [hn : Nonempty α] (hd : Directed (· ≥ ·) f) (hb : ∀ i, NeBot (f i)) :
    NeBot (infi f) :=
  if hι : Nonempty ι then @infi_ne_bot_of_directed' _ _ _ hι hd hb
  else
    ⟨fun h : infi f = ⊥ =>
      have : univ ⊆ (∅ : Set α) := by
        rw [← principal_mono, principal_univ, principal_empty, ← h]
        exact le_infi fun i => False.elim <| hι ⟨i⟩
      let ⟨x⟩ := hn
      this (mem_univ x)⟩

theorem infi_ne_bot_iff_of_directed' {f : ι → Filter α} [Nonempty ι] (hd : Directed (· ≥ ·) f) :
    NeBot (infi f) ↔ ∀ i, NeBot (f i) :=
  ⟨fun H i => H.mono (infi_le _ i), infi_ne_bot_of_directed' hd⟩

theorem infi_ne_bot_iff_of_directed {f : ι → Filter α} [Nonempty α] (hd : Directed (· ≥ ·) f) :
    NeBot (infi f) ↔ ∀ i, NeBot (f i) :=
  ⟨fun H i => H.mono (infi_le _ i), infi_ne_bot_of_directed hd⟩

@[elab_as_eliminator]
theorem infi_sets_induct {f : ι → Filter α} {s : Set α} (hs : s ∈ infi f) {p : Set α → Prop} (uni : p Univ)
    (ins : ∀ {i s₁ s₂}, s₁ ∈ f i → p s₂ → p (s₁ ∩ s₂)) : p s := by
  rw [mem_infi_finite'] at hs
  simp only [Finset.inf_eq_infi] at hs
  rcases hs with ⟨is, his⟩
  revert s
  refine' Finset.induction_on is _ _
  · intro s hs
    rwa [mem_top.1 hs]
    
  · rintro ⟨i⟩ js his ih s hs
    rw [Finset.inf_insert, mem_inf_iff] at hs
    rcases hs with ⟨s₁, hs₁, s₂, hs₂, rfl⟩
    exact ins hs₁ (ih hs₂)
    

/-! #### `principal` equations -/


@[simp]
theorem inf_principal {s t : Set α} : 𝓟 s⊓𝓟 t = 𝓟 (s ∩ t) :=
  le_antisymmₓ
    (by
      simp only [← le_principal_iff, ← mem_inf_iff] <;> exact ⟨s, subset.rfl, t, subset.rfl, rfl⟩)
    (by
      simp [← le_inf_iff, ← inter_subset_left, ← inter_subset_right])

@[simp]
theorem sup_principal {s t : Set α} : 𝓟 s⊔𝓟 t = 𝓟 (s ∪ t) :=
  Filter.ext fun u => by
    simp only [← union_subset_iff, ← mem_sup, ← mem_principal]

@[simp]
theorem supr_principal {ι : Sort w} {s : ι → Set α} : (⨆ x, 𝓟 (s x)) = 𝓟 (⋃ i, s i) :=
  Filter.ext fun x => by
    simp only [← mem_supr, ← mem_principal, ← Union_subset_iff]

@[simp]
theorem principal_eq_bot_iff {s : Set α} : 𝓟 s = ⊥ ↔ s = ∅ :=
  empty_mem_iff_bot.symm.trans <| mem_principal.trans subset_empty_iff

@[simp]
theorem principal_ne_bot_iff {s : Set α} : NeBot (𝓟 s) ↔ s.Nonempty :=
  ne_bot_iff.trans <| (not_congr principal_eq_bot_iff).trans ne_empty_iff_nonempty

theorem is_compl_principal (s : Set α) : IsCompl (𝓟 s) (𝓟 (sᶜ)) :=
  IsCompl.of_eq
      (by
        rw [inf_principal, inter_compl_self, principal_empty]) <|
    by
    rw [sup_principal, union_compl_self, principal_univ]

theorem mem_inf_principal' {f : Filter α} {s t : Set α} : s ∈ f⊓𝓟 t ↔ tᶜ ∪ s ∈ f := by
  simp only [le_principal_iff, ← (is_compl_principal s).le_left_iff, ← disjoint_assoc, ← inf_principal,
    (is_compl_principal (t ∩ sᶜ)).le_right_iff, ← compl_inter, ← compl_compl]

theorem mem_inf_principal {f : Filter α} {s t : Set α} : s ∈ f⊓𝓟 t ↔ { x | x ∈ t → x ∈ s } ∈ f := by
  simp only [← mem_inf_principal', ← imp_iff_not_or]
  rfl

theorem supr_inf_principal (f : ι → Filter α) (s : Set α) : (⨆ i, f i⊓𝓟 s) = (⨆ i, f i)⊓𝓟 s := by
  ext
  simp only [← mem_supr, ← mem_inf_principal]

theorem inf_principal_eq_bot {f : Filter α} {s : Set α} : f⊓𝓟 s = ⊥ ↔ sᶜ ∈ f := by
  rw [← empty_mem_iff_bot, mem_inf_principal]
  rfl

theorem mem_of_eq_bot {f : Filter α} {s : Set α} (h : f⊓𝓟 (sᶜ) = ⊥) : s ∈ f := by
  rwa [inf_principal_eq_bot, compl_compl] at h

theorem diff_mem_inf_principal_compl {f : Filter α} {s : Set α} (hs : s ∈ f) (t : Set α) : s \ t ∈ f⊓𝓟 (tᶜ) :=
  inter_mem_inf hs <| mem_principal_self (tᶜ)

theorem principal_le_iff {s : Set α} {f : Filter α} : 𝓟 s ≤ f ↔ ∀, ∀ V ∈ f, ∀, s ⊆ V := by
  change (∀ V, V ∈ f → V ∈ _) ↔ _
  simp_rw [mem_principal]

@[simp]
theorem infi_principal_finset {ι : Type w} (s : Finset ι) (f : ι → Set α) : (⨅ i ∈ s, 𝓟 (f i)) = 𝓟 (⋂ i ∈ s, f i) := by
  induction' s using Finset.induction_on with i s hi hs
  · simp
    
  · rw [Finset.infi_insert, Finset.set_bInter_insert, hs, inf_principal]
    

@[simp]
theorem infi_principal_fintype {ι : Type w} [Fintype ι] (f : ι → Set α) : (⨅ i, 𝓟 (f i)) = 𝓟 (⋂ i, f i) := by
  simpa using infi_principal_finset Finset.univ f

theorem infi_principal_finite {ι : Type w} {s : Set ι} (hs : s.Finite) (f : ι → Set α) :
    (⨅ i ∈ s, 𝓟 (f i)) = 𝓟 (⋂ i ∈ s, f i) := by
  lift s to Finset ι using hs
  exact_mod_cast infi_principal_finset s f

end Lattice

@[mono]
theorem join_mono {f₁ f₂ : Filter (Filter α)} (h : f₁ ≤ f₂) : join f₁ ≤ join f₂ := fun s hs => h hs

/-! ### Eventually -/


/-- `f.eventually p` or `∀ᶠ x in f, p x` mean that `{x | p x} ∈ f`. E.g., `∀ᶠ x in at_top, p x`
means that `p` holds true for sufficiently large `x`. -/
protected def Eventually (p : α → Prop) (f : Filter α) : Prop :=
  { x | p x } ∈ f

-- mathport name: «expr∀ᶠ in , »
notation3"∀ᶠ "(...)" in "f", "r:(scoped p => Filter.Eventually p f) => r

theorem eventually_iff {f : Filter α} {P : α → Prop} : (∀ᶠ x in f, P x) ↔ { x | P x } ∈ f :=
  Iff.rfl

@[simp]
theorem eventually_mem_set {s : Set α} {l : Filter α} : (∀ᶠ x in l, x ∈ s) ↔ s ∈ l :=
  Iff.rfl

protected theorem ext' {f₁ f₂ : Filter α} (h : ∀ p : α → Prop, (∀ᶠ x in f₁, p x) ↔ ∀ᶠ x in f₂, p x) : f₁ = f₂ :=
  Filter.ext h

theorem Eventually.filter_mono {f₁ f₂ : Filter α} (h : f₁ ≤ f₂) {p : α → Prop} (hp : ∀ᶠ x in f₂, p x) :
    ∀ᶠ x in f₁, p x :=
  h hp

theorem eventually_of_mem {f : Filter α} {P : α → Prop} {U : Set α} (hU : U ∈ f) (h : ∀, ∀ x ∈ U, ∀, P x) :
    ∀ᶠ x in f, P x :=
  mem_of_superset hU h

protected theorem Eventually.and {p q : α → Prop} {f : Filter α} :
    f.Eventually p → f.Eventually q → ∀ᶠ x in f, p x ∧ q x :=
  inter_mem

@[simp]
theorem eventually_true (f : Filter α) : ∀ᶠ x in f, True :=
  univ_mem

theorem eventually_of_forall {p : α → Prop} {f : Filter α} (hp : ∀ x, p x) : ∀ᶠ x in f, p x :=
  univ_mem' hp

@[simp]
theorem eventually_false_iff_eq_bot {f : Filter α} : (∀ᶠ x in f, False) ↔ f = ⊥ :=
  empty_mem_iff_bot

@[simp]
theorem eventually_const {f : Filter α} [t : NeBot f] {p : Prop} : (∀ᶠ x in f, p) ↔ p :=
  Classical.by_cases
    (fun h : p => by
      simp [← h])
    fun h => by
    simpa [← h] using t.ne

theorem eventually_iff_exists_mem {p : α → Prop} {f : Filter α} : (∀ᶠ x in f, p x) ↔ ∃ v ∈ f, ∀, ∀ y ∈ v, ∀, p y :=
  exists_mem_subset_iff.symm

theorem Eventually.exists_mem {p : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x) : ∃ v ∈ f, ∀, ∀ y ∈ v, ∀, p y :=
  eventually_iff_exists_mem.1 hp

theorem Eventually.mp {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x) (hq : ∀ᶠ x in f, p x → q x) :
    ∀ᶠ x in f, q x :=
  mp_mem hp hq

theorem Eventually.mono {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x) (hq : ∀ x, p x → q x) : ∀ᶠ x in f, q x :=
  hp.mp (eventually_of_forall hq)

@[simp]
theorem eventually_and {p q : α → Prop} {f : Filter α} : (∀ᶠ x in f, p x ∧ q x) ↔ (∀ᶠ x in f, p x) ∧ ∀ᶠ x in f, q x :=
  inter_mem_iff

theorem Eventually.congr {f : Filter α} {p q : α → Prop} (h' : ∀ᶠ x in f, p x) (h : ∀ᶠ x in f, p x ↔ q x) :
    ∀ᶠ x in f, q x :=
  h'.mp (h.mono fun x hx => hx.mp)

theorem eventually_congr {f : Filter α} {p q : α → Prop} (h : ∀ᶠ x in f, p x ↔ q x) :
    (∀ᶠ x in f, p x) ↔ ∀ᶠ x in f, q x :=
  ⟨fun hp => hp.congr h, fun hq =>
    hq.congr <| by
      simpa only [← Iff.comm] using h⟩

@[simp]
theorem eventually_all {ι} [Fintype ι] {l} {p : ι → α → Prop} : (∀ᶠ x in l, ∀ i, p i x) ↔ ∀ i, ∀ᶠ x in l, p i x := by
  simpa only [← Filter.Eventually, ← set_of_forall] using Inter_mem

@[simp]
theorem eventually_all_finite {ι} {I : Set ι} (hI : I.Finite) {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀, ∀ i ∈ I, ∀, p i x) ↔ ∀, ∀ i ∈ I, ∀, ∀ᶠ x in l, p i x := by
  simpa only [← Filter.Eventually, ← set_of_forall] using bInter_mem hI

alias eventually_all_finite ← _root_.set.finite.eventually_all

attribute [protected] Set.Finite.eventually_all

@[simp]
theorem eventually_all_finset {ι} (I : Finset ι) {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀, ∀ i ∈ I, ∀, p i x) ↔ ∀, ∀ i ∈ I, ∀, ∀ᶠ x in l, p i x :=
  I.finite_to_set.eventually_all

alias eventually_all_finset ← _root_.finset.eventually_all

attribute [protected] Finset.eventually_all

@[simp]
theorem eventually_or_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∀ᶠ x in f, p ∨ q x) ↔ p ∨ ∀ᶠ x in f, q x :=
  Classical.by_cases
    (fun h : p => by
      simp [← h])
    fun h => by
    simp [← h]

@[simp]
theorem eventually_or_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∀ᶠ x in f, p x ∨ q) ↔ (∀ᶠ x in f, p x) ∨ q := by
  simp only [← or_comm _ q, ← eventually_or_distrib_left]

@[simp]
theorem eventually_imp_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∀ᶠ x in f, p → q x) ↔ p → ∀ᶠ x in f, q x := by
  simp only [← imp_iff_not_or, ← eventually_or_distrib_left]

@[simp]
theorem eventually_bot {p : α → Prop} : ∀ᶠ x in ⊥, p x :=
  ⟨⟩

@[simp]
theorem eventually_top {p : α → Prop} : (∀ᶠ x in ⊤, p x) ↔ ∀ x, p x :=
  Iff.rfl

@[simp]
theorem eventually_sup {p : α → Prop} {f g : Filter α} : (∀ᶠ x in f⊔g, p x) ↔ (∀ᶠ x in f, p x) ∧ ∀ᶠ x in g, p x :=
  Iff.rfl

@[simp]
theorem eventually_Sup {p : α → Prop} {fs : Set (Filter α)} : (∀ᶠ x in sup fs, p x) ↔ ∀, ∀ f ∈ fs, ∀, ∀ᶠ x in f, p x :=
  Iff.rfl

@[simp]
theorem eventually_supr {p : α → Prop} {fs : β → Filter α} : (∀ᶠ x in ⨆ b, fs b, p x) ↔ ∀ b, ∀ᶠ x in fs b, p x :=
  mem_supr

@[simp]
theorem eventually_principal {a : Set α} {p : α → Prop} : (∀ᶠ x in 𝓟 a, p x) ↔ ∀, ∀ x ∈ a, ∀, p x :=
  Iff.rfl

theorem eventually_inf {f g : Filter α} {p : α → Prop} :
    (∀ᶠ x in f⊓g, p x) ↔ ∃ s ∈ f, ∃ t ∈ g, ∀, ∀ x ∈ s ∩ t, ∀, p x :=
  mem_inf_iff_superset

theorem eventually_inf_principal {f : Filter α} {p : α → Prop} {s : Set α} :
    (∀ᶠ x in f⊓𝓟 s, p x) ↔ ∀ᶠ x in f, x ∈ s → p x :=
  mem_inf_principal

/-! ### Frequently -/


/-- `f.frequently p` or `∃ᶠ x in f, p x` mean that `{x | ¬p x} ∉ f`. E.g., `∃ᶠ x in at_top, p x`
means that there exist arbitrarily large `x` for which `p` holds true. -/
protected def Frequently (p : α → Prop) (f : Filter α) : Prop :=
  ¬∀ᶠ x in f, ¬p x

-- mathport name: «expr∃ᶠ in , »
notation3"∃ᶠ "(...)" in "f", "r:(scoped p => Filter.Frequently p f) => r

theorem Eventually.frequently {f : Filter α} [NeBot f] {p : α → Prop} (h : ∀ᶠ x in f, p x) : ∃ᶠ x in f, p x :=
  compl_not_mem h

theorem frequently_of_forall {f : Filter α} [NeBot f] {p : α → Prop} (h : ∀ x, p x) : ∃ᶠ x in f, p x :=
  Eventually.frequently (eventually_of_forall h)

theorem Frequently.mp {p q : α → Prop} {f : Filter α} (h : ∃ᶠ x in f, p x) (hpq : ∀ᶠ x in f, p x → q x) :
    ∃ᶠ x in f, q x :=
  mt (fun hq => hq.mp <| hpq.mono fun x => mt) h

theorem Frequently.filter_mono {p : α → Prop} {f g : Filter α} (h : ∃ᶠ x in f, p x) (hle : f ≤ g) : ∃ᶠ x in g, p x :=
  mt (fun h' => h'.filter_mono hle) h

theorem Frequently.mono {p q : α → Prop} {f : Filter α} (h : ∃ᶠ x in f, p x) (hpq : ∀ x, p x → q x) : ∃ᶠ x in f, q x :=
  h.mp (eventually_of_forall hpq)

theorem Frequently.and_eventually {p q : α → Prop} {f : Filter α} (hp : ∃ᶠ x in f, p x) (hq : ∀ᶠ x in f, q x) :
    ∃ᶠ x in f, p x ∧ q x := by
  refine' mt (fun h => hq.mp <| h.mono _) hp
  exact fun x hpq hq hp => hpq ⟨hp, hq⟩

theorem Eventually.and_frequently {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ x in f, p x) (hq : ∃ᶠ x in f, q x) :
    ∃ᶠ x in f, p x ∧ q x := by
  simpa only [← And.comm] using hq.and_eventually hp

theorem Frequently.exists {p : α → Prop} {f : Filter α} (hp : ∃ᶠ x in f, p x) : ∃ x, p x := by
  by_contra H
  replace H : ∀ᶠ x in f, ¬p x
  exact eventually_of_forall (not_exists.1 H)
  exact hp H

theorem Eventually.exists {p : α → Prop} {f : Filter α} [NeBot f] (hp : ∀ᶠ x in f, p x) : ∃ x, p x :=
  hp.Frequently.exists

theorem frequently_iff_forall_eventually_exists_and {p : α → Prop} {f : Filter α} :
    (∃ᶠ x in f, p x) ↔ ∀ {q : α → Prop}, (∀ᶠ x in f, q x) → ∃ x, p x ∧ q x :=
  ⟨fun hp q hq => (hp.and_eventually hq).exists, fun H hp => by
    simpa only [← and_not_selfₓ, ← exists_false] using H hp⟩

theorem frequently_iff {f : Filter α} {P : α → Prop} : (∃ᶠ x in f, P x) ↔ ∀ {U}, U ∈ f → ∃ x ∈ U, P x := by
  simp only [← frequently_iff_forall_eventually_exists_and, ← exists_prop, ← and_comm (P _)]
  rfl

@[simp]
theorem not_eventually {p : α → Prop} {f : Filter α} : (¬∀ᶠ x in f, p x) ↔ ∃ᶠ x in f, ¬p x := by
  simp [← Filter.Frequently]

@[simp]
theorem not_frequently {p : α → Prop} {f : Filter α} : (¬∃ᶠ x in f, p x) ↔ ∀ᶠ x in f, ¬p x := by
  simp only [← Filter.Frequently, ← not_not]

@[simp]
theorem frequently_true_iff_ne_bot (f : Filter α) : (∃ᶠ x in f, True) ↔ NeBot f := by
  simp [← Filter.Frequently, -not_eventually, ← eventually_false_iff_eq_bot, ← ne_bot_iff]

@[simp]
theorem frequently_false (f : Filter α) : ¬∃ᶠ x in f, False := by
  simp

@[simp]
theorem frequently_const {f : Filter α} [NeBot f] {p : Prop} : (∃ᶠ x in f, p) ↔ p :=
  Classical.by_cases
    (fun h : p => by
      simpa [← h] )
    fun h => by
    simp [← h]

@[simp]
theorem frequently_or_distrib {f : Filter α} {p q : α → Prop} :
    (∃ᶠ x in f, p x ∨ q x) ↔ (∃ᶠ x in f, p x) ∨ ∃ᶠ x in f, q x := by
  simp only [← Filter.Frequently, not_and_distrib, ← not_or_distrib, ← eventually_and]

theorem frequently_or_distrib_left {f : Filter α} [NeBot f] {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p ∨ q x) ↔ p ∨ ∃ᶠ x in f, q x := by
  simp

theorem frequently_or_distrib_right {f : Filter α} [NeBot f] {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x ∨ q) ↔ (∃ᶠ x in f, p x) ∨ q := by
  simp

@[simp]
theorem frequently_imp_distrib {f : Filter α} {p q : α → Prop} :
    (∃ᶠ x in f, p x → q x) ↔ (∀ᶠ x in f, p x) → ∃ᶠ x in f, q x := by
  simp [← imp_iff_not_or, ← not_eventually, ← frequently_or_distrib]

theorem frequently_imp_distrib_left {f : Filter α} [NeBot f] {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p → q x) ↔ p → ∃ᶠ x in f, q x := by
  simp

theorem frequently_imp_distrib_right {f : Filter α} [NeBot f] {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x → q) ↔ (∀ᶠ x in f, p x) → q := by
  simp

@[simp]
theorem eventually_imp_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∀ᶠ x in f, p x → q) ↔ (∃ᶠ x in f, p x) → q := by
  simp only [← imp_iff_not_or, ← eventually_or_distrib_right, ← not_frequently]

@[simp]
theorem frequently_and_distrib_left {f : Filter α} {p : Prop} {q : α → Prop} :
    (∃ᶠ x in f, p ∧ q x) ↔ p ∧ ∃ᶠ x in f, q x := by
  simp only [← Filter.Frequently, ← not_and, ← eventually_imp_distrib_left, ← not_imp]

@[simp]
theorem frequently_and_distrib_right {f : Filter α} {p : α → Prop} {q : Prop} :
    (∃ᶠ x in f, p x ∧ q) ↔ (∃ᶠ x in f, p x) ∧ q := by
  simp only [← and_comm _ q, ← frequently_and_distrib_left]

@[simp]
theorem frequently_bot {p : α → Prop} : ¬∃ᶠ x in ⊥, p x := by
  simp

@[simp]
theorem frequently_top {p : α → Prop} : (∃ᶠ x in ⊤, p x) ↔ ∃ x, p x := by
  simp [← Filter.Frequently]

@[simp]
theorem frequently_principal {a : Set α} {p : α → Prop} : (∃ᶠ x in 𝓟 a, p x) ↔ ∃ x ∈ a, p x := by
  simp [← Filter.Frequently, ← not_forall]

theorem frequently_sup {p : α → Prop} {f g : Filter α} : (∃ᶠ x in f⊔g, p x) ↔ (∃ᶠ x in f, p x) ∨ ∃ᶠ x in g, p x := by
  simp only [← Filter.Frequently, ← eventually_sup, ← not_and_distrib]

@[simp]
theorem frequently_Sup {p : α → Prop} {fs : Set (Filter α)} : (∃ᶠ x in sup fs, p x) ↔ ∃ f ∈ fs, ∃ᶠ x in f, p x := by
  simp [← Filter.Frequently, -not_eventually, ← not_forall]

@[simp]
theorem frequently_supr {p : α → Prop} {fs : β → Filter α} : (∃ᶠ x in ⨆ b, fs b, p x) ↔ ∃ b, ∃ᶠ x in fs b, p x := by
  simp [← Filter.Frequently, -not_eventually, ← not_forall]

/-!
### Relation “eventually equal”
-/


/-- Two functions `f` and `g` are *eventually equal* along a filter `l` if the set of `x` such that
`f x = g x` belongs to `l`. -/
def EventuallyEq (l : Filter α) (f g : α → β) : Prop :=
  ∀ᶠ x in l, f x = g x

-- mathport name: «expr =ᶠ[ ] »
notation:50 f " =ᶠ[" l:50 "] " g:50 => EventuallyEq l f g

theorem EventuallyEq.eventually {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) : ∀ᶠ x in l, f x = g x :=
  h

theorem EventuallyEq.rw {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) (p : α → β → Prop) (hf : ∀ᶠ x in l, p x (f x)) :
    ∀ᶠ x in l, p x (g x) :=
  hf.congr <| h.mono fun x hx => hx ▸ Iff.rfl

theorem eventually_eq_set {s t : Set α} {l : Filter α} : s =ᶠ[l] t ↔ ∀ᶠ x in l, x ∈ s ↔ x ∈ t :=
  eventually_congr <| eventually_of_forall fun x => ⟨Eq.to_iff, Iff.to_eq⟩

alias eventually_eq_set ↔ eventually_eq.mem_iff eventually.set_eq

@[simp]
theorem eventually_eq_univ {s : Set α} {l : Filter α} : s =ᶠ[l] univ ↔ s ∈ l := by
  simp [← eventually_eq_set]

theorem EventuallyEq.exists_mem {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) : ∃ s ∈ l, EqOn f g s :=
  h.exists_mem

theorem eventually_eq_of_mem {l : Filter α} {f g : α → β} {s : Set α} (hs : s ∈ l) (h : EqOn f g s) : f =ᶠ[l] g :=
  eventually_of_mem hs h

theorem eventually_eq_iff_exists_mem {l : Filter α} {f g : α → β} : f =ᶠ[l] g ↔ ∃ s ∈ l, EqOn f g s :=
  eventually_iff_exists_mem

theorem EventuallyEq.filter_mono {l l' : Filter α} {f g : α → β} (h₁ : f =ᶠ[l] g) (h₂ : l' ≤ l) : f =ᶠ[l'] g :=
  h₂ h₁

@[refl]
theorem EventuallyEq.refl (l : Filter α) (f : α → β) : f =ᶠ[l] f :=
  eventually_of_forall fun x => rfl

theorem EventuallyEq.rfl {l : Filter α} {f : α → β} : f =ᶠ[l] f :=
  EventuallyEq.refl l f

@[symm]
theorem EventuallyEq.symm {f g : α → β} {l : Filter α} (H : f =ᶠ[l] g) : g =ᶠ[l] f :=
  H.mono fun _ => Eq.symm

@[trans]
theorem EventuallyEq.trans {l : Filter α} {f g h : α → β} (H₁ : f =ᶠ[l] g) (H₂ : g =ᶠ[l] h) : f =ᶠ[l] h :=
  H₂.rw (fun x y => f x = y) H₁

theorem EventuallyEq.prod_mk {l} {f f' : α → β} (hf : f =ᶠ[l] f') {g g' : α → γ} (hg : g =ᶠ[l] g') :
    (fun x => (f x, g x)) =ᶠ[l] fun x => (f' x, g' x) :=
  hf.mp <|
    hg.mono <| by
      intros
      simp only [*]

theorem EventuallyEq.fun_comp {f g : α → β} {l : Filter α} (H : f =ᶠ[l] g) (h : β → γ) : h ∘ f =ᶠ[l] h ∘ g :=
  H.mono fun x hx => congr_arg h hx

theorem EventuallyEq.comp₂ {δ} {f f' : α → β} {g g' : α → γ} {l} (Hf : f =ᶠ[l] f') (h : β → γ → δ) (Hg : g =ᶠ[l] g') :
    (fun x => h (f x) (g x)) =ᶠ[l] fun x => h (f' x) (g' x) :=
  (Hf.prod_mk Hg).fun_comp (uncurry h)

@[to_additive]
theorem EventuallyEq.mul [Mul β] {f f' g g' : α → β} {l : Filter α} (h : f =ᶠ[l] g) (h' : f' =ᶠ[l] g') :
    (fun x => f x * f' x) =ᶠ[l] fun x => g x * g' x :=
  h.comp₂ (· * ·) h'

@[to_additive]
theorem EventuallyEq.inv [Inv β] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) :
    (fun x => (f x)⁻¹) =ᶠ[l] fun x => (g x)⁻¹ :=
  h.fun_comp Inv.inv

@[to_additive]
theorem EventuallyEq.div [Div β] {f f' g g' : α → β} {l : Filter α} (h : f =ᶠ[l] g) (h' : f' =ᶠ[l] g') :
    (fun x => f x / f' x) =ᶠ[l] fun x => g x / g' x :=
  h.comp₂ (· / ·) h'

@[to_additive]
theorem EventuallyEq.const_smul {𝕜} [HasSmul 𝕜 β] {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) (c : 𝕜) :
    (fun x => c • f x) =ᶠ[l] fun x => c • g x :=
  h.fun_comp fun x => c • x

@[to_additive]
theorem EventuallyEq.smul {𝕜} [HasSmul 𝕜 β] {l : Filter α} {f f' : α → 𝕜} {g g' : α → β} (hf : f =ᶠ[l] f')
    (hg : g =ᶠ[l] g') : (fun x => f x • g x) =ᶠ[l] fun x => f' x • g' x :=
  hf.comp₂ (· • ·) hg

theorem EventuallyEq.sup [HasSup β] {l : Filter α} {f f' g g' : α → β} (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
    (fun x => f x⊔g x) =ᶠ[l] fun x => f' x⊔g' x :=
  hf.comp₂ (·⊔·) hg

theorem EventuallyEq.inf [HasInf β] {l : Filter α} {f f' g g' : α → β} (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
    (fun x => f x⊓g x) =ᶠ[l] fun x => f' x⊓g' x :=
  hf.comp₂ (·⊓·) hg

theorem EventuallyEq.preimage {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) (s : Set β) : f ⁻¹' s =ᶠ[l] g ⁻¹' s :=
  h.fun_comp s

theorem EventuallyEq.inter {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s ∩ s' : Set α) =ᶠ[l] (t ∩ t' : Set α) :=
  h.comp₂ (· ∧ ·) h'

theorem EventuallyEq.union {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s ∪ s' : Set α) =ᶠ[l] (t ∪ t' : Set α) :=
  h.comp₂ (· ∨ ·) h'

theorem EventuallyEq.compl {s t : Set α} {l : Filter α} (h : s =ᶠ[l] t) : (sᶜ : Set α) =ᶠ[l] (tᶜ : Set α) :=
  h.fun_comp Not

theorem EventuallyEq.diff {s t s' t' : Set α} {l : Filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
    (s \ s' : Set α) =ᶠ[l] (t \ t' : Set α) :=
  h.inter h'.compl

theorem eventually_eq_empty {s : Set α} {l : Filter α} : s =ᶠ[l] (∅ : Set α) ↔ ∀ᶠ x in l, x ∉ s :=
  eventually_eq_set.trans <| by
    simp

theorem inter_eventually_eq_left {s t : Set α} {l : Filter α} : (s ∩ t : Set α) =ᶠ[l] s ↔ ∀ᶠ x in l, x ∈ s → x ∈ t := by
  simp only [← eventually_eq_set, ← mem_inter_eq, ← and_iff_left_iff_imp]

theorem inter_eventually_eq_right {s t : Set α} {l : Filter α} : (s ∩ t : Set α) =ᶠ[l] t ↔ ∀ᶠ x in l, x ∈ t → x ∈ s :=
  by
  rw [inter_comm, inter_eventually_eq_left]

@[simp]
theorem eventually_eq_principal {s : Set α} {f g : α → β} : f =ᶠ[𝓟 s] g ↔ EqOn f g s :=
  Iff.rfl

theorem eventually_eq_inf_principal_iff {F : Filter α} {s : Set α} {f g : α → β} :
    f =ᶠ[F⊓𝓟 s] g ↔ ∀ᶠ x in F, x ∈ s → f x = g x :=
  eventually_inf_principal

theorem EventuallyEq.sub_eq [AddGroupₓ β] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) : f - g =ᶠ[l] 0 := by
  simpa using (eventually_eq.sub (eventually_eq.refl l f) h).symm

theorem eventually_eq_iff_sub [AddGroupₓ β] {f g : α → β} {l : Filter α} : f =ᶠ[l] g ↔ f - g =ᶠ[l] 0 :=
  ⟨fun h => h.sub_eq, fun h => by
    simpa using h.add (eventually_eq.refl l g)⟩

section LE

variable [LE β] {l : Filter α}

/-- A function `f` is eventually less than or equal to a function `g` at a filter `l`. -/
def EventuallyLe (l : Filter α) (f g : α → β) : Prop :=
  ∀ᶠ x in l, f x ≤ g x

-- mathport name: «expr ≤ᶠ[ ] »
notation:50 f " ≤ᶠ[" l:50 "] " g:50 => EventuallyLe l f g

theorem EventuallyLe.congr {f f' g g' : α → β} (H : f ≤ᶠ[l] g) (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') : f' ≤ᶠ[l] g' :=
  H.mp <|
    hg.mp <|
      hf.mono fun x hf hg H => by
        rwa [hf, hg] at H

theorem eventually_le_congr {f f' g g' : α → β} (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') : f ≤ᶠ[l] g ↔ f' ≤ᶠ[l] g' :=
  ⟨fun H => H.congr hf hg, fun H => H.congr hf.symm hg.symm⟩

end LE

section Preorderₓ

variable [Preorderₓ β] {l : Filter α} {f g h : α → β}

theorem EventuallyEq.le (h : f =ᶠ[l] g) : f ≤ᶠ[l] g :=
  h.mono fun x => le_of_eqₓ

@[refl]
theorem EventuallyLe.refl (l : Filter α) (f : α → β) : f ≤ᶠ[l] f :=
  EventuallyEq.rfl.le

theorem EventuallyLe.rfl : f ≤ᶠ[l] f :=
  EventuallyLe.refl l f

@[trans]
theorem EventuallyLe.trans (H₁ : f ≤ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₂.mp <| H₁.mono fun x => le_transₓ

@[trans]
theorem EventuallyEq.trans_le (H₁ : f =ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₁.le.trans H₂

@[trans]
theorem EventuallyLe.trans_eq (H₁ : f ≤ᶠ[l] g) (H₂ : g =ᶠ[l] h) : f ≤ᶠ[l] h :=
  H₁.trans H₂.le

end Preorderₓ

theorem EventuallyLe.antisymm [PartialOrderₓ β] {l : Filter α} {f g : α → β} (h₁ : f ≤ᶠ[l] g) (h₂ : g ≤ᶠ[l] f) :
    f =ᶠ[l] g :=
  h₂.mp <| h₁.mono fun x => le_antisymmₓ

theorem eventually_le_antisymm_iff [PartialOrderₓ β] {l : Filter α} {f g : α → β} : f =ᶠ[l] g ↔ f ≤ᶠ[l] g ∧ g ≤ᶠ[l] f :=
  by
  simp only [← eventually_eq, ← eventually_le, ← le_antisymm_iffₓ, ← eventually_and]

theorem EventuallyLe.le_iff_eq [PartialOrderₓ β] {l : Filter α} {f g : α → β} (h : f ≤ᶠ[l] g) : g ≤ᶠ[l] f ↔ g =ᶠ[l] f :=
  ⟨fun h' => h'.antisymm h, EventuallyEq.le⟩

theorem Eventually.ne_of_lt [Preorderₓ β] {l : Filter α} {f g : α → β} (h : ∀ᶠ x in l, f x < g x) :
    ∀ᶠ x in l, f x ≠ g x :=
  h.mono fun x hx => hx.Ne

theorem Eventually.ne_top_of_lt [PartialOrderₓ β] [OrderTop β] {l : Filter α} {f g : α → β} (h : ∀ᶠ x in l, f x < g x) :
    ∀ᶠ x in l, f x ≠ ⊤ :=
  h.mono fun x hx => hx.ne_top

theorem Eventually.lt_top_of_ne [PartialOrderₓ β] [OrderTop β] {l : Filter α} {f : α → β} (h : ∀ᶠ x in l, f x ≠ ⊤) :
    ∀ᶠ x in l, f x < ⊤ :=
  h.mono fun x hx => hx.lt_top

theorem Eventually.lt_top_iff_ne_top [PartialOrderₓ β] [OrderTop β] {l : Filter α} {f : α → β} :
    (∀ᶠ x in l, f x < ⊤) ↔ ∀ᶠ x in l, f x ≠ ⊤ :=
  ⟨Eventually.ne_of_lt, Eventually.lt_top_of_ne⟩

@[mono]
theorem EventuallyLe.inter {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : s' ≤ᶠ[l] t') :
    (s ∩ s' : Set α) ≤ᶠ[l] (t ∩ t' : Set α) :=
  h'.mp <| h.mono fun x => And.imp

@[mono]
theorem EventuallyLe.union {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : s' ≤ᶠ[l] t') :
    (s ∪ s' : Set α) ≤ᶠ[l] (t ∪ t' : Set α) :=
  h'.mp <| h.mono fun x => Or.imp

@[mono]
theorem EventuallyLe.compl {s t : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) : (tᶜ : Set α) ≤ᶠ[l] (sᶜ : Set α) :=
  h.mono fun x => mt

@[mono]
theorem EventuallyLe.diff {s t s' t' : Set α} {l : Filter α} (h : s ≤ᶠ[l] t) (h' : t' ≤ᶠ[l] s') :
    (s \ s' : Set α) ≤ᶠ[l] (t \ t' : Set α) :=
  h.inter h'.compl

theorem EventuallyLe.mul_le_mul [OrderedSemiring β] {l : Filter α} {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂)
    (hg : g₁ ≤ᶠ[l] g₂) (hg₀ : 0 ≤ᶠ[l] g₁) (hf₀ : 0 ≤ᶠ[l] f₂) : f₁ * g₁ ≤ᶠ[l] f₂ * g₂ := by
  filter_upwards [hf, hg, hg₀, hf₀] with x using mul_le_mul

theorem EventuallyLe.mul_nonneg [OrderedSemiring β] {l : Filter α} {f g : α → β} (hf : 0 ≤ᶠ[l] f) (hg : 0 ≤ᶠ[l] g) :
    0 ≤ᶠ[l] f * g := by
  filter_upwards [hf, hg] with x using mul_nonneg

theorem eventually_sub_nonneg [OrderedRing β] {l : Filter α} {f g : α → β} : 0 ≤ᶠ[l] g - f ↔ f ≤ᶠ[l] g :=
  eventually_congr <| eventually_of_forall fun x => sub_nonneg

theorem EventuallyLe.sup [SemilatticeSup β] {l : Filter α} {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) :
    f₁⊔g₁ ≤ᶠ[l] f₂⊔g₂ := by
  filter_upwards [hf, hg] with x hfx hgx using sup_le_sup hfx hgx

theorem EventuallyLe.sup_le [SemilatticeSup β] {l : Filter α} {f g h : α → β} (hf : f ≤ᶠ[l] h) (hg : g ≤ᶠ[l] h) :
    f⊔g ≤ᶠ[l] h := by
  filter_upwards [hf, hg] with x hfx hgx using sup_le hfx hgx

theorem EventuallyLe.le_sup_of_le_left [SemilatticeSup β] {l : Filter α} {f g h : α → β} (hf : h ≤ᶠ[l] f) :
    h ≤ᶠ[l] f⊔g := by
  filter_upwards [hf] with x hfx using le_sup_of_le_left hfx

theorem EventuallyLe.le_sup_of_le_right [SemilatticeSup β] {l : Filter α} {f g h : α → β} (hg : h ≤ᶠ[l] g) :
    h ≤ᶠ[l] f⊔g := by
  filter_upwards [hg] with x hgx using le_sup_of_le_right hgx

theorem join_le {f : Filter (Filter α)} {l : Filter α} (h : ∀ᶠ m in f, m ≤ l) : join f ≤ l := fun s hs =>
  h.mono fun m hm => hm hs

/-! ### Push-forwards, pull-backs, and the monad structure -/


section Map

/-- The forward map of a filter -/
def map (m : α → β) (f : Filter α) : Filter β where
  Sets := Preimage m ⁻¹' f.Sets
  univ_sets := univ_mem
  sets_of_superset := fun s t hs st => mem_of_superset hs <| preimage_mono st
  inter_sets := fun s t hs ht => inter_mem hs ht

@[simp]
theorem map_principal {s : Set α} {f : α → β} : map f (𝓟 s) = 𝓟 (Set.Image f s) :=
  Filter.ext fun a => image_subset_iff.symm

variable {f : Filter α} {m : α → β} {m' : β → γ} {s : Set α} {t : Set β}

@[simp]
theorem eventually_map {P : β → Prop} : (∀ᶠ b in map m f, P b) ↔ ∀ᶠ a in f, P (m a) :=
  Iff.rfl

@[simp]
theorem frequently_map {P : β → Prop} : (∃ᶠ b in map m f, P b) ↔ ∃ᶠ a in f, P (m a) :=
  Iff.rfl

@[simp]
theorem mem_map : t ∈ map m f ↔ m ⁻¹' t ∈ f :=
  Iff.rfl

theorem mem_map' : t ∈ map m f ↔ { x | m x ∈ t } ∈ f :=
  Iff.rfl

theorem image_mem_map (hs : s ∈ f) : m '' s ∈ map m f :=
  f.sets_of_superset hs <| subset_preimage_image m s

theorem image_mem_map_iff (hf : Injective m) : m '' s ∈ map m f ↔ s ∈ f :=
  ⟨fun h => by
    rwa [← preimage_image_eq s hf], image_mem_map⟩

theorem range_mem_map : Range m ∈ map m f := by
  rw [← image_univ]
  exact image_mem_map univ_mem

theorem mem_map_iff_exists_image : t ∈ map m f ↔ ∃ s ∈ f, m '' s ⊆ t :=
  ⟨fun ht => ⟨m ⁻¹' t, ht, image_preimage_subset _ _⟩, fun ⟨s, hs, ht⟩ => mem_of_superset (image_mem_map hs) ht⟩

@[simp]
theorem map_id : Filter.map id f = f :=
  filter_eq <| rfl

@[simp]
theorem map_id' : Filter.map (fun x => x) f = f :=
  map_id

@[simp]
theorem map_compose : Filter.map m' ∘ Filter.map m = Filter.map (m' ∘ m) :=
  funext fun _ => filter_eq <| rfl

@[simp]
theorem map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f :=
  congr_fun (@Filter.map_compose m m') f

/-- If functions `m₁` and `m₂` are eventually equal at a filter `f`, then
they map this filter to the same filter. -/
theorem map_congr {m₁ m₂ : α → β} {f : Filter α} (h : m₁ =ᶠ[f] m₂) : map m₁ f = map m₂ f :=
  Filter.ext' fun p => by
    simp only [← eventually_map]
    exact eventually_congr (h.mono fun x hx => hx ▸ Iff.rfl)

end Map

section Comap

/-- The inverse map of a filter. A set `s` belongs to `filter.comap f l` if either of the following
equivalent conditions hold.

1. There exists a set `t ∈ l` such that `f ⁻¹' t ⊆ s`. This is used as a definition.
2. The set `{y | ∀ x, f x = y → x ∈ s}` belongs to `l`, see `filter.mem_comap'`.
3. The set `(f '' sᶜ)ᶜ` belongs to `l`, see `filter.mem_comap_iff_compl` and
`filter.compl_mem_comap`. -/
def comap (m : α → β) (f : Filter β) : Filter α where
  Sets := { s | ∃ t ∈ f, m ⁻¹' t ⊆ s }
  univ_sets :=
    ⟨Univ, univ_mem, by
      simp only [← subset_univ, ← preimage_univ]⟩
  sets_of_superset := fun a b ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ => ⟨a' ∩ b', inter_mem ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩

variable {f : α → β} {l : Filter β} {p : α → Prop} {s : Set α}

theorem mem_comap' : s ∈ comap f l ↔ { y | ∀ ⦃x⦄, f x = y → x ∈ s } ∈ l :=
  ⟨fun ⟨t, ht, hts⟩ =>
    (mem_of_superset ht) fun y hy x hx =>
      hts <|
        mem_preimage.2 <| by
          rwa [hx],
    fun h => ⟨_, h, fun x hx => hx rfl⟩⟩

@[simp]
theorem eventually_comap : (∀ᶠ a in comap f l, p a) ↔ ∀ᶠ b in l, ∀ a, f a = b → p a :=
  mem_comap'

@[simp]
theorem frequently_comap : (∃ᶠ a in comap f l, p a) ↔ ∃ᶠ b in l, ∃ a, f a = b ∧ p a := by
  simp only [← Filter.Frequently, ← eventually_comap, ← not_exists, ← not_and]

theorem mem_comap_iff_compl : s ∈ comap f l ↔ (f '' sᶜ)ᶜ ∈ l := by
  simp only [← mem_comap', ← compl_def, ← mem_image, ← mem_set_of_eq, ← not_exists, ← not_and', ← not_not]

theorem compl_mem_comap : sᶜ ∈ comap f l ↔ (f '' s)ᶜ ∈ l := by
  rw [mem_comap_iff_compl, compl_compl]

end Comap

/-- The monadic bind operation on filter is defined the usual way in terms of `map` and `join`.

Unfortunately, this `bind` does not result in the expected applicative. See `filter.seq` for the
applicative instance. -/
def bind (f : Filter α) (m : α → Filter β) : Filter β :=
  join (map m f)

/-- The applicative sequentiation operation. This is not induced by the bind operation. -/
def seq (f : Filter (α → β)) (g : Filter α) : Filter β :=
  ⟨{ s | ∃ u ∈ f, ∃ t ∈ g, ∀, ∀ m ∈ u, ∀, ∀, ∀ x ∈ t, ∀, (m : α → β) x ∈ s },
    ⟨Univ, univ_mem, Univ, univ_mem, by
      simp only [← forall_prop_of_true, ← mem_univ, ← forall_true_iff]⟩,
    fun s₀ s₁ ⟨t₀, t₁, h₀, h₁, h⟩ hst => ⟨t₀, t₁, h₀, h₁, fun x hx y hy => hst <| h _ hx _ hy⟩,
    fun s₀ s₁ ⟨t₀, ht₀, t₁, ht₁, ht⟩ ⟨u₀, hu₀, u₁, hu₁, hu⟩ =>
    ⟨t₀ ∩ u₀, inter_mem ht₀ hu₀, t₁ ∩ u₁, inter_mem ht₁ hu₁, fun x ⟨hx₀, hx₁⟩ x ⟨hy₀, hy₁⟩ =>
      ⟨ht _ hx₀ _ hy₀, hu _ hx₁ _ hy₁⟩⟩⟩

/-- `pure x` is the set of sets that contain `x`. It is equal to `𝓟 {x}` but
with this definition we have `s ∈ pure a` defeq `a ∈ s`. -/
instance : Pure Filter :=
  ⟨fun (α : Type u) x =>
    { Sets := { s | x ∈ s }, inter_sets := fun s t => And.intro, sets_of_superset := fun s t hs hst => hst hs,
      univ_sets := trivialₓ }⟩

instance : Bind Filter :=
  ⟨@Filter.bind⟩

instance : Seqₓ Filter :=
  ⟨@Filter.seq⟩

instance : Functor Filter where map := @Filter.map

theorem pure_sets (a : α) : (pure a : Filter α).Sets = { s | a ∈ s } :=
  rfl

@[simp]
theorem mem_pure {a : α} {s : Set α} : s ∈ (pure a : Filter α) ↔ a ∈ s :=
  Iff.rfl

@[simp]
theorem eventually_pure {a : α} {p : α → Prop} : (∀ᶠ x in pure a, p x) ↔ p a :=
  Iff.rfl

@[simp]
theorem principal_singleton (a : α) : 𝓟 {a} = pure a :=
  Filter.ext fun s => by
    simp only [← mem_pure, ← mem_principal, ← singleton_subset_iff]

@[simp]
theorem map_pure (f : α → β) (a : α) : map f (pure a) = pure (f a) :=
  rfl

@[simp]
theorem join_pure (f : Filter α) : join (pure f) = f :=
  Filter.ext fun s => Iff.rfl

@[simp]
theorem pure_bind (a : α) (m : α → Filter β) : bind (pure a) m = m a := by
  simp only [← Bind.bind, ← bind, ← map_pure, ← join_pure]

section

/-- The monad structure on filters. -/
-- this section needs to be before applicative, otherwise the wrong instance will be chosen
protected def monad : Monadₓ Filter where map := @Filter.map

attribute [local instance] Filter.monad

protected theorem is_lawful_monad : IsLawfulMonad Filter :=
  { id_map := fun α f => filter_eq rfl, pure_bind := fun α β => pure_bind,
    bind_assoc := fun α β γ f m₁ m₂ => filter_eq rfl,
    bind_pure_comp_eq_map := fun α β f x =>
      Filter.ext fun s => by
        simp only [← Bind.bind, ← bind, ← Functor.map, ← mem_map', ← mem_join, ← mem_set_of_eq, ← comp, ← mem_pure] }

end

instance : Applicativeₓ Filter where
  map := @Filter.map
  seq := @Filter.seq

instance : Alternativeₓ Filter where
  failure := fun α => ⊥
  orelse := fun α x y => x⊔y

@[simp]
theorem map_def {α β} (m : α → β) (f : Filter α) : m <$> f = map m f :=
  rfl

@[simp]
theorem bind_def {α β} (f : Filter α) (m : α → Filter β) : f >>= m = bind f m :=
  rfl

/-! #### `map` and `comap` equations -/


section Map

variable {f f₁ f₂ : Filter α} {g g₁ g₂ : Filter β} {m : α → β} {m' : β → γ} {s : Set α} {t : Set β}

@[simp]
theorem mem_comap : s ∈ comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s :=
  Iff.rfl

theorem preimage_mem_comap (ht : t ∈ g) : m ⁻¹' t ∈ comap m g :=
  ⟨t, ht, Subset.rfl⟩

theorem Eventually.comap {p : β → Prop} (hf : ∀ᶠ b in g, p b) (f : α → β) : ∀ᶠ a in comap f g, p (f a) :=
  preimage_mem_comap hf

theorem comap_id : comap id f = f :=
  le_antisymmₓ (fun s => preimage_mem_comap) fun s ⟨t, ht, hst⟩ => mem_of_superset ht hst

theorem comap_const_of_not_mem {x : β} (ht : t ∈ g) (hx : x ∉ t) : comap (fun y : α => x) g = ⊥ :=
  empty_mem_iff_bot.1 <| mem_comap'.2 <| (mem_of_superset ht) fun x' hx' y h => hx <| h.symm ▸ hx'

theorem comap_const_of_mem {x : β} (h : ∀, ∀ t ∈ g, ∀, x ∈ t) : comap (fun y : α => x) g = ⊤ :=
  top_unique fun s hs => univ_mem' fun y => h _ (mem_comap'.1 hs) rfl

theorem map_const [NeBot f] {c : β} : (f.map fun x => c) = pure c := by
  ext s
  by_cases' h : c ∈ s <;> simp [← h]

theorem comap_comap {m : γ → β} {n : β → α} : comap m (comap n f) = comap (n ∘ m) f :=
  Filter.coext fun s => by
    simp only [← compl_mem_comap, ← image_image]

section comm

/-!
The variables in the following lemmas are used as in this diagram:
```
    φ
  α → β
θ ↓   ↓ ψ
  γ → δ
    ρ
```
-/


variable {φ : α → β} {θ : α → γ} {ψ : β → δ} {ρ : γ → δ} (H : ψ ∘ φ = ρ ∘ θ)

include H

theorem map_comm (F : Filter α) : map ψ (map φ F) = map ρ (map θ F) := by
  rw [Filter.map_map, H, ← Filter.map_map]

theorem comap_comm (G : Filter δ) : comap φ (comap ψ G) = comap θ (comap ρ G) := by
  rw [Filter.comap_comap, H, ← Filter.comap_comap]

end comm

theorem _root_.function.semiconj.filter_map {f : α → β} {ga : α → α} {gb : β → β} (h : Function.Semiconj f ga gb) :
    Function.Semiconj (map f) (map ga) (map gb) :=
  map_comm h.comp_eq

theorem _root_.commute.filter_map {f g : α → α} (h : Function.Commute f g) : Function.Commute (map f) (map g) :=
  h.filterMap

theorem _root_.function.semiconj.filter_comap {f : α → β} {ga : α → α} {gb : β → β} (h : Function.Semiconj f ga gb) :
    Function.Semiconj (comap f) (comap gb) (comap ga) :=
  comap_comm h.comp_eq.symm

theorem _root_.commute.filter_comap {f g : α → α} (h : Function.Commute f g) : Function.Commute (comap f) (comap g) :=
  h.filter_comap

@[simp]
theorem comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 (m ⁻¹' t) :=
  Filter.ext fun s =>
    ⟨fun ⟨u, (hu : t ⊆ u), (b : preimage m u ⊆ s)⟩ => (preimage_mono hu).trans b, fun h => ⟨t, Subset.refl t, h⟩⟩

@[simp]
theorem comap_pure {b : β} : comap m (pure b) = 𝓟 (m ⁻¹' {b}) := by
  rw [← principal_singleton, comap_principal]

theorem map_le_iff_le_comap : map m f ≤ g ↔ f ≤ comap m g :=
  ⟨fun h s ⟨t, ht, hts⟩ => mem_of_superset (h ht) hts, fun h s ht => h ⟨_, ht, Subset.rfl⟩⟩

theorem gc_map_comap (m : α → β) : GaloisConnection (map m) (comap m) := fun f g => map_le_iff_le_comap

@[mono]
theorem map_mono : Monotone (map m) :=
  (gc_map_comap m).monotone_l

@[mono]
theorem comap_mono : Monotone (comap m) :=
  (gc_map_comap m).monotone_u

@[simp]
theorem map_bot : map m ⊥ = ⊥ :=
  (gc_map_comap m).l_bot

@[simp]
theorem map_sup : map m (f₁⊔f₂) = map m f₁⊔map m f₂ :=
  (gc_map_comap m).l_sup

@[simp]
theorem map_supr {f : ι → Filter α} : map m (⨆ i, f i) = ⨆ i, map m (f i) :=
  (gc_map_comap m).l_supr

@[simp]
theorem map_top (f : α → β) : map f ⊤ = 𝓟 (Range f) := by
  rw [← principal_univ, map_principal, image_univ]

@[simp]
theorem comap_top : comap m ⊤ = ⊤ :=
  (gc_map_comap m).u_top

@[simp]
theorem comap_inf : comap m (g₁⊓g₂) = comap m g₁⊓comap m g₂ :=
  (gc_map_comap m).u_inf

@[simp]
theorem comap_infi {f : ι → Filter β} : comap m (⨅ i, f i) = ⨅ i, comap m (f i) :=
  (gc_map_comap m).u_infi

theorem le_comap_top (f : α → β) (l : Filter α) : l ≤ comap f ⊤ := by
  rw [comap_top]
  exact le_top

theorem map_comap_le : map m (comap m g) ≤ g :=
  (gc_map_comap m).l_u_le _

theorem le_comap_map : f ≤ comap m (map m f) :=
  (gc_map_comap m).le_u_l _

@[simp]
theorem comap_bot : comap m ⊥ = ⊥ :=
  bot_unique fun s _ =>
    ⟨∅, mem_bot, by
      simp only [← empty_subset, ← preimage_empty]⟩

theorem comap_inf_principal_range : comap m (g⊓𝓟 (Range m)) = comap m g := by
  simp

theorem disjoint_comap (h : Disjoint g₁ g₂) : Disjoint (comap m g₁) (comap m g₂) := by
  simp only [← disjoint_iff, comap_inf, ← h.eq_bot, ← comap_bot]

theorem comap_supr {ι} {f : ι → Filter β} {m : α → β} : comap m (supr f) = ⨆ i, comap m (f i) :=
  le_antisymmₓ
    (fun s hs =>
      have : ∀ i, ∃ t, t ∈ f i ∧ m ⁻¹' t ⊆ s := by
        simpa only [← mem_comap, ← exists_prop, ← mem_supr] using mem_supr.1 hs
      let ⟨t, ht⟩ := Classical.axiom_of_choice this
      ⟨⋃ i, t i, mem_supr.2 fun i => (f i).sets_of_superset (ht i).1 (subset_Union _ _), by
        rw [preimage_Union, Union_subset_iff]
        exact fun i => (ht i).2⟩)
    (supr_le fun i => comap_mono <| le_supr _ _)

theorem comap_Sup {s : Set (Filter β)} {m : α → β} : comap m (sup s) = ⨆ f ∈ s, comap m f := by
  simp only [← Sup_eq_supr, ← comap_supr, ← eq_self_iff_true]

theorem comap_sup : comap m (g₁⊔g₂) = comap m g₁⊔comap m g₂ := by
  rw [sup_eq_supr, comap_supr, supr_bool_eq, Bool.cond_tt, Bool.cond_ff]

theorem map_comap (f : Filter β) (m : α → β) : (f.comap m).map m = f⊓𝓟 (Range m) := by
  refine' le_antisymmₓ (le_inf map_comap_le <| le_principal_iff.2 range_mem_map) _
  rintro t' ⟨t, ht, sub⟩
  refine' mem_inf_principal.2 (mem_of_superset ht _)
  rintro _ hxt ⟨x, rfl⟩
  exact sub hxt

theorem map_comap_of_mem {f : Filter β} {m : α → β} (hf : Range m ∈ f) : (f.comap m).map m = f := by
  rw [map_comap, inf_eq_left.2 (le_principal_iff.2 hf)]

instance [CanLift α β] : CanLift (Filter α) (Filter β) where
  coe := map CanLift.coe
  cond := fun f => ∀ᶠ x : α in f, CanLift.Cond β x
  prf := fun f hf => ⟨comap CanLift.coe f, map_comap_of_mem <| hf.mono CanLift.prf⟩

theorem comap_le_comap_iff {f g : Filter β} {m : α → β} (hf : Range m ∈ f) : comap m f ≤ comap m g ↔ f ≤ g :=
  ⟨fun h => map_comap_of_mem hf ▸ (map_mono h).trans map_comap_le, fun h => comap_mono h⟩

theorem map_comap_of_surjective {f : α → β} (hf : Surjective f) (l : Filter β) : map f (comap f l) = l :=
  map_comap_of_mem <| by
    simp only [← hf.range_eq, ← univ_mem]

theorem _root_.function.surjective.filter_map_top {f : α → β} (hf : Surjective f) : map f ⊤ = ⊤ :=
  (congr_arg _ comap_top).symm.trans <| map_comap_of_surjective hf ⊤

theorem subtype_coe_map_comap (s : Set α) (f : Filter α) : map (coe : s → α) (comap (coe : s → α) f) = f⊓𝓟 s := by
  rw [map_comap, Subtype.range_coe]

theorem subtype_coe_map_comap_prod (s : Set α) (f : Filter (α × α)) :
    map (coe : s × s → α × α) (comap (coe : s × s → α × α) f) = f⊓𝓟 (s ×ˢ s) := by
  have : (coe : s × s → α × α) = fun x => (x.1, x.2) := by
    ext ⟨x, y⟩ <;> rfl
  simp [← this, ← map_comap, prod_range_range_eq]

theorem image_mem_of_mem_comap {f : Filter α} {c : β → α} (h : Range c ∈ f) {W : Set β} (W_in : W ∈ comap c f) :
    c '' W ∈ f := by
  rw [← map_comap_of_mem h]
  exact image_mem_map W_in

theorem image_coe_mem_of_mem_comap {f : Filter α} {U : Set α} (h : U ∈ f) {W : Set U}
    (W_in : W ∈ comap (coe : U → α) f) : coe '' W ∈ f :=
  image_mem_of_mem_comap
    (by
      simp [← h])
    W_in

theorem comap_map {f : Filter α} {m : α → β} (h : Injective m) : comap m (map m f) = f :=
  le_antisymmₓ
    (fun s hs =>
      mem_of_superset (preimage_mem_comap <| image_mem_map hs) <| by
        simp only [← preimage_image_eq s h])
    le_comap_map

theorem mem_comap_iff {f : Filter β} {m : α → β} (inj : Injective m) (large : Set.Range m ∈ f) {S : Set α} :
    S ∈ comap m f ↔ m '' S ∈ f := by
  rw [← image_mem_map_iff inj, map_comap_of_mem large]

theorem map_le_map_iff_of_inj_on {l₁ l₂ : Filter α} {f : α → β} {s : Set α} (h₁ : s ∈ l₁) (h₂ : s ∈ l₂)
    (hinj : InjOn f s) : map f l₁ ≤ map f l₂ ↔ l₁ ≤ l₂ :=
  ⟨fun h t ht =>
    mp_mem h₁ <|
      (mem_of_superset (h <| image_mem_map (inter_mem h₂ ht))) fun y ⟨x, ⟨hxs, hxt⟩, hxy⟩ hys => hinj hxs hys hxy ▸ hxt,
    fun h => map_mono h⟩

theorem map_le_map_iff {f g : Filter α} {m : α → β} (hm : Injective m) : map m f ≤ map m g ↔ f ≤ g := by
  rw [map_le_iff_le_comap, comap_map hm]

theorem map_eq_map_iff_of_inj_on {f g : Filter α} {m : α → β} {s : Set α} (hsf : s ∈ f) (hsg : s ∈ g) (hm : InjOn m s) :
    map m f = map m g ↔ f = g := by
  simp only [← le_antisymm_iffₓ, ← map_le_map_iff_of_inj_on hsf hsg hm, ← map_le_map_iff_of_inj_on hsg hsf hm]

theorem map_inj {f g : Filter α} {m : α → β} (hm : Injective m) : map m f = map m g ↔ f = g :=
  map_eq_map_iff_of_inj_on univ_mem univ_mem (hm.InjOn _)

theorem map_injective {m : α → β} (hm : Injective m) : Injective (map m) := fun f g => (map_inj hm).1

theorem comap_ne_bot_iff {f : Filter β} {m : α → β} : NeBot (comap m f) ↔ ∀, ∀ t ∈ f, ∀, ∃ a, m a ∈ t := by
  simp only [forall_mem_nonempty_iff_ne_bot, ← mem_comap, ← forall_exists_index]
  exact ⟨fun h t t_in => h (m ⁻¹' t) t t_in subset.rfl, fun h s t ht hst => (h t ht).imp hst⟩

theorem comap_ne_bot {f : Filter β} {m : α → β} (hm : ∀, ∀ t ∈ f, ∀, ∃ a, m a ∈ t) : NeBot (comap m f) :=
  comap_ne_bot_iff.mpr hm

theorem comap_ne_bot_iff_frequently {f : Filter β} {m : α → β} : NeBot (comap m f) ↔ ∃ᶠ y in f, y ∈ Range m := by
  simp [← comap_ne_bot_iff, ← frequently_iff, exists_and_distrib_left, ← And.comm]

theorem comap_ne_bot_iff_compl_range {f : Filter β} {m : α → β} : NeBot (comap m f) ↔ Range mᶜ ∉ f :=
  comap_ne_bot_iff_frequently

theorem NeBot.comap_of_range_mem {f : Filter β} {m : α → β} (hf : NeBot f) (hm : Range m ∈ f) : NeBot (comap m f) :=
  comap_ne_bot_iff_frequently.2 <| Eventually.frequently hm

@[simp]
theorem comap_fst_ne_bot_iff {f : Filter α} : (f.comap (Prod.fst : α × β → α)).ne_bot ↔ f.ne_bot ∧ Nonempty β := by
  cases is_empty_or_nonempty β
  · rw [filter_eq_bot_of_is_empty (f.comap _), ← not_iff_not] <;> [simp [*], infer_instance]
    
  · simp [← comap_ne_bot_iff_frequently, ← h]
    

@[instance]
theorem comap_fst_ne_bot [Nonempty β] {f : Filter α} [NeBot f] : (f.comap (Prod.fst : α × β → α)).ne_bot :=
  comap_fst_ne_bot_iff.2 ⟨‹_›, ‹_›⟩

@[simp]
theorem comap_snd_ne_bot_iff {f : Filter β} : (f.comap (Prod.snd : α × β → β)).ne_bot ↔ Nonempty α ∧ f.ne_bot := by
  cases' is_empty_or_nonempty α with hα hα
  · rw [filter_eq_bot_of_is_empty (f.comap _), ← not_iff_not] <;> [simp , infer_instance]
    
  · simp [← comap_ne_bot_iff_frequently, ← hα]
    

@[instance]
theorem comap_snd_ne_bot [Nonempty α] {f : Filter β} [NeBot f] : (f.comap (Prod.snd : α × β → β)).ne_bot :=
  comap_snd_ne_bot_iff.2 ⟨‹_›, ‹_›⟩

theorem comap_eval_ne_bot_iff' {ι : Type _} {α : ι → Type _} {i : ι} {f : Filter (α i)} :
    (comap (eval i) f).ne_bot ↔ (∀ j, Nonempty (α j)) ∧ NeBot f := by
  cases' is_empty_or_nonempty (∀ j, α j) with H H
  · rw [filter_eq_bot_of_is_empty (f.comap _), ← not_iff_not] <;> [skip, assumption]
    simp [Classical.nonempty_piₓ]
    
  · have : ∀ j, Nonempty (α j) := Classical.nonempty_piₓ.1 H
    simp [← comap_ne_bot_iff_frequently, *]
    

@[simp]
theorem comap_eval_ne_bot_iff {ι : Type _} {α : ι → Type _} [∀ j, Nonempty (α j)] {i : ι} {f : Filter (α i)} :
    (comap (eval i) f).ne_bot ↔ NeBot f := by
  simp [← comap_eval_ne_bot_iff', *]

@[instance]
theorem comap_eval_ne_bot {ι : Type _} {α : ι → Type _} [∀ j, Nonempty (α j)] (i : ι) (f : Filter (α i)) [NeBot f] :
    (comap (eval i) f).ne_bot :=
  comap_eval_ne_bot_iff.2 ‹_›

theorem comap_inf_principal_ne_bot_of_image_mem {f : Filter β} {m : α → β} (hf : NeBot f) {s : Set α}
    (hs : m '' s ∈ f) : NeBot (comap m f⊓𝓟 s) := by
  refine' ⟨compl_compl s ▸ mt mem_of_eq_bot _⟩
  rintro ⟨t, ht, hts⟩
  rcases hf.nonempty_of_mem (inter_mem hs ht) with ⟨_, ⟨x, hxs, rfl⟩, hxt⟩
  exact absurd hxs (hts hxt)

theorem comap_coe_ne_bot_of_le_principal {s : Set γ} {l : Filter γ} [h : NeBot l] (h' : l ≤ 𝓟 s) :
    NeBot (comap (coe : s → γ) l) :=
  h.comap_of_range_mem <| (@Subtype.range_coe γ s).symm ▸ h' (mem_principal_self s)

theorem NeBot.comap_of_surj {f : Filter β} {m : α → β} (hf : NeBot f) (hm : Surjective m) : NeBot (comap m f) :=
  hf.comap_of_range_mem <| univ_mem' hm

theorem NeBot.comap_of_image_mem {f : Filter β} {m : α → β} (hf : NeBot f) {s : Set α} (hs : m '' s ∈ f) :
    NeBot (comap m f) :=
  hf.comap_of_range_mem <| mem_of_superset hs (image_subset_range _ _)

@[simp]
theorem map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥ :=
  ⟨by
    rw [← empty_mem_iff_bot, ← empty_mem_iff_bot]
    exact id, fun h => by
    simp only [← h, ← map_bot]⟩

theorem map_ne_bot_iff (f : α → β) {F : Filter α} : NeBot (map f F) ↔ NeBot F := by
  simp only [← ne_bot_iff, ← Ne, ← map_eq_bot_iff]

theorem NeBot.map (hf : NeBot f) (m : α → β) : NeBot (map m f) :=
  (map_ne_bot_iff m).2 hf

theorem NeBot.of_map : NeBot (f.map m) → NeBot f :=
  (map_ne_bot_iff m).1

instance map_ne_bot [hf : NeBot f] : NeBot (f.map m) :=
  hf.map m

theorem sInter_comap_sets (f : α → β) (F : Filter β) : ⋂₀ (comap f F).Sets = ⋂ U ∈ F, f ⁻¹' U := by
  ext x
  suffices (∀ (A : Set α) (B : Set β), B ∈ F → f ⁻¹' B ⊆ A → x ∈ A) ↔ ∀ B : Set β, B ∈ F → f x ∈ B by
    simp only [← mem_sInter, ← mem_Inter, ← Filter.mem_sets, ← mem_comap, ← this, ← and_imp, ← exists_prop, ←
      mem_preimage, ← exists_imp_distrib]
  constructor
  · intro h U U_in
    simpa only [← subset.refl, ← forall_prop_of_true, ← mem_preimage] using h (f ⁻¹' U) U U_in
    
  · intro h V U U_in f_U_V
    exact f_U_V (h U U_in)
    

end Map

-- this is a generic rule for monotone functions:
theorem map_infi_le {f : ι → Filter α} {m : α → β} : map m (infi f) ≤ ⨅ i, map m (f i) :=
  le_infi fun i => map_mono <| infi_le _ _

theorem map_infi_eq {f : ι → Filter α} {m : α → β} (hf : Directed (· ≥ ·) f) [Nonempty ι] :
    map m (infi f) = ⨅ i, map m (f i) :=
  map_infi_le.antisymm fun s (hs : Preimage m s ∈ infi f) =>
    let ⟨i, hi⟩ := (mem_infi_of_directed hf _).1 hs
    have : (⨅ i, map m (f i)) ≤ 𝓟 s :=
      infi_le_of_le i <| by
        simp only [← le_principal_iff, ← mem_map]
        assumption
    Filter.le_principal_iff.1 this

theorem map_binfi_eq {ι : Type w} {f : ι → Filter α} {m : α → β} {p : ι → Prop}
    (h : DirectedOn (f ⁻¹'o (· ≥ ·)) { x | p x }) (ne : ∃ i, p i) :
    map m (⨅ (i) (h : p i), f i) = ⨅ (i) (h : p i), map m (f i) := by
  have := nonempty_subtype.2 Ne
  simp only [← infi_subtype']
  exact map_infi_eq h.directed_coe

theorem map_inf_le {f g : Filter α} {m : α → β} : map m (f⊓g) ≤ map m f⊓map m g :=
  (@map_mono _ _ m).map_inf_le f g

theorem map_inf {f g : Filter α} {m : α → β} (h : Injective m) : map m (f⊓g) = map m f⊓map m g := by
  refine' map_inf_le.antisymm _
  rintro t ⟨s₁, hs₁, s₂, hs₂, ht : m ⁻¹' t = s₁ ∩ s₂⟩
  refine' mem_inf_of_inter (image_mem_map hs₁) (image_mem_map hs₂) _
  rw [image_inter h, image_subset_iff, ht]

theorem map_inf' {f g : Filter α} {m : α → β} {t : Set α} (htf : t ∈ f) (htg : t ∈ g) (h : InjOn m t) :
    map m (f⊓g) = map m f⊓map m g := by
  lift f to Filter t using htf
  lift g to Filter t using htg
  replace h : injective (m ∘ coe) := h.injective
  simp only [← map_map, map_inf Subtype.coe_injective, ← map_inf h]

theorem disjoint_map {m : α → β} (hm : Injective m) {f₁ f₂ : Filter α} :
    Disjoint (map m f₁) (map m f₂) ↔ Disjoint f₁ f₂ := by
  simp only [← disjoint_iff, map_inf hm, ← map_eq_bot_iff]

theorem map_eq_comap_of_inverse {f : Filter α} {m : α → β} {n : β → α} (h₁ : m ∘ n = id) (h₂ : n ∘ m = id) :
    map m f = comap n f :=
  le_antisymmₓ
    (fun b ⟨a, ha, (h : preimage n a ⊆ b)⟩ =>
      f.sets_of_superset ha <|
        calc
          a = Preimage (n ∘ m) a := by
            simp only [← h₂, ← preimage_id, ← eq_self_iff_true]
          _ ⊆ Preimage m b := preimage_mono h
          )
    fun b (hb : Preimage m b ∈ f) =>
    ⟨Preimage m b, hb,
      show Preimage (m ∘ n) b ⊆ b by
        simp only [← h₁] <;> apply subset.refl⟩

theorem map_equiv_symm (e : α ≃ β) (f : Filter β) : map e.symm f = comap e f :=
  map_eq_comap_of_inverse e.symm_comp_self e.self_comp_symm

theorem comap_equiv_symm (e : α ≃ β) (f : Filter α) : comap e.symm f = map e f :=
  (map_eq_comap_of_inverse e.self_comp_symm e.symm_comp_self).symm

theorem map_swap_eq_comap_swap {f : Filter (α × β)} : Prod.swap <$> f = comap Prod.swap f :=
  map_eq_comap_of_inverse Prod.swap_swap_eq Prod.swap_swap_eq

/-- A useful lemma when dealing with uniformities. -/
theorem map_swap4_eq_comap {f : Filter ((α × β) × γ × δ)} :
    map (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f =
      comap (fun p : (α × γ) × β × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f :=
  map_eq_comap_of_inverse (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl) (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl)

theorem le_map {f : Filter α} {m : α → β} {g : Filter β} (h : ∀, ∀ s ∈ f, ∀, m '' s ∈ g) : g ≤ f.map m := fun s hs =>
  mem_of_superset (h _ hs) <| image_preimage_subset _ _

theorem le_map_iff {f : Filter α} {m : α → β} {g : Filter β} : g ≤ f.map m ↔ ∀, ∀ s ∈ f, ∀, m '' s ∈ g :=
  ⟨fun h s hs => h (image_mem_map hs), le_map⟩

protected theorem push_pull (f : α → β) (F : Filter α) (G : Filter β) : map f (F⊓comap f G) = map f F⊓G := by
  apply le_antisymmₓ
  · calc map f (F⊓comap f G) ≤ map f F⊓(map f <| comap f G) := map_inf_le _ ≤ map f F⊓G :=
        inf_le_inf_left (map f F) map_comap_le
    
  · rintro U ⟨V, V_in, W, ⟨Z, Z_in, hZ⟩, h⟩
    apply mem_inf_of_inter (image_mem_map V_in) Z_in
    calc f '' V ∩ Z = f '' (V ∩ f ⁻¹' Z) := by
        rw [image_inter_preimage]_ ⊆ f '' (V ∩ W) :=
        image_subset _ (inter_subset_inter_right _ ‹_›)_ = f '' (f ⁻¹' U) := by
        rw [h]_ ⊆ U := image_preimage_subset f U
    

protected theorem push_pull' (f : α → β) (F : Filter α) (G : Filter β) : map f (comap f G⊓F) = G⊓map f F := by
  simp only [← Filter.push_pull, ← inf_comm]

section Applicativeₓ

theorem singleton_mem_pure {a : α} : {a} ∈ (pure a : Filter α) :=
  mem_singleton a

theorem pure_injective : Injective (pure : α → Filter α) := fun a b hab => (Filter.ext_iff.1 hab { x | a = x }).1 rfl

instance pure_ne_bot {α : Type u} {a : α} : NeBot (pure a) :=
  ⟨mt empty_mem_iff_bot.2 <| not_mem_empty a⟩

@[simp]
theorem le_pure_iff {f : Filter α} {a : α} : f ≤ pure a ↔ {a} ∈ f :=
  ⟨fun h => h singleton_mem_pure, fun h s hs => mem_of_superset h <| singleton_subset_iff.2 hs⟩

theorem mem_seq_def {f : Filter (α → β)} {g : Filter α} {s : Set β} :
    s ∈ f.seq g ↔ ∃ u ∈ f, ∃ t ∈ g, ∀, ∀ x ∈ u, ∀, ∀, ∀ y ∈ t, ∀, (x : α → β) y ∈ s :=
  Iff.rfl

theorem mem_seq_iff {f : Filter (α → β)} {g : Filter α} {s : Set β} : s ∈ f.seq g ↔ ∃ u ∈ f, ∃ t ∈ g, Set.Seq u t ⊆ s :=
  by
  simp only [← mem_seq_def, ← seq_subset, ← exists_prop, ← iff_selfₓ]

theorem mem_map_seq_iff {f : Filter α} {g : Filter β} {m : α → β → γ} {s : Set γ} :
    s ∈ (f.map m).seq g ↔ ∃ t u, t ∈ g ∧ u ∈ f ∧ ∀, ∀ x ∈ u, ∀, ∀, ∀ y ∈ t, ∀, m x y ∈ s :=
  Iff.intro (fun ⟨t, ht, s, hs, hts⟩ => ⟨s, m ⁻¹' t, hs, ht, fun a => hts _⟩) fun ⟨t, s, ht, hs, hts⟩ =>
    ⟨m '' s, image_mem_map hs, t, ht, fun f ⟨a, has, Eq⟩ => Eq ▸ hts _ has⟩

theorem seq_mem_seq {f : Filter (α → β)} {g : Filter α} {s : Set (α → β)} {t : Set α} (hs : s ∈ f) (ht : t ∈ g) :
    s.seq t ∈ f.seq g :=
  ⟨s, hs, t, ht, fun f hf a ha => ⟨f, hf, a, ha, rfl⟩⟩

theorem le_seq {f : Filter (α → β)} {g : Filter α} {h : Filter β} (hh : ∀, ∀ t ∈ f, ∀, ∀, ∀ u ∈ g, ∀, Set.Seq t u ∈ h) :
    h ≤ seq f g := fun s ⟨t, ht, u, hu, hs⟩ =>
  (mem_of_superset (hh _ ht _ hu)) fun b ⟨m, hm, a, ha, Eq⟩ => Eq ▸ hs _ hm _ ha

@[mono]
theorem seq_mono {f₁ f₂ : Filter (α → β)} {g₁ g₂ : Filter α} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.seq g₁ ≤ f₂.seq g₂ :=
  le_seq fun s hs t ht => seq_mem_seq (hf hs) (hg ht)

@[simp]
theorem pure_seq_eq_map (g : α → β) (f : Filter α) : seq (pure g) f = f.map g := by
  refine' le_antisymmₓ (le_map fun s hs => _) (le_seq fun s hs t ht => _)
  · rw [← singleton_seq]
    apply seq_mem_seq _ hs
    exact singleton_mem_pure
    
  · refine' sets_of_superset (map g f) (image_mem_map ht) _
    rintro b ⟨a, ha, rfl⟩
    exact ⟨g, hs, a, ha, rfl⟩
    

@[simp]
theorem seq_pure (f : Filter (α → β)) (a : α) : seq f (pure a) = map (fun g : α → β => g a) f := by
  refine' le_antisymmₓ (le_map fun s hs => _) (le_seq fun s hs t ht => _)
  · rw [← seq_singleton]
    exact seq_mem_seq hs singleton_mem_pure
    
  · refine' sets_of_superset (map (fun g : α → β => g a) f) (image_mem_map hs) _
    rintro b ⟨g, hg, rfl⟩
    exact ⟨g, hg, a, ht, rfl⟩
    

@[simp]
theorem seq_assoc (x : Filter α) (g : Filter (α → β)) (h : Filter (β → γ)) :
    seq h (seq g x) = seq (seq (map (· ∘ ·) h) g) x := by
  refine' le_antisymmₓ (le_seq fun s hs t ht => _) (le_seq fun s hs t ht => _)
  · rcases mem_seq_iff.1 hs with ⟨u, hu, v, hv, hs⟩
    rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hu⟩
    refine' mem_of_superset _ (Set.seq_mono ((Set.seq_mono hu subset.rfl).trans hs) subset.rfl)
    rw [← Set.seq_seq]
    exact seq_mem_seq hw (seq_mem_seq hv ht)
    
  · rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩
    refine' mem_of_superset _ (Set.seq_mono subset.rfl ht)
    rw [Set.seq_seq]
    exact seq_mem_seq (seq_mem_seq (image_mem_map hs) hu) hv
    

theorem prod_map_seq_comm (f : Filter α) (g : Filter β) : (map Prod.mk f).seq g = seq (map (fun b a => (a, b)) g) f :=
  by
  refine' le_antisymmₓ (le_seq fun s hs t ht => _) (le_seq fun s hs t ht => _)
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    refine' mem_of_superset _ (Set.seq_mono hs subset.rfl)
    rw [← Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu
    
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    refine' mem_of_superset _ (Set.seq_mono hs subset.rfl)
    rw [Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu
    

instance : IsLawfulFunctor (Filter : Type u → Type u) where
  id_map := fun α f => map_id
  comp_map := fun α β γ f g a => map_map.symm

instance : IsLawfulApplicative (Filter : Type u → Type u) where
  pure_seq_eq_map := fun α β => pure_seq_eq_map
  map_pure := fun α β => map_pure
  seq_pure := fun α β => seq_pure
  seq_assoc := fun α β γ => seq_assoc

instance : IsCommApplicative (Filter : Type u → Type u) :=
  ⟨fun α β f g => prod_map_seq_comm f g⟩

theorem seq_eq_filter_seq.{l} {α β : Type l} (f : Filter (α → β)) (g : Filter α) : f <*> g = seq f g :=
  rfl

end Applicativeₓ

/-! #### `bind` equations -/


section Bind

@[simp]
theorem eventually_bind {f : Filter α} {m : α → Filter β} {p : β → Prop} :
    (∀ᶠ y in bind f m, p y) ↔ ∀ᶠ x in f, ∀ᶠ y in m x, p y :=
  Iff.rfl

@[simp]
theorem eventually_eq_bind {f : Filter α} {m : α → Filter β} {g₁ g₂ : β → γ} :
    g₁ =ᶠ[bind f m] g₂ ↔ ∀ᶠ x in f, g₁ =ᶠ[m x] g₂ :=
  Iff.rfl

@[simp]
theorem eventually_le_bind [LE γ] {f : Filter α} {m : α → Filter β} {g₁ g₂ : β → γ} :
    g₁ ≤ᶠ[bind f m] g₂ ↔ ∀ᶠ x in f, g₁ ≤ᶠ[m x] g₂ :=
  Iff.rfl

theorem mem_bind' {s : Set β} {f : Filter α} {m : α → Filter β} : s ∈ bind f m ↔ { a | s ∈ m a } ∈ f :=
  Iff.rfl

@[simp]
theorem mem_bind {s : Set β} {f : Filter α} {m : α → Filter β} : s ∈ bind f m ↔ ∃ t ∈ f, ∀, ∀ x ∈ t, ∀, s ∈ m x :=
  calc
    s ∈ bind f m ↔ { a | s ∈ m a } ∈ f := Iff.rfl
    _ ↔ ∃ t ∈ f, t ⊆ { a | s ∈ m a } := exists_mem_subset_iff.symm
    _ ↔ ∃ t ∈ f, ∀, ∀ x ∈ t, ∀, s ∈ m x := Iff.rfl
    

theorem bind_le {f : Filter α} {g : α → Filter β} {l : Filter β} (h : ∀ᶠ x in f, g x ≤ l) : f.bind g ≤ l :=
  join_le <| eventually_map.2 h

@[mono]
theorem bind_mono {f₁ f₂ : Filter α} {g₁ g₂ : α → Filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ᶠ[f₁] g₂) :
    bind f₁ g₁ ≤ bind f₂ g₂ := by
  refine' le_transₓ (fun s hs => _) (join_mono <| map_mono hf)
  simp only [← mem_join, ← mem_bind', ← mem_map] at hs⊢
  filter_upwards [hg, hs] with _ hx hs using hx hs

theorem bind_inf_principal {f : Filter α} {g : α → Filter β} {s : Set β} : (f.bind fun x => g x⊓𝓟 s) = f.bind g⊓𝓟 s :=
  Filter.ext fun s => by
    simp only [← mem_bind, ← mem_inf_principal]

theorem sup_bind {f g : Filter α} {h : α → Filter β} : bind (f⊔g) h = bind f h⊔bind g h := by
  simp only [← bind, ← sup_join, ← map_sup, ← eq_self_iff_true]

theorem principal_bind {s : Set α} {f : α → Filter β} : bind (𝓟 s) f = ⨆ x ∈ s, f x :=
  show join (map f (𝓟 s)) = ⨆ x ∈ s, f x by
    simp only [← Sup_image, ← join_principal_eq_Sup, ← map_principal, ← eq_self_iff_true]

end Bind

section ListTraverse

/- This is a separate section in order to open `list`, but mostly because of universe
   equality requirements in `traverse` -/
open List

theorem sequence_mono : ∀ as bs : List (Filter α), Forall₂ (· ≤ ·) as bs → sequence as ≤ sequence bs
  | [], [], forall₂.nil => le_rfl
  | a :: as, b :: bs, forall₂.cons h hs => seq_mono (map_mono h) (sequence_mono as bs hs)

variable {α' β' γ' : Type u} {f : β' → Filter α'} {s : γ' → Set α'}

theorem mem_traverse :
    ∀ (fs : List β') (us : List γ'), Forall₂ (fun b c => s c ∈ f b) fs us → traverse s us ∈ traverse f fs
  | [], [], forall₂.nil => mem_pure.2 <| mem_singletonₓ _
  | f :: fs, u :: us, forall₂.cons h hs => seq_mem_seq (image_mem_map h) (mem_traverse fs us hs)

theorem mem_traverse_iff (fs : List β') (t : Set (List α')) :
    t ∈ traverse f fs ↔ ∃ us : List (Set α'), Forall₂ (fun b (s : Set α') => s ∈ f b) fs us ∧ sequence us ⊆ t := by
  constructor
  · induction fs generalizing t
    case nil =>
      simp only [← sequence, ← mem_pure, ← imp_self, ← forall₂_nil_left_iff, ← exists_eq_left, ← Set.pure_def, ←
        singleton_subset_iff, ← traverse_nil]
    case cons b fs ih t =>
      intro ht
      rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩
      rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hwu⟩
      rcases ih v hv with ⟨us, hus, hu⟩
      exact ⟨w :: us, forall₂.cons hw hus, (Set.seq_mono hwu hu).trans ht⟩
    
  · rintro ⟨us, hus, hs⟩
    exact mem_of_superset (mem_traverse _ _ hus) hs
    

end ListTraverse

/-! ### Limits -/


/-- `tendsto` is the generic "limit of a function" predicate.
  `tendsto f l₁ l₂` asserts that for every `l₂` neighborhood `a`,
  the `f`-preimage of `a` is an `l₁` neighborhood. -/
def Tendsto (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.map f ≤ l₂

theorem tendsto_def {f : α → β} {l₁ : Filter α} {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ ∀, ∀ s ∈ l₂, ∀, f ⁻¹' s ∈ l₁ :=
  Iff.rfl

theorem tendsto_iff_eventually {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ ⦃p : β → Prop⦄, (∀ᶠ y in l₂, p y) → ∀ᶠ x in l₁, p (f x) :=
  Iff.rfl

theorem Tendsto.eventually {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {p : β → Prop} (hf : Tendsto f l₁ l₂)
    (h : ∀ᶠ y in l₂, p y) : ∀ᶠ x in l₁, p (f x) :=
  hf h

theorem Tendsto.frequently {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {p : β → Prop} (hf : Tendsto f l₁ l₂)
    (h : ∃ᶠ x in l₁, p (f x)) : ∃ᶠ y in l₂, p y :=
  mt hf.Eventually h

theorem Tendsto.frequently_map {l₁ : Filter α} {l₂ : Filter β} {p : α → Prop} {q : β → Prop} (f : α → β)
    (c : Filter.Tendsto f l₁ l₂) (w : ∀ x, p x → q (f x)) (h : ∃ᶠ x in l₁, p x) : ∃ᶠ y in l₂, q y :=
  c.Frequently (h.mono w)

@[simp]
theorem tendsto_bot {f : α → β} {l : Filter β} : Tendsto f ⊥ l := by
  simp [← tendsto]

@[simp]
theorem tendsto_top {f : α → β} {l : Filter α} : Tendsto f l ⊤ :=
  le_top

theorem le_map_of_right_inverse {mab : α → β} {mba : β → α} {f : Filter α} {g : Filter β} (h₁ : mab ∘ mba =ᶠ[g] id)
    (h₂ : Tendsto mba g f) : g ≤ map mab f := by
  rw [← @map_id _ g, ← map_congr h₁, ← map_map]
  exact map_mono h₂

theorem tendsto_of_is_empty [IsEmpty α] {f : α → β} {la : Filter α} {lb : Filter β} : Tendsto f la lb := by
  simp only [← filter_eq_bot_of_is_empty la, ← tendsto_bot]

theorem eventually_eq_of_left_inv_of_right_inv {f : α → β} {g₁ g₂ : β → α} {fa : Filter α} {fb : Filter β}
    (hleft : ∀ᶠ x in fa, g₁ (f x) = x) (hright : ∀ᶠ y in fb, f (g₂ y) = y) (htendsto : Tendsto g₂ fb fa) :
    g₁ =ᶠ[fb] g₂ :=
  (htendsto.Eventually hleft).mp <| hright.mono fun y hr hl => (congr_arg g₁ hr.symm).trans hl

theorem tendsto_iff_comap {f : α → β} {l₁ : Filter α} {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ l₁ ≤ l₂.comap f :=
  map_le_iff_le_comap

alias tendsto_iff_comap ↔ tendsto.le_comap _

protected theorem Tendsto.disjoint {f : α → β} {la₁ la₂ : Filter α} {lb₁ lb₂ : Filter β} (h₁ : Tendsto f la₁ lb₁)
    (hd : Disjoint lb₁ lb₂) (h₂ : Tendsto f la₂ lb₂) : Disjoint la₁ la₂ :=
  (disjoint_comap hd).mono h₁.le_comap h₂.le_comap

theorem tendsto_congr' {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) :
    Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂ := by
  rw [tendsto, tendsto, map_congr hl]

theorem Tendsto.congr' {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) (h : Tendsto f₁ l₁ l₂) :
    Tendsto f₂ l₁ l₂ :=
  (tendsto_congr' hl).1 h

theorem tendsto_congr {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (h : ∀ x, f₁ x = f₂ x) :
    Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂ :=
  tendsto_congr' (univ_mem' h)

theorem Tendsto.congr {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (h : ∀ x, f₁ x = f₂ x) :
    Tendsto f₁ l₁ l₂ → Tendsto f₂ l₁ l₂ :=
  (tendsto_congr h).1

theorem tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x ≤ y :=
  Iff.rfl

theorem tendsto_id {x : Filter α} : Tendsto id x x :=
  le_reflₓ x

theorem Tendsto.comp {f : α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ} (hg : Tendsto g y z)
    (hf : Tendsto f x y) : Tendsto (g ∘ f) x z := fun s hs => hf (hg hs)

theorem Tendsto.mono_left {f : α → β} {x y : Filter α} {z : Filter β} (hx : Tendsto f x z) (h : y ≤ x) :
    Tendsto f y z :=
  (map_mono h).trans hx

theorem Tendsto.mono_right {f : α → β} {x : Filter α} {y z : Filter β} (hy : Tendsto f x y) (hz : y ≤ z) :
    Tendsto f x z :=
  le_transₓ hy hz

theorem Tendsto.ne_bot {f : α → β} {x : Filter α} {y : Filter β} (h : Tendsto f x y) [hx : NeBot x] : NeBot y :=
  (hx.map _).mono h

theorem tendsto_map {f : α → β} {x : Filter α} : Tendsto f x (map f x) :=
  le_reflₓ (map f x)

theorem tendsto_map' {f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ} (h : Tendsto (f ∘ g) x y) :
    Tendsto f (map g x) y := by
  rwa [tendsto, map_map]

@[simp]
theorem tendsto_map'_iff {f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ} :
    Tendsto f (map g x) y ↔ Tendsto (f ∘ g) x y := by
  rw [tendsto, map_map]
  rfl

theorem tendsto_comap {f : α → β} {x : Filter β} : Tendsto f (comap f x) x :=
  map_comap_le

@[simp]
theorem tendsto_comap_iff {f : α → β} {g : β → γ} {a : Filter α} {c : Filter γ} :
    Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c :=
  ⟨fun h => tendsto_comap.comp h, fun h =>
    map_le_iff_le_comap.mp <| by
      rwa [map_map]⟩

theorem tendsto_comap'_iff {m : α → β} {f : Filter α} {g : Filter β} {i : γ → α} (h : Range i ∈ f) :
    Tendsto (m ∘ i) (comap i f) g ↔ Tendsto m f g := by
  rw [tendsto, ← map_compose]
  simp only [← (· ∘ ·), ← map_comap_of_mem h, ← tendsto]

theorem Tendsto.of_tendsto_comp {f : α → β} {g : β → γ} {a : Filter α} {b : Filter β} {c : Filter γ}
    (hfg : Tendsto (g ∘ f) a c) (hg : comap g c ≤ b) : Tendsto f a b := by
  rw [tendsto_iff_comap] at hfg⊢
  calc a ≤ comap (g ∘ f) c := hfg _ ≤ comap f b := by
      simpa [← comap_comap] using comap_mono hg

theorem comap_eq_of_inverse {f : Filter α} {g : Filter β} {φ : α → β} (ψ : β → α) (eq : ψ ∘ φ = id) (hφ : Tendsto φ f g)
    (hψ : Tendsto ψ g f) : comap φ g = f := by
  refine' ((comap_mono <| map_le_iff_le_comap.1 hψ).trans _).antisymm (map_le_iff_le_comap.1 hφ)
  rw [comap_comap, Eq, comap_id]
  exact le_rfl

theorem map_eq_of_inverse {f : Filter α} {g : Filter β} {φ : α → β} (ψ : β → α) (eq : φ ∘ ψ = id) (hφ : Tendsto φ f g)
    (hψ : Tendsto ψ g f) : map φ f = g := by
  refine' le_antisymmₓ hφ (le_transₓ _ (map_mono hψ))
  rw [map_map, Eq, map_id]
  exact le_rfl

theorem tendsto_inf {f : α → β} {x : Filter α} {y₁ y₂ : Filter β} :
    Tendsto f x (y₁⊓y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂ := by
  simp only [← tendsto, ← le_inf_iff, ← iff_selfₓ]

theorem tendsto_inf_left {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tendsto f x₁ y) : Tendsto f (x₁⊓x₂) y :=
  le_transₓ (map_mono inf_le_left) h

theorem tendsto_inf_right {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tendsto f x₂ y) : Tendsto f (x₁⊓x₂) y :=
  le_transₓ (map_mono inf_le_right) h

theorem Tendsto.inf {f : α → β} {x₁ x₂ : Filter α} {y₁ y₂ : Filter β} (h₁ : Tendsto f x₁ y₁) (h₂ : Tendsto f x₂ y₂) :
    Tendsto f (x₁⊓x₂) (y₁⊓y₂) :=
  tendsto_inf.2 ⟨tendsto_inf_left h₁, tendsto_inf_right h₂⟩

@[simp]
theorem tendsto_infi {f : α → β} {x : Filter α} {y : ι → Filter β} : Tendsto f x (⨅ i, y i) ↔ ∀ i, Tendsto f x (y i) :=
  by
  simp only [← tendsto, ← iff_selfₓ, ← le_infi_iff]

theorem tendsto_infi' {f : α → β} {x : ι → Filter α} {y : Filter β} (i : ι) (hi : Tendsto f (x i) y) :
    Tendsto f (⨅ i, x i) y :=
  hi.mono_left <| infi_le _ _

@[simp]
theorem tendsto_sup {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} :
    Tendsto f (x₁⊔x₂) y ↔ Tendsto f x₁ y ∧ Tendsto f x₂ y := by
  simp only [← tendsto, ← map_sup, ← sup_le_iff]

theorem Tendsto.sup {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} :
    Tendsto f x₁ y → Tendsto f x₂ y → Tendsto f (x₁⊔x₂) y := fun h₁ h₂ => tendsto_sup.mpr ⟨h₁, h₂⟩

@[simp]
theorem tendsto_supr {f : α → β} {x : ι → Filter α} {y : Filter β} : Tendsto f (⨆ i, x i) y ↔ ∀ i, Tendsto f (x i) y :=
  by
  simp only [← tendsto, ← map_supr, ← supr_le_iff]

@[simp]
theorem tendsto_principal {f : α → β} {l : Filter α} {s : Set β} : Tendsto f l (𝓟 s) ↔ ∀ᶠ a in l, f a ∈ s := by
  simp only [← tendsto, ← le_principal_iff, ← mem_map', ← Filter.Eventually]

@[simp]
theorem tendsto_principal_principal {f : α → β} {s : Set α} {t : Set β} :
    Tendsto f (𝓟 s) (𝓟 t) ↔ ∀, ∀ a ∈ s, ∀, f a ∈ t := by
  simp only [← tendsto_principal, ← eventually_principal]

@[simp]
theorem tendsto_pure {f : α → β} {a : Filter α} {b : β} : Tendsto f a (pure b) ↔ ∀ᶠ x in a, f x = b := by
  simp only [← tendsto, ← le_pure_iff, ← mem_map', ← mem_singleton_iff, ← Filter.Eventually]

theorem tendsto_pure_pure (f : α → β) (a : α) : Tendsto f (pure a) (pure (f a)) :=
  tendsto_pure.2 rfl

theorem tendsto_const_pure {a : Filter α} {b : β} : Tendsto (fun x => b) a (pure b) :=
  tendsto_pure.2 <| univ_mem' fun _ => rfl

theorem pure_le_iff {a : α} {l : Filter α} : pure a ≤ l ↔ ∀, ∀ s ∈ l, ∀, a ∈ s :=
  Iff.rfl

theorem tendsto_pure_left {f : α → β} {a : α} {l : Filter β} : Tendsto f (pure a) l ↔ ∀, ∀ s ∈ l, ∀, f a ∈ s :=
  Iff.rfl

@[simp]
theorem map_inf_principal_preimage {f : α → β} {s : Set β} {l : Filter α} : map f (l⊓𝓟 (f ⁻¹' s)) = map f l⊓𝓟 s :=
  Filter.ext fun t => by
    simp only [← mem_map', ← mem_inf_principal, ← mem_set_of_eq, ← mem_preimage]

/-- If two filters are disjoint, then a function cannot tend to both of them along a non-trivial
filter. -/
theorem Tendsto.not_tendsto {f : α → β} {a : Filter α} {b₁ b₂ : Filter β} (hf : Tendsto f a b₁) [NeBot a]
    (hb : Disjoint b₁ b₂) : ¬Tendsto f a b₂ := fun hf' => (tendsto_inf.2 ⟨hf, hf'⟩).ne_bot.Ne hb.eq_bot

theorem Tendsto.if {l₁ : Filter α} {l₂ : Filter β} {f g : α → β} {p : α → Prop} [∀ x, Decidable (p x)]
    (h₀ : Tendsto f (l₁⊓𝓟 { x | p x }) l₂) (h₁ : Tendsto g (l₁⊓𝓟 { x | ¬p x }) l₂) :
    Tendsto (fun x => if p x then f x else g x) l₁ l₂ := by
  simp only [← tendsto_def, ← mem_inf_principal] at *
  intro s hs
  filter_upwards [h₀ s hs, h₁ s hs]
  simp only [← mem_preimage]
  intro x hp₀ hp₁
  split_ifs
  exacts[hp₀ h, hp₁ h]

theorem Tendsto.piecewise {l₁ : Filter α} {l₂ : Filter β} {f g : α → β} {s : Set α} [∀ x, Decidable (x ∈ s)]
    (h₀ : Tendsto f (l₁⊓𝓟 s) l₂) (h₁ : Tendsto g (l₁⊓𝓟 (sᶜ)) l₂) : Tendsto (piecewise s f g) l₁ l₂ :=
  h₀.if h₁

/-! ### Products of filters -/


section Prod

variable {s : Set α} {t : Set β} {f : Filter α} {g : Filter β}

/-- Product of filters. This is the filter generated by cartesian products
  of elements of the component filters. -/
/- The product filter cannot be defined using the monad structure on filters. For example:

  F := do {x ← seq, y ← top, return (x, y)}
  hence:
    s ∈ F  ↔  ∃ n, [n..∞] × univ ⊆ s

  G := do {y ← top, x ← seq, return (x, y)}
  hence:
    s ∈ G  ↔  ∀ i:ℕ, ∃ n, [n..∞] × {i} ⊆ s

  Now ⋃ i, [i..∞] × {i}  is in G but not in F.

  As product filter we want to have F as result.
-/
protected def prod (f : Filter α) (g : Filter β) : Filter (α × β) :=
  f.comap Prod.fst⊓g.comap Prod.snd

-- mathport name: «expr ×ᶠ »
localized [Filter] infixl:60 " ×ᶠ " => Filter.prod

theorem prod_mem_prod {s : Set α} {t : Set β} {f : Filter α} {g : Filter β} (hs : s ∈ f) (ht : t ∈ g) :
    s ×ˢ t ∈ f ×ᶠ g :=
  inter_mem_inf (preimage_mem_comap hs) (preimage_mem_comap ht)

theorem mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} : s ∈ f ×ᶠ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ×ˢ t₂ ⊆ s :=
  by
  simp only [← Filter.prod]
  constructor
  · rintro ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, rfl⟩
    exact ⟨s₁, hs₁, s₂, hs₂, fun p ⟨h, h'⟩ => ⟨hts₁ h, hts₂ h'⟩⟩
    
  · rintro ⟨t₁, ht₁, t₂, ht₂, h⟩
    exact mem_inf_of_inter (preimage_mem_comap ht₁) (preimage_mem_comap ht₂) h
    

@[simp]
theorem prod_mem_prod_iff {s : Set α} {t : Set β} {f : Filter α} {g : Filter β} [f.ne_bot] [g.ne_bot] :
    s ×ˢ t ∈ f ×ᶠ g ↔ s ∈ f ∧ t ∈ g :=
  ⟨fun h =>
    let ⟨s', hs', t', ht', H⟩ := mem_prod_iff.1 h
    (prod_subset_prod_iff.1 H).elim (fun ⟨hs's, ht't⟩ => ⟨mem_of_superset hs' hs's, mem_of_superset ht' ht't⟩) fun h =>
      h.elim (fun hs'e => absurd hs'e (nonempty_of_mem hs').ne_empty) fun ht'e =>
        absurd ht'e (nonempty_of_mem ht').ne_empty,
    fun h => prod_mem_prod h.1 h.2⟩

theorem mem_prod_principal {f : Filter α} {s : Set (α × β)} {t : Set β} :
    s ∈ f ×ᶠ 𝓟 t ↔ { a | ∀, ∀ b ∈ t, ∀, (a, b) ∈ s } ∈ f := by
  rw [← @exists_mem_subset_iff _ f, mem_prod_iff]
  refine' exists₂_congrₓ fun u u_in => ⟨_, fun h => ⟨t, mem_principal_self t, _⟩⟩
  · rintro ⟨v, v_in, hv⟩ a a_in b b_in
    exact hv (mk_mem_prod a_in <| v_in b_in)
    
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact h hx y hy
    

theorem mem_prod_top {f : Filter α} {s : Set (α × β)} : s ∈ f ×ᶠ (⊤ : Filter β) ↔ { a | ∀ b, (a, b) ∈ s } ∈ f := by
  rw [← principal_univ, mem_prod_principal]
  simp only [← mem_univ, ← forall_true_left]

theorem comap_prod (f : α → β × γ) (b : Filter β) (c : Filter γ) :
    comap f (b ×ᶠ c) = comap (Prod.fst ∘ f) b⊓comap (Prod.snd ∘ f) c := by
  erw [comap_inf, Filter.comap_comap, Filter.comap_comap]

theorem prod_top {f : Filter α} : f ×ᶠ (⊤ : Filter β) = f.comap Prod.fst := by
  rw [Filter.prod, comap_top, inf_top_eq]

theorem sup_prod (f₁ f₂ : Filter α) (g : Filter β) : f₁⊔f₂ ×ᶠ g = (f₁ ×ᶠ g)⊔(f₂ ×ᶠ g) := by
  rw [Filter.prod, comap_sup, inf_sup_right, ← Filter.prod, ← Filter.prod]

theorem prod_sup (f : Filter α) (g₁ g₂ : Filter β) : f ×ᶠ g₁⊔g₂ = (f ×ᶠ g₁)⊔(f ×ᶠ g₂) := by
  rw [Filter.prod, comap_sup, inf_sup_left, ← Filter.prod, ← Filter.prod]

theorem eventually_prod_iff {p : α × β → Prop} {f : Filter α} {g : Filter β} :
    (∀ᶠ x in f ×ᶠ g, p x) ↔
      ∃ (pa : α → Prop)(ha : ∀ᶠ x in f, pa x)(pb : β → Prop)(hb : ∀ᶠ y in g, pb y),
        ∀ {x}, pa x → ∀ {y}, pb y → p (x, y) :=
  by
  simpa only [← Set.prod_subset_iff] using @mem_prod_iff α β p f g

theorem tendsto_fst {f : Filter α} {g : Filter β} : Tendsto Prod.fst (f ×ᶠ g) f :=
  tendsto_inf_left tendsto_comap

theorem tendsto_snd {f : Filter α} {g : Filter β} : Tendsto Prod.snd (f ×ᶠ g) g :=
  tendsto_inf_right tendsto_comap

theorem Tendsto.prod_mk {f : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ} (h₁ : Tendsto m₁ f g)
    (h₂ : Tendsto m₂ f h) : Tendsto (fun x => (m₁ x, m₂ x)) f (g ×ᶠ h) :=
  tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

theorem tendsto_prod_swap {α1 α2 : Type _} {a1 : Filter α1} {a2 : Filter α2} :
    Tendsto (Prod.swap : α1 × α2 → α2 × α1) (a1 ×ᶠ a2) (a2 ×ᶠ a1) :=
  tendsto_snd.prod_mk tendsto_fst

theorem Eventually.prod_inl {la : Filter α} {p : α → Prop} (h : ∀ᶠ x in la, p x) (lb : Filter β) :
    ∀ᶠ x in la ×ᶠ lb, p (x : α × β).1 :=
  tendsto_fst.Eventually h

theorem Eventually.prod_inr {lb : Filter β} {p : β → Prop} (h : ∀ᶠ x in lb, p x) (la : Filter α) :
    ∀ᶠ x in la ×ᶠ lb, p (x : α × β).2 :=
  tendsto_snd.Eventually h

theorem Eventually.prod_mk {la : Filter α} {pa : α → Prop} (ha : ∀ᶠ x in la, pa x) {lb : Filter β} {pb : β → Prop}
    (hb : ∀ᶠ y in lb, pb y) : ∀ᶠ p in la ×ᶠ lb, pa (p : α × β).1 ∧ pb p.2 :=
  (ha.prod_inl lb).And (hb.prod_inr la)

theorem EventuallyEq.prod_map {δ} {la : Filter α} {fa ga : α → γ} (ha : fa =ᶠ[la] ga) {lb : Filter β} {fb gb : β → δ}
    (hb : fb =ᶠ[lb] gb) : Prod.map fa fb =ᶠ[la ×ᶠ lb] Prod.map ga gb :=
  (Eventually.prod_mk ha hb).mono fun x h => Prod.extₓ h.1 h.2

theorem EventuallyLe.prod_map {δ} [LE γ] [LE δ] {la : Filter α} {fa ga : α → γ} (ha : fa ≤ᶠ[la] ga) {lb : Filter β}
    {fb gb : β → δ} (hb : fb ≤ᶠ[lb] gb) : Prod.map fa fb ≤ᶠ[la ×ᶠ lb] Prod.map ga gb :=
  Eventually.prod_mk ha hb

theorem Eventually.curry {la : Filter α} {lb : Filter β} {p : α × β → Prop} (h : ∀ᶠ x in la ×ᶠ lb, p x) :
    ∀ᶠ x in la, ∀ᶠ y in lb, p (x, y) := by
  rcases eventually_prod_iff.1 h with ⟨pa, ha, pb, hb, h⟩
  exact ha.mono fun a ha => hb.mono fun b hb => h ha hb

/-- A fact that is eventually true about all pairs `l ×ᶠ l` is eventually true about
all diagonal pairs `(i, i)` -/
theorem Eventually.diag_of_prod {f : Filter α} {p : α × α → Prop} (h : ∀ᶠ i in f ×ᶠ f, p i) : ∀ᶠ i in f, p (i, i) := by
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h
  apply (ht.and hs).mono fun x hx => hst hx.1 hx.2

theorem tendsto_diag : Tendsto (fun i => (i, i)) f (f ×ᶠ f) :=
  tendsto_iff_eventually.mpr fun _ hpr => hpr.diag_of_prod

theorem prod_infi_left [Nonempty ι] {f : ι → Filter α} {g : Filter β} : (⨅ i, f i) ×ᶠ g = ⨅ i, f i ×ᶠ g := by
  rw [Filter.prod, comap_infi, infi_inf]
  simp only [← Filter.prod, ← eq_self_iff_true]

theorem prod_infi_right [Nonempty ι] {f : Filter α} {g : ι → Filter β} : (f ×ᶠ ⨅ i, g i) = ⨅ i, f ×ᶠ g i := by
  rw [Filter.prod, comap_infi, inf_infi]
  simp only [← Filter.prod, ← eq_self_iff_true]

@[mono]
theorem prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁ ×ᶠ g₁ ≤ f₂ ×ᶠ g₂ :=
  inf_le_inf (comap_mono hf) (comap_mono hg)

theorem prod_comap_comap_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂}
    {m₁ : β₁ → α₁} {m₂ : β₂ → α₂} :
    comap m₁ f₁ ×ᶠ comap m₂ f₂ = comap (fun p : β₁ × β₂ => (m₁ p.1, m₂ p.2)) (f₁ ×ᶠ f₂) := by
  simp only [← Filter.prod, ← comap_comap, ← eq_self_iff_true, ← comap_inf]

theorem prod_comm' : f ×ᶠ g = comap Prod.swap (g ×ᶠ f) := by
  simp only [← Filter.prod, ← comap_comap, ← (· ∘ ·), ← inf_comm, ← Prod.fst_swap, ← eq_self_iff_true, ← Prod.snd_swap,
    ← comap_inf]

theorem prod_comm : f ×ᶠ g = map (fun p : β × α => (p.2, p.1)) (g ×ᶠ f) := by
  rw [prod_comm', ← map_swap_eq_comap_swap]
  rfl

theorem prod_assoc (f : Filter α) (g : Filter β) (h : Filter γ) :
    map (Equivₓ.prodAssoc α β γ) (f ×ᶠ g ×ᶠ h) = f ×ᶠ (g ×ᶠ h) := by
  simp_rw [← comap_equiv_symm, Filter.prod, comap_inf, comap_comap, inf_assoc, Function.comp,
    Equivₓ.prod_assoc_symm_apply]

theorem prod_assoc_symm (f : Filter α) (g : Filter β) (h : Filter γ) :
    map (Equivₓ.prodAssoc α β γ).symm (f ×ᶠ (g ×ᶠ h)) = f ×ᶠ g ×ᶠ h := by
  simp_rw [map_equiv_symm, Filter.prod, comap_inf, comap_comap, inf_assoc, Function.comp, Equivₓ.prod_assoc_apply]

theorem tendsto_prod_assoc {f : Filter α} {g : Filter β} {h : Filter γ} :
    Tendsto (Equivₓ.prodAssoc α β γ) (f ×ᶠ g ×ᶠ h) (f ×ᶠ (g ×ᶠ h)) :=
  (prod_assoc f g h).le

theorem tendsto_prod_assoc_symm {f : Filter α} {g : Filter β} {h : Filter γ} :
    Tendsto (Equivₓ.prodAssoc α β γ).symm (f ×ᶠ (g ×ᶠ h)) (f ×ᶠ g ×ᶠ h) :=
  (prod_assoc_symm f g h).le

/-- A useful lemma when dealing with uniformities. -/
theorem map_swap4_prod {f : Filter α} {g : Filter β} {h : Filter γ} {k : Filter δ} :
    map (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (f ×ᶠ g ×ᶠ (h ×ᶠ k)) = f ×ᶠ h ×ᶠ (g ×ᶠ k) := by
  simp_rw [map_swap4_eq_comap, Filter.prod, comap_inf, comap_comap, inf_assoc, inf_left_comm]

theorem tendsto_swap4_prod {f : Filter α} {g : Filter β} {h : Filter γ} {k : Filter δ} :
    Tendsto (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (f ×ᶠ g ×ᶠ (h ×ᶠ k)) (f ×ᶠ h ×ᶠ (g ×ᶠ k)) :=
  map_swap4_prod.le

theorem prod_map_map_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂}
    {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} : map m₁ f₁ ×ᶠ map m₂ f₂ = map (fun p : α₁ × α₂ => (m₁ p.1, m₂ p.2)) (f₁ ×ᶠ f₂) :=
  le_antisymmₓ
    (fun s hs =>
      let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs
      Filter.sets_of_superset _ (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂)) <|
        calc
          (m₁ '' s₁) ×ˢ (m₂ '' s₂) = (fun p : α₁ × α₂ => (m₁ p.1, m₂ p.2)) '' s₁ ×ˢ s₂ := Set.prod_image_image_eq
          _ ⊆ _ := by
            rwa [image_subset_iff]
          )
    ((Tendsto.comp le_rfl tendsto_fst).prod_mk (Tendsto.comp le_rfl tendsto_snd))

theorem prod_map_map_eq' {α₁ : Type _} {α₂ : Type _} {β₁ : Type _} {β₂ : Type _} (f : α₁ → α₂) (g : β₁ → β₂)
    (F : Filter α₁) (G : Filter β₁) : map f F ×ᶠ map g G = map (Prod.map f g) (F ×ᶠ G) :=
  prod_map_map_eq

theorem le_prod_map_fst_snd {f : Filter (α × β)} : f ≤ map Prod.fst f ×ᶠ map Prod.snd f :=
  le_inf le_comap_map le_comap_map

theorem Tendsto.prod_map {δ : Type _} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β} {c : Filter γ}
    {d : Filter δ} (hf : Tendsto f a c) (hg : Tendsto g b d) : Tendsto (Prod.map f g) (a ×ᶠ b) (c ×ᶠ d) := by
  erw [tendsto, ← prod_map_map_eq]
  exact Filter.prod_mono hf hg

protected theorem map_prod (m : α × β → γ) (f : Filter α) (g : Filter β) :
    map m (f ×ᶠ g) = (f.map fun a b => m (a, b)).seq g := by
  simp [← Filter.ext_iff, ← mem_prod_iff, ← mem_map_seq_iff]
  intro s
  constructor
  exact fun ⟨t, ht, s, hs, h⟩ => ⟨s, hs, t, ht, fun x hx y hy => @h ⟨x, y⟩ ⟨hx, hy⟩⟩
  exact fun ⟨s, hs, t, ht, h⟩ => ⟨t, ht, s, hs, fun ⟨x, y⟩ ⟨hx, hy⟩ => h x hx y hy⟩

theorem prod_eq {f : Filter α} {g : Filter β} : f ×ᶠ g = (f.map Prod.mk).seq g := by
  have h := f.map_prod id g
  rwa [map_id] at h

theorem prod_inf_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} : (f₁ ×ᶠ g₁)⊓(f₂ ×ᶠ g₂) = f₁⊓f₂ ×ᶠ g₁⊓g₂ := by
  simp only [← Filter.prod, ← comap_inf, ← inf_comm, ← inf_assoc, ← inf_left_comm]

@[simp]
theorem prod_bot {f : Filter α} : f ×ᶠ (⊥ : Filter β) = ⊥ := by
  simp [← Filter.prod]

@[simp]
theorem bot_prod {g : Filter β} : (⊥ : Filter α) ×ᶠ g = ⊥ := by
  simp [← Filter.prod]

@[simp]
theorem prod_principal_principal {s : Set α} {t : Set β} : 𝓟 s ×ᶠ 𝓟 t = 𝓟 (s ×ˢ t) := by
  simp only [← Filter.prod, ← comap_principal, ← principal_eq_iff_eq, ← comap_principal, ← inf_principal] <;> rfl

@[simp]
theorem pure_prod {a : α} {f : Filter β} : pure a ×ᶠ f = map (Prod.mk a) f := by
  rw [prod_eq, map_pure, pure_seq_eq_map]

theorem map_pure_prod (f : α → β → γ) (a : α) (B : Filter β) :
    Filter.map (Function.uncurry f) (pure a ×ᶠ B) = Filter.map (f a) B := by
  rw [Filter.pure_prod]
  rfl

@[simp]
theorem prod_pure {f : Filter α} {b : β} : f ×ᶠ pure b = map (fun a => (a, b)) f := by
  rw [prod_eq, seq_pure, map_map]

theorem prod_pure_pure {a : α} {b : β} : pure a ×ᶠ pure b = pure (a, b) := by
  simp

theorem prod_eq_bot {f : Filter α} {g : Filter β} : f ×ᶠ g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := by
  constructor
  · intro h
    rcases mem_prod_iff.1 (empty_mem_iff_bot.2 h) with ⟨s, hs, t, ht, hst⟩
    rw [subset_empty_iff, Set.prod_eq_empty_iff] at hst
    cases' hst with s_eq t_eq
    · left
      exact empty_mem_iff_bot.1 (s_eq ▸ hs)
      
    · right
      exact empty_mem_iff_bot.1 (t_eq ▸ ht)
      
    
  · rintro (rfl | rfl)
    exact bot_prod
    exact prod_bot
    

theorem prod_ne_bot {f : Filter α} {g : Filter β} : NeBot (f ×ᶠ g) ↔ NeBot f ∧ NeBot g := by
  simp only [← ne_bot_iff, ← Ne, ← prod_eq_bot, ← not_or_distrib]

theorem NeBot.prod {f : Filter α} {g : Filter β} (hf : NeBot f) (hg : NeBot g) : NeBot (f ×ᶠ g) :=
  prod_ne_bot.2 ⟨hf, hg⟩

instance prod_ne_bot' {f : Filter α} {g : Filter β} [hf : NeBot f] [hg : NeBot g] : NeBot (f ×ᶠ g) :=
  hf.Prod hg

theorem tendsto_prod_iff {f : α × β → γ} {x : Filter α} {y : Filter β} {z : Filter γ} :
    Filter.Tendsto f (x ×ᶠ y) z ↔ ∀, ∀ W ∈ z, ∀, ∃ U ∈ x, ∃ V ∈ y, ∀ x y, x ∈ U → y ∈ V → f (x, y) ∈ W := by
  simp only [← tendsto_def, ← mem_prod_iff, ← prod_sub_preimage_iff, ← exists_prop, ← iff_selfₓ]

theorem tendsto_prod_iff' {f : Filter α} {g : Filter β} {g' : Filter γ} {s : α → β × γ} :
    Tendsto s f (g ×ᶠ g') ↔ Tendsto (fun n => (s n).1) f g ∧ Tendsto (fun n => (s n).2) f g' := by
  unfold Filter.prod
  simp only [← tendsto_inf, ← tendsto_comap_iff, ← iff_selfₓ]

end Prod

/-! ### Coproducts of filters -/


section Coprod

variable {f : Filter α} {g : Filter β}

/-- Coproduct of filters. -/
protected def coprod (f : Filter α) (g : Filter β) : Filter (α × β) :=
  f.comap Prod.fst⊔g.comap Prod.snd

theorem mem_coprod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} :
    s ∈ f.coprod g ↔ (∃ t₁ ∈ f, Prod.fst ⁻¹' t₁ ⊆ s) ∧ ∃ t₂ ∈ g, Prod.snd ⁻¹' t₂ ⊆ s := by
  simp [← Filter.coprod]

@[simp]
theorem bot_coprod (l : Filter β) : (⊥ : Filter α).coprod l = comap Prod.snd l := by
  simp [← Filter.coprod]

@[simp]
theorem coprod_bot (l : Filter α) : l.coprod (⊥ : Filter β) = comap Prod.fst l := by
  simp [← Filter.coprod]

theorem bot_coprod_bot : (⊥ : Filter α).coprod (⊥ : Filter β) = ⊥ := by
  simp

theorem compl_mem_coprod {s : Set (α × β)} {la : Filter α} {lb : Filter β} :
    sᶜ ∈ la.coprod lb ↔ (Prod.fst '' s)ᶜ ∈ la ∧ (Prod.snd '' s)ᶜ ∈ lb := by
  simp only [← Filter.coprod, ← mem_sup, ← compl_mem_comap]

@[mono]
theorem coprod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.coprod g₁ ≤ f₂.coprod g₂ :=
  sup_le_sup (comap_mono hf) (comap_mono hg)

theorem coprod_ne_bot_iff : (f.coprod g).ne_bot ↔ f.ne_bot ∧ Nonempty β ∨ Nonempty α ∧ g.ne_bot := by
  simp [← Filter.coprod]

@[instance]
theorem coprod_ne_bot_left [NeBot f] [Nonempty β] : (f.coprod g).ne_bot :=
  coprod_ne_bot_iff.2 (Or.inl ⟨‹_›, ‹_›⟩)

@[instance]
theorem coprod_ne_bot_right [NeBot g] [Nonempty α] : (f.coprod g).ne_bot :=
  coprod_ne_bot_iff.2 (Or.inr ⟨‹_›, ‹_›⟩)

theorem principal_coprod_principal (s : Set α) (t : Set β) : (𝓟 s).coprod (𝓟 t) = 𝓟 ((sᶜ ×ˢ tᶜ)ᶜ) := by
  rw [Filter.coprod, comap_principal, comap_principal, sup_principal, Set.prod_eq, compl_inter, preimage_compl,
    preimage_compl, compl_compl, compl_compl]

-- this inequality can be strict; see `map_const_principal_coprod_map_id_principal` and
-- `map_prod_map_const_id_principal_coprod_principal` below.
theorem map_prod_map_coprod_le {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂}
    {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} : map (Prod.map m₁ m₂) (f₁.coprod f₂) ≤ (map m₁ f₁).coprod (map m₂ f₂) := by
  intro s
  simp only [← mem_map, ← mem_coprod_iff]
  rintro ⟨⟨u₁, hu₁, h₁⟩, u₂, hu₂, h₂⟩
  refine' ⟨⟨m₁ ⁻¹' u₁, hu₁, fun _ hx => h₁ _⟩, ⟨m₂ ⁻¹' u₂, hu₂, fun _ hx => h₂ _⟩⟩ <;> convert hx

/-- Characterization of the coproduct of the `filter.map`s of two principal filters `𝓟 {a}` and
`𝓟 {i}`, the first under the constant function `λ a, b` and the second under the identity function.
Together with the next lemma, `map_prod_map_const_id_principal_coprod_principal`, this provides an
example showing that the inequality in the lemma `map_prod_map_coprod_le` can be strict. -/
theorem map_const_principal_coprod_map_id_principal {α β ι : Type _} (a : α) (b : β) (i : ι) :
    (map (fun _ : α => b) (𝓟 {a})).coprod (map id (𝓟 {i})) =
      𝓟 (({b} : Set β) ×ˢ (Univ : Set ι) ∪ (Univ : Set β) ×ˢ ({i} : Set ι)) :=
  by
  simp only [← map_principal, ← Filter.coprod, ← comap_principal, ← sup_principal, ← image_singleton, ← image_id, ←
    prod_univ, ← univ_prod]

/-- Characterization of the `filter.map` of the coproduct of two principal filters `𝓟 {a}` and
`𝓟 {i}`, under the `prod.map` of two functions, respectively the constant function `λ a, b` and the
identity function.  Together with the previous lemma,
`map_const_principal_coprod_map_id_principal`, this provides an example showing that the inequality
in the lemma `map_prod_map_coprod_le` can be strict. -/
theorem map_prod_map_const_id_principal_coprod_principal {α β ι : Type _} (a : α) (b : β) (i : ι) :
    map (Prod.map (fun _ : α => b) id) ((𝓟 {a}).coprod (𝓟 {i})) = 𝓟 (({b} : Set β) ×ˢ (Univ : Set ι)) := by
  rw [principal_coprod_principal, map_principal]
  congr
  ext ⟨b', i'⟩
  constructor
  · rintro ⟨⟨a'', i''⟩, h₁, h₂, h₃⟩
    simp
    
  · rintro ⟨h₁, h₂⟩
    use (a, i')
    simpa using h₁.symm
    

theorem Tendsto.prod_map_coprod {δ : Type _} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β} {c : Filter γ}
    {d : Filter δ} (hf : Tendsto f a c) (hg : Tendsto g b d) : Tendsto (Prod.map f g) (a.coprod b) (c.coprod d) :=
  map_prod_map_coprod_le.trans (coprod_mono hf hg)

end Coprod

end Filter

open Filter

theorem Set.EqOn.eventually_eq {α β} {s : Set α} {f g : α → β} (h : EqOn f g s) : f =ᶠ[𝓟 s] g :=
  h

theorem Set.EqOn.eventually_eq_of_mem {α β} {s : Set α} {l : Filter α} {f g : α → β} (h : EqOn f g s) (hl : s ∈ l) :
    f =ᶠ[l] g :=
  h.EventuallyEq.filter_mono <| Filter.le_principal_iff.2 hl

theorem HasSubset.Subset.eventually_le {α} {l : Filter α} {s t : Set α} (h : s ⊆ t) : s ≤ᶠ[l] t :=
  Filter.eventually_of_forall h

theorem Set.MapsTo.tendsto {α β} {s : Set α} {t : Set β} {f : α → β} (h : MapsTo f s t) :
    Filter.Tendsto f (𝓟 s) (𝓟 t) :=
  Filter.tendsto_principal_principal.2 h


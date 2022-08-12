/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/
import Mathbin.Combinatorics.SimpleGraph.Subgraph
import Mathbin.Combinatorics.SimpleGraph.Clique
import Mathbin.Data.Nat.Lattice
import Mathbin.Data.Setoid.Partition
import Mathbin.Order.Antichain

/-!
# Graph Coloring

This module defines colorings of simple graphs (also known as proper
colorings in the literature). A graph coloring is the attribution of
"colors" to all of its vertices such that adjacent vertices have
different colors. A coloring can be represented as a homomorphism into
a complete graph, whose vertices represent the colors.

## Main definitions

* `G.coloring α` is the type of `α`-colorings of a simple graph `G`,
  with `α` being the set of available colors. The type is defined to
  be homomorphisms from `G` into the complete graph on `α`, and
  colorings have a coercion to `V → α`.

* `G.colorable n` is the proposition that `G` is `n`-colorable, which
  is whether there exists a coloring with at most *n* colors.

* `G.chromatic_number` is the minimal `n` such that `G` is
  `n`-colorable, or `0` if it cannot be colored with finitely many
  colors.

* `C.color_class c` is the set of vertices colored by `c : α` in the
  coloring `C : G.coloring α`.

* `C.color_classes` is the set containing all color classes.

## Todo:

  * Gather material from:
    * https://github.com/leanprover-community/mathlib/blob/simple_graph_matching/src/combinatorics/simple_graph/coloring.lean
    * https://github.com/kmill/lean-graphcoloring/blob/master/src/graph.lean

  * Trees

  * Planar graphs

  * Chromatic polynomials

  * develop API for partial colorings, likely as colorings of subgraphs (`H.coe.coloring α`)
-/


universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-- An `α`-coloring of a simple graph `G` is a homomorphism of `G` into the complete graph on `α`.
This is also known as a proper coloring.
-/
abbrev Coloring (α : Type v) :=
  G →g (⊤ : SimpleGraph α)

variable {G} {α : Type v} (C : G.Coloring α)

theorem Coloring.valid {v w : V} (h : G.Adj v w) : C v ≠ C w :=
  C.map_rel h

/-- Construct a term of `simple_graph.coloring` using a function that
assigns vertices to colors and a proof that it is as proper coloring.

(Note: this is a definitionally the constructor for `simple_graph.hom`,
but with a syntactically better proper coloring hypothesis.)
-/
@[matchPattern]
def Coloring.mk (color : V → α) (valid : ∀ {v w : V}, G.Adj v w → color v ≠ color w) : G.Coloring α :=
  ⟨color, @valid⟩

/-- The color class of a given color.
-/
def Coloring.ColorClass (c : α) : Set V :=
  { v : V | C v = c }

/-- The set containing all color classes. -/
def Coloring.ColorClasses : Set (Set V) :=
  (Setoidₓ.ker C).Classes

theorem Coloring.mem_color_class (v : V) : v ∈ C.ColorClass (C v) :=
  rfl

theorem Coloring.color_classes_is_partition : Setoidₓ.IsPartition C.ColorClasses :=
  Setoidₓ.is_partition_classes (Setoidₓ.ker C)

theorem Coloring.mem_color_classes {v : V} : C.ColorClass (C v) ∈ C.ColorClasses :=
  ⟨v, rfl⟩

theorem Coloring.color_classes_finite_of_fintype [Fintype α] : C.ColorClasses.Finite := by
  rw [Set.finite_def]
  apply Setoidₓ.nonempty_fintype_classes_ker

theorem Coloring.card_color_classes_le [Fintype α] [Fintype C.ColorClasses] :
    Fintype.card C.ColorClasses ≤ Fintype.card α :=
  Setoidₓ.card_classes_ker_le C

theorem Coloring.not_adj_of_mem_color_class {c : α} {v w : V} (hv : v ∈ C.ColorClass c) (hw : w ∈ C.ColorClass c) :
    ¬G.Adj v w := fun h => C.valid h (Eq.trans hv (Eq.symm hw))

theorem Coloring.color_classes_independent (c : α) : IsAntichain G.Adj (C.ColorClass c) := fun v hv w hw h =>
  C.not_adj_of_mem_color_class hv hw

-- TODO make this computable
noncomputable instance [Fintype V] [Fintype α] : Fintype (Coloring G α) := by
  classical
  change Fintype (RelHom G.adj (⊤ : SimpleGraph α).Adj)
  apply Fintype.ofInjective _ RelHom.coe_fn_injective
  infer_instance

variable (G)

/-- Whether a graph can be colored by at most `n` colors. -/
def Colorable (n : ℕ) : Prop :=
  Nonempty (G.Coloring (Finₓ n))

/-- The coloring of an empty graph. -/
def coloringOfIsEmpty [IsEmpty V] : G.Coloring α :=
  Coloring.mk isEmptyElim fun v => isEmptyElim

theorem colorable_of_is_empty [IsEmpty V] (n : ℕ) : G.Colorable n :=
  ⟨G.coloringOfIsEmpty⟩

theorem is_empty_of_colorable_zero (h : G.Colorable 0) : IsEmpty V := by
  constructor
  intro v
  obtain ⟨i, hi⟩ := h.some v
  exact Nat.not_lt_zeroₓ _ hi

/-- The "tautological" coloring of a graph, using the vertices of the graph as colors. -/
def selfColoring : G.Coloring V :=
  Coloring.mk id fun v w => G.ne_of_adj

/-- The chromatic number of a graph is the minimal number of colors needed to color it.
If `G` isn't colorable with finitely many colors, this will be 0. -/
noncomputable def chromaticNumber : ℕ :=
  inf { n : ℕ | G.Colorable n }

/-- Given an embedding, there is an induced embedding of colorings. -/
def recolorOfEmbedding {α β : Type _} (f : α ↪ β) : G.Coloring α ↪ G.Coloring β where
  toFun := fun C => (Embedding.completeGraph f).toHom.comp C
  inj' := by
    -- this was strangely painful; seems like missing lemmas about embeddings
    intro C C' h
    dsimp' only  at h
    ext v
    apply (embedding.complete_graph f).inj'
    change ((embedding.complete_graph f).toHom.comp C) v = _
    rw [h]
    rfl

/-- Given an equivalence, there is an induced equivalence between colorings. -/
def recolorOfEquiv {α β : Type _} (f : α ≃ β) : G.Coloring α ≃ G.Coloring β where
  toFun := G.recolorOfEmbedding f.toEmbedding
  invFun := G.recolorOfEmbedding f.symm.toEmbedding
  left_inv := fun C => by
    ext v
    apply Equivₓ.symm_apply_apply
  right_inv := fun C => by
    ext v
    apply Equivₓ.apply_symm_apply

/-- There is a noncomputable embedding of `α`-colorings to `β`-colorings if
`β` has at least as large a cardinality as `α`. -/
noncomputable def recolorOfCardLe {α β : Type _} [Fintype α] [Fintype β] (hn : Fintype.card α ≤ Fintype.card β) :
    G.Coloring α ↪ G.Coloring β :=
  G.recolorOfEmbedding <| (Function.Embedding.nonempty_of_card_le hn).some

variable {G}

theorem Colorable.mono {n m : ℕ} (h : n ≤ m) (hc : G.Colorable n) : G.Colorable m :=
  ⟨G.recolorOfCardLe
      (by
        simp [← h])
      hc.some⟩

theorem Coloring.to_colorable [Fintype α] (C : G.Coloring α) : G.Colorable (Fintype.card α) :=
  ⟨G.recolorOfCardLe
      (by
        simp )
      C⟩

theorem colorable_of_fintype (G : SimpleGraph V) [Fintype V] : G.Colorable (Fintype.card V) :=
  G.selfColoring.to_colorable

/-- Noncomputably get a coloring from colorability. -/
noncomputable def Colorable.toColoring [Fintype α] {n : ℕ} (hc : G.Colorable n) (hn : n ≤ Fintype.card α) :
    G.Coloring α := by
  rw [← Fintype.card_fin n] at hn
  exact G.recolor_of_card_le hn hc.some

theorem Colorable.of_embedding {V' : Type _} {G' : SimpleGraph V'} (f : G ↪g G') {n : ℕ} (h : G'.Colorable n) :
    G.Colorable n :=
  ⟨(h.toColoring
          (by
            simp )).comp
      f⟩

theorem colorable_iff_exists_bdd_nat_coloring (n : ℕ) : G.Colorable n ↔ ∃ C : G.Coloring ℕ, ∀ v, C v < n := by
  constructor
  · rintro hc
    have C : G.coloring (Finₓ n) :=
      hc.to_coloring
        (by
          simp )
    let f := embedding.complete_graph (Finₓ.coeEmbedding n).toEmbedding
    use f.to_hom.comp C
    intro v
    cases' C with color valid
    exact Finₓ.is_lt (color v)
    
  · rintro ⟨C, Cf⟩
    refine' ⟨coloring.mk _ _⟩
    · exact fun v => ⟨C v, Cf v⟩
      
    · rintro v w hvw
      simp only [← Subtype.mk_eq_mk, ← Ne.def]
      exact C.valid hvw
      
    

theorem colorable_set_nonempty_of_colorable {n : ℕ} (hc : G.Colorable n) : { n : ℕ | G.Colorable n }.Nonempty :=
  ⟨n, hc⟩

theorem chromatic_number_bdd_below : BddBelow { n : ℕ | G.Colorable n } :=
  ⟨0, fun _ _ => zero_le _⟩

theorem chromatic_number_le_of_colorable {n : ℕ} (hc : G.Colorable n) : G.chromaticNumber ≤ n := by
  rw [chromatic_number]
  apply cInf_le chromatic_number_bdd_below
  fconstructor
  exact Classical.choice hc

theorem chromatic_number_le_card [Fintype α] (C : G.Coloring α) : G.chromaticNumber ≤ Fintype.card α :=
  cInf_le chromatic_number_bdd_below C.to_colorable

theorem colorable_chromatic_number {m : ℕ} (hc : G.Colorable m) : G.Colorable G.chromaticNumber := by
  dsimp' only [← chromatic_number]
  rw [Nat.Inf_def]
  apply Nat.find_specₓ
  exact colorable_set_nonempty_of_colorable hc

theorem colorable_chromatic_number_of_fintype (G : SimpleGraph V) [Fintype V] : G.Colorable G.chromaticNumber :=
  colorable_chromatic_number G.colorable_of_fintype

theorem chromatic_number_le_one_of_subsingleton (G : SimpleGraph V) [Subsingleton V] : G.chromaticNumber ≤ 1 := by
  rw [chromatic_number]
  apply cInf_le chromatic_number_bdd_below
  fconstructor
  refine' coloring.mk (fun _ => 0) _
  intro v w
  rw [Subsingleton.elimₓ v w]
  simp

theorem chromatic_number_eq_zero_of_isempty (G : SimpleGraph V) [IsEmpty V] : G.chromaticNumber = 0 := by
  rw [← nonpos_iff_eq_zero]
  apply cInf_le chromatic_number_bdd_below
  apply colorable_of_is_empty

theorem is_empty_of_chromatic_number_eq_zero (G : SimpleGraph V) [Fintype V] (h : G.chromaticNumber = 0) : IsEmpty V :=
  by
  have h' := G.colorable_chromatic_number_of_fintype
  rw [h] at h'
  exact G.is_empty_of_colorable_zero h'

theorem chromatic_number_pos [Nonempty V] {n : ℕ} (hc : G.Colorable n) : 0 < G.chromaticNumber := by
  apply le_cInf (colorable_set_nonempty_of_colorable hc)
  intro m hm
  by_contra h'
  simp only [← not_leₓ, ← Nat.lt_one_iff] at h'
  subst h'
  obtain ⟨i, hi⟩ := hm.some (Classical.arbitrary V)
  exact Nat.not_lt_zeroₓ _ hi

theorem colorable_of_chromatic_number_pos (h : 0 < G.chromaticNumber) : G.Colorable G.chromaticNumber := by
  obtain ⟨h, hn⟩ := Nat.nonempty_of_pos_Inf h
  exact colorable_chromatic_number hn

theorem Colorable.mono_left {G' : SimpleGraph V} (h : G ≤ G') {n : ℕ} (hc : G'.Colorable n) : G.Colorable n :=
  ⟨hc.some.comp (Hom.mapSpanningSubgraphs h)⟩

theorem Colorable.chromatic_number_le_of_forall_imp {V' : Type _} {G' : SimpleGraph V'} {m : ℕ} (hc : G'.Colorable m)
    (h : ∀ n, G'.Colorable n → G.Colorable n) : G.chromaticNumber ≤ G'.chromaticNumber := by
  apply cInf_le chromatic_number_bdd_below
  apply h
  apply colorable_chromatic_number hc

theorem Colorable.chromatic_number_mono (G' : SimpleGraph V) {m : ℕ} (hc : G'.Colorable m) (h : G ≤ G') :
    G.chromaticNumber ≤ G'.chromaticNumber :=
  hc.chromatic_number_le_of_forall_imp fun n => Colorable.mono_left h

theorem Colorable.chromatic_number_mono_of_embedding {V' : Type _} {G' : SimpleGraph V'} {n : ℕ} (h : G'.Colorable n)
    (f : G ↪g G') : G.chromaticNumber ≤ G'.chromaticNumber :=
  h.chromatic_number_le_of_forall_imp fun _ => Colorable.of_embedding f

theorem chromatic_number_eq_card_of_forall_surj [Fintype α] (C : G.Coloring α)
    (h : ∀ C' : G.Coloring α, Function.Surjective C') : G.chromaticNumber = Fintype.card α := by
  apply le_antisymmₓ
  · apply chromatic_number_le_card C
    
  · by_contra hc
    rw [not_leₓ] at hc
    obtain ⟨n, cn, hc⟩ := exists_lt_of_cInf_lt (colorable_set_nonempty_of_colorable C.to_colorable) hc
    rw [← Fintype.card_fin n] at hc
    have f := (Function.Embedding.nonempty_of_card_le (le_of_ltₓ hc)).some
    have C' := cn.some
    specialize h (G.recolor_of_embedding f C')
    change Function.Surjective (f ∘ C') at h
    have h1 : Function.Surjective f := Function.Surjective.of_comp h
    have h2 := Fintype.card_le_of_surjective _ h1
    exact Nat.lt_le_antisymmₓ hc h2
    

theorem chromatic_number_bot [Nonempty V] : (⊥ : SimpleGraph V).chromaticNumber = 1 := by
  let C : (⊥ : SimpleGraph V).Coloring (Finₓ 1) := coloring.mk (fun _ => 0) fun v w h => False.elim h
  apply le_antisymmₓ
  · exact chromatic_number_le_card C
    
  · exact chromatic_number_pos C.to_colorable
    

@[simp]
theorem chromatic_number_top [Fintype V] : (⊤ : SimpleGraph V).chromaticNumber = Fintype.card V := by
  apply chromatic_number_eq_card_of_forall_surj (self_coloring _)
  intro C
  rw [← Fintype.injective_iff_surjective]
  intro v w
  contrapose
  intro h
  exact C.valid h

theorem chromatic_number_top_eq_zero_of_infinite (V : Type _) [Infinite V] : (⊤ : SimpleGraph V).chromaticNumber = 0 :=
  by
  let n := (⊤ : SimpleGraph V).chromaticNumber
  by_contra hc
  replace hc := pos_iff_ne_zero.mpr hc
  apply Nat.not_succ_le_selfₓ n
  convert_to (⊤ : SimpleGraph { m | m < n + 1 }).chromaticNumber ≤ _
  · simp
    
  refine' (colorable_of_chromatic_number_pos hc).chromatic_number_mono_of_embedding _
  apply embedding.complete_graph
  exact (Function.Embedding.subtype _).trans (Infinite.natEmbedding V)

/-- The bicoloring of a complete bipartite graph using whether a vertex
is on the left or on the right. -/
def CompleteBipartiteGraph.bicoloring (V W : Type _) : (completeBipartiteGraph V W).Coloring Bool :=
  Coloring.mk (fun v => v.isRight)
    (by
      intro v w
      cases v <;> cases w <;> simp )

theorem CompleteBipartiteGraph.chromatic_number {V W : Type _} [Nonempty V] [Nonempty W] :
    (completeBipartiteGraph V W).chromaticNumber = 2 := by
  apply chromatic_number_eq_card_of_forall_surj (complete_bipartite_graph.bicoloring V W)
  intro C b
  have v := Classical.arbitrary V
  have w := Classical.arbitrary W
  have h : (completeBipartiteGraph V W).Adj (Sum.inl v) (Sum.inr w) := by
    simp
  have hn := C.valid h
  by_cases' he : C (Sum.inl v) = b
  · exact ⟨_, he⟩
    
  · by_cases' he' : C (Sum.inr w) = b
    · exact ⟨_, he'⟩
      
    · exfalso
      cases b <;>
        simp only [← eq_tt_eq_not_eq_ff, ← eq_ff_eq_not_eq_tt] at he he' <;> rw [he, he'] at hn <;> contradiction
      
    

/-! ### Cliques -/


theorem IsClique.card_le_of_coloring {s : Finset V} (h : G.IsClique s) [Fintype α] (C : G.Coloring α) :
    s.card ≤ Fintype.card α := by
  rw [is_clique_iff_induce_eq] at h
  have f : G.induce ↑s ↪g G := embedding.induce ↑s
  rw [h] at f
  convert Fintype.card_le_of_injective _ (C.comp f.to_hom).injective_of_top_hom using 1
  simp

theorem IsClique.card_le_of_colorable {s : Finset V} (h : G.IsClique s) {n : ℕ} (hc : G.Colorable n) : s.card ≤ n := by
  convert h.card_le_of_coloring hc.some
  simp

-- TODO eliminate `fintype V` constraint once chromatic numbers are refactored.
-- This is just to ensure the chromatic number exists.
theorem IsClique.card_le_chromatic_number [Fintype V] {s : Finset V} (h : G.IsClique s) : s.card ≤ G.chromaticNumber :=
  h.card_le_of_colorable G.colorable_chromatic_number_of_fintype

protected theorem Colorable.clique_free {n m : ℕ} (hc : G.Colorable n) (hm : n < m) : G.CliqueFree m := by
  by_contra h
  simp only [← clique_free, ← is_n_clique_iff, ← not_forall, ← not_not] at h
  obtain ⟨s, h, rfl⟩ := h
  exact Nat.lt_le_antisymmₓ hm (h.card_le_of_colorable hc)

-- TODO eliminate `fintype V` constraint once chromatic numbers are refactored.
-- This is just to ensure the chromatic number exists.
theorem clique_free_of_chromatic_number_lt [Fintype V] {n : ℕ} (hc : G.chromaticNumber < n) : G.CliqueFree n :=
  G.colorable_chromatic_number_of_fintype.CliqueFree hc

end SimpleGraph


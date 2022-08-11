/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Combinatorics.SimpleGraph.Subgraph
import Mathbin.Data.List.Default

/-!

# Graph connectivity

In a simple graph,

* A *walk* is a finite sequence of adjacent vertices, and can be
  thought of equally well as a sequence of directed edges.

* A *trail* is a walk whose edges each appear no more than once.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the
  same and whose vertices except for the first appear no more than once.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `simple_graph.walk` (with accompanying pattern definitions
  `simple_graph.walk.nil'` and `simple_graph.walk.cons'`)

* `simple_graph.walk.is_trail`, `simple_graph.walk.is_path`, and `simple_graph.walk.is_cycle`.

* `simple_graph.path`

* `simple_graph.walk.map` and `simple_graph.path.map` for the induced map on walks,
  given an (injective) graph homomorphism.

* `simple_graph.reachable` for the relation of whether there exists
  a walk between a given pair of vertices

* `simple_graph.preconnected` and `simple_graph.connected` are predicates
  on simple graphs for whether every vertex can be reached from every other,
  and in the latter case, whether the vertex type is nonempty.

* `simple_graph.subgraph.connected` gives subgraphs the connectivity
  predicate via `simple_graph.subgraph.coe`.

* `simple_graph.connected_component` is the type of connected components of
  a given graph.

## Tags
walks, trails, paths, circuits, cycles

-/


open Function

universe u v

namespace SimpleGraph

variable {V : Type u} {V' : Type v} (G : SimpleGraph V) (G' : SimpleGraph V')

/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `simple_graph.walk.support`.

See `simple_graph.walk.nil'` and `simple_graph.walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk : V → V → Type u
  | nil {u : V} : walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : walk v w) : walk u w
  deriving DecidableEq

attribute [refl] walk.nil

instance Walk.inhabited (v : V) : Inhabited (G.Walk v v) :=
  ⟨by
    rfl⟩

namespace Walk

variable {G}

/-- Pattern to get `walk.nil` with the vertex as an explicit argument. -/
@[matchPattern]
abbrev nil' (u : V) : G.Walk u u :=
  walk.nil

/-- Pattern to get `walk.cons` with the vertices as explicit arguments. -/
@[matchPattern]
abbrev cons' (u v w : V) (h : G.Adj u v) (p : G.Walk v w) : G.Walk u w :=
  Walk.cons h p

theorem exists_eq_cons_of_ne :
    ∀ {u v : V} (hne : u ≠ v) (p : G.Walk u v), ∃ (w : V)(h : G.Adj u w)(p' : G.Walk w v), p = cons h p'
  | _, _, hne, nil => (hne rfl).elim
  | _, _, _, cons h p' => ⟨_, h, p', rfl⟩

/-- The length of a walk is the number of edges/darts along it. -/
def length : ∀ {u v : V}, G.Walk u v → ℕ
  | _, _, nil => 0
  | _, _, cons _ q => q.length.succ

/-- The concatenation of two compatible walks. -/
@[trans]
def append : ∀ {u v w : V}, G.Walk u v → G.Walk v w → G.Walk u w
  | _, _, _, nil, q => q
  | _, _, _, cons h p, q => cons h (p.append q)

/-- The concatenation of the reverse of the first walk with the second walk. -/
protected def reverseAux : ∀ {u v w : V}, G.Walk u v → G.Walk u w → G.Walk v w
  | _, _, _, nil, q => q
  | _, _, _, cons h p, q => reverse_aux p (cons (G.symm h) q)

/-- The walk in reverse. -/
@[symm]
def reverse {u v : V} (w : G.Walk u v) : G.Walk v u :=
  w.reverseAux nil

/-- Get the `n`th vertex from a walk, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than or equal to `p.length`, the result is the path's endpoint. -/
def getVert : ∀ {u v : V} (p : G.Walk u v) (n : ℕ), V
  | u, v, nil, _ => u
  | u, v, cons _ _, 0 => u
  | u, v, cons _ q, n + 1 => q.getVert n

@[simp]
theorem get_vert_zero {u v} (w : G.Walk u v) : w.getVert 0 = u := by
  cases w <;> rfl

theorem get_vert_of_length_le {u v} (w : G.Walk u v) {i : ℕ} (hi : w.length ≤ i) : w.getVert i = v := by
  induction' w with _ x y z hxy wyz IH generalizing i
  · rfl
    
  · cases i
    · cases hi
      
    · exact IH (Nat.succ_le_succ_iff.1 hi)
      
    

@[simp]
theorem get_vert_length {u v} (w : G.Walk u v) : w.getVert w.length = v :=
  w.get_vert_of_length_le rfl.le

theorem adj_get_vert_succ {u v} (w : G.Walk u v) {i : ℕ} (hi : i < w.length) :
    G.Adj (w.getVert i) (w.getVert (i + 1)) := by
  induction' w with _ x y z hxy wyz IH generalizing i
  · cases hi
    
  · cases i
    · simp [← get_vert, ← hxy]
      
    · exact IH (Nat.succ_lt_succ_iff.1 hi)
      
    

@[simp]
theorem cons_append {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (q : G.Walk w x) :
    (cons h p).append q = cons h (p.append q) :=
  rfl

@[simp]
theorem cons_nil_append {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h nil).append p = cons h p :=
  rfl

@[simp]
theorem append_nil : ∀ {u v : V} (p : G.Walk u v), p.append nil = p
  | _, _, nil => rfl
  | _, _, cons h p => by
    rw [cons_append, append_nil]

@[simp]
theorem nil_append {u v : V} (p : G.Walk u v) : nil.append p = p :=
  rfl

theorem append_assoc :
    ∀ {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk w x), p.append (q.append r) = (p.append q).append r
  | _, _, _, _, nil, _, _ => rfl
  | _, _, _, _, cons h p', q, r => by
    dunfold append
    rw [append_assoc]

@[simp]
theorem reverse_nil {u : V} : (nil : G.Walk u u).reverse = nil :=
  rfl

theorem reverse_singleton {u v : V} (h : G.Adj u v) : (cons h nil).reverse = cons (G.symm h) nil :=
  rfl

@[simp]
theorem cons_reverse_aux {u v w x : V} (p : G.Walk u v) (q : G.Walk w x) (h : G.Adj w u) :
    (cons h p).reverseAux q = p.reverseAux (cons (G.symm h) q) :=
  rfl

@[simp]
protected theorem append_reverse_aux :
    ∀ {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk u x),
      (p.append q).reverseAux r = q.reverseAux (p.reverseAux r)
  | _, _, _, _, nil, _, _ => rfl
  | _, _, _, _, cons h p', q, r => append_reverse_aux p' q (cons (G.symm h) r)

@[simp]
protected theorem reverse_aux_append :
    ∀ {u v w x : V} (p : G.Walk u v) (q : G.Walk u w) (r : G.Walk w x),
      (p.reverseAux q).append r = p.reverseAux (q.append r)
  | _, _, _, _, nil, _, _ => rfl
  | _, _, _, _, cons h p', q, r => by
    simp [← reverse_aux_append p' (cons (G.symm h) q) r]

protected theorem reverse_aux_eq_reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    p.reverseAux q = p.reverse.append q := by
  simp [← reverse]

@[simp]
theorem reverse_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).reverse = p.reverse.append (cons (G.symm h) nil) := by
  simp [← reverse]

@[simp]
theorem reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  simp [← reverse]

@[simp]
theorem reverse_reverse : ∀ {u v : V} (p : G.Walk u v), p.reverse.reverse = p
  | _, _, nil => rfl
  | _, _, cons h p => by
    simp [← reverse_reverse]

@[simp]
theorem length_nil {u : V} : (nil : G.Walk u u).length = 0 :=
  rfl

@[simp]
theorem length_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).length = p.length + 1 :=
  rfl

@[simp]
theorem length_append : ∀ {u v w : V} (p : G.Walk u v) (q : G.Walk v w), (p.append q).length = p.length + q.length
  | _, _, _, nil, _ => by
    simp
  | _, _, _, cons _ _, _ => by
    simp [← length_append, ← add_left_commₓ, ← add_commₓ]

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
@[simp]
protected theorem length_reverse_aux :
    ∀ {u v w : V} (p : G.Walk u v) (q : G.Walk u w), (p.reverseAux q).length = p.length + q.length
  | _, _, _, nil, _ => by
    simp
  | _, _, _, cons _ _, _ => by
    simp [← length_reverse_aux, ← Nat.add_succ, ← Nat.succ_add]

@[simp]
theorem length_reverse {u v : V} (p : G.Walk u v) : p.reverse.length = p.length := by
  simp [← reverse]

theorem eq_of_length_eq_zero : ∀ {u v : V} {p : G.Walk u v}, p.length = 0 → u = v
  | _, _, nil, _ => rfl

@[simp]
theorem exists_length_eq_zero_iff {u v : V} : (∃ p : G.Walk u v, p.length = 0) ↔ u = v := by
  constructor
  · rintro ⟨p, hp⟩
    exact eq_of_length_eq_zero hp
    
  · rintro rfl
    exact ⟨nil, rfl⟩
    

@[simp]
theorem length_eq_zero_iff {u : V} {p : G.Walk u u} : p.length = 0 ↔ p = nil := by
  cases p <;> simp

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support : ∀ {u v : V}, G.Walk u v → List V
  | u, v, nil => [u]
  | u, v, cons h p => u :: p.Support

/-- The `darts` of a walk is the list of darts it visits in order. -/
def darts : ∀ {u v : V}, G.Walk u v → List G.Dart
  | u, v, nil => []
  | u, v, cons h p => ⟨(u, _), h⟩ :: p.darts

/-- The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `simple_graph.walk.darts`. -/
def edges {u v : V} (p : G.Walk u v) : List (Sym2 V) :=
  p.darts.map Dart.edge

@[simp]
theorem support_nil {u : V} : (nil : G.Walk u u).Support = [u] :=
  rfl

@[simp]
theorem support_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).Support = u :: p.Support :=
  rfl

theorem support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').Support = p.Support ++ p'.Support.tail := by
  induction p <;> cases p' <;> simp [*]

@[simp]
theorem support_reverse {u v : V} (p : G.Walk u v) : p.reverse.Support = p.Support.reverse := by
  induction p <;> simp [← support_append, *]

theorem support_ne_nil {u v : V} (p : G.Walk u v) : p.Support ≠ [] := by
  cases p <;> simp

theorem tail_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').Support.tail = p.Support.tail ++ p'.Support.tail := by
  rw [support_append, List.tail_append_of_ne_nil _ _ (support_ne_nil _)]

theorem support_eq_cons {u v : V} (p : G.Walk u v) : p.Support = u :: p.Support.tail := by
  cases p <;> simp

@[simp]
theorem start_mem_support {u v : V} (p : G.Walk u v) : u ∈ p.Support := by
  cases p <;> simp

@[simp]
theorem end_mem_support {u v : V} (p : G.Walk u v) : v ∈ p.Support := by
  induction p <;> simp [*]

theorem mem_support_iff {u v w : V} (p : G.Walk u v) : w ∈ p.Support ↔ w = u ∨ w ∈ p.Support.tail := by
  cases p <;> simp

theorem mem_support_nil_iff {u v : V} : u ∈ (nil : G.Walk v v).Support ↔ u = v := by
  simp

@[simp]
theorem mem_tail_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t ∈ (p.append p').Support.tail ↔ t ∈ p.Support.tail ∨ t ∈ p'.Support.tail := by
  rw [tail_support_append, List.mem_appendₓ]

@[simp]
theorem end_mem_tail_support_of_ne {u v : V} (h : u ≠ v) (p : G.Walk u v) : v ∈ p.Support.tail := by
  obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp

@[simp]
theorem mem_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t ∈ (p.append p').Support ↔ t ∈ p.Support ∨ t ∈ p'.Support := by
  simp only [← mem_support_iff, ← mem_tail_support_append_iff]
  by_cases' h : t = v <;>
    by_cases' h' : t = u <;>
      subst_vars <;>
        try
            have := Ne.symm h' <;>
          simp [*]

theorem coe_support {u v : V} (p : G.Walk u v) : (p.Support : Multiset V) = {u} + p.Support.tail := by
  cases p <;> rfl

theorem coe_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').Support : Multiset V) = {u} + p.Support.tail + p'.Support.tail := by
  rw [support_append, ← Multiset.coe_add, coe_support]

theorem coe_support_append' [DecidableEq V] {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').Support : Multiset V) = p.Support + p'.Support - {v} := by
  rw [support_append, ← Multiset.coe_add]
  simp only [← coe_support]
  rw [add_commₓ {v}]
  simp only [add_assocₓ, ← add_tsub_cancel_right]

theorem chain_adj_support : ∀ {u v w : V} (h : G.Adj u v) (p : G.Walk v w), List.Chain G.Adj u p.Support
  | _, _, _, h, nil => List.Chain.cons h List.Chain.nil
  | _, _, _, h, cons h' p => List.Chain.cons h (chain_adj_support h' p)

theorem chain'_adj_support : ∀ {u v : V} (p : G.Walk u v), List.Chain' G.Adj p.Support
  | _, _, nil => List.Chain.nil
  | _, _, cons h p => chain_adj_support h p

theorem chain_dart_adj_darts : ∀ {d : G.Dart} {v w : V} (h : d.snd = v) (p : G.Walk v w), List.Chain G.DartAdj d p.darts
  | _, _, _, h, nil => List.Chain.nil
  | _, _, _, h, cons h' p => List.Chain.cons h (chain_dart_adj_darts rfl p)

theorem chain'_dart_adj_darts : ∀ {u v : V} (p : G.Walk u v), List.Chain' G.DartAdj p.darts
  | _, _, nil => trivialₓ
  | _, _, cons h p => chain_dart_adj_darts rfl p

/-- Every edge in a walk's edge list is an edge of the graph.
It is written in this form (rather than using `⊆`) to avoid unsightly coercions. -/
theorem edges_subset_edge_set : ∀ {u v : V} (p : G.Walk u v) ⦃e : Sym2 V⦄ (h : e ∈ p.edges), e ∈ G.EdgeSet
  | _, _, cons h' p', e, h => by
    rcases h with ⟨rfl, h⟩ <;> solve_by_elim

@[simp]
theorem darts_nil {u : V} : (nil : G.Walk u u).darts = [] :=
  rfl

@[simp]
theorem darts_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).darts = ⟨(u, v), h⟩ :: p.darts :=
  rfl

@[simp]
theorem darts_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) : (p.append p').darts = p.darts ++ p'.darts := by
  induction p <;> simp [*]

@[simp]
theorem darts_reverse {u v : V} (p : G.Walk u v) : p.reverse.darts = (p.darts.map Dart.symm).reverse := by
  induction p <;> simp [*, ← Sym2.eq_swap]

theorem mem_darts_reverse {u v : V} {d : G.Dart} {p : G.Walk u v} : d ∈ p.reverse.darts ↔ d.symm ∈ p.darts := by
  simp

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem cons_map_snd_darts {u v : V} (p : G.Walk u v) : u :: p.darts.map Dart.snd = p.Support := by
  induction p <;> simp [*]

theorem map_snd_darts {u v : V} (p : G.Walk u v) : p.darts.map Dart.snd = p.Support.tail := by
  simpa using congr_arg List.tail (cons_map_snd_darts p)

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem map_fst_darts_append {u v : V} (p : G.Walk u v) : p.darts.map Dart.fst ++ [v] = p.Support := by
  induction p <;> simp [*]

theorem map_fst_darts {u v : V} (p : G.Walk u v) : p.darts.map Dart.fst = p.Support.init := by
  simpa! using congr_arg List.init (map_fst_darts_append p)

@[simp]
theorem edges_nil {u : V} : (nil : G.Walk u u).edges = [] :=
  rfl

@[simp]
theorem edges_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).edges = ⟦(u, v)⟧ :: p.edges :=
  rfl

@[simp]
theorem edges_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) : (p.append p').edges = p.edges ++ p'.edges := by
  simp [← edges]

@[simp]
theorem edges_reverse {u v : V} (p : G.Walk u v) : p.reverse.edges = p.edges.reverse := by
  simp [← edges]

@[simp]
theorem length_support {u v : V} (p : G.Walk u v) : p.Support.length = p.length + 1 := by
  induction p <;> simp [*]

@[simp]
theorem length_darts {u v : V} (p : G.Walk u v) : p.darts.length = p.length := by
  induction p <;> simp [*]

@[simp]
theorem length_edges {u v : V} (p : G.Walk u v) : p.edges.length = p.length := by
  simp [← edges]

theorem dart_fst_mem_support_of_mem_darts : ∀ {u v : V} (p : G.Walk u v) {d : G.Dart}, d ∈ p.darts → d.fst ∈ p.Support
  | u, v, cons h p', d, hd => by
    simp only [← support_cons, ← darts_cons, ← List.mem_cons_iff] at hd⊢
    rcases hd with (rfl | hd)
    · exact Or.inl rfl
      
    · exact Or.inr (dart_fst_mem_support_of_mem_darts _ hd)
      

theorem dart_snd_mem_support_of_mem_darts {u v : V} (p : G.Walk u v) {d : G.Dart} (h : d ∈ p.darts) :
    d.snd ∈ p.Support := by
  simpa using
    p.reverse.dart_fst_mem_support_of_mem_darts
      (by
        simp [← h] : d.symm ∈ p.reverse.darts)

theorem fst_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : ⟦(t, u)⟧ ∈ p.edges) : t ∈ p.Support := by
  obtain ⟨d, hd, he⟩ := list.mem_map.mp he
  rw [dart_edge_eq_mk_iff'] at he
  rcases he with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact dart_fst_mem_support_of_mem_darts _ hd
    
  · exact dart_snd_mem_support_of_mem_darts _ hd
    

theorem snd_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : ⟦(t, u)⟧ ∈ p.edges) : u ∈ p.Support := by
  rw [Sym2.eq_swap] at he
  exact p.fst_mem_support_of_mem_edges he

theorem darts_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.Support.Nodup) : p.darts.Nodup := by
  induction p
  · simp
    
  · simp only [← darts_cons, ← support_cons, ← List.nodup_cons] at h⊢
    refine' ⟨fun h' => h.1 (dart_fst_mem_support_of_mem_darts p_p h'), p_ih h.2⟩
    

theorem edges_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.Support.Nodup) : p.edges.Nodup := by
  induction p
  · simp
    
  · simp only [← edges_cons, ← support_cons, ← List.nodup_cons] at h⊢
    exact ⟨fun h' => h.1 (fst_mem_support_of_mem_edges p_p h'), p_ih h.2⟩
    

/-! ### Trails, paths, circuits, cycles -/


/-- A *trail* is a walk with no repeating edges. -/
structure IsTrail {u v : V} (p : G.Walk u v) : Prop where
  edges_nodup : p.edges.Nodup

-- ./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure
/-- A *path* is a walk with no repeating vertices.
Use `simple_graph.walk.is_path.mk'` for a simpler constructor. -/
structure IsPath {u v : V} (p : G.Walk u v) extends
  "./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure" : Prop where
  support_nodup : p.Support.Nodup

-- ./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure
/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
structure IsCircuit {u : V} (p : G.Walk u u) extends
  "./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure" : Prop where
  ne_nil : p ≠ nil

-- ./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure
/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure IsCycle {u : V} (p : G.Walk u u) extends
  "./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure" : Prop where
  support_nodup : p.Support.tail.Nodup

theorem is_trail_def {u v : V} (p : G.Walk u v) : p.IsTrail ↔ p.edges.Nodup :=
  ⟨IsTrail.edges_nodup, fun h => ⟨h⟩⟩

theorem IsPath.mk' {u v : V} {p : G.Walk u v} (h : p.Support.Nodup) : IsPath p :=
  ⟨⟨edges_nodup_of_support_nodup h⟩, h⟩

theorem is_path_def {u v : V} (p : G.Walk u v) : p.IsPath ↔ p.Support.Nodup :=
  ⟨IsPath.support_nodup, IsPath.mk'⟩

theorem is_cycle_def {u : V} (p : G.Walk u u) : p.IsCycle ↔ IsTrail p ∧ p ≠ nil ∧ p.Support.tail.Nodup :=
  Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩

@[simp]
theorem IsTrail.nil {u : V} : (nil : G.Walk u u).IsTrail :=
  ⟨by
    simp [← edges]⟩

theorem IsTrail.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} : (cons h p).IsTrail → p.IsTrail := by
  simp [← is_trail_def]

@[simp]
theorem cons_is_trail_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsTrail ↔ p.IsTrail ∧ ⟦(u, v)⟧ ∉ p.edges := by
  simp [← is_trail_def, ← and_comm]

theorem IsTrail.reverse {u v : V} (p : G.Walk u v) (h : p.IsTrail) : p.reverse.IsTrail := by
  simpa [← is_trail_def] using h

@[simp]
theorem reverse_is_trail_iff {u v : V} (p : G.Walk u v) : p.reverse.IsTrail ↔ p.IsTrail := by
  constructor <;>
    · intro h
      convert h.reverse _
      try
        rw [reverse_reverse]
      

theorem IsTrail.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w} (h : (p.append q).IsTrail) : p.IsTrail :=
  by
  rw [is_trail_def, edges_append, List.nodup_append] at h
  exact ⟨h.1⟩

theorem IsTrail.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w} (h : (p.append q).IsTrail) : q.IsTrail :=
  by
  rw [is_trail_def, edges_append, List.nodup_append] at h
  exact ⟨h.2.1⟩

theorem IsTrail.count_edges_le_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail) (e : Sym2 V) :
    p.edges.count e ≤ 1 :=
  List.nodup_iff_count_le_one.mp h.edges_nodup e

theorem IsTrail.count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail) {e : Sym2 V}
    (he : e ∈ p.edges) : p.edges.count e = 1 :=
  List.count_eq_one_of_mem h.edges_nodup he

@[simp]
theorem IsPath.nil {u : V} : (nil : G.Walk u u).IsPath := by
  fconstructor <;> simp

theorem IsPath.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} : (cons h p).IsPath → p.IsPath := by
  simp [← is_path_def]

@[simp]
theorem cons_is_path_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).IsPath ↔ p.IsPath ∧ u ∉ p.Support :=
  by
  constructor <;> simp (config := { contextual := true })[← is_path_def]

theorem IsPath.reverse {u v : V} {p : G.Walk u v} (h : p.IsPath) : p.reverse.IsPath := by
  simpa [← is_path_def] using h

@[simp]
theorem is_path_reverse_iff {u v : V} (p : G.Walk u v) : p.reverse.IsPath ↔ p.IsPath := by
  constructor <;> intro h <;> convert h.reverse <;> simp

theorem IsPath.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w} : (p.append q).IsPath → p.IsPath := by
  simp only [← is_path_def, ← support_append]
  exact List.Nodupₓ.of_append_left

theorem IsPath.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w} (h : (p.append q).IsPath) : q.IsPath := by
  rw [← is_path_reverse_iff] at h⊢
  rw [reverse_append] at h
  apply h.of_append_left

@[simp]
theorem IsCycle.not_of_nil {u : V} : ¬(nil : G.Walk u u).IsCycle := fun h => h.ne_nil rfl

/-! ### Walk decompositions -/


section WalkDecomp

variable [DecidableEq V]

/-- Given a vertex in the support of a path, give the path up until (and including) that vertex. -/
def takeUntil : ∀ {v w : V} (p : G.Walk v w) (u : V) (h : u ∈ p.Support), G.Walk v u
  | v, w, nil, u, h => by
    rw [mem_support_nil_iff.mp h]
  | v, w, cons r p, u, h =>
    if hx : v = u then by
      subst u
    else cons r (take_until p _ <| h.casesOn (fun h' => (hx h'.symm).elim) id)

/-- Given a vertex in the support of a path, give the path from (and including) that vertex to
the end. In other words, drop vertices from the front of a path until (and not including)
that vertex. -/
def dropUntil : ∀ {v w : V} (p : G.Walk v w) (u : V) (h : u ∈ p.Support), G.Walk u w
  | v, w, nil, u, h => by
    rw [mem_support_nil_iff.mp h]
  | v, w, cons r p, u, h =>
    if hx : v = u then by
      subst u
      exact cons r p
    else drop_until p _ <| h.casesOn (fun h' => (hx h'.symm).elim) id

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
/-- The `take_until` and `drop_until` functions split a walk into two pieces.
The lemma `count_support_take_until_eq_one` specifies where this split occurs. -/
@[simp]
theorem take_spec {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) : (p.takeUntil u h).append (p.dropUntil u h) = p :=
  by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    rfl
    
  · obtain rfl | h := h
    · simp
      
    · simp only
      split_ifs with h' <;> subst_vars <;> simp [*]
      
    

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
@[simp]
theorem count_support_take_until_eq_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) :
    (p.takeUntil u h).Support.count u = 1 := by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    simp
    
  · obtain rfl | h := h
    · simp
      
    · simp only
      split_ifs with h' <;> rw [eq_comm] at h' <;> subst_vars <;> simp [*, ← List.count_cons]
      
    

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem count_edges_take_until_le_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) (x : V) :
    (p.takeUntil u h).edges.count ⟦(u, x)⟧ ≤ 1 := by
  induction' p with u' u' v' w' ha p' ih
  · rw [mem_support_nil_iff] at h
    subst u
    simp
    
  · obtain rfl | h := h
    · simp
      
    · simp only
      split_ifs with h'
      · subst h'
        simp
        
      · rw [edges_cons, List.count_cons]
        split_ifs with h''
        · rw [Sym2.eq_iff] at h''
          obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h''
          · exact (h' rfl).elim
            
          · cases p' <;> simp
            
          
        · apply ih
          
        
      
    

theorem support_take_until_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) :
    (p.takeUntil u h).Support ⊆ p.Support := fun x hx => by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inl hx

theorem support_drop_until_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) :
    (p.dropUntil u h).Support ⊆ p.Support := fun x hx => by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inr hx

theorem darts_take_until_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) : (p.takeUntil u h).darts ⊆ p.darts :=
  fun x hx => by
  rw [← take_spec p h, darts_append, List.mem_appendₓ]
  exact Or.inl hx

theorem darts_drop_until_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) : (p.dropUntil u h).darts ⊆ p.darts :=
  fun x hx => by
  rw [← take_spec p h, darts_append, List.mem_appendₓ]
  exact Or.inr hx

theorem edges_take_until_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) : (p.takeUntil u h).edges ⊆ p.edges :=
  List.map_subsetₓ _ (p.darts_take_until_subset h)

theorem edges_drop_until_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) : (p.dropUntil u h).edges ⊆ p.edges :=
  List.map_subsetₓ _ (p.darts_drop_until_subset h)

theorem length_take_until_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) : (p.takeUntil u h).length ≤ p.length :=
  by
  have := congr_arg walk.length (p.take_spec h)
  rw [length_append] at this
  exact Nat.Le.intro this

theorem length_drop_until_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) : (p.dropUntil u h).length ≤ p.length :=
  by
  have := congr_arg walk.length (p.take_spec h)
  rw [length_append, add_commₓ] at this
  exact Nat.Le.intro this

protected theorem IsTrail.take_until {u v w : V} {p : G.Walk v w} (hc : p.IsTrail) (h : u ∈ p.Support) :
    (p.takeUntil u h).IsTrail :=
  IsTrail.of_append_left
    (by
      rwa [← take_spec _ h] at hc)

protected theorem IsTrail.drop_until {u v w : V} {p : G.Walk v w} (hc : p.IsTrail) (h : u ∈ p.Support) :
    (p.dropUntil u h).IsTrail :=
  IsTrail.of_append_right
    (by
      rwa [← take_spec _ h] at hc)

protected theorem IsPath.take_until {u v w : V} {p : G.Walk v w} (hc : p.IsPath) (h : u ∈ p.Support) :
    (p.takeUntil u h).IsPath :=
  IsPath.of_append_left
    (by
      rwa [← take_spec _ h] at hc)

protected theorem IsPath.drop_until {u v w : V} (p : G.Walk v w) (hc : p.IsPath) (h : u ∈ p.Support) :
    (p.dropUntil u h).IsPath :=
  IsPath.of_append_right
    (by
      rwa [← take_spec _ h] at hc)

/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.Support) : G.Walk u u :=
  (c.dropUntil u h).append (c.takeUntil u h)

@[simp]
theorem support_rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.Support) : (c.rotate h).Support.tail ~r c.Support.tail :=
  by
  simp only [← rotate, ← tail_support_append]
  apply List.IsRotated.trans List.is_rotated_append
  rw [← tail_support_append, take_spec]

theorem rotate_darts {u v : V} (c : G.Walk v v) (h : u ∈ c.Support) : (c.rotate h).darts ~r c.darts := by
  simp only [← rotate, ← darts_append]
  apply List.IsRotated.trans List.is_rotated_append
  rw [← darts_append, take_spec]

theorem rotate_edges {u v : V} (c : G.Walk v v) (h : u ∈ c.Support) : (c.rotate h).edges ~r c.edges :=
  (rotate_darts c h).map _

protected theorem IsTrail.rotate {u v : V} {c : G.Walk v v} (hc : c.IsTrail) (h : u ∈ c.Support) :
    (c.rotate h).IsTrail := by
  rw [is_trail_def, (c.rotate_edges h).Perm.nodup_iff]
  exact hc.edges_nodup

protected theorem IsCircuit.rotate {u v : V} {c : G.Walk v v} (hc : c.IsCircuit) (h : u ∈ c.Support) :
    (c.rotate h).IsCircuit := by
  refine' ⟨hc.to_trail.rotate _, _⟩
  cases c
  · exact (hc.ne_nil rfl).elim
    
  · intro hn
    have hn' := congr_arg length hn
    rw [rotate, length_append, add_commₓ, ← length_append, take_spec] at hn'
    simpa using hn'
    

protected theorem IsCycle.rotate {u v : V} {c : G.Walk v v} (hc : c.IsCycle) (h : u ∈ c.Support) :
    (c.rotate h).IsCycle := by
  refine' ⟨hc.to_circuit.rotate _, _⟩
  rw [List.IsRotated.nodup_iff (support_rotate _ _)]
  exact hc.support_nodup

end WalkDecomp

end Walk

/-! ### Walks to paths -/


/-- The type for paths between two vertices. -/
abbrev Path (u v : V) :=
  { p : G.Walk u v // p.IsPath }

namespace Walk

variable {G} [DecidableEq V]

/-- Given a walk, produces a walk from it by bypassing subwalks between repeated vertices.
The result is a path, as shown in `simple_graph.walk.bypass_is_path`.
This is packaged up in `simple_graph.walk.to_path`. -/
def bypass : ∀ {u v : V}, G.Walk u v → G.Walk u v
  | u, v, nil => nil
  | u, v, cons ha p =>
    let p' := p.bypass
    if hs : u ∈ p'.Support then p'.dropUntil u hs else cons ha p'

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem bypass_is_path {u v : V} (p : G.Walk u v) : p.bypass.IsPath := by
  induction p
  · simp
    
  · simp only [← bypass]
    split_ifs
    · apply is_path.drop_until
      assumption
      
    · simp [*, ← cons_is_path_iff]
      
    

theorem length_bypass_le {u v : V} (p : G.Walk u v) : p.bypass.length ≤ p.length := by
  induction p
  · rfl
    
  · simp only [← bypass]
    split_ifs
    · trans
      apply length_drop_until_le
      rw [length_cons]
      exact le_add_right p_ih
      
    · rw [length_cons, length_cons]
      exact add_le_add_right p_ih 1
      
    

/-- Given a walk, produces a path with the same endpoints using `simple_graph.walk.bypass`. -/
def toPath {u v : V} (p : G.Walk u v) : G.Path u v :=
  ⟨p.bypass, p.bypass_is_path⟩

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem support_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.Support ⊆ p.Support := by
  induction p
  · simp
    
  · simp only
    split_ifs
    · apply List.Subset.trans (support_drop_until_subset _ _)
      apply List.subset_cons_of_subsetₓ
      assumption
      
    · rw [support_cons]
      apply List.cons_subset_consₓ
      assumption
      
    

theorem support_to_path_subset {u v : V} (p : G.Walk u v) : (p.toPath : G.Walk u v).Support ⊆ p.Support :=
  support_bypass_subset _

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem darts_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.darts ⊆ p.darts := by
  induction p
  · simp
    
  · simp only
    split_ifs
    · apply List.Subset.trans (darts_drop_until_subset _ _)
      apply List.subset_cons_of_subsetₓ _ p_ih
      
    · rw [darts_cons]
      exact List.cons_subset_consₓ _ p_ih
      
    

theorem edges_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.edges ⊆ p.edges :=
  List.map_subsetₓ _ p.darts_bypass_subset

theorem darts_to_path_subset {u v : V} (p : G.Walk u v) : (p.toPath : G.Walk u v).darts ⊆ p.darts :=
  darts_bypass_subset _

theorem edges_to_path_subset {u v : V} (p : G.Walk u v) : (p.toPath : G.Walk u v).edges ⊆ p.edges :=
  edges_bypass_subset _

end Walk

/-! ## Mapping paths -/


namespace Walk

variable {G G'}

/-- Given a graph homomorphism, map walks to walks. -/
protected def map (f : G →g G') : ∀ {u v : V}, G.Walk u v → G'.Walk (f u) (f v)
  | _, _, nil => nil
  | _, _, cons h p => cons (f.map_adj h) (map p)

variable (f : G →g G') {u v : V} (p : G.Walk u v)

@[simp]
theorem map_nil : (nil : G.Walk u u).map f = nil :=
  rfl

@[simp]
theorem map_cons {w : V} (h : G.Adj w u) : (cons h p).map f = cons (f.map_adj h) (p.map f) :=
  rfl

@[simp]
theorem length_map : (p.map f).length = p.length := by
  induction p <;> simp [*]

theorem map_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) : (p.append q).map f = (p.map f).append (q.map f) := by
  induction p <;> simp [*]

@[simp]
theorem reverse_map : (p.map f).reverse = p.reverse.map f := by
  induction p <;> simp [← map_append, *]

@[simp]
theorem support_map : (p.map f).Support = p.Support.map f := by
  induction p <;> simp [*]

@[simp]
theorem darts_map : (p.map f).darts = p.darts.map f.mapDart := by
  induction p <;> simp [*]

@[simp]
theorem edges_map : (p.map f).edges = p.edges.map (Sym2.map f) := by
  induction p <;> simp [*]

variable {p f}

theorem map_is_path_of_injective (hinj : Function.Injective f) (hp : p.IsPath) : (p.map f).IsPath := by
  induction' p with w u v w huv hvw ih
  · simp
    
  · rw [walk.cons_is_path_iff] at hp
    simp [← ih hp.1]
    intro x hx hf
    cases hinj hf
    exact hp.2 hx
    

protected theorem IsPath.of_map {f : G →g G'} (hp : (p.map f).IsPath) : p.IsPath := by
  induction' p with w u v w huv hvw ih
  · simp
    
  · rw [map_cons, walk.cons_is_path_iff, support_map] at hp
    rw [walk.cons_is_path_iff]
    cases' hp with hp1 hp2
    refine' ⟨ih hp1, _⟩
    contrapose! hp2
    exact List.mem_map_of_memₓ f hp2
    

theorem map_is_path_iff_of_injective (hinj : Function.Injective f) : (p.map f).IsPath ↔ p.IsPath :=
  ⟨IsPath.of_map, map_is_path_of_injective hinj⟩

variable (p f)

theorem map_injective_of_injective {f : G →g G'} (hinj : Function.Injective f) (u v : V) :
    Function.Injective (Walk.map f : G.Walk u v → G'.Walk (f u) (f v)) := by
  intro p p' h
  induction' p with _ _ _ _ _ _ ih generalizing p'
  · cases p'
    · rfl
      
    simpa using h
    
  · induction p'
    · simpa using h
      
    · simp only [← map_cons] at h
      cases hinj h.1
      simp only [← eq_self_iff_true, ← heq_iff_eq, ← true_andₓ]
      apply ih
      simpa using h.2
      
    

end Walk

namespace Path

variable {G G'}

/-- Given an injective graph homomorphism, map paths to paths. -/
@[simps]
protected def map (f : G →g G') (hinj : Function.Injective f) {u v : V} (p : G.Path u v) : G'.Path (f u) (f v) :=
  ⟨Walk.map f p, Walk.map_is_path_of_injective hinj p.2⟩

theorem map_injective {f : G →g G'} (hinj : Function.Injective f) (u v : V) :
    Function.Injective (Path.map f hinj : G.Path u v → G'.Path (f u) (f v)) := by
  rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
  simp only [← path.map, ← Subtype.coe_mk] at h
  simp [← walk.map_injective_of_injective hinj u v h]

/-- Given a graph embedding, map paths to paths. -/
@[simps]
protected def mapEmbedding (f : G ↪g G') {u v : V} (p : G.Path u v) : G'.Path (f u) (f v) :=
  Path.map f.toHom f.Injective p

theorem map_embedding_injective (f : G ↪g G') (u v : V) :
    Function.Injective (Path.mapEmbedding f : G.Path u v → G'.Path (f u) (f v)) :=
  map_injective f.Injective u v

end Path

/-! ## Deleting edges -/


namespace Walk

variable {G}

/-- Given a walk that avoids a set of edges, produce a walk in the graph
with those edges deleted. -/
@[simp]
def toDeleteEdges (s : Set (Sym2 V)) :
    ∀ {v w : V} (p : G.Walk v w) (hp : ∀ e, e ∈ p.edges → ¬e ∈ s), (G.deleteEdges s).Walk v w
  | _, _, nil, _ => nil
  | _, _, cons' u v w huv p, hp =>
    cons
      ((G.delete_edges_adj _ _ _).mpr
        ⟨huv,
          hp ⟦(u, v)⟧
            (by
              simp )⟩)
      (p.toDeleteEdges fun e he =>
        hp e
          (by
            simp [← he]))

/-- Given a walk that avoids an edge, create a walk in the subgraph with that edge deleted.
This is an abbreviation for `simple_graph.walk.to_delete_edges`. -/
abbrev toDeleteEdge {v w : V} (e : Sym2 V) (p : G.Walk v w) (hp : e ∉ p.edges) : (G.deleteEdges {e}).Walk v w :=
  p.toDeleteEdges {e} fun e' => by
    contrapose!
    simp (config := { contextual := true })[← hp]

@[simp]
theorem map_to_delete_edges_eq (s : Set (Sym2 V)) {v w : V} {p : G.Walk v w} (hp) :
    Walk.map (Hom.mapSpanningSubgraphs (G.delete_edges_le s)) (p.toDeleteEdges s hp) = p := by
  induction p <;> simp [*]

theorem IsPath.to_delete_edges (s : Set (Sym2 V)) {v w : V} {p : G.Walk v w} (h : p.IsPath) (hp) :
    (p.toDeleteEdges s hp).IsPath := by
  rw [← map_to_delete_edges_eq s hp] at h
  exact h.of_map

end Walk

/-! ## `reachable` and `connected` -/


/-- Two vertices are *reachable* if there is a walk between them.
This is equivalent to `relation.refl_trans_gen` of `G.adj`.
See `simple_graph.reachable_iff_refl_trans_gen`. -/
def Reachable (u v : V) : Prop :=
  Nonempty (G.Walk u v)

variable {G}

theorem reachable_iff_nonempty_univ {u v : V} : G.Reachable u v ↔ (Set.Univ : Set (G.Walk u v)).Nonempty :=
  Set.nonempty_iff_univ_nonempty

protected theorem Reachable.elim {p : Prop} {u v : V} (h : G.Reachable u v) (hp : G.Walk u v → p) : p :=
  Nonempty.elimₓ h hp

protected theorem Reachable.elim_path {p : Prop} {u v : V} (h : G.Reachable u v) (hp : G.Path u v → p) : p := by
  classical
  exact h.elim fun q => hp q.toPath

@[refl]
protected theorem Reachable.refl (u : V) : G.Reachable u u := by
  fconstructor
  rfl

protected theorem Reachable.rfl {u : V} : G.Reachable u u :=
  Reachable.refl _

@[symm]
protected theorem Reachable.symm {u v : V} (huv : G.Reachable u v) : G.Reachable v u :=
  huv.elim fun p => ⟨p.reverse⟩

@[trans]
protected theorem Reachable.trans {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) : G.Reachable u w :=
  huv.elim fun puv => hvw.elim fun pvw => ⟨puv.append pvw⟩

theorem reachable_iff_refl_trans_gen (u v : V) : G.Reachable u v ↔ Relation.ReflTransGen G.Adj u v := by
  constructor
  · rintro ⟨h⟩
    induction h
    · rfl
      
    · exact (Relation.ReflTransGen.single h_h).trans h_ih
      
    
  · intro h
    induction' h with _ _ _ ha hr
    · rfl
      
    · exact reachable.trans hr ⟨walk.cons ha walk.nil⟩
      
    

variable (G)

theorem reachable_is_equivalence : Equivalenceₓ G.Reachable :=
  mk_equivalence _ (@Reachable.refl _ G) (@Reachable.symm _ G) (@Reachable.trans _ G)

/-- The equivalence relation on vertices given by `simple_graph.reachable`. -/
def reachableSetoid : Setoidₓ V :=
  Setoidₓ.mk _ G.reachable_is_equivalence

/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop :=
  ∀ u v : V, G.Reachable u v

theorem Preconnected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G →g H) (hf : Surjective f)
    (hG : G.Preconnected) : H.Preconnected :=
  hf.forall₂.2 fun a b => (hG _ _).map <| Walk.map _

theorem Iso.preconnected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) : G.Preconnected ↔ H.Preconnected :=
  ⟨Preconnected.map e.toHom e.toEquiv.Surjective, Preconnected.map e.symm.toHom e.symm.toEquiv.Surjective⟩

/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `has_coe_to_fun` instance so that `h u v` can be used instead
of `h.preconnected u v`. -/
@[protect_proj, mk_iff]
structure Connected : Prop where
  Preconnected : G.Preconnected
  [Nonempty : Nonempty V]

instance : CoeFun G.Connected fun _ => ∀ u v : V, G.Reachable u v :=
  ⟨fun h => h.Preconnected⟩

theorem Connected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G →g H) (hf : Surjective f) (hG : G.Connected) :
    H.Connected := by
  have := hG.nonempty.map f
  exact ⟨hG.preconnected.map f hf⟩

theorem Iso.connected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) : G.Connected ↔ H.Connected :=
  ⟨Connected.map e.toHom e.toEquiv.Surjective, Connected.map e.symm.toHom e.symm.toEquiv.Surjective⟩

/-- The quotient of `V` by the `simple_graph.reachable` relation gives the connected
components of a graph. -/
def ConnectedComponent :=
  Quot G.Reachable

/-- Gives the connected component containing a particular vertex. -/
def connectedComponentMk (v : V) : G.ConnectedComponent :=
  Quot.mk G.Reachable v

instance ConnectedComponent.inhabited [Inhabited V] : Inhabited G.ConnectedComponent :=
  ⟨G.connectedComponentMk default⟩

section ConnectedComponent

variable {G}

@[elab_as_eliminator]
protected theorem ConnectedComponent.ind {β : G.ConnectedComponent → Prop} (h : ∀ v : V, β (G.connectedComponentMk v))
    (c : G.ConnectedComponent) : β c :=
  Quot.ind h c

@[elab_as_eliminator]
protected theorem ConnectedComponent.ind₂ {β : G.ConnectedComponent → G.ConnectedComponent → Prop}
    (h : ∀ v w : V, β (G.connectedComponentMk v) (G.connectedComponentMk w)) (c d : G.ConnectedComponent) : β c d :=
  Quot.induction_on₂ c d h

protected theorem ConnectedComponent.sound {v w : V} :
    G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk w :=
  Quot.sound

protected theorem ConnectedComponent.exact {v w : V} :
    G.connectedComponentMk v = G.connectedComponentMk w → G.Reachable v w :=
  @Quotientₓ.exact _ G.reachableSetoid _ _

@[simp]
protected theorem ConnectedComponent.eq {v w : V} :
    G.connectedComponentMk v = G.connectedComponentMk w ↔ G.Reachable v w :=
  @Quotientₓ.eq _ G.reachableSetoid _ _

/-- The `connected_component` specialization of `quot.lift`. Provides the stronger
assumption that the vertices are connected by a path. -/
protected def ConnectedComponent.lift {β : Sort _} (f : V → β)
    (h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w) : G.ConnectedComponent → β :=
  Quot.lift f fun v w (h' : G.Reachable v w) => h'.elim_path fun hp => h v w hp hp.2

@[simp]
protected theorem ConnectedComponent.lift_mk {β : Sort _} {f : V → β}
    {h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w} {v : V} :
    ConnectedComponent.lift f h (G.connectedComponentMk v) = f v :=
  rfl

protected theorem ConnectedComponent.exists {p : G.ConnectedComponent → Prop} :
    (∃ c : G.ConnectedComponent, p c) ↔ ∃ v, p (G.connectedComponentMk v) :=
  (surjective_quot_mk G.Reachable).exists

protected theorem ConnectedComponent.forall {p : G.ConnectedComponent → Prop} :
    (∀ c : G.ConnectedComponent, p c) ↔ ∀ v, p (G.connectedComponentMk v) :=
  (surjective_quot_mk G.Reachable).forall

theorem Preconnected.subsingleton_connected_component (h : G.Preconnected) : Subsingleton G.ConnectedComponent :=
  ⟨ConnectedComponent.ind₂ fun v w => ConnectedComponent.sound (h v w)⟩

end ConnectedComponent

variable {G}

/-- A subgraph is connected if it is connected as a simple graph. -/
abbrev Subgraph.Connected (H : G.Subgraph) : Prop :=
  H.coe.Connected

theorem Preconnected.set_univ_walk_nonempty (hconn : G.Preconnected) (u v : V) :
    (Set.Univ : Set (G.Walk u v)).Nonempty := by
  rw [← Set.nonempty_iff_univ_nonempty]
  exact hconn u v

theorem Connected.set_univ_walk_nonempty (hconn : G.Connected) (u v : V) : (Set.Univ : Set (G.Walk u v)).Nonempty :=
  hconn.Preconnected.set_univ_walk_nonempty u v

/-! ### Walks of a given length -/


section WalkCounting

theorem set_walk_self_length_zero_eq (u : V) : { p : G.Walk u u | p.length = 0 } = {Walk.nil} := by
  ext p
  simp

theorem set_walk_length_zero_eq_of_ne {u v : V} (h : u ≠ v) : { p : G.Walk u v | p.length = 0 } = ∅ := by
  ext p
  simp only [← Set.mem_set_of_eq, ← Set.mem_empty_eq, ← iff_falseₓ]
  exact fun h' => absurd (walk.eq_of_length_eq_zero h') h

theorem set_walk_length_succ_eq (u v : V) (n : ℕ) :
    { p : G.Walk u v | p.length = n.succ } =
      ⋃ (w : V) (h : G.Adj u w), Walk.cons h '' { p' : G.Walk w v | p'.length = n } :=
  by
  ext p
  cases' p with _ _ w _ huw pwv
  · simp [← eq_comm]
    
  · simp only [← Nat.succ_eq_add_one, ← Set.mem_set_of_eq, ← walk.length_cons, ← add_left_injₓ, ← Set.mem_Union, ←
      Set.mem_image, ← exists_prop]
    constructor
    · rintro rfl
      exact ⟨w, huw, pwv, rfl, rfl, HEq.rfl⟩
      
    · rintro ⟨w, huw, pwv, rfl, rfl, rfl⟩
      rfl
      
    

variable (G) [Fintype V] [DecidableRel G.Adj] [DecidableEq V]

/-- The `finset` of length-`n` walks from `u` to `v`.
This is used to give `{p : G.walk u v | p.length = n}` a `fintype` instance, and it
can also be useful as a recursive description of this set when `V` is finite.

See `simple_graph.coe_finset_walk_length_eq` for the relationship between this `finset` and
the set of length-`n` walks. -/
def finsetWalkLength : ∀ (n : ℕ) (u v : V), Finset (G.Walk u v)
  | 0, u, v =>
    if h : u = v then by
      subst u
      exact {walk.nil}
    else ∅
  | n + 1, u, v =>
    Finset.univ.bUnion fun w : V =>
      if h : G.Adj u w then
        (finset_walk_length n w v).map
          ⟨fun p => Walk.cons h p, fun p q => by
            simp ⟩
      else ∅

theorem coe_finset_walk_length_eq (n : ℕ) (u v : V) :
    (G.finsetWalkLength n u v : Set (G.Walk u v)) = { p : G.Walk u v | p.length = n } := by
  induction' n with n ih generalizing u v
  · obtain rfl | huv := eq_or_ne u v <;> simp [← finset_walk_length, ← set_walk_length_zero_eq_of_ne, *]
    
  · simp only [← finset_walk_length, ← set_walk_length_succ_eq, ← Finset.coe_bUnion, ← Finset.mem_coe, ←
      Finset.mem_univ, ← Set.Union_true]
    ext p
    simp only [← Set.mem_Union, ← Finset.mem_coe, ← Set.mem_image, ← Set.mem_set_of_eq]
    congr 2
    ext w
    simp only [← Set.ext_iff, ← Finset.mem_coe, ← Set.mem_set_of_eq] at ih
    split_ifs with huw <;> simp [← huw, ← ih]
    

variable {G}

theorem Walk.length_eq_of_mem_finset_walk_length {n : ℕ} {u v : V} (p : G.Walk u v) :
    p ∈ G.finsetWalkLength n u v → p.length = n :=
  (Set.ext_iff.mp (G.coe_finset_walk_length_eq n u v) p).mp

variable (G)

instance fintypeSetWalkLength (u v : V) (n : ℕ) : Fintype { p : G.Walk u v | p.length = n } :=
  (Fintype.subtype (G.finsetWalkLength n u v)) fun p => by
    rw [← Finset.mem_coe, coe_finset_walk_length_eq]

theorem set_walk_length_to_finset_eq (n : ℕ) (u v : V) :
    { p : G.Walk u v | p.length = n }.toFinset = G.finsetWalkLength n u v := by
  ext p
  simp [coe_finset_walk_length_eq]

/- See `simple_graph.adj_matrix_pow_apply_eq_card_walk` for the cardinality in terms of the `n`th
power of the adjacency matrix. -/
theorem card_set_walk_length_eq (u v : V) (n : ℕ) :
    Fintype.card { p : G.Walk u v | p.length = n } = (G.finsetWalkLength n u v).card :=
  (Fintype.card_of_subtype (G.finsetWalkLength n u v)) fun p => by
    rw [← Finset.mem_coe, coe_finset_walk_length_eq]

end WalkCounting

end SimpleGraph


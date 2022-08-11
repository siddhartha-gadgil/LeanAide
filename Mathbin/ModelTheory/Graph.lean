/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.ModelTheory.Satisfiability
import Mathbin.Combinatorics.SimpleGraph.Basic

/-!
# First-Ordered Structures in Graph Theory
This file defines first-order languages, structures, and theories in graph theory.

## Main Definitions
* `first_order.language.graph` is the language consisting of a single relation representing
adjacency.
* `simple_graph.Structure` is the first-order structure corresponding to a given simple graph.
* `first_order.language.Theory.simple_graph` is the theory of simple graphs.
* `first_order.language.simple_graph_of_structure` gives the simple graph corresponding to a model
of the theory of simple graphs.

-/


universe u v w w'

namespace FirstOrder

namespace Language

open FirstOrder

open Structure

variable {L : Language.{u, v}} {α : Type w} {V : Type w'} {n : ℕ}

/-! ### Simple Graphs -/


/-- The language consisting of a single relation representing adjacency. -/
protected def graph : Language :=
  Language.mk₂ Empty Empty Empty Empty Unit

/-- The symbol representing the adjacency relation. -/
def adj : Language.graph.Relations 2 :=
  Unit.star

/-- Any simple graph can be thought of as a structure in the language of graphs. -/
def _root_.simple_graph.Structure (G : SimpleGraph V) : Language.graph.Structure V :=
  Structure.mk₂ Empty.elim Empty.elim Empty.elim Empty.elim fun _ => G.Adj

namespace Graph

instance : IsRelational Language.graph :=
  language.is_relational_mk₂

instance : Subsingleton (Language.graph.Relations n) :=
  language.subsingleton_mk₂_relations

end Graph

/-- The theory of simple graphs. -/
protected def Theory.SimpleGraph : Language.graph.Theory :=
  {adj.Irreflexive, adj.Symmetric}

@[simp]
theorem Theory.simple_graph_model_iff [Language.graph.Structure V] :
    V ⊨ Theory.simple_graph ↔
      (Irreflexive fun x y : V => RelMap adj ![x, y]) ∧ Symmetric fun x y : V => RelMap adj ![x, y] :=
  by
  simp [← Theory.simple_graph]

instance simple_graph_model (G : SimpleGraph V) : @Theory.Model _ V G.Structure Theory.SimpleGraph := by
  simp only [← Theory.simple_graph_model_iff, ← rel_map_apply₂]
  exact ⟨G.loopless, G.symm⟩

variable (V)

/-- Any model of the theory of simple graphs represents a simple graph. -/
@[simps]
def simpleGraphOfStructure [Language.graph.Structure V] [V ⊨ Theory.simple_graph] : SimpleGraph V where
  Adj := fun x y => RelMap adj ![x, y]
  symm :=
    Relations.realize_symmetric.1
      (Theory.realize_sentence_of_mem Theory.SimpleGraph (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  loopless := Relations.realize_irreflexive.1 (Theory.realize_sentence_of_mem Theory.SimpleGraph (Set.mem_insert _ _))

variable {V}

@[simp]
theorem _root_.simple_graph.simple_graph_of_structure (G : SimpleGraph V) :
    @simpleGraphOfStructure V G.Structure _ = G := by
  ext
  rfl

@[simp]
theorem Structure_simple_graph_of_structure [S : Language.graph.Structure V] [V ⊨ Theory.simple_graph] :
    (simpleGraphOfStructure V).Structure = S := by
  ext n f xs
  · exact (is_relational.empty_functions n).elim f
    
  · ext n r xs
    rw [iff_eq_eq]
    cases n
    · exact r.elim
      
    · cases n
      · exact r.elim
        
      · cases n
        · cases r
          change rel_map adj ![xs 0, xs 1] = _
          refine' congr rfl (funext _)
          simp [← Finₓ.forall_fin_two]
          
        · exact r.elim
          
        
      
    

theorem Theory.simple_graph_is_satisfiable : Theory.IsSatisfiable Theory.SimpleGraph :=
  ⟨@Theory.ModelCat.of _ _ Unit (SimpleGraph.structure ⊥) _ _⟩

end Language

end FirstOrder


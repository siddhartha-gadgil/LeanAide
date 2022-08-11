/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Adam Topaz
-/
import Mathbin.AlgebraicTopology.SimplexCategory
import Mathbin.Topology.Category.Top.Basic
import Mathbin.Topology.Instances.Nnreal

/-!
# Topological simplices

We define the natural functor from `simplex_category` to `Top` sending `[n]` to the
topological `n`-simplex.
This is used to define `Top.to_sSet` in `algebraic_topology.simpliciaL_set`.
-/


noncomputable section

namespace SimplexCategory

open Simplicial Nnreal BigOperators Classical

attribute [local instance] CategoryTheory.ConcreteCategory.hasCoeToSort CategoryTheory.ConcreteCategory.hasCoeToFun

/-- The topological simplex associated to `x : simplex_category`.
  This is the object part of the functor `simplex_category.to_Top`. -/
def ToTopObj (x : SimplexCategory) :=
  { f : x → ℝ≥0 | (∑ i, f i) = 1 }

instance (x : SimplexCategory) : CoeFun x.ToTopObj fun _ => x → ℝ≥0 :=
  ⟨fun f => (f : x → ℝ≥0 )⟩

@[ext]
theorem ToTopObj.ext {x : SimplexCategory} (f g : x.ToTopObj) : (f : x → ℝ≥0 ) = g → f = g :=
  Subtype.ext

/-- A morphism in `simplex_category` induces a map on the associated topological spaces. -/
def toTopMap {x y : SimplexCategory} (f : x ⟶ y) : x.ToTopObj → y.ToTopObj := fun g =>
  ⟨fun i => ∑ j in Finset.univ.filter fun k => f k = i, g j, by
    dsimp' [← to_Top_obj]
    simp only [← Finset.filter_congr_decidable, ← Finset.sum_congr]
    rw [← Finset.sum_bUnion]
    convert g.2
    · rw [Finset.eq_univ_iff_forall]
      intro i
      rw [Finset.mem_bUnion]
      exact
        ⟨f i, by
          simp , by
          simp ⟩
      
    · intro i hi j hj h e he
      apply h
      simp only [← true_andₓ, ← Finset.inf_eq_inter, ← Finset.mem_univ, ← Finset.mem_filter, ← Finset.mem_inter] at he
      rw [← he.1, ← he.2]
      ⟩

@[simp]
theorem coe_to_Top_map {x y : SimplexCategory} (f : x ⟶ y) (g : x.ToTopObj) (i : y) :
    toTopMap f g i = ∑ j in Finset.univ.filter fun k => f k = i, g j :=
  rfl

@[continuity]
theorem continuous_to_Top_map {x y : SimplexCategory} (f : x ⟶ y) : Continuous (toTopMap f) :=
  continuous_subtype_mk _ <|
    continuous_pi fun i =>
      (continuous_finset_sum _) fun j hj => Continuous.comp (continuous_apply _) continuous_subtype_val

/-- The functor associating the topological `n`-simplex to `[n] : simplex_category`. -/
@[simps]
def toTop : SimplexCategory ⥤ Top where
  obj := fun x => Top.of x.ToTopObj
  map := fun x y f => ⟨toTopMap f⟩
  map_id' := by
    intro x
    ext f i : 3
    change (finset.univ.filter fun k => k = i).Sum _ = _
    simp [← Finset.sum_filter]
  map_comp' := by
    intro x y z f g
    ext h i : 3
    dsimp'
    erw [← Finset.sum_bUnion]
    apply Finset.sum_congr
    · exact
        Finset.ext fun j =>
          ⟨fun hj => by
            simpa using hj, fun hj => by
            simpa using hj⟩
      
    · tauto
      
    · intro j hj k hk h e he
      apply h
      simp only [← true_andₓ, ← Finset.inf_eq_inter, ← Finset.mem_univ, ← Finset.mem_filter, ← Finset.mem_inter] at he
      rw [← he.1, ← he.2]
      

end SimplexCategory


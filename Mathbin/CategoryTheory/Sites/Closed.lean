/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Sites.SheafOfTypes
import Mathbin.Order.Closure

/-!
# Closed sieves

A natural closure operator on sieves is a closure operator on `sieve X` for each `X` which commutes
with pullback.
We show that a Grothendieck topology `J` induces a natural closure operator, and define what the
closed sieves are. The collection of `J`-closed sieves forms a presheaf which is a sheaf for `J`,
and further this presheaf can be used to determine the Grothendieck topology from the sheaf
predicate.
Finally we show that a natural closure operator on sieves induces a Grothendieck topology, and hence
that natural closure operators are in bijection with Grothendieck topologies.

## Main definitions

* `category_theory.grothendieck_topology.close`: Sends a sieve `S` on `X` to the set of arrows
  which it covers. This has all the usual properties of a closure operator, as well as commuting
  with pullback.
* `category_theory.grothendieck_topology.closure_operator`: The bundled `closure_operator` given
  by `category_theory.grothendieck_topology.close`.
* `category_theory.grothendieck_topology.closed`: A sieve `S` on `X` is closed for the topology `J`
   if it contains every arrow it covers.
* `category_theory.functor.closed_sieves`: The presheaf sending `X` to the collection of `J`-closed
  sieves on `X`. This is additionally shown to be a sheaf for `J`, and if this is a sheaf for a
  different topology `J'`, then `J' ≤ J`.
* `category_theory.grothendieck_topology.topology_of_closure_operator`: A closure operator on the
  set of sieves on every object which commutes with pullback additionally induces a Grothendieck
  topology, giving a bijection with `category_theory.grothendieck_topology.closure_operator`.


## Tags

closed sieve, closure, Grothendieck topology

## References

* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable (J₁ J₂ : GrothendieckTopology C)

namespace GrothendieckTopology

/-- The `J`-closure of a sieve is the collection of arrows which it covers. -/
@[simps]
def close {X : C} (S : Sieve X) : Sieve X where
  Arrows := fun Y f => J₁.Covers S f
  downward_closed' := fun Y Z f hS => J₁.arrow_stable _ _ hS

/-- Any sieve is smaller than its closure. -/
theorem le_close {X : C} (S : Sieve X) : S ≤ J₁.close S := fun Y g hg =>
  J₁.covering_of_eq_top (S.pullback_eq_top_of_mem hg)

/-- A sieve is closed for the Grothendieck topology if it contains every arrow it covers.
In the case of the usual topology on a topological space, this means that the open cover contains
every open set which it covers.

Note this has no relation to a closed subset of a topological space.
-/
def IsClosed {X : C} (S : Sieve X) : Prop :=
  ∀ ⦃Y : C⦄ (f : Y ⟶ X), J₁.Covers S f → S f

/-- If `S` is `J₁`-closed, then `S` covers exactly the arrows it contains. -/
theorem covers_iff_mem_of_closed {X : C} {S : Sieve X} (h : J₁.IsClosed S) {Y : C} (f : Y ⟶ X) : J₁.Covers S f ↔ S f :=
  ⟨h _, J₁.arrow_max _ _⟩

/-- Being `J`-closed is stable under pullback. -/
theorem is_closed_pullback {X Y : C} (f : Y ⟶ X) (S : Sieve X) : J₁.IsClosed S → J₁.IsClosed (S.pullback f) :=
  fun hS Z g hg =>
  hS (g ≫ f)
    (by
      rwa [J₁.covers_iff, sieve.pullback_comp])

/-- The closure of a sieve `S` is the largest closed sieve which contains `S` (justifying the name
"closure").
-/
theorem le_close_of_is_closed {X : C} {S T : Sieve X} (h : S ≤ T) (hT : J₁.IsClosed T) : J₁.close S ≤ T := fun Y f hf =>
  hT _ (J₁.superset_covering (Sieve.pullback_monotone f h) hf)

/-- The closure of a sieve is closed. -/
theorem close_is_closed {X : C} (S : Sieve X) : J₁.IsClosed (J₁.close S) := fun Y g hg =>
  J₁.arrow_trans g _ S hg fun Z h hS => hS

/-- The sieve `S` is closed iff its closure is equal to itself. -/
theorem is_closed_iff_close_eq_self {X : C} (S : Sieve X) : J₁.IsClosed S ↔ J₁.close S = S := by
  constructor
  · intro h
    apply le_antisymmₓ
    · intro Y f hf
      rw [← J₁.covers_iff_mem_of_closed h]
      apply hf
      
    · apply J₁.le_close
      
    
  · intro e
    rw [← e]
    apply J₁.close_is_closed
    

theorem close_eq_self_of_is_closed {X : C} {S : Sieve X} (hS : J₁.IsClosed S) : J₁.close S = S :=
  (J₁.is_closed_iff_close_eq_self S).1 hS

/-- Closing under `J` is stable under pullback. -/
theorem pullback_close {X Y : C} (f : Y ⟶ X) (S : Sieve X) : J₁.close (S.pullback f) = (J₁.close S).pullback f := by
  apply le_antisymmₓ
  · refine' J₁.le_close_of_is_closed (sieve.pullback_monotone _ (J₁.le_close S)) _
    apply J₁.is_closed_pullback _ _ (J₁.close_is_closed _)
    
  · intro Z g hg
    change _ ∈ J₁ _
    rw [← sieve.pullback_comp]
    apply hg
    

@[mono]
theorem monotone_close {X : C} : Monotone (J₁.close : Sieve X → Sieve X) := fun S₁ S₂ h =>
  J₁.le_close_of_is_closed (h.trans (J₁.le_close _)) (J₁.close_is_closed S₂)

@[simp]
theorem close_close {X : C} (S : Sieve X) : J₁.close (J₁.close S) = J₁.close S :=
  le_antisymmₓ (J₁.le_close_of_is_closed le_rfl (J₁.close_is_closed S)) (J₁.monotone_close (J₁.le_close _))

/-- The sieve `S` is in the topology iff its closure is the maximal sieve. This shows that the closure
operator determines the topology.
-/
theorem close_eq_top_iff_mem {X : C} (S : Sieve X) : J₁.close S = ⊤ ↔ S ∈ J₁ X := by
  constructor
  · intro h
    apply J₁.transitive (J₁.top_mem X)
    intro Y f hf
    change J₁.close S f
    rwa [h]
    
  · intro hS
    rw [eq_top_iff]
    intro Y f hf
    apply J₁.pullback_stable _ hS
    

/-- A Grothendieck topology induces a natural family of closure operators on sieves. -/
@[simps (config := { rhsMd := semireducible })]
def closureOperator (X : C) : ClosureOperator (Sieve X) :=
  ClosureOperator.mk' J₁.close
    (fun S₁ S₂ h => J₁.le_close_of_is_closed (h.trans (J₁.le_close _)) (J₁.close_is_closed S₂)) J₁.le_close fun S =>
    J₁.le_close_of_is_closed le_rfl (J₁.close_is_closed S)

@[simp]
theorem closed_iff_closed {X : C} (S : Sieve X) : S ∈ (J₁.ClosureOperator X).closed ↔ J₁.IsClosed S :=
  (J₁.is_closed_iff_close_eq_self S).symm

end GrothendieckTopology

/-- The presheaf sending each object to the set of `J`-closed sieves on it. This presheaf is a `J`-sheaf
(and will turn out to be a subobject classifier for the category of `J`-sheaves).
-/
@[simps]
def Functor.closedSieves : Cᵒᵖ ⥤ Type max v u where
  obj := fun X => { S : Sieve X.unop // J₁.IsClosed S }
  map := fun X Y f S => ⟨S.1.pullback f.unop, J₁.is_closed_pullback f.unop _ S.2⟩

/-- The presheaf of `J`-closed sieves is a `J`-sheaf.
The proof of this is adapted from [MM92], Chatper III, Section 7, Lemma 1.
-/
theorem classifier_is_sheaf : Presieve.IsSheaf J₁ (Functor.closedSieves J₁) := by
  intro X S hS
  rw [← presieve.is_separated_for_and_exists_is_amalgamation_iff_sheaf_for]
  refine' ⟨_, _⟩
  · rintro x ⟨M, hM⟩ ⟨N, hN⟩ hM₂ hN₂
    ext
    dsimp' only [← Subtype.coe_mk]
    rw [← J₁.covers_iff_mem_of_closed hM, ← J₁.covers_iff_mem_of_closed hN]
    have q : ∀ ⦃Z : C⦄ (g : Z ⟶ X) (hg : S g), M.pullback g = N.pullback g := by
      intro Z g hg
      apply congr_arg Subtype.val ((hM₂ g hg).trans (hN₂ g hg).symm)
    have MSNS : M⊓S = N⊓S := by
      ext Z g
      rw [sieve.inter_apply, sieve.inter_apply, and_comm (N g), and_comm]
      apply and_congr_right
      intro hg
      rw [sieve.pullback_eq_top_iff_mem, sieve.pullback_eq_top_iff_mem, q g hg]
    constructor
    · intro hf
      rw [J₁.covers_iff]
      apply J₁.superset_covering (sieve.pullback_monotone f inf_le_left)
      rw [← MSNS]
      apply J₁.arrow_intersect f M S hf (J₁.pullback_stable _ hS)
      
    · intro hf
      rw [J₁.covers_iff]
      apply J₁.superset_covering (sieve.pullback_monotone f inf_le_left)
      rw [MSNS]
      apply J₁.arrow_intersect f N S hf (J₁.pullback_stable _ hS)
      
    
  · intro x hx
    rw [presieve.compatible_iff_sieve_compatible] at hx
    let M := sieve.bind S fun Y f hf => (x f hf).1
    have : ∀ ⦃Y⦄ (f : Y ⟶ X) (hf : S f), M.pullback f = (x f hf).1 := by
      intro Y f hf
      apply le_antisymmₓ
      · rintro Z u ⟨W, g, f', hf', hg : (x f' hf').1 _, c⟩
        rw [sieve.pullback_eq_top_iff_mem, ←
          show (x (u ≫ f) _).1 = (x f hf).1.pullback u from congr_arg Subtype.val (hx f u hf)]
        simp_rw [← c]
        rw [show (x (g ≫ f') _).1 = _ from congr_arg Subtype.val (hx f' g hf')]
        apply sieve.pullback_eq_top_of_mem _ hg
        
      · apply sieve.le_pullback_bind S fun Y f hf => (x f hf).1
        
    refine' ⟨⟨_, J₁.close_is_closed M⟩, _⟩
    · intro Y f hf
      ext1
      dsimp'
      rw [← J₁.pullback_close, this _ hf]
      apply le_antisymmₓ (J₁.le_close_of_is_closed le_rfl (x f hf).2) (J₁.le_close _)
      
    

/-- If presheaf of `J₁`-closed sieves is a `J₂`-sheaf then `J₁ ≤ J₂`. Note the converse is true by
`classifier_is_sheaf` and `is_sheaf_of_le`.
-/
theorem le_topology_of_closed_sieves_is_sheaf {J₁ J₂ : GrothendieckTopology C}
    (h : Presieve.IsSheaf J₁ (Functor.closedSieves J₂)) : J₁ ≤ J₂ := fun X S hS => by
  rw [← J₂.close_eq_top_iff_mem]
  have : J₂.is_closed (⊤ : sieve X) := by
    intro Y f hf
    trivial
  suffices (⟨J₂.close S, J₂.close_is_closed S⟩ : Subtype _) = ⟨⊤, this⟩ by
    rw [Subtype.ext_iff] at this
    exact this
  apply (h S hS).IsSeparatedFor.ext
  · intro Y f hf
    ext1
    dsimp'
    rw [sieve.pullback_top, ← J₂.pullback_close, S.pullback_eq_top_of_mem hf, J₂.close_eq_top_iff_mem]
    apply J₂.top_mem
    

/-- If being a sheaf for `J₁` is equivalent to being a sheaf for `J₂`, then `J₁ = J₂`. -/
theorem topology_eq_iff_same_sheaves {J₁ J₂ : GrothendieckTopology C} :
    J₁ = J₂ ↔ ∀ P : Cᵒᵖ ⥤ Type max v u, Presieve.IsSheaf J₁ P ↔ Presieve.IsSheaf J₂ P := by
  constructor
  · rintro rfl
    intro P
    rfl
    
  · intro h
    apply le_antisymmₓ
    · apply le_topology_of_closed_sieves_is_sheaf
      rw [h]
      apply classifier_is_sheaf
      
    · apply le_topology_of_closed_sieves_is_sheaf
      rw [← h]
      apply classifier_is_sheaf
      
    

/-- A closure (increasing, inflationary and idempotent) operation on sieves that commutes with pullback
induces a Grothendieck topology.
In fact, such operations are in bijection with Grothendieck topologies.
-/
@[simps]
def topologyOfClosureOperator (c : ∀ X : C, ClosureOperator (Sieve X))
    (hc : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) (S : Sieve X), c _ (S.pullback f) = (c _ S).pullback f) : GrothendieckTopology C where
  Sieves := fun X => { S | c X S = ⊤ }
  top_mem' := fun X => top_unique ((c X).le_closure _)
  pullback_stable' := fun X Y S f hS => by
    rw [Set.mem_set_of_eq] at hS
    rw [Set.mem_set_of_eq, hc, hS, sieve.pullback_top]
  transitive' := fun X S hS R hR => by
    rw [Set.mem_set_of_eq] at hS
    rw [Set.mem_set_of_eq, ← (c X).idempotent, eq_top_iff, ← hS]
    apply (c X).Monotone fun Y f hf => _
    rw [sieve.pullback_eq_top_iff_mem, ← hc]
    apply hR hf

/-- The topology given by the closure operator `J.close` on a Grothendieck topology is the same as `J`.
-/
theorem topology_of_closure_operator_self :
    (topologyOfClosureOperator J₁.ClosureOperator fun X Y => J₁.pullback_close) = J₁ := by
  ext X S
  apply grothendieck_topology.close_eq_top_iff_mem

theorem topology_of_closure_operator_close (c : ∀ X : C, ClosureOperator (Sieve X))
    (pb : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) (S : Sieve X), c Y (S.pullback f) = (c X S).pullback f) (X : C) (S : Sieve X) :
    (topologyOfClosureOperator c pb).close S = c X S := by
  ext
  change c _ (sieve.pullback f S) = ⊤ ↔ c _ S f
  rw [pb, sieve.pullback_eq_top_iff_mem]

end CategoryTheory


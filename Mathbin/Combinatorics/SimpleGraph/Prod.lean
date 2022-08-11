/-
Copyright (c) 2022 George Peter Banyard, Yaël Dillies, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Peter Banyard, Yaël Dillies, Kyle Miller
-/
import Mathbin.Combinatorics.SimpleGraph.Connectivity

/-!
# Graph products

This file defines the box product of graphs and other product constructions. The box product of `G`
and `H` is the graph on the product of the vertices such that `x` and `y` are related iff they agree
on one component and the other one is related via either `G` or `H`. For example, the box product of
two edges is a square.

## Main declarations

* `simple_graph.box_prod`: The box product.

## Notation

* `G □ H`: The box product of `G` and `H`.

## TODO

Define all other graph products!
-/


variable {α β γ : Type _}

namespace SimpleGraph

variable {G : SimpleGraph α} {H : SimpleGraph β} {I : SimpleGraph γ} {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

/-- Box product of simple graphs. It relates `(a₁, b)` and `(a₂, b)` if `G` relates `a₁` and `a₂`,
and `(a, b₁)` and `(a, b₂)` if `H` relates `b₁` and `b₂`. -/
def boxProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj := fun x y => G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1
  symm := fun x y => by
    simp [← and_comm, ← or_comm, ← eq_comm, ← adj_comm]
  loopless := fun x => by
    simp

-- mathport name: «expr □ »
infixl:70 " □ " => boxProd

@[simp]
theorem box_prod_adj : (G □ H).Adj x y ↔ G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1 :=
  Iff.rfl

@[simp]
theorem box_prod_adj_left : (G □ H).Adj (a₁, b) (a₂, b) ↔ G.Adj a₁ a₂ := by
  rw [box_prod_adj, and_iff_left rfl, or_iff_left fun h : H.adj b b ∧ _ => h.1.Ne rfl]

@[simp]
theorem box_prod_adj_right : (G □ H).Adj (a, b₁) (a, b₂) ↔ H.Adj b₁ b₂ := by
  rw [box_prod_adj, and_iff_left rfl, or_iff_right fun h : G.adj a a ∧ _ => h.1.Ne rfl]

variable (G H I)

/-- The box product is commutative up to isomorphism. `equiv.prod_comm` as a graph isomorphism. -/
@[simps]
def boxProdComm : G □ H ≃g H □ G :=
  ⟨Equivₓ.prodComm _ _, fun x y => or_comm _ _⟩

/-- The box product is associative up to isomorphism. `equiv.prod_assoc` as a graph isomorphism. -/
@[simps]
def boxProdAssoc : G □ H □ I ≃g G □ (H □ I) :=
  ⟨Equivₓ.prodAssoc _ _ _, fun x y => by
    simp only [← box_prod_adj, ← Equivₓ.prod_assoc_apply, ← or_and_distrib_right, ← or_assoc, ← Prod.ext_iff, ←
      and_assoc, ← @And.comm (x.1.1 = _)]⟩

/-- The embedding of `G` into `G □ H` given by `b`. -/
@[simps]
def boxProdLeft (b : β) : G ↪g G □ H where
  toFun := fun a => (a, b)
  inj' := fun a₁ a₂ => congr_arg Prod.fst
  map_rel_iff' := fun a₁ a₂ => box_prod_adj_left

/-- The embedding of `H` into `G □ H` given by `a`. -/
@[simps]
def boxProdRight (a : α) : H ↪g G □ H where
  toFun := Prod.mk a
  inj' := fun b₁ b₂ => congr_arg Prod.snd
  map_rel_iff' := fun b₁ b₂ => box_prod_adj_right

namespace Walk

variable {G}

/-- Turn a walk on `G` into a walk on `G □ H`. -/
protected def boxProdLeft (b : β) : G.Walk a₁ a₂ → (G □ H).Walk (a₁, b) (a₂, b) :=
  Walk.map (G.boxProdLeft H b).toHom

variable (G) {H}

/-- Turn a walk on `H` into a walk on `G □ H`. -/
protected def boxProdRight (a : α) : H.Walk b₁ b₂ → (G □ H).Walk (a, b₁) (a, b₂) :=
  Walk.map (G.boxProdRight H a).toHom

variable {G} [DecidableEq α] [DecidableEq β] [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- Project a walk on `G □ H` to a walk on `G` by discarding the moves in the direction of `H`. -/
def ofBoxProdLeft : ∀ {x y : α × β}, (G □ H).Walk x y → G.Walk x.1 y.1
  | _, _, nil => nil
  | x, z, cons h w =>
    Or.byCases h (fun hG => w.ofBoxProdLeft.cons hG.1) fun hH =>
      show G.Walk x.1 z.1 by
        rw [hH.2] <;> exact w.of_box_prod_left

/-- Project a walk on `G □ H` to a walk on `H` by discarding the moves in the direction of `G`. -/
def ofBoxProdRight : ∀ {x y : α × β}, (G □ H).Walk x y → H.Walk x.2 y.2
  | _, _, nil => nil
  | x, z, cons h w =>
    (Or.symm h).byCases (fun hH => w.ofBoxProdRight.cons hH.1) fun hG =>
      show H.Walk x.2 z.2 by
        rw [hG.2] <;> exact w.of_box_prod_right

@[simp]
theorem of_box_prod_left_box_prod_left : ∀ {a₁ a₂ : α} (w : G.Walk a₁ a₂), (w.boxProdLeft H b).ofBoxProdLeft = w
  | _, _, nil => rfl
  | _, _, cons' x y z h w => by
    rw [walk.box_prod_left, map_cons, of_box_prod_left, Or.byCases, dif_pos, ← walk.box_prod_left,
      of_box_prod_left_box_prod_left]
    exacts[rfl, ⟨h, rfl⟩]

@[simp]
theorem of_box_prod_left_box_prod_right : ∀ {b₁ b₂ : α} (w : G.Walk b₁ b₂), (w.boxProdRight G a).ofBoxProdRight = w
  | _, _, nil => rfl
  | _, _, cons' x y z h w => by
    rw [walk.box_prod_right, map_cons, of_box_prod_right, Or.byCases, dif_pos, ← walk.box_prod_right,
      of_box_prod_left_box_prod_right]
    exacts[rfl, ⟨h, rfl⟩]

end Walk

variable {G H}

protected theorem Preconnected.box_prod (hG : G.Preconnected) (hH : H.Preconnected) : (G □ H).Preconnected := by
  rintro x y
  obtain ⟨w₁⟩ := hG x.1 y.1
  obtain ⟨w₂⟩ := hH x.2 y.2
  rw [← @Prod.mk.eta _ _ x, ← @Prod.mk.eta _ _ y]
  exact ⟨(w₁.box_prod_left _ _).append (w₂.box_prod_right _ _)⟩

protected theorem Preconnected.of_box_prod_left [Nonempty β] (h : (G □ H).Preconnected) : G.Preconnected := by
  classical
  rintro a₁ a₂
  obtain ⟨w⟩ := h (a₁, Classical.arbitrary _) (a₂, Classical.arbitrary _)
  exact ⟨w.of_box_prod_left⟩

protected theorem Preconnected.of_box_prod_right [Nonempty α] (h : (G □ H).Preconnected) : H.Preconnected := by
  classical
  rintro b₁ b₂
  obtain ⟨w⟩ := h (Classical.arbitrary _, b₁) (Classical.arbitrary _, b₂)
  exact ⟨w.of_box_prod_right⟩

protected theorem Connected.box_prod (hG : G.Connected) (hH : H.Connected) : (G □ H).Connected := by
  have := hG.nonempty
  have := hH.nonempty
  exact ⟨hG.preconnected.box_prod hH.preconnected⟩

protected theorem Connected.of_box_prod_left (h : (G □ H).Connected) : G.Connected := by
  have := (nonempty_prod.1 h.nonempty).1
  have := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.of_box_prod_left⟩

protected theorem Connected.of_box_prod_right (h : (G □ H).Connected) : H.Connected := by
  have := (nonempty_prod.1 h.nonempty).1
  have := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.of_box_prod_right⟩

@[simp]
theorem box_prod_connected : (G □ H).Connected ↔ G.Connected ∧ H.Connected :=
  ⟨fun h => ⟨h.ofBoxProdLeft, h.ofBoxProdRight⟩, fun h => h.1.boxProd h.2⟩

end SimpleGraph


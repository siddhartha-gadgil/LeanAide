/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Order.ConditionallyCompleteLattice

/-!
# Tooling to make copies of lattice structures

Sometimes it is useful to make a copy of a lattice structure
where one replaces the data parts with provably equal definitions
that have better definitional properties.
-/


open Order

universe u

variable {α : Type u}

/-- A function to create a provable equal copy of a bounded order
with possibly different definitional equalities. -/
def BoundedOrder.copy {h : LE α} {h' : LE α} (c : @BoundedOrder α h') (top : α) (eq_top : top = @BoundedOrder.top α _ c)
    (bot : α) (eq_bot : bot = @BoundedOrder.bot α _ c) (le_eq : ∀ x y : α, (@LE.le α h) x y ↔ x ≤ y) :
    @BoundedOrder α h := by
  refine' { top, bot.. }
  all_goals
    abstract 
      subst_vars
      cases c
      simp_rw [le_eq]
      assumption

/-- A function to create a provable equal copy of a lattice
with possibly different definitional equalities. -/
def Lattice.copy (c : Lattice α) (le : α → α → Prop) (eq_le : le = @Lattice.Le α c) (sup : α → α → α)
    (eq_sup : sup = @Lattice.sup α c) (inf : α → α → α) (eq_inf : inf = @Lattice.inf α c) : Lattice α := by
  refine' { le, sup, inf.. }
  all_goals
    abstract 
      subst_vars
      cases c
      assumption

/-- A function to create a provable equal copy of a distributive lattice
with possibly different definitional equalities. -/
def DistribLattice.copy (c : DistribLattice α) (le : α → α → Prop) (eq_le : le = @DistribLattice.Le α c)
    (sup : α → α → α) (eq_sup : sup = @DistribLattice.sup α c) (inf : α → α → α)
    (eq_inf : inf = @DistribLattice.inf α c) : DistribLattice α := by
  refine' { le, sup, inf.. }
  all_goals
    abstract 
      subst_vars
      cases c
      assumption

/-- A function to create a provable equal copy of a complete lattice
with possibly different definitional equalities. -/
def CompleteLattice.copy (c : CompleteLattice α) (le : α → α → Prop) (eq_le : le = @CompleteLattice.Le α c) (top : α)
    (eq_top : top = @CompleteLattice.top α c) (bot : α) (eq_bot : bot = @CompleteLattice.bot α c) (sup : α → α → α)
    (eq_sup : sup = @CompleteLattice.sup α c) (inf : α → α → α) (eq_inf : inf = @CompleteLattice.inf α c)
    (Sup : Set α → α) (eq_Sup : Sup = @CompleteLattice.supₓ α c) (Inf : Set α → α)
    (eq_Inf : Inf = @CompleteLattice.infₓ α c) : CompleteLattice α := by
  refine'
    { Lattice.copy (@CompleteLattice.toLattice α c) le eq_le sup eq_sup inf eq_inf with le, top, bot, sup, inf, sup,
      inf.. }
  all_goals
    abstract 
      subst_vars
      cases c
      assumption

/-- A function to create a provable equal copy of a frame with possibly different definitional
equalities. -/
def Frame.copy (c : Frame α) (le : α → α → Prop) (eq_le : le = @Frame.Le α c) (top : α) (eq_top : top = @Frame.top α c)
    (bot : α) (eq_bot : bot = @Frame.bot α c) (sup : α → α → α) (eq_sup : sup = @Frame.sup α c) (inf : α → α → α)
    (eq_inf : inf = @Frame.inf α c) (Sup : Set α → α) (eq_Sup : Sup = @Frame.supₓ α c) (Inf : Set α → α)
    (eq_Inf : Inf = @Frame.infₓ α c) : Frame α := by
  refine'
    { CompleteLattice.copy (@frame.to_complete_lattice α c) le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf Sup
        eq_Sup Inf eq_Inf with
      le, top, bot, sup, inf, sup, inf.. }
  all_goals
    abstract 
      subst_vars
      cases c
      assumption

/-- A function to create a provable equal copy of a coframe with possibly different definitional
equalities. -/
def Coframe.copy (c : Coframe α) (le : α → α → Prop) (eq_le : le = @Coframe.Le α c) (top : α)
    (eq_top : top = @Coframe.top α c) (bot : α) (eq_bot : bot = @Coframe.bot α c) (sup : α → α → α)
    (eq_sup : sup = @Coframe.sup α c) (inf : α → α → α) (eq_inf : inf = @Coframe.inf α c) (Sup : Set α → α)
    (eq_Sup : Sup = @Coframe.supₓ α c) (Inf : Set α → α) (eq_Inf : Inf = @Coframe.infₓ α c) : Coframe α := by
  refine'
    { CompleteLattice.copy (@coframe.to_complete_lattice α c) le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf Sup
        eq_Sup Inf eq_Inf with
      le, top, bot, sup, inf, sup, inf.. }
  all_goals
    abstract 
      subst_vars
      cases c
      assumption

/-- A function to create a provable equal copy of a complete distributive lattice
with possibly different definitional equalities. -/
def CompleteDistribLattice.copy (c : CompleteDistribLattice α) (le : α → α → Prop)
    (eq_le : le = @CompleteDistribLattice.Le α c) (top : α) (eq_top : top = @CompleteDistribLattice.top α c) (bot : α)
    (eq_bot : bot = @CompleteDistribLattice.bot α c) (sup : α → α → α) (eq_sup : sup = @CompleteDistribLattice.sup α c)
    (inf : α → α → α) (eq_inf : inf = @CompleteDistribLattice.inf α c) (Sup : Set α → α)
    (eq_Sup : Sup = @CompleteDistribLattice.supₓ α c) (Inf : Set α → α)
    (eq_Inf : Inf = @CompleteDistribLattice.infₓ α c) : CompleteDistribLattice α :=
  { Frame.copy (@CompleteDistribLattice.toFrame α c) le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf Sup eq_Sup Inf
      eq_Inf,
    Coframe.copy (@CompleteDistribLattice.toCoframe α c) le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf Sup eq_Sup
      Inf eq_Inf with }

/-- A function to create a provable equal copy of a conditionally complete lattice
with possibly different definitional equalities. -/
def ConditionallyCompleteLattice.copy (c : ConditionallyCompleteLattice α) (le : α → α → Prop)
    (eq_le : le = @ConditionallyCompleteLattice.Le α c) (sup : α → α → α)
    (eq_sup : sup = @ConditionallyCompleteLattice.sup α c) (inf : α → α → α)
    (eq_inf : inf = @ConditionallyCompleteLattice.inf α c) (Sup : Set α → α)
    (eq_Sup : Sup = @ConditionallyCompleteLattice.supₓ α c) (Inf : Set α → α)
    (eq_Inf : Inf = @ConditionallyCompleteLattice.infₓ α c) : ConditionallyCompleteLattice α := by
  refine' { le, sup, inf, sup, inf.. }
  all_goals
    abstract 
      subst_vars
      cases c
      assumption


/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/
import Mathbin.Algebra.Order.Hom.Monoid
import Mathbin.SetTheory.Game.Ordinal

/-!
# Surreal numbers

The basic theory of surreal numbers, built on top of the theory of combinatorial (pre-)games.

A pregame is `numeric` if all the Left options are strictly smaller than all the Right options, and
all those options are themselves numeric. In terms of combinatorial games, the numeric games have
"frozen"; you can only make your position worse by playing, and Left is some definite "number" of
moves ahead (or behind) Right.

A surreal number is an equivalence class of numeric pregames.

In fact, the surreals form a complete ordered field, containing a copy of the reals (and much else
besides!) but we do not yet have a complete development.

## Order properties

Surreal numbers inherit the relations `≤` and `<` from games (`surreal.has_le` and
`surreal.has_lt`), and these relations satisfy the axioms of a partial order.

## Algebraic operations

We show that the surreals form a linear ordered commutative group.

One can also map all the ordinals into the surreals!

### Multiplication of surreal numbers

The proof that multiplication lifts to surreal numbers is surprisingly difficult and is currently
missing in the library. A sample proof can be found in Theorem 3.8 in the second reference below.
The difficulty lies in the length of the proof and the number of theorems that need to proven
simultaneously. This will make for a fun and challenging project.

The branch `surreal_mul` contains some progress on this proof.

### Todo

- Define the field structure on the surreals.

## References

* [Conway, *On numbers and games*][conway2001]
* [Schleicher, Stoll, *An introduction to Conway's games and numbers*][schleicher_stoll]
-/


universe u

-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Pgame.Equiv

-- mathport name: «expr ⧏ »
local infixl:50 " ⧏ " => Pgame.Lf

namespace Pgame

/-- A pre-game is numeric if everything in the L set is less than everything in the R set,
and all the elements of L and R are also numeric. -/
def Numeric : Pgame → Prop
  | ⟨l, r, L, R⟩ => (∀ i j, L i < R j) ∧ (∀ i, numeric (L i)) ∧ ∀ j, numeric (R j)

theorem numeric_def {x : Pgame} :
    Numeric x ↔ (∀ i j, x.moveLeft i < x.moveRight j) ∧ (∀ i, Numeric (x.moveLeft i)) ∧ ∀ j, Numeric (x.moveRight j) :=
  by
  cases x
  rfl

namespace Numeric

theorem mk {x : Pgame} (h₁ : ∀ i j, x.moveLeft i < x.moveRight j) (h₂ : ∀ i, Numeric (x.moveLeft i))
    (h₃ : ∀ j, Numeric (x.moveRight j)) : Numeric x :=
  numeric_def.2 ⟨h₁, h₂, h₃⟩

theorem left_lt_right {x : Pgame} (o : Numeric x) (i : x.LeftMoves) (j : x.RightMoves) : x.moveLeft i < x.moveRight j :=
  by
  cases x
  exact o.1 i j

theorem move_left {x : Pgame} (o : Numeric x) (i : x.LeftMoves) : Numeric (x.moveLeft i) := by
  cases x
  exact o.2.1 i

theorem move_right {x : Pgame} (o : Numeric x) (j : x.RightMoves) : Numeric (x.moveRight j) := by
  cases x
  exact o.2.2 j

end Numeric

@[elab_as_eliminator]
theorem numeric_rec {C : Pgame → Prop}
    (H :
      ∀ (l r) (L : l → Pgame) (R : r → Pgame),
        (∀ i j, L i < R j) →
          (∀ i, Numeric (L i)) → (∀ i, Numeric (R i)) → (∀ i, C (L i)) → (∀ i, C (R i)) → C ⟨l, r, L, R⟩) :
    ∀ x, Numeric x → C x
  | ⟨l, r, L, R⟩, ⟨h, hl, hr⟩ => H _ _ _ _ h hl hr (fun i => numeric_rec _ (hl i)) fun i => numeric_rec _ (hr i)

theorem lf_asymm {x y : Pgame} (ox : Numeric x) (oy : Numeric y) : x ⧏ y → ¬y ⧏ x := by
  refine' numeric_rec (fun xl xr xL xR hx oxl oxr IHxl IHxr => _) x ox y oy
  refine' numeric_rec fun yl yr yL yR hy oyl oyr IHyl IHyr => _
  rw [mk_lf_mk, mk_lf_mk]
  rintro (⟨i, h₁⟩ | ⟨j, h₁⟩) (⟨i, h₂⟩ | ⟨j, h₂⟩)
  · exact IHxl _ _ (oyl _) (h₁.move_left_lf _) (h₂.move_left_lf _)
    
  · exact (le_transₓ h₂ h₁).not_gf (lf_of_lt (hy _ _))
    
  · exact (le_transₓ h₁ h₂).not_gf (lf_of_lt (hx _ _))
    
  · exact IHxr _ _ (oyr _) (h₁.lf_move_right _) (h₂.lf_move_right _)
    

theorem le_of_lf {x y : Pgame} (h : x ⧏ y) (ox : Numeric x) (oy : Numeric y) : x ≤ y :=
  not_lf.1 (lf_asymm ox oy h)

alias le_of_lf ← lf.le

theorem lt_of_lf {x y : Pgame} (h : x ⧏ y) (ox : Numeric x) (oy : Numeric y) : x < y :=
  (lt_or_fuzzy_of_lf h).resolve_right (not_fuzzy_of_le (h.le ox oy))

alias lt_of_lf ← lf.lt

theorem lf_iff_lt {x y : Pgame} (ox : Numeric x) (oy : Numeric y) : x ⧏ y ↔ x < y :=
  ⟨fun h => h.lt ox oy, lf_of_lt⟩

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- Definition of `x ≤ y` on numeric pre-games, in terms of `<` -/
theorem le_iff_forall_lt {x y : Pgame} (ox : x.Numeric) (oy : y.Numeric) :
    x ≤ y ↔ (∀ i, x.moveLeft i < y) ∧ ∀ j, x < y.moveRight j := by
  refine' le_iff_forall_lf.trans (and_congr _ _) <;>
    refine' forall_congrₓ fun i => lf_iff_lt _ _ <;> apply_rules [numeric.move_left, numeric.move_right]

/-- Definition of `x < y` on numeric pre-games, in terms of `≤` -/
theorem lt_iff_exists_le {x y : Pgame} (ox : x.Numeric) (oy : y.Numeric) :
    x < y ↔ (∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y := by
  rw [← lf_iff_lt ox oy, lf_iff_exists_le]

theorem lt_of_exists_le {x y : Pgame} (ox : x.Numeric) (oy : y.Numeric) :
    ((∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y) → x < y :=
  (lt_iff_exists_le ox oy).2

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- The definition of `x < y` on numeric pre-games, in terms of `<` two moves later. -/
theorem lt_def {x y : Pgame} (ox : x.Numeric) (oy : y.Numeric) :
    x < y ↔
      (∃ i, (∀ i', x.moveLeft i' < y.moveLeft i) ∧ ∀ j, x < (y.moveLeft i).moveRight j) ∨
        ∃ j, (∀ i, (x.moveRight j).moveLeft i < y) ∧ ∀ j', x.moveRight j < y.moveRight j' :=
  by
  rw [← lf_iff_lt ox oy, lf_def]
  refine' or_congr _ _ <;>
    refine' exists_congr fun x_1 => _ <;>
      refine' and_congr _ _ <;>
        refine' forall_congrₓ fun i => lf_iff_lt _ _ <;> apply_rules [numeric.move_left, numeric.move_right]

theorem not_fuzzy {x y : Pgame} (ox : Numeric x) (oy : Numeric y) : ¬Fuzzy x y := fun h =>
  not_lf.2 ((lf_of_fuzzy h).le ox oy) h.2

theorem lt_or_equiv_or_gt {x y : Pgame} (ox : Numeric x) (oy : Numeric y) : x < y ∨ (x ≈ y) ∨ y < x :=
  ((lf_or_equiv_or_gf x y).imp fun h => h.lt ox oy) <| Or.imp_rightₓ fun h => h.lt oy ox

theorem numeric_of_is_empty (x : Pgame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : Numeric x :=
  Numeric.mk isEmptyElim isEmptyElim isEmptyElim

theorem numeric_of_is_empty_left_moves (x : Pgame) [IsEmpty x.LeftMoves] : (∀ j, Numeric (x.moveRight j)) → Numeric x :=
  Numeric.mk isEmptyElim isEmptyElim

theorem numeric_of_is_empty_right_moves (x : Pgame) [IsEmpty x.RightMoves] (H : ∀ i, Numeric (x.moveLeft i)) :
    Numeric x :=
  Numeric.mk (fun _ => isEmptyElim) H isEmptyElim

theorem numeric_zero : Numeric 0 :=
  numeric_of_is_empty 0

theorem numeric_one : Numeric 1 :=
  (numeric_of_is_empty_right_moves 1) fun _ => numeric_zero

theorem Numeric.neg : ∀ {x : Pgame} (o : Numeric x), Numeric (-x)
  | ⟨l, r, L, R⟩, o => ⟨fun j i => neg_lt_neg_iff.2 (o.1 i j), fun j => (o.2.2 j).neg, fun i => (o.2.1 i).neg⟩

namespace Numeric

theorem move_left_lt {x : Pgame} (o : Numeric x) (i) : x.moveLeft i < x :=
  (Pgame.move_left_lf i).lt (o.moveLeft i) o

theorem move_left_le {x : Pgame} (o : Numeric x) (i) : x.moveLeft i ≤ x :=
  (o.move_left_lt i).le

theorem lt_move_right {x : Pgame} (o : Numeric x) (j) : x < x.moveRight j :=
  (Pgame.lf_move_right j).lt o (o.moveRight j)

theorem le_move_right {x : Pgame} (o : Numeric x) (j) : x ≤ x.moveRight j :=
  (o.lt_move_right j).le

theorem add : ∀ {x y : Pgame} (ox : Numeric x) (oy : Numeric y), Numeric (x + y)
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ox, oy =>
    ⟨by
      rintro (ix | iy) (jx | jy)
      · exact add_lt_add_right (ox.1 ix jx) _
        
      · exact
          (add_lf_add_of_lf_of_le (Pgame.lf_mk _ _ ix) (oy.le_move_right jy)).lt ((ox.move_left ix).add oy)
            (ox.add (oy.move_right jy))
        
      · exact
          (add_lf_add_of_lf_of_le (Pgame.mk_lf _ _ jx) (oy.move_left_le iy)).lt (ox.add (oy.move_left iy))
            ((ox.move_right jx).add oy)
        
      · exact add_lt_add_left (oy.1 iy jy) ⟨xl, xr, xL, xR⟩
        ,
      by
      constructor
      · rintro (ix | iy)
        · exact (ox.move_left ix).add oy
          
        · exact ox.add (oy.move_left iy)
          
        
      · rintro (jx | jy)
        · apply (ox.move_right jx).add oy
          
        · apply ox.add (oy.move_right jy)
          
        ⟩

theorem sub {x y : Pgame} (ox : Numeric x) (oy : Numeric y) : Numeric (x - y) :=
  ox.add oy.neg

end Numeric

/-- Pre-games defined by natural numbers are numeric. -/
theorem numeric_nat : ∀ n : ℕ, Numeric n
  | 0 => numeric_zero
  | n + 1 => (numeric_nat n).add numeric_one

/-- Ordinal games are numeric. -/
theorem numeric_to_pgame (o : Ordinal) : o.toPgame.Numeric := by
  induction' o using Ordinal.induction with o IH
  apply numeric_of_is_empty_right_moves
  simpa using fun i => IH _ (Ordinal.to_left_moves_to_pgame_symm_lt i)

end Pgame

/-- The equivalence on numeric pre-games. -/
def Surreal.Equiv (x y : { x // Pgame.Numeric x }) : Prop :=
  x.1.Equiv y.1

open Pgame

instance Surreal.setoid : Setoidₓ { x // Pgame.Numeric x } :=
  ⟨fun x y => x.1 ≈ y.1, fun x => equiv_rfl, fun x y => Pgame.Equiv.symm, fun x y z => Pgame.Equiv.trans⟩

/-- The type of surreal numbers. These are the numeric pre-games quotiented
by the equivalence relation `x ≈ y ↔ x ≤ y ∧ y ≤ x`. In the quotient,
the order becomes a total order. -/
def Surreal :=
  Quotientₓ Surreal.setoid

namespace Surreal

/-- Construct a surreal number from a numeric pre-game. -/
def mk (x : Pgame) (h : x.Numeric) : Surreal :=
  ⟦⟨x, h⟩⟧

instance : Zero Surreal :=
  ⟨mk 0 numeric_zero⟩

instance : One Surreal :=
  ⟨mk 1 numeric_one⟩

instance : Inhabited Surreal :=
  ⟨0⟩

/-- Lift an equivalence-respecting function on pre-games to surreals. -/
def lift {α} (f : ∀ x, Numeric x → α) (H : ∀ {x y} (hx : Numeric x) (hy : Numeric y), x.Equiv y → f x hx = f y hy) :
    Surreal → α :=
  Quotientₓ.lift (fun x : { x // Numeric x } => f x.1 x.2) fun x y => H x.2 y.2

/-- Lift a binary equivalence-respecting function on pre-games to surreals. -/
def lift₂ {α} (f : ∀ x y, Numeric x → Numeric y → α)
    (H :
      ∀ {x₁ y₁ x₂ y₂} (ox₁ : Numeric x₁) (oy₁ : Numeric y₁) (ox₂ : Numeric x₂) (oy₂ : Numeric y₂),
        x₁.Equiv x₂ → y₁.Equiv y₂ → f x₁ y₁ ox₁ oy₁ = f x₂ y₂ ox₂ oy₂) :
    Surreal → Surreal → α :=
  lift (fun x ox => lift (fun y oy => f x y ox oy) fun y₁ y₂ oy₁ oy₂ => H _ _ _ _ equiv_rfl) fun x₁ x₂ ox₁ ox₂ h =>
    funext <| Quotientₓ.ind fun ⟨y, oy⟩ => H _ _ _ _ h equiv_rfl

instance : LE Surreal :=
  ⟨lift₂ (fun x y _ _ => x ≤ y) fun x₁ y₁ x₂ y₂ _ _ _ _ hx hy => propext (le_congr hx hy)⟩

instance : LT Surreal :=
  ⟨lift₂ (fun x y _ _ => x < y) fun x₁ y₁ x₂ y₂ _ _ _ _ hx hy => propext (lt_congr hx hy)⟩

/-- Addition on surreals is inherited from pre-game addition:
the sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : Add Surreal :=
  ⟨Surreal.lift₂ (fun (x y : Pgame) ox oy => ⟦⟨x + y, ox.add oy⟩⟧) fun x₁ y₁ x₂ y₂ _ _ _ _ hx hy =>
      Quotientₓ.sound (Pgame.add_congr hx hy)⟩

/-- Negation for surreal numbers is inherited from pre-game negation:
the negation of `{L | R}` is `{-R | -L}`. -/
instance : Neg Surreal :=
  ⟨Surreal.lift (fun x ox => ⟦⟨-x, ox.neg⟩⟧) fun _ _ _ _ a => Quotientₓ.sound (Pgame.neg_equiv_neg_iff.2 a)⟩

instance : OrderedAddCommGroup Surreal where
  add := (· + ·)
  add_assoc := by
    rintro ⟨_⟩ ⟨_⟩ ⟨_⟩
    exact Quotientₓ.sound add_assoc_equiv
  zero := 0
  zero_add := by
    rintro ⟨_⟩
    exact Quotientₓ.sound (Pgame.zero_add_equiv a)
  add_zero := by
    rintro ⟨_⟩
    exact Quotientₓ.sound (Pgame.add_zero_equiv a)
  neg := Neg.neg
  add_left_neg := by
    rintro ⟨_⟩
    exact Quotientₓ.sound (Pgame.add_left_neg_equiv a)
  add_comm := by
    rintro ⟨_⟩ ⟨_⟩
    exact Quotientₓ.sound Pgame.add_comm_equiv
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by
    rintro ⟨_⟩
    apply @le_rfl Pgame
  le_trans := by
    rintro ⟨_⟩ ⟨_⟩ ⟨_⟩
    apply @le_transₓ Pgame
  lt_iff_le_not_le := by
    rintro ⟨_, ox⟩ ⟨_, oy⟩
    apply @lt_iff_le_not_leₓ Pgame
  le_antisymm := by
    rintro ⟨_⟩ ⟨_⟩ h₁ h₂
    exact Quotientₓ.sound ⟨h₁, h₂⟩
  add_le_add_left := by
    rintro ⟨_⟩ ⟨_⟩ hx ⟨_⟩
    exact @add_le_add_left Pgame _ _ _ _ _ hx _

noncomputable instance : LinearOrderedAddCommGroup Surreal :=
  { Surreal.orderedAddCommGroup with
    le_total := by
      rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩ <;> classical <;> exact or_iff_not_imp_left.2 fun h => (Pgame.not_le.1 h).le oy ox,
    decidableLe := Classical.decRel _ }

instance : AddMonoidWithOneₓ Surreal :=
  AddMonoidWithOneₓ.unary

/-- Casts a `surreal` number into a `game`. -/
def toGame : Surreal →+o Game where
  toFun := lift (fun x _ => ⟦x⟧) fun x y ox oy => Quot.sound
  map_zero' := rfl
  map_add' := by
    rintro ⟨_, _⟩ ⟨_, _⟩
    rfl
  monotone' := by
    rintro ⟨_, _⟩ ⟨_, _⟩
    exact id

theorem zero_to_game : toGame 0 = 0 :=
  rfl

@[simp]
theorem one_to_game : toGame 1 = 1 :=
  rfl

@[simp]
theorem nat_to_game : ∀ n : ℕ, toGame n = n :=
  map_nat_cast' _ one_to_game

end Surreal

open Surreal

namespace Ordinal

/-- Converts an ordinal into the corresponding surreal. -/
noncomputable def toSurreal : Ordinal ↪o Surreal where
  toFun := fun o => mk _ (numeric_to_pgame o)
  inj' := fun a b h => to_pgame_equiv_iff.1 (Quotientₓ.exact h)
  map_rel_iff' := @to_pgame_le_iff

end Ordinal


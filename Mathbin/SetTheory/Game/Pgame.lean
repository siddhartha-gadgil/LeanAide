/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison
-/
import Mathbin.Data.Fin.Basic
import Mathbin.Data.List.Basic
import Mathbin.Logic.Relation

/-!
# Combinatorial (pre-)games.

The basic theory of combinatorial games, following Conway's book `On Numbers and Games`. We
construct "pregames", define an ordering and arithmetic operations on them, then show that the
operations descend to "games", defined via the equivalence relation `p ≈ q ↔ p ≤ q ∧ q ≤ p`.

The surreal numbers will be built as a quotient of a subtype of pregames.

A pregame (`pgame` below) is axiomatised via an inductive type, whose sole constructor takes two
types (thought of as indexing the possible moves for the players Left and Right), and a pair of
functions out of these types to `pgame` (thought of as describing the resulting game after making a
move).

Combinatorial games themselves, as a quotient of pregames, are constructed in `game.lean`.

## Conway induction

By construction, the induction principle for pregames is exactly "Conway induction". That is, to
prove some predicate `pgame → Prop` holds for all pregames, it suffices to prove that for every
pregame `g`, if the predicate holds for every game resulting from making a move, then it also holds
for `g`.

While it is often convenient to work "by induction" on pregames, in some situations this becomes
awkward, so we also define accessor functions `pgame.left_moves`, `pgame.right_moves`,
`pgame.move_left` and `pgame.move_right`. There is a relation `pgame.subsequent p q`, saying that
`p` can be reached by playing some non-empty sequence of moves starting from `q`, an instance
`well_founded subsequent`, and a local tactic `pgame_wf_tac` which is helpful for discharging proof
obligations in inductive proofs relying on this relation.

## Order properties

Pregames have both a `≤` and a `<` relation, satisfying the usual properties of a `preorder`. The
relation `0 < x` means that `x` can always be won by Left, while `0 ≤ x` means that `x` can be won
by Left as the second player.

It turns out to be quite convenient to define various relations on top of these. We define the "less
or fuzzy" relation `x ⧏ y` as `¬ y ≤ x`, the equivalence relation `x ≈ y` as `x ≤ y ∧ y ≤ x`, and
the fuzzy relation `x ∥ y` as `x ⧏ y ∧ y ⧏ x`. If `0 ⧏ x`, then `x` can be won by Left as the
first player. If `x ≈ 0`, then `x` can be won by the second player. If `x ∥ 0`, then `x` can be won
by the first player.

Statements like `zero_le_lf`, `zero_lf_le`, etc. unfold these definitions. The theorems `le_def` and
`lf_def` give a recursive characterisation of each relation in terms of themselves two moves later.
The theorems `zero_le`, `zero_lf`, etc. also take into account that `0` has no moves.

Later, games will be defined as the quotient by the `≈` relation; that is to say, the
`antisymmetrization` of `pgame`.

## Algebraic structures

We next turn to defining the operations necessary to make games into a commutative additive group.
Addition is defined for $x = \{xL | xR\}$ and $y = \{yL | yR\}$ by $x + y = \{xL + y, x + yL | xR +
y, x + yR\}$. Negation is defined by $\{xL | xR\} = \{-xR | -xL\}$.

The order structures interact in the expected way with addition, so we have
```
theorem le_iff_sub_nonneg {x y : pgame} : x ≤ y ↔ 0 ≤ y - x := sorry
theorem lt_iff_sub_pos {x y : pgame} : x < y ↔ 0 < y - x := sorry
```

We show that these operations respect the equivalence relation, and hence descend to games. At the
level of games, these operations satisfy all the laws of a commutative group. To prove the necessary
equivalence relations at the level of pregames, we introduce the notion of a `relabelling` of a
game, and show, for example, that there is a relabelling between `x + (y + z)` and `(x + y) + z`.

## Future work

* The theory of dominated and reversible positions, and unique normal form for short games.
* Analysis of basic domineering positions.
* Hex.
* Temperature.
* The development of surreal numbers, based on this development of combinatorial games, is still
  quite incomplete.

## References

The material here is all drawn from
* [Conway, *On numbers and games*][conway2001]

An interested reader may like to formalise some of the material from
* [Andreas Blass, *A game semantics for linear logic*][MR1167694]
* [André Joyal, *Remarques sur la théorie des jeux à deux personnes*][joyal1997]
-/


open Function Relation

universe u

/-! ### Pre-game moves -/


/-- The type of pre-games, before we have quotiented
  by equivalence (`pgame.setoid`). In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a pre-game is built
  inductively from two families of pre-games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC. -/
inductive Pgame : Type (u + 1)
  | mk : ∀ α β : Type u, (α → Pgame) → (β → Pgame) → Pgame

namespace Pgame

/-- The indexing type for allowable moves by Left. -/
def LeftMoves : Pgame → Type u
  | mk l _ _ _ => l

/-- The indexing type for allowable moves by Right. -/
def RightMoves : Pgame → Type u
  | mk _ r _ _ => r

/-- The new game after Left makes an allowed move. -/
def moveLeft : ∀ g : Pgame, LeftMoves g → Pgame
  | mk l _ L _ => L

/-- The new game after Right makes an allowed move. -/
def moveRight : ∀ g : Pgame, RightMoves g → Pgame
  | mk _ r _ R => R

@[simp]
theorem left_moves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : Pgame).LeftMoves = xl :=
  rfl

@[simp]
theorem move_left_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : Pgame).moveLeft = xL :=
  rfl

@[simp]
theorem right_moves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : Pgame).RightMoves = xr :=
  rfl

@[simp]
theorem move_right_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : Pgame).moveRight = xR :=
  rfl

/-- Construct a pre-game from list of pre-games describing the available moves for Left and Right.
-/
-- TODO define this at the level of games, as well, and perhaps also for finsets of games.
def ofLists (L R : List Pgame.{u}) : Pgame.{u} :=
  mk (ULift (Finₓ L.length)) (ULift (Finₓ R.length)) (fun i => L.nthLe i.down i.down.is_lt) fun j =>
    R.nthLe j.down j.down.Prop

theorem left_moves_of_lists (L R : List Pgame) : (ofLists L R).LeftMoves = ULift (Finₓ L.length) :=
  rfl

theorem right_moves_of_lists (L R : List Pgame) : (ofLists L R).RightMoves = ULift (Finₓ R.length) :=
  rfl

/-- Converts a number into a left move for `of_lists`. -/
def toOfListsLeftMoves {L R : List Pgame} : Finₓ L.length ≃ (ofLists L R).LeftMoves :=
  ((Equivₓ.cast (left_moves_of_lists L R).symm).trans Equivₓ.ulift).symm

/-- Converts a number into a right move for `of_lists`. -/
def toOfListsRightMoves {L R : List Pgame} : Finₓ R.length ≃ (ofLists L R).RightMoves :=
  ((Equivₓ.cast (right_moves_of_lists L R).symm).trans Equivₓ.ulift).symm

theorem of_lists_move_left {L R : List Pgame} (i : Finₓ L.length) :
    (ofLists L R).moveLeft (toOfListsLeftMoves i) = L.nthLe i i.is_lt :=
  rfl

@[simp]
theorem of_lists_move_left' {L R : List Pgame} (i : (ofLists L R).LeftMoves) :
    (ofLists L R).moveLeft i = L.nthLe (toOfListsLeftMoves.symm i) (toOfListsLeftMoves.symm i).is_lt :=
  rfl

theorem of_lists_move_right {L R : List Pgame} (i : Finₓ R.length) :
    (ofLists L R).moveRight (toOfListsRightMoves i) = R.nthLe i i.is_lt :=
  rfl

@[simp]
theorem of_lists_move_right' {L R : List Pgame} (i : (ofLists L R).RightMoves) :
    (ofLists L R).moveRight i = R.nthLe (toOfListsRightMoves.symm i) (toOfListsRightMoves.symm i).is_lt :=
  rfl

/-- A variant of `pgame.rec_on` expressed in terms of `pgame.move_left` and `pgame.move_right`.

Both this and `pgame.rec_on` describe Conway induction on games. -/
@[elab_as_eliminator]
def moveRecOn {C : Pgame → Sort _} (x : Pgame)
    (IH : ∀ y : Pgame, (∀ i, C (y.moveLeft i)) → (∀ j, C (y.moveRight j)) → C y) : C x :=
  x.recOn fun yl yr yL yR => IH (mk yl yr yL yR)

/-- `is_option x y` means that `x` is either a left or right option for `y`. -/
@[mk_iff]
inductive IsOption : Pgame → Pgame → Prop
  | move_left {x : Pgame} (i : x.LeftMoves) : is_option (x.moveLeft i) x
  | move_right {x : Pgame} (i : x.RightMoves) : is_option (x.moveRight i) x

theorem IsOption.mk_left {xl xr : Type u} (xL : xl → Pgame) (xR : xr → Pgame) (i : xl) :
    (xL i).IsOption (mk xl xr xL xR) :=
  @IsOption.move_left (mk _ _ _ _) i

theorem IsOption.mk_right {xl xr : Type u} (xL : xl → Pgame) (xR : xr → Pgame) (i : xr) :
    (xR i).IsOption (mk xl xr xL xR) :=
  @IsOption.move_right (mk _ _ _ _) i

theorem wf_is_option : WellFounded IsOption :=
  ⟨fun x =>
    (moveRecOn x) fun x IHl IHr =>
      (Acc.intro x) fun y h => by
        induction' h with _ i _ j
        · exact IHl i
          
        · exact IHr j
          ⟩

/-- `subsequent x y` says that `x` can be obtained by playing some nonempty sequence of moves from
`y`. It is the transitive closure of `is_option`. -/
def Subsequent : Pgame → Pgame → Prop :=
  TransGen IsOption

instance : IsTrans _ Subsequent :=
  trans_gen.is_trans

@[trans]
theorem Subsequent.trans {x y z} : Subsequent x y → Subsequent y z → Subsequent x z :=
  trans_gen.trans

theorem wf_subsequent : WellFounded Subsequent :=
  wf_is_option.TransGen

instance : HasWellFounded Pgame :=
  ⟨_, wf_subsequent⟩

theorem Subsequent.move_left {x : Pgame} (i : x.LeftMoves) : Subsequent (x.moveLeft i) x :=
  TransGen.single (IsOption.move_left i)

theorem Subsequent.move_right {x : Pgame} (j : x.RightMoves) : Subsequent (x.moveRight j) x :=
  TransGen.single (IsOption.move_right j)

theorem Subsequent.mk_left {xl xr} (xL : xl → Pgame) (xR : xr → Pgame) (i : xl) : Subsequent (xL i) (mk xl xr xL xR) :=
  @Subsequent.move_left (mk _ _ _ _) i

theorem Subsequent.mk_right {xl xr} (xL : xl → Pgame) (xR : xr → Pgame) (j : xr) : Subsequent (xR j) (mk xl xr xL xR) :=
  @Subsequent.move_right (mk _ _ _ _) j

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- A local tactic for proving well-foundedness of recursive definitions involving pregames. -/
unsafe def pgame_wf_tac :=
  sorry

/-! ### Basic pre-games -/


/-- The pre-game `zero` is defined by `0 = { | }`. -/
instance : Zero Pgame :=
  ⟨⟨Pempty, Pempty, Pempty.elimₓ, Pempty.elimₓ⟩⟩

@[simp]
theorem zero_left_moves : LeftMoves 0 = Pempty :=
  rfl

@[simp]
theorem zero_right_moves : RightMoves 0 = Pempty :=
  rfl

instance is_empty_zero_left_moves : IsEmpty (LeftMoves 0) :=
  Pempty.is_empty

instance is_empty_zero_right_moves : IsEmpty (RightMoves 0) :=
  Pempty.is_empty

instance : Inhabited Pgame :=
  ⟨0⟩

/-- The pre-game `one` is defined by `1 = { 0 | }`. -/
instance : One Pgame :=
  ⟨⟨PUnit, Pempty, fun _ => 0, Pempty.elimₓ⟩⟩

@[simp]
theorem one_left_moves : LeftMoves 1 = PUnit :=
  rfl

@[simp]
theorem one_move_left (x) : moveLeft 1 x = 0 :=
  rfl

@[simp]
theorem one_right_moves : RightMoves 1 = Pempty :=
  rfl

instance uniqueOneLeftMoves : Unique (LeftMoves 1) :=
  PUnit.unique

instance is_empty_one_right_moves : IsEmpty (RightMoves 1) :=
  Pempty.is_empty

/-! ### Pre-game order relations -/


/-- Define simultaneously by mutual induction the `≤` relation and its swapped converse `⧏` on
  pre-games.

  The ZFC definition says that `x = {xL | xR}` is less or equal to `y = {yL | yR}` if
  `∀ x₁ ∈ xL, x₁ ⧏ y` and `∀ y₂ ∈ yR, x ⧏ y₂`, where `x ⧏ y` means `¬ y ≤ x`. This is a tricky
  induction because it only decreases one side at a time, and it also swaps the arguments in the
  definition of `≤`. The solution is to define `x ≤ y` and `x ⧏ y` simultaneously. -/
def leLf : ∀ x y : Pgame.{u}, Prop × Prop
  | mk xl xr xL xR,
    mk yl yr yL yR =>-- the orderings of the clauses here are carefully chosen so that
    --   and.left/or.inl refer to moves by Left, and
    --   and.right/or.inr refer to moves by Right.
    ((∀ i, (le_lf (xL i) ⟨yl, yr, yL, yR⟩).2) ∧ ∀ j, (le_lf ⟨xl, xr, xL, xR⟩ (yR j)).2,
      (∃ i, (le_lf ⟨xl, xr, xL, xR⟩ (yL i)).1) ∨ ∃ j, (le_lf (xR j) ⟨yl, yr, yL, yR⟩).1)

/-- The less or equal relation on pre-games.

If `0 ≤ x`, then Left can win `x` as the second player. -/
instance : LE Pgame :=
  ⟨fun x y => (leLf x y).1⟩

/-- The less or fuzzy relation on pre-games.

If `0 ⧏ x`, then Left can win `x` as the first player. -/
def Lf (x y : Pgame) : Prop :=
  (leLf x y).2

-- mathport name: «expr ⧏ »
localized [Pgame] infixl:50 " ⧏ " => Pgame.Lf

/-- Definition of `x ≤ y` on pre-games built using the constructor. -/
@[simp]
theorem mk_le_mk {xl xr xL xR yl yr yL yR} :
    mk xl xr xL xR ≤ mk yl yr yL yR ↔ (∀ i, xL i ⧏ mk yl yr yL yR) ∧ ∀ j, mk xl xr xL xR ⧏ yR j :=
  show (leLf _ _).1 ↔ _ by
    rw [le_lf]
    rfl

/-- Definition of `x ≤ y` on pre-games, in terms of `⧏` -/
theorem le_iff_forall_lf {x y : Pgame} : x ≤ y ↔ (∀ i, x.moveLeft i ⧏ y) ∧ ∀ j, x ⧏ y.moveRight j := by
  cases x
  cases y
  exact mk_le_mk

theorem le_of_forall_lf {x y : Pgame} (h₁ : ∀ i, x.moveLeft i ⧏ y) (h₂ : ∀ j, x ⧏ y.moveRight j) : x ≤ y :=
  le_iff_forall_lf.2 ⟨h₁, h₂⟩

/-- Definition of `x ⧏ y` on pre-games built using the constructor. -/
@[simp]
theorem mk_lf_mk {xl xr xL xR yl yr yL yR} :
    mk xl xr xL xR ⧏ mk yl yr yL yR ↔ (∃ i, mk xl xr xL xR ≤ yL i) ∨ ∃ j, xR j ≤ mk yl yr yL yR :=
  show (leLf _ _).2 ↔ _ by
    rw [le_lf]
    rfl

/-- Definition of `x ⧏ y` on pre-games, in terms of `≤` -/
theorem lf_iff_exists_le {x y : Pgame} : x ⧏ y ↔ (∃ i, x ≤ y.moveLeft i) ∨ ∃ j, x.moveRight j ≤ y := by
  cases x
  cases y
  exact mk_lf_mk

private theorem not_le_lf {x y : Pgame} : (¬x ≤ y ↔ y ⧏ x) ∧ (¬x ⧏ y ↔ y ≤ x) := by
  induction' x with xl xr xL xR IHxl IHxr generalizing y
  induction' y with yl yr yL yR IHyl IHyr
  simp only [← mk_le_mk, ← mk_lf_mk, ← IHxl, ← IHxr, ← IHyl, ← IHyr, ← not_and_distrib, ← not_or_distrib, ← not_forall,
    ← not_exists, ← and_comm, ← or_comm, ← iff_selfₓ, ← and_selfₓ]

@[simp]
protected theorem not_le {x y : Pgame} : ¬x ≤ y ↔ y ⧏ x :=
  not_le_lf.1

@[simp]
theorem not_lf {x y : Pgame} : ¬x ⧏ y ↔ y ≤ x :=
  not_le_lf.2

theorem _root_.has_le.le.not_gf {x y : Pgame} : x ≤ y → ¬y ⧏ x :=
  not_lf.2

theorem Lf.not_ge {x y : Pgame} : x ⧏ y → ¬y ≤ x :=
  Pgame.not_le.2

theorem le_or_gf (x y : Pgame) : x ≤ y ∨ y ⧏ x := by
  rw [← Pgame.not_le]
  apply em

theorem move_left_lf_of_le {x y : Pgame} (h : x ≤ y) (i) : x.moveLeft i ⧏ y :=
  (le_iff_forall_lf.1 h).1 i

alias move_left_lf_of_le ← _root_.has_le.le.move_left_lf

theorem lf_move_right_of_le {x y : Pgame} (h : x ≤ y) (j) : x ⧏ y.moveRight j :=
  (le_iff_forall_lf.1 h).2 j

alias lf_move_right_of_le ← _root_.has_le.le.lf_move_right

theorem lf_of_move_right_le {x y : Pgame} {j} (h : x.moveRight j ≤ y) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inr ⟨j, h⟩

theorem lf_of_le_move_left {x y : Pgame} {i} (h : x ≤ y.moveLeft i) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inl ⟨i, h⟩

theorem lf_of_le_mk {xl xr xL xR y} : mk xl xr xL xR ≤ y → ∀ i, xL i ⧏ y :=
  move_left_lf_of_le

theorem lf_of_mk_le {x yl yr yL yR} : x ≤ mk yl yr yL yR → ∀ j, x ⧏ yR j :=
  lf_move_right_of_le

theorem mk_lf_of_le {xl xr y j} (xL) {xR : xr → Pgame} : xR j ≤ y → mk xl xr xL xR ⧏ y :=
  @lf_of_move_right_le (mk _ _ _ _) y j

theorem lf_mk_of_le {x yl yr} {yL : yl → Pgame} (yR) {i} : x ≤ yL i → x ⧏ mk yl yr yL yR :=
  @lf_of_le_move_left x (mk _ _ _ _) i

/- We prove that `x ≤ y → y ≤ z ← x ≤ z` inductively, by also simultaneously proving its cyclic
reorderings. This auxiliary lemma is used during said induction. -/
private theorem le_trans_aux {x y z : Pgame} (h₁ : ∀ {i}, y ≤ z → z ≤ x.moveLeft i → y ≤ x.moveLeft i)
    (h₂ : ∀ {j}, z.moveRight j ≤ x → x ≤ y → z.moveRight j ≤ y) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z :=
  le_of_forall_lf (fun i => Pgame.not_le.1 fun h => (h₁ hyz h).not_gf <| hxy.move_left_lf i) fun j =>
    Pgame.not_le.1 fun h => (h₂ h hxy).not_gf <| hyz.lf_move_right j

instance : LT Pgame :=
  ⟨fun x y => x ≤ y ∧ x ⧏ y⟩

instance : Preorderₓ Pgame :=
  { Pgame.hasLe, Pgame.hasLt with
    le_refl := fun x => by
      induction' x with _ _ _ _ IHl IHr
      exact le_of_forall_lf (fun i => lf_of_le_move_left (IHl i)) fun i => lf_of_move_right_le (IHr i),
    le_trans := by
      suffices : ∀ {x y z : Pgame}, (x ≤ y → y ≤ z → x ≤ z) ∧ (y ≤ z → z ≤ x → y ≤ x) ∧ (z ≤ x → x ≤ y → z ≤ y)
      exact fun x y z => this.1
      intro x y z
      induction' x with xl xr xL xR IHxl IHxr generalizing y z
      induction' y with yl yr yL yR IHyl IHyr generalizing z
      induction' z with zl zr zL zR IHzl IHzr
      exact
        ⟨le_trans_aux (fun i => (IHxl i).2.1) fun j => (IHzr j).2.2,
          le_trans_aux (fun i => (IHyl i).2.2) fun j => (IHxr j).1,
          le_trans_aux (fun i => (IHzl i).1) fun j => (IHyr j).2.1⟩,
    lt_iff_le_not_le := fun x y => by
      rw [Pgame.not_le]
      rfl }

theorem lt_iff_le_and_lf {x y : Pgame} : x < y ↔ x ≤ y ∧ x ⧏ y :=
  Iff.rfl

theorem lt_of_le_of_lf {x y : Pgame} (h₁ : x ≤ y) (h₂ : x ⧏ y) : x < y :=
  ⟨h₁, h₂⟩

theorem lf_of_lt {x y : Pgame} (h : x < y) : x ⧏ y :=
  h.2

alias lf_of_lt ← _root_.has_lt.lt.lf

theorem lf_irrefl (x : Pgame) : ¬x ⧏ x :=
  le_rfl.not_gf

instance : IsIrrefl _ (· ⧏ ·) :=
  ⟨lf_irrefl⟩

@[trans]
theorem lf_of_le_of_lf {x y z : Pgame} (h₁ : x ≤ y) (h₂ : y ⧏ z) : x ⧏ z := by
  rw [← Pgame.not_le] at h₂⊢
  exact fun h₃ => h₂ (h₃.trans h₁)

@[trans]
theorem lf_of_lf_of_le {x y z : Pgame} (h₁ : x ⧏ y) (h₂ : y ≤ z) : x ⧏ z := by
  rw [← Pgame.not_le] at h₁⊢
  exact fun h₃ => h₁ (h₂.trans h₃)

alias lf_of_le_of_lf ← _root_.has_le.le.trans_lf

alias lf_of_lf_of_le ← lf.trans_le

@[trans]
theorem lf_of_lt_of_lf {x y z : Pgame} (h₁ : x < y) (h₂ : y ⧏ z) : x ⧏ z :=
  h₁.le.trans_lf h₂

@[trans]
theorem lf_of_lf_of_lt {x y z : Pgame} (h₁ : x ⧏ y) (h₂ : y < z) : x ⧏ z :=
  h₁.trans_le h₂.le

alias lf_of_lt_of_lf ← _root_.has_lt.lt.trans_lf

alias lf_of_lf_of_lt ← lf.trans_lt

theorem move_left_lf {x : Pgame} : ∀ i, x.moveLeft i ⧏ x :=
  le_rfl.move_left_lf

theorem lf_move_right {x : Pgame} : ∀ j, x ⧏ x.moveRight j :=
  le_rfl.lf_move_right

theorem lf_mk {xl xr} (xL : xl → Pgame) (xR : xr → Pgame) (i) : xL i ⧏ mk xl xr xL xR :=
  @move_left_lf (mk _ _ _ _) i

theorem mk_lf {xl xr} (xL : xl → Pgame) (xR : xr → Pgame) (j) : mk xl xr xL xR ⧏ xR j :=
  @lf_move_right (mk _ _ _ _) j

/-- This special case of `pgame.le_of_forall_lf` is useful when dealing with surreals, where `<` is
preferred over `⧏`. -/
theorem le_of_forall_lt {x y : Pgame} (h₁ : ∀ i, x.moveLeft i < y) (h₂ : ∀ j, x < y.moveRight j) : x ≤ y :=
  le_of_forall_lf (fun i => (h₁ i).Lf) fun i => (h₂ i).Lf

/-- The definition of `x ≤ y` on pre-games, in terms of `≤` two moves later. -/
theorem le_def {x y : Pgame} :
    x ≤ y ↔
      (∀ i, (∃ i', x.moveLeft i ≤ y.moveLeft i') ∨ ∃ j, (x.moveLeft i).moveRight j ≤ y) ∧
        ∀ j, (∃ i, x ≤ (y.moveRight j).moveLeft i) ∨ ∃ j', x.moveRight j' ≤ y.moveRight j :=
  by
  rw [le_iff_forall_lf]
  conv => lhs simp only [← lf_iff_exists_le]

/-- The definition of `x ⧏ y` on pre-games, in terms of `⧏` two moves later. -/
theorem lf_def {x y : Pgame} :
    x ⧏ y ↔
      (∃ i, (∀ i', x.moveLeft i' ⧏ y.moveLeft i) ∧ ∀ j, x ⧏ (y.moveLeft i).moveRight j) ∨
        ∃ j, (∀ i, (x.moveRight j).moveLeft i ⧏ y) ∧ ∀ j', x.moveRight j ⧏ y.moveRight j' :=
  by
  rw [lf_iff_exists_le]
  conv => lhs simp only [← le_iff_forall_lf]

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ⧏`. -/
theorem zero_le_lf {x : Pgame} : 0 ≤ x ↔ ∀ j, 0 ⧏ x.moveRight j := by
  rw [le_iff_forall_lf]
  simp

/-- The definition of `x ≤ 0` on pre-games, in terms of `⧏ 0`. -/
theorem le_zero_lf {x : Pgame} : x ≤ 0 ↔ ∀ i, x.moveLeft i ⧏ 0 := by
  rw [le_iff_forall_lf]
  simp

/-- The definition of `0 ⧏ x` on pre-games, in terms of `0 ≤`. -/
theorem zero_lf_le {x : Pgame} : 0 ⧏ x ↔ ∃ i, 0 ≤ x.moveLeft i := by
  rw [lf_iff_exists_le]
  simp

/-- The definition of `x ⧏ 0` on pre-games, in terms of `≤ 0`. -/
theorem lf_zero_le {x : Pgame} : x ⧏ 0 ↔ ∃ j, x.moveRight j ≤ 0 := by
  rw [lf_iff_exists_le]
  simp

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ≤` two moves later. -/
theorem zero_le {x : Pgame} : 0 ≤ x ↔ ∀ j, ∃ i, 0 ≤ (x.moveRight j).moveLeft i := by
  rw [le_def]
  simp

/-- The definition of `x ≤ 0` on pre-games, in terms of `≤ 0` two moves later. -/
theorem le_zero {x : Pgame} : x ≤ 0 ↔ ∀ i, ∃ j, (x.moveLeft i).moveRight j ≤ 0 := by
  rw [le_def]
  simp

/-- The definition of `0 ⧏ x` on pre-games, in terms of `0 ⧏` two moves later. -/
theorem zero_lf {x : Pgame} : 0 ⧏ x ↔ ∃ i, ∀ j, 0 ⧏ (x.moveLeft i).moveRight j := by
  rw [lf_def]
  simp

/-- The definition of `x ⧏ 0` on pre-games, in terms of `⧏ 0` two moves later. -/
theorem lf_zero {x : Pgame} : x ⧏ 0 ↔ ∃ j, ∀ i, (x.moveRight j).moveLeft i ⧏ 0 := by
  rw [lf_def]
  simp

@[simp]
theorem zero_le_of_is_empty_right_moves (x : Pgame) [IsEmpty x.RightMoves] : 0 ≤ x :=
  zero_le.2 isEmptyElim

@[simp]
theorem le_zero_of_is_empty_left_moves (x : Pgame) [IsEmpty x.LeftMoves] : x ≤ 0 :=
  le_zero.2 isEmptyElim

/-- Given a game won by the right player when they play second, provide a response to any move by
left. -/
noncomputable def rightResponse {x : Pgame} (h : x ≤ 0) (i : x.LeftMoves) : (x.moveLeft i).RightMoves :=
  Classical.some <| (le_zero.1 h) i

/-- Show that the response for right provided by `right_response` preserves the right-player-wins
condition. -/
theorem right_response_spec {x : Pgame} (h : x ≤ 0) (i : x.LeftMoves) :
    (x.moveLeft i).moveRight (rightResponse h i) ≤ 0 :=
  Classical.some_spec <| (le_zero.1 h) i

/-- Given a game won by the left player when they play second, provide a response to any move by
right. -/
noncomputable def leftResponse {x : Pgame} (h : 0 ≤ x) (j : x.RightMoves) : (x.moveRight j).LeftMoves :=
  Classical.some <| (zero_le.1 h) j

/-- Show that the response for left provided by `left_response` preserves the left-player-wins
condition. -/
theorem left_response_spec {x : Pgame} (h : 0 ≤ x) (j : x.RightMoves) :
    0 ≤ (x.moveRight j).moveLeft (leftResponse h j) :=
  Classical.some_spec <| (zero_le.1 h) j

/-- The equivalence relation on pre-games. Two pre-games `x`, `y` are equivalent if `x ≤ y` and
`y ≤ x`.

If `x ≈ 0`, then the second player can always win `x`. -/
def Equiv (x y : Pgame) : Prop :=
  x ≤ y ∧ y ≤ x

instance : IsEquiv _ (· ≈ ·) where
  refl := fun x => ⟨le_rfl, le_rfl⟩
  trans := fun x y z ⟨xy, yx⟩ ⟨yz, zy⟩ => ⟨xy.trans yz, zy.trans yx⟩
  symm := fun x y => And.symm

theorem Equiv.le {x y : Pgame} (h : x ≈ y) : x ≤ y :=
  h.1

theorem Equiv.ge {x y : Pgame} (h : x ≈ y) : y ≤ x :=
  h.2

@[refl, simp]
theorem equiv_rfl {x} : x ≈ x :=
  refl x

theorem equiv_refl (x) : x ≈ x :=
  refl x

@[symm]
protected theorem Equiv.symm {x y} : x ≈ y → y ≈ x :=
  symm

@[trans]
protected theorem Equiv.trans {x y z} : x ≈ y → y ≈ z → x ≈ z :=
  trans

protected theorem equiv_comm {x y} : x ≈ y ↔ y ≈ x :=
  comm

theorem equiv_of_eq {x y} (h : x = y) : x ≈ y := by
  subst h

@[trans]
theorem le_of_le_of_equiv {x y z} (h₁ : x ≤ y) (h₂ : y ≈ z) : x ≤ z :=
  h₁.trans h₂.1

@[trans]
theorem le_of_equiv_of_le {x y z} (h₁ : x ≈ y) : y ≤ z → x ≤ z :=
  h₁.1.trans

theorem Lf.not_equiv {x y} (h : x ⧏ y) : ¬x ≈ y := fun h' => h.not_ge h'.2

theorem Lf.not_equiv' {x y} (h : x ⧏ y) : ¬y ≈ x := fun h' => h.not_ge h'.1

theorem Lf.not_gt {x y} (h : x ⧏ y) : ¬y < x := fun h' => h.not_ge h'.le

theorem le_congr_imp {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ ≤ y₁) : x₂ ≤ y₂ :=
  hx.2.trans (h.trans hy.1)

theorem le_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ≤ y₁ ↔ x₂ ≤ y₂ :=
  ⟨le_congr_imp hx hy, le_congr_imp hx.symm hy.symm⟩

theorem le_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ ≤ y ↔ x₂ ≤ y :=
  le_congr hx equiv_rfl

theorem le_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x ≤ y₁ ↔ x ≤ y₂ :=
  le_congr equiv_rfl hy

theorem lf_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ ↔ x₂ ⧏ y₂ :=
  Pgame.not_le.symm.trans <| (not_congr (le_congr hy hx)).trans Pgame.not_le

theorem lf_congr_imp {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ → x₂ ⧏ y₂ :=
  (lf_congr hx hy).1

theorem lf_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ ⧏ y ↔ x₂ ⧏ y :=
  lf_congr hx equiv_rfl

theorem lf_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x ⧏ y₁ ↔ x ⧏ y₂ :=
  lf_congr equiv_rfl hy

@[trans]
theorem lf_of_lf_of_equiv {x y z} (h₁ : x ⧏ y) (h₂ : y ≈ z) : x ⧏ z :=
  lf_congr_imp equiv_rfl h₂ h₁

@[trans]
theorem lf_of_equiv_of_lf {x y z} (h₁ : x ≈ y) : y ⧏ z → x ⧏ z :=
  lf_congr_imp h₁.symm equiv_rfl

@[trans]
theorem lt_of_lt_of_equiv {x y z} (h₁ : x < y) (h₂ : y ≈ z) : x < z :=
  h₁.trans_le h₂.1

@[trans]
theorem lt_of_equiv_of_lt {x y z} (h₁ : x ≈ y) : y < z → x < z :=
  h₁.1.trans_lt

theorem lt_congr_imp {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ < y₁) : x₂ < y₂ :=
  hx.2.trans_lt (h.trans_le hy.1)

theorem lt_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
  ⟨lt_congr_imp hx hy, lt_congr_imp hx.symm hy.symm⟩

theorem lt_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ < y ↔ x₂ < y :=
  lt_congr hx equiv_rfl

theorem lt_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x < y₁ ↔ x < y₂ :=
  lt_congr equiv_rfl hy

theorem lt_or_equiv_of_le {x y : Pgame} (h : x ≤ y) : x < y ∨ x ≈ y :=
  and_or_distrib_left.mp ⟨h, (em <| y ≤ x).swap.imp_left Pgame.not_le.1⟩

theorem lf_or_equiv_or_gf (x y : Pgame) : x ⧏ y ∨ x ≈ y ∨ y ⧏ x := by
  by_cases' h : x ⧏ y
  · exact Or.inl h
    
  · right
    cases' lt_or_equiv_of_le (Pgame.not_lf.1 h) with h' h'
    · exact Or.inr h'.lf
      
    · exact Or.inl h'.symm
      
    

theorem equiv_congr_left {y₁ y₂} : y₁ ≈ y₂ ↔ ∀ x₁, x₁ ≈ y₁ ↔ x₁ ≈ y₂ :=
  ⟨fun h x₁ => ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩, fun h => (h y₁).1 <| equiv_rfl⟩

theorem equiv_congr_right {x₁ x₂} : x₁ ≈ x₂ ↔ ∀ y₁, x₁ ≈ y₁ ↔ x₂ ≈ y₁ :=
  ⟨fun h y₁ => ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩, fun h => (h x₂).2 <| equiv_rfl⟩

theorem equiv_of_mk_equiv {x y : Pgame} (L : x.LeftMoves ≃ y.LeftMoves) (R : x.RightMoves ≃ y.RightMoves)
    (hl : ∀ i : x.LeftMoves, x.moveLeft i ≈ y.moveLeft (L i))
    (hr : ∀ j : y.RightMoves, x.moveRight (R.symm j) ≈ y.moveRight j) : x ≈ y := by
  fconstructor <;> rw [le_def]
  · exact ⟨fun i => Or.inl ⟨L i, (hl i).1⟩, fun j => Or.inr ⟨R.symm j, (hr j).1⟩⟩
    
  · fconstructor
    · intro i
      left
      specialize hl (L.symm i)
      simp only [← move_left_mk, ← Equivₓ.apply_symm_apply] at hl
      use ⟨L.symm i, hl.2⟩
      
    · intro j
      right
      specialize hr (R j)
      simp only [← move_right_mk, ← Equivₓ.symm_apply_apply] at hr
      use ⟨R j, hr.2⟩
      
    

/-- The fuzzy, confused, or incomparable relation on pre-games.

If `x ∥ 0`, then the first player can always win `x`. -/
def Fuzzy (x y : Pgame) : Prop :=
  x ⧏ y ∧ y ⧏ x

-- mathport name: «expr ∥ »
localized [Pgame] infixl:50 " ∥ " => Pgame.Fuzzy

@[symm]
theorem Fuzzy.swap {x y : Pgame} : x ∥ y → y ∥ x :=
  And.swap

instance : IsSymm _ (· ∥ ·) :=
  ⟨fun x y => Fuzzy.swap⟩

theorem Fuzzy.swap_iff {x y : Pgame} : x ∥ y ↔ y ∥ x :=
  ⟨Fuzzy.swap, Fuzzy.swap⟩

theorem fuzzy_irrefl (x : Pgame) : ¬x ∥ x := fun h => lf_irrefl x h.1

instance : IsIrrefl _ (· ∥ ·) :=
  ⟨fuzzy_irrefl⟩

theorem lf_iff_lt_or_fuzzy {x y : Pgame} : x ⧏ y ↔ x < y ∨ x ∥ y := by
  simp only [← lt_iff_le_and_lf, ← fuzzy, Pgame.not_le]
  tauto!

theorem lf_of_fuzzy {x y : Pgame} (h : x ∥ y) : x ⧏ y :=
  lf_iff_lt_or_fuzzy.2 (Or.inr h)

alias lf_of_fuzzy ← fuzzy.lf

theorem lt_or_fuzzy_of_lf {x y : Pgame} : x ⧏ y → x < y ∨ x ∥ y :=
  lf_iff_lt_or_fuzzy.1

theorem Fuzzy.not_equiv {x y : Pgame} (h : x ∥ y) : ¬x ≈ y := fun h' => h'.1.not_gf h.2

theorem Fuzzy.not_equiv' {x y : Pgame} (h : x ∥ y) : ¬y ≈ x := fun h' => h'.2.not_gf h.2

theorem not_fuzzy_of_le {x y : Pgame} (h : x ≤ y) : ¬x ∥ y := fun h' => h'.2.not_ge h

theorem not_fuzzy_of_ge {x y : Pgame} (h : y ≤ x) : ¬x ∥ y := fun h' => h'.1.not_ge h

theorem Equiv.not_fuzzy {x y : Pgame} (h : x ≈ y) : ¬x ∥ y :=
  not_fuzzy_of_le h.1

theorem Equiv.not_fuzzy' {x y : Pgame} (h : x ≈ y) : ¬y ∥ x :=
  not_fuzzy_of_le h.2

theorem fuzzy_congr {x₁ y₁ x₂ y₂ : Pgame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ∥ y₁ ↔ x₂ ∥ y₂ :=
  show _ ∧ _ ↔ _ ∧ _ by
    rw [lf_congr hx hy, lf_congr hy hx]

theorem fuzzy_congr_imp {x₁ y₁ x₂ y₂ : Pgame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ∥ y₁ → x₂ ∥ y₂ :=
  (fuzzy_congr hx hy).1

theorem fuzzy_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ ∥ y ↔ x₂ ∥ y :=
  fuzzy_congr hx equiv_rfl

theorem fuzzy_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x ∥ y₁ ↔ x ∥ y₂ :=
  fuzzy_congr equiv_rfl hy

@[trans]
theorem fuzzy_of_fuzzy_of_equiv {x y z} (h₁ : x ∥ y) (h₂ : y ≈ z) : x ∥ z :=
  (fuzzy_congr_right h₂).1 h₁

@[trans]
theorem fuzzy_of_equiv_of_fuzzy {x y z} (h₁ : x ≈ y) (h₂ : y ∥ z) : x ∥ z :=
  (fuzzy_congr_left h₁).2 h₂

/-- Exactly one of the following is true (although we don't prove this here). -/
theorem lt_or_equiv_or_gt_or_fuzzy (x y : Pgame) : x < y ∨ x ≈ y ∨ y < x ∨ x ∥ y := by
  cases' le_or_gf x y with h₁ h₁ <;> cases' le_or_gf y x with h₂ h₂
  · right
    left
    exact ⟨h₁, h₂⟩
    
  · left
    exact ⟨h₁, h₂⟩
    
  · right
    right
    left
    exact ⟨h₂, h₁⟩
    
  · right
    right
    right
    exact ⟨h₂, h₁⟩
    

theorem lt_or_equiv_or_gf (x y : Pgame) : x < y ∨ x ≈ y ∨ y ⧏ x := by
  rw [lf_iff_lt_or_fuzzy, fuzzy.swap_iff]
  exact lt_or_equiv_or_gt_or_fuzzy x y

/-! ### Relabellings -/


/-- `restricted x y` says that Left always has no more moves in `x` than in `y`,
     and Right always has no more moves in `y` than in `x` -/
inductive Restricted : Pgame.{u} → Pgame.{u} → Type (u + 1)
  | mk :
    ∀ {x y : Pgame} (L : x.LeftMoves → y.LeftMoves) (R : y.RightMoves → x.RightMoves),
      (∀ i, restricted (x.moveLeft i) (y.moveLeft (L i))) →
        (∀ j, restricted (x.moveRight (R j)) (y.moveRight j)) → restricted x y

/-- The identity restriction. -/
@[refl]
def Restricted.refl : ∀ x : Pgame, Restricted x x
  | x => ⟨_, _, fun i => restricted.refl _, fun j => restricted.refl _⟩

instance (x : Pgame) : Inhabited (Restricted x x) :=
  ⟨Restricted.refl _⟩

/-- Transitivity of restriction. -/
def Restricted.trans : ∀ {x y z : Pgame} (r : Restricted x y) (s : Restricted y z), Restricted x z
  | x, y, z, ⟨L₁, R₁, hL₁, hR₁⟩, ⟨L₂, R₂, hL₂, hR₂⟩ =>
    ⟨_, _, fun i => (hL₁ i).trans (hL₂ _), fun j => (hR₁ _).trans (hR₂ j)⟩

theorem Restricted.le : ∀ {x y : Pgame} (r : Restricted x y), x ≤ y
  | x, y, ⟨L, R, hL, hR⟩ => le_def.2 ⟨fun i => Or.inl ⟨L i, (hL i).le⟩, fun i => Or.inr ⟨R i, (hR i).le⟩⟩

/-- `relabelling x y` says that `x` and `y` are really the same game, just dressed up differently.
Specifically, there is a bijection between the moves for Left in `x` and in `y`, and similarly
for Right, and under these bijections we inductively have `relabelling`s for the consequent games.
-/
inductive Relabelling : Pgame.{u} → Pgame.{u} → Type (u + 1)
  | mk :
    ∀ {x y : Pgame} (L : x.LeftMoves ≃ y.LeftMoves) (R : x.RightMoves ≃ y.RightMoves),
      (∀ i, relabelling (x.moveLeft i) (y.moveLeft (L i))) →
        (∀ j, relabelling (x.moveRight (R.symm j)) (y.moveRight j)) → relabelling x y

-- mathport name: «expr ≡r »
localized [Pgame] infixl:50 " ≡r " => Pgame.Relabelling

namespace Relabelling

variable {x y : Pgame.{u}}

/-- If `x` is a relabelling of `y`, then `x` is a restriction of  `y`. -/
def restricted : ∀ {x y : Pgame} (r : x ≡r y), Restricted x y
  | x, y, ⟨L, R, hL, hR⟩ => ⟨L, R.symm, fun i => (hL i).Restricted, fun j => (hR j).Restricted⟩

/-- The identity relabelling. -/
-- It's not the case that `restricted x y → restricted y x → relabelling x y`,
-- but if we insisted that the maps in a restriction were injective, then one
-- could use Schröder-Bernstein for do this.
@[refl]
def refl : ∀ x : Pgame, x ≡r x
  | x => ⟨Equivₓ.refl _, Equivₓ.refl _, fun i => refl _, fun j => refl _⟩

instance (x : Pgame) : Inhabited (x ≡r x) :=
  ⟨refl _⟩

/-- Flip a relabelling. -/
@[symm]
def symm : ∀ {x y : Pgame}, x ≡r y → y ≡r x
  | x, y, ⟨L, R, hL, hR⟩ =>
    ⟨L.symm, R.symm, fun i => by
      simpa using (hL (L.symm i)).symm, fun j => by
      simpa using (hR (R j)).symm⟩

theorem le (r : x ≡r y) : x ≤ y :=
  r.Restricted.le

theorem ge (r : x ≡r y) : y ≤ x :=
  r.symm.Restricted.le

/-- A relabelling lets us prove equivalence of games. -/
theorem equiv (r : x ≡r y) : x ≈ y :=
  ⟨r.le, r.Ge⟩

/-- Transitivity of relabelling. -/
@[trans]
def trans : ∀ {x y z : Pgame}, x ≡r y → y ≡r z → x ≡r z
  | x, y, z, ⟨L₁, R₁, hL₁, hR₁⟩, ⟨L₂, R₂, hL₂, hR₂⟩ =>
    ⟨L₁.trans L₂, R₁.trans R₂, fun i => by
      simpa using (hL₁ i).trans (hL₂ _), fun j => by
      simpa using (hR₁ _).trans (hR₂ j)⟩

/-- Any game without left or right moves is a relabelling of 0. -/
def isEmpty (x : Pgame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≡r 0 :=
  ⟨Equivₓ.equivPempty _, Equivₓ.equivPempty _, isEmptyElim, isEmptyElim⟩

end Relabelling

theorem Equiv.is_empty (x : Pgame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≈ 0 :=
  (Relabelling.isEmpty x).Equiv

instance {x y : Pgame} : Coe (x ≡r y) (x ≈ y) :=
  ⟨Relabelling.equiv⟩

/-- Replace the types indexing the next moves for Left and Right by equivalent types. -/
def relabel {x : Pgame} {xl' xr'} (el : x.LeftMoves ≃ xl') (er : x.RightMoves ≃ xr') : Pgame :=
  ⟨xl', xr', fun i => x.moveLeft (el.symm i), fun j => x.moveRight (er.symm j)⟩

@[simp]
theorem relabel_move_left' {x : Pgame} {xl' xr'} (el : x.LeftMoves ≃ xl') (er : x.RightMoves ≃ xr') (i : xl') :
    moveLeft (relabel el er) i = x.moveLeft (el.symm i) :=
  rfl

@[simp]
theorem relabel_move_left {x : Pgame} {xl' xr'} (el : x.LeftMoves ≃ xl') (er : x.RightMoves ≃ xr') (i : x.LeftMoves) :
    moveLeft (relabel el er) (el i) = x.moveLeft i := by
  simp

@[simp]
theorem relabel_move_right' {x : Pgame} {xl' xr'} (el : x.LeftMoves ≃ xl') (er : x.RightMoves ≃ xr') (j : xr') :
    moveRight (relabel el er) j = x.moveRight (er.symm j) :=
  rfl

@[simp]
theorem relabel_move_right {x : Pgame} {xl' xr'} (el : x.LeftMoves ≃ xl') (er : x.RightMoves ≃ xr') (j : x.RightMoves) :
    moveRight (relabel el er) (er j) = x.moveRight j := by
  simp

/-- The game obtained by relabelling the next moves is a relabelling of the original game. -/
def relabelRelabelling {x : Pgame} {xl' xr'} (el : x.LeftMoves ≃ xl') (er : x.RightMoves ≃ xr') : x ≡r relabel el er :=
  Relabelling.mk el er
    (fun i => by
      simp )
    fun j => by
    simp

/-! ### Negation -/


/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : Pgame → Pgame
  | ⟨l, r, L, R⟩ => ⟨r, l, fun i => neg (R i), fun i => neg (L i)⟩

instance : Neg Pgame :=
  ⟨neg⟩

@[simp]
theorem neg_def {xl xr xL xR} : -mk xl xr xL xR = mk xr xl (fun j => -xR j) fun i => -xL i :=
  rfl

instance : HasInvolutiveNeg Pgame :=
  { Pgame.hasNeg with
    neg_neg := fun x => by
      induction' x with xl xr xL xR ihL ihR
      simp_rw [neg_def, ihL, ihR]
      exact ⟨rfl, rfl, HEq.rfl, HEq.rfl⟩ }

@[simp]
protected theorem neg_zero : -(0 : Pgame) = 0 := by
  dsimp' [← Zero.zero, ← Neg.neg, ← neg]
  congr <;> funext i <;> cases i

@[simp]
theorem neg_of_lists (L R : List Pgame) : -ofLists L R = ofLists (R.map fun x => -x) (L.map fun x => -x) := by
  simp only [← of_lists, ← neg_def, ← List.length_mapₓ, ← List.nth_le_map', ← eq_self_iff_true, ← true_andₓ]
  constructor
  all_goals
    apply hfunext
    · simp
      
    · intro a a' ha
      congr 2
      have : ∀ {m n} (h₁ : m = n) {b : ULift (Finₓ m)} {c : ULift (Finₓ n)} (h₂ : HEq b c), (b.down : ℕ) = ↑c.down := by
        rintro m n rfl b c rfl
        rfl
      exact this (List.length_mapₓ _ _).symm ha
      

theorem is_option_neg {x y : Pgame} : IsOption x (-y) ↔ IsOption (-x) y := by
  rw [is_option_iff, is_option_iff, or_comm]
  cases y
  apply or_congr <;>
    · apply exists_congr
      intro
      rw [← neg_eq_iff_neg_eq]
      exact eq_comm
      

@[simp]
theorem is_option_neg_neg {x y : Pgame} : IsOption (-x) (-y) ↔ IsOption x y := by
  rw [is_option_neg, neg_negₓ]

theorem left_moves_neg : ∀ x : Pgame, (-x).LeftMoves = x.RightMoves
  | ⟨_, _, _, _⟩ => rfl

theorem right_moves_neg : ∀ x : Pgame, (-x).RightMoves = x.LeftMoves
  | ⟨_, _, _, _⟩ => rfl

/-- Turns a right move for `x` into a left move for `-x` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesNeg {x : Pgame} : x.RightMoves ≃ (-x).LeftMoves :=
  Equivₓ.cast (left_moves_neg x).symm

/-- Turns a left move for `x` into a right move for `-x` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesNeg {x : Pgame} : x.LeftMoves ≃ (-x).RightMoves :=
  Equivₓ.cast (right_moves_neg x).symm

theorem move_left_neg {x : Pgame} (i) : (-x).moveLeft (toLeftMovesNeg i) = -x.moveRight i := by
  cases x
  rfl

@[simp]
theorem move_left_neg' {x : Pgame} (i) : (-x).moveLeft i = -x.moveRight (toLeftMovesNeg.symm i) := by
  cases x
  rfl

theorem move_right_neg {x : Pgame} (i) : (-x).moveRight (toRightMovesNeg i) = -x.moveLeft i := by
  cases x
  rfl

@[simp]
theorem move_right_neg' {x : Pgame} (i) : (-x).moveRight i = -x.moveLeft (toRightMovesNeg.symm i) := by
  cases x
  rfl

theorem move_left_neg_symm {x : Pgame} (i) : x.moveLeft (toRightMovesNeg.symm i) = -(-x).moveRight i := by
  simp

theorem move_left_neg_symm' {x : Pgame} (i) : x.moveLeft i = -(-x).moveRight (toRightMovesNeg i) := by
  simp

theorem move_right_neg_symm {x : Pgame} (i) : x.moveRight (toLeftMovesNeg.symm i) = -(-x).moveLeft i := by
  simp

theorem move_right_neg_symm' {x : Pgame} (i) : x.moveRight i = -(-x).moveLeft (toLeftMovesNeg i) := by
  simp

/-- If `x` has the same moves as `y`, then `-x` has the sames moves as `-y`. -/
def Relabelling.negCongr : ∀ {x y : Pgame}, x ≡r y → -x ≡r -y
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨L, R, hL, hR⟩ =>
    ⟨R, L, fun i =>
      relabelling.neg_congr
        (by
          simpa using hR (R i)),
      fun i =>
      relabelling.neg_congr
        (by
          simpa using hL (L.symm i))⟩

private theorem neg_le_lf_neg_iff : ∀ {x y : Pgame.{u}}, (-y ≤ -x ↔ x ≤ y) ∧ (-y ⧏ -x ↔ x ⧏ y)
  | mk xl xr xL xR, mk yl yr yL yR => by
    simp_rw [neg_def, mk_le_mk, mk_lf_mk, ← neg_def]
    constructor
    · rw [and_comm]
      apply and_congr <;> exact forall_congrₓ fun _ => neg_le_lf_neg_iff.2
      
    · rw [or_comm]
      apply or_congr <;> exact exists_congr fun _ => neg_le_lf_neg_iff.1
      

@[simp]
theorem neg_le_neg_iff {x y : Pgame} : -y ≤ -x ↔ x ≤ y :=
  neg_le_lf_neg_iff.1

@[simp]
theorem neg_lf_neg_iff {x y : Pgame} : -y ⧏ -x ↔ x ⧏ y :=
  neg_le_lf_neg_iff.2

@[simp]
theorem neg_lt_neg_iff {x y : Pgame} : -y < -x ↔ x < y := by
  rw [lt_iff_le_and_lf, lt_iff_le_and_lf, neg_le_neg_iff, neg_lf_neg_iff]

@[simp]
theorem neg_equiv_neg_iff {x y : Pgame} : -x ≈ -y ↔ x ≈ y := by
  rw [Equivₓ, Equivₓ, neg_le_neg_iff, neg_le_neg_iff, And.comm]

@[simp]
theorem neg_fuzzy_neg_iff {x y : Pgame} : -x ∥ -y ↔ x ∥ y := by
  rw [fuzzy, fuzzy, neg_lf_neg_iff, neg_lf_neg_iff, And.comm]

theorem neg_le_iff {x y : Pgame} : -y ≤ x ↔ -x ≤ y := by
  rw [← neg_negₓ x, neg_le_neg_iff, neg_negₓ]

theorem neg_lf_iff {x y : Pgame} : -y ⧏ x ↔ -x ⧏ y := by
  rw [← neg_negₓ x, neg_lf_neg_iff, neg_negₓ]

theorem neg_lt_iff {x y : Pgame} : -y < x ↔ -x < y := by
  rw [← neg_negₓ x, neg_lt_neg_iff, neg_negₓ]

theorem neg_equiv_iff {x y : Pgame} : -x ≈ y ↔ x ≈ -y := by
  rw [← neg_negₓ y, neg_equiv_neg_iff, neg_negₓ]

theorem neg_fuzzy_iff {x y : Pgame} : -x ∥ y ↔ x ∥ -y := by
  rw [← neg_negₓ y, neg_fuzzy_neg_iff, neg_negₓ]

theorem le_neg_iff {x y : Pgame} : y ≤ -x ↔ x ≤ -y := by
  rw [← neg_negₓ x, neg_le_neg_iff, neg_negₓ]

theorem lf_neg_iff {x y : Pgame} : y ⧏ -x ↔ x ⧏ -y := by
  rw [← neg_negₓ x, neg_lf_neg_iff, neg_negₓ]

theorem lt_neg_iff {x y : Pgame} : y < -x ↔ x < -y := by
  rw [← neg_negₓ x, neg_lt_neg_iff, neg_negₓ]

@[simp]
theorem neg_le_zero_iff {x : Pgame} : -x ≤ 0 ↔ 0 ≤ x := by
  rw [neg_le_iff, Pgame.neg_zero]

@[simp]
theorem zero_le_neg_iff {x : Pgame} : 0 ≤ -x ↔ x ≤ 0 := by
  rw [le_neg_iff, Pgame.neg_zero]

@[simp]
theorem neg_lf_zero_iff {x : Pgame} : -x ⧏ 0 ↔ 0 ⧏ x := by
  rw [neg_lf_iff, Pgame.neg_zero]

@[simp]
theorem zero_lf_neg_iff {x : Pgame} : 0 ⧏ -x ↔ x ⧏ 0 := by
  rw [lf_neg_iff, Pgame.neg_zero]

@[simp]
theorem neg_lt_zero_iff {x : Pgame} : -x < 0 ↔ 0 < x := by
  rw [neg_lt_iff, Pgame.neg_zero]

@[simp]
theorem zero_lt_neg_iff {x : Pgame} : 0 < -x ↔ x < 0 := by
  rw [lt_neg_iff, Pgame.neg_zero]

@[simp]
theorem neg_equiv_zero_iff {x : Pgame} : -x ≈ 0 ↔ x ≈ 0 := by
  rw [neg_equiv_iff, Pgame.neg_zero]

@[simp]
theorem neg_fuzzy_zero_iff {x : Pgame} : -x ∥ 0 ↔ x ∥ 0 := by
  rw [neg_fuzzy_iff, Pgame.neg_zero]

@[simp]
theorem zero_equiv_neg_iff {x : Pgame} : 0 ≈ -x ↔ 0 ≈ x := by
  rw [← neg_equiv_iff, Pgame.neg_zero]

@[simp]
theorem zero_fuzzy_neg_iff {x : Pgame} : 0 ∥ -x ↔ 0 ∥ x := by
  rw [← neg_fuzzy_iff, Pgame.neg_zero]

/-! ### Addition and subtraction -/


/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : Add Pgame.{u} :=
  ⟨fun x y => by
    induction' x with xl xr xL xR IHxl IHxr generalizing y
    induction' y with yl yr yL yR IHyl IHyr
    have y := mk yl yr yL yR
    refine' ⟨Sum xl yl, Sum xr yr, Sum.rec _ _, Sum.rec _ _⟩
    · exact fun i => IHxl i y
      
    · exact IHyl
      
    · exact fun i => IHxr i y
      
    · exact IHyr
      ⟩

/-- The pre-game `((0+1)+⋯)+1`. -/
instance : HasNatCast Pgame :=
  ⟨Nat.unaryCast⟩

@[simp]
protected theorem nat_succ (n : ℕ) : ((n + 1 : ℕ) : Pgame) = n + 1 :=
  rfl

instance is_empty_left_moves_add (x y : Pgame.{u}) [IsEmpty x.LeftMoves] [IsEmpty y.LeftMoves] :
    IsEmpty (x + y).LeftMoves := by
  cases x
  cases y
  apply is_empty_sum.2 ⟨_, _⟩
  assumption'

instance is_empty_right_moves_add (x y : Pgame.{u}) [IsEmpty x.RightMoves] [IsEmpty y.RightMoves] :
    IsEmpty (x + y).RightMoves := by
  cases x
  cases y
  apply is_empty_sum.2 ⟨_, _⟩
  assumption'

/-- `x + 0` has exactly the same moves as `x`. -/
def addZeroRelabelling : ∀ x : Pgame.{u}, x + 0 ≡r x
  | mk xl xr xL xR => by
    refine' ⟨Equivₓ.sumEmpty xl Pempty, Equivₓ.sumEmpty xr Pempty, _, _⟩
    · rintro (⟨i⟩ | ⟨⟨⟩⟩)
      apply add_zero_relabelling
      
    · rintro j
      apply add_zero_relabelling
      

/-- `x + 0` is equivalent to `x`. -/
theorem add_zero_equiv (x : Pgame.{u}) : x + 0 ≈ x :=
  (addZeroRelabelling x).Equiv

/-- `0 + x` has exactly the same moves as `x`. -/
def zeroAddRelabelling : ∀ x : Pgame.{u}, 0 + x ≡r x
  | mk xl xr xL xR => by
    refine' ⟨Equivₓ.emptySum Pempty xl, Equivₓ.emptySum Pempty xr, _, _⟩
    · rintro (⟨⟨⟩⟩ | ⟨i⟩)
      apply zero_add_relabelling
      
    · rintro j
      apply zero_add_relabelling
      

/-- `0 + x` is equivalent to `x`. -/
theorem zero_add_equiv (x : Pgame.{u}) : 0 + x ≈ x :=
  (zeroAddRelabelling x).Equiv

theorem left_moves_add : ∀ x y : Pgame.{u}, (x + y).LeftMoves = Sum x.LeftMoves y.LeftMoves
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl

theorem right_moves_add : ∀ x y : Pgame.{u}, (x + y).RightMoves = Sum x.RightMoves y.RightMoves
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl

/-- Converts a left move for `x` or `y` into a left move for `x + y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesAdd {x y : Pgame} : Sum x.LeftMoves y.LeftMoves ≃ (x + y).LeftMoves :=
  Equivₓ.cast (left_moves_add x y).symm

/-- Converts a right move for `x` or `y` into a right move for `x + y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesAdd {x y : Pgame} : Sum x.RightMoves y.RightMoves ≃ (x + y).RightMoves :=
  Equivₓ.cast (right_moves_add x y).symm

@[simp]
theorem mk_add_move_left_inl {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft (Sum.inl i) = (mk xl xr xL xR).moveLeft i + mk yl yr yL yR :=
  rfl

@[simp]
theorem add_move_left_inl {x : Pgame} (y : Pgame) (i) :
    (x + y).moveLeft (toLeftMovesAdd (Sum.inl i)) = x.moveLeft i + y := by
  cases x
  cases y
  rfl

@[simp]
theorem mk_add_move_right_inl {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight (Sum.inl i) = (mk xl xr xL xR).moveRight i + mk yl yr yL yR :=
  rfl

@[simp]
theorem add_move_right_inl {x : Pgame} (y : Pgame) (i) :
    (x + y).moveRight (toRightMovesAdd (Sum.inl i)) = x.moveRight i + y := by
  cases x
  cases y
  rfl

@[simp]
theorem mk_add_move_left_inr {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft (Sum.inr i) = mk xl xr xL xR + (mk yl yr yL yR).moveLeft i :=
  rfl

@[simp]
theorem add_move_left_inr (x : Pgame) {y : Pgame} (i) :
    (x + y).moveLeft (toLeftMovesAdd (Sum.inr i)) = x + y.moveLeft i := by
  cases x
  cases y
  rfl

@[simp]
theorem mk_add_move_right_inr {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight (Sum.inr i) = mk xl xr xL xR + (mk yl yr yL yR).moveRight i :=
  rfl

@[simp]
theorem add_move_right_inr (x : Pgame) {y : Pgame} (i) :
    (x + y).moveRight (toRightMovesAdd (Sum.inr i)) = x + y.moveRight i := by
  cases x
  cases y
  rfl

theorem left_moves_add_cases {x y : Pgame} (k) {P : (x + y).LeftMoves → Prop}
    (hl : ∀ i, P <| toLeftMovesAdd (Sum.inl i)) (hr : ∀ i, P <| toLeftMovesAdd (Sum.inr i)) : P k := by
  rw [← to_left_moves_add.apply_symm_apply k]
  cases' to_left_moves_add.symm k with i i
  · exact hl i
    
  · exact hr i
    

theorem right_moves_add_cases {x y : Pgame} (k) {P : (x + y).RightMoves → Prop}
    (hl : ∀ j, P <| toRightMovesAdd (Sum.inl j)) (hr : ∀ j, P <| toRightMovesAdd (Sum.inr j)) : P k := by
  rw [← to_right_moves_add.apply_symm_apply k]
  cases' to_right_moves_add.symm k with i i
  · exact hl i
    
  · exact hr i
    

instance is_empty_nat_right_moves : ∀ n : ℕ, IsEmpty (RightMoves n)
  | 0 => Pempty.is_empty
  | n + 1 => by
    have := is_empty_nat_right_moves n
    rw [Pgame.nat_succ, right_moves_add]
    infer_instance

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w + y` has the same moves as `x + z`. -/
def Relabelling.addCongr : ∀ {w x y z : Pgame.{u}}, w ≡r x → y ≡r z → w + y ≡r x + z
  | ⟨wl, wr, wL, wR⟩, ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨zl, zr, zL, zR⟩, ⟨L₁, R₁, hL₁, hR₁⟩, ⟨L₂, R₂, hL₂, hR₂⟩ => by
    let Hwx : ⟨wl, wr, wL, wR⟩ ≡r ⟨xl, xr, xL, xR⟩ := ⟨L₁, R₁, hL₁, hR₁⟩
    let Hyz : ⟨yl, yr, yL, yR⟩ ≡r ⟨zl, zr, zL, zR⟩ := ⟨L₂, R₂, hL₂, hR₂⟩
    refine' ⟨Equivₓ.sumCongr L₁ L₂, Equivₓ.sumCongr R₁ R₂, _, _⟩ <;> rintro (i | j)
    · exact (hL₁ i).addCongr Hyz
      
    · exact Hwx.add_congr (hL₂ j)
      
    · exact (hR₁ i).addCongr Hyz
      
    · exact Hwx.add_congr (hR₂ j)
      

instance : Sub Pgame :=
  ⟨fun x y => x + -y⟩

@[simp]
theorem sub_zero (x : Pgame) : x - 0 = x + 0 :=
  show x + -0 = x + 0 by
    rw [Pgame.neg_zero]

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w - y` has the same moves as `x - z`. -/
def Relabelling.subCongr {w x y z : Pgame} (h₁ : w ≡r x) (h₂ : y ≡r z) : w - y ≡r x - z :=
  h₁.addCongr h₂.negCongr

/-- `-(x + y)` has exactly the same moves as `-x + -y`. -/
def negAddRelabelling : ∀ x y : Pgame, -(x + y) ≡r -x + -y
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    refine' ⟨Equivₓ.refl _, Equivₓ.refl _, _, _⟩
    all_goals
      exact fun j => Sum.casesOn j (fun j => neg_add_relabelling _ _) fun j => neg_add_relabelling ⟨xl, xr, xL, xR⟩ _

theorem neg_add_le {x y : Pgame} : -(x + y) ≤ -x + -y :=
  (negAddRelabelling x y).le

/-- `x + y` has exactly the same moves as `y + x`. -/
def addCommRelabelling : ∀ x y : Pgame.{u}, x + y ≡r y + x
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine' ⟨Equivₓ.sumComm _ _, Equivₓ.sumComm _ _, _, _⟩ <;>
      rintro (_ | _) <;>
        · dsimp' [← left_moves_add, ← right_moves_add]
          apply add_comm_relabelling
          

theorem add_comm_le {x y : Pgame} : x + y ≤ y + x :=
  (addCommRelabelling x y).le

theorem add_comm_equiv {x y : Pgame} : x + y ≈ y + x :=
  (addCommRelabelling x y).Equiv

/-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
def addAssocRelabelling : ∀ x y z : Pgame.{u}, x + y + z ≡r x + (y + z)
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨zl, zr, zL, zR⟩ => by
    refine' ⟨Equivₓ.sumAssoc _ _ _, Equivₓ.sumAssoc _ _ _, _, _⟩
    all_goals
      first |
        rintro (⟨i | i⟩ | i)|
        rintro (j | ⟨j | j⟩)
      · apply add_assoc_relabelling
        
      · apply add_assoc_relabelling ⟨xl, xr, xL, xR⟩
        
      · apply add_assoc_relabelling ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩
        

theorem add_assoc_equiv {x y z : Pgame} : x + y + z ≈ x + (y + z) :=
  (addAssocRelabelling x y z).Equiv

theorem add_left_neg_le_zero : ∀ x : Pgame, -x + x ≤ 0
  | ⟨xl, xr, xL, xR⟩ =>
    le_zero.2 fun i => by
      cases i
      · -- If Left played in -x, Right responds with the same move in x.
        refine' ⟨@to_right_moves_add _ ⟨_, _, _, _⟩ (Sum.inr i), _⟩
        convert @add_left_neg_le_zero (xR i)
        apply add_move_right_inr
        
      · -- If Left in x, Right responds with the same move in -x.
        dsimp'
        refine' ⟨@to_right_moves_add ⟨_, _, _, _⟩ _ (Sum.inl i), _⟩
        convert @add_left_neg_le_zero (xL i)
        apply add_move_right_inl
        

theorem zero_le_add_left_neg (x : Pgame) : 0 ≤ -x + x := by
  rw [← neg_le_neg_iff, Pgame.neg_zero]
  exact neg_add_le.trans (add_left_neg_le_zero _)

theorem add_left_neg_equiv (x : Pgame) : -x + x ≈ 0 :=
  ⟨add_left_neg_le_zero x, zero_le_add_left_neg x⟩

theorem add_right_neg_le_zero (x : Pgame) : x + -x ≤ 0 :=
  add_comm_le.trans (add_left_neg_le_zero x)

theorem zero_le_add_right_neg (x : Pgame) : 0 ≤ x + -x :=
  (zero_le_add_left_neg x).trans add_comm_le

theorem add_right_neg_equiv (x : Pgame) : x + -x ≈ 0 :=
  ⟨add_right_neg_le_zero x, zero_le_add_right_neg x⟩

theorem sub_self_equiv : ∀ x, x - x ≈ 0 :=
  add_right_neg_equiv

private theorem add_le_add_right' : ∀ {x y z : Pgame} (h : x ≤ y), x + z ≤ y + z
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => fun h => by
    refine' le_def.2 ⟨fun i => _, fun i => _⟩ <;> cases i
    · rw [le_def] at h
      cases h
      rcases h_left i with (⟨i', ih⟩ | ⟨j, jh⟩)
      · exact Or.inl ⟨to_left_moves_add (Sum.inl i'), add_le_add_right' ih⟩
        
      · refine' Or.inr ⟨to_right_moves_add (Sum.inl j), _⟩
        convert add_le_add_right' jh
        apply add_move_right_inl
        
      
    · exact Or.inl ⟨@to_left_moves_add _ ⟨_, _, _, _⟩ (Sum.inr i), add_le_add_right' h⟩
      
    · rw [le_def] at h
      cases h
      rcases h_right i with (⟨i, ih⟩ | ⟨j', jh⟩)
      · refine' Or.inl ⟨to_left_moves_add (Sum.inl i), _⟩
        convert add_le_add_right' ih
        apply add_move_left_inl
        
      · exact Or.inr ⟨to_right_moves_add (Sum.inl j'), add_le_add_right' jh⟩
        
      
    · exact Or.inr ⟨@to_right_moves_add _ ⟨_, _, _, _⟩ (Sum.inr i), add_le_add_right' h⟩
      

instance covariant_class_swap_add_le : CovariantClass Pgame Pgame (swap (· + ·)) (· ≤ ·) :=
  ⟨fun x y z => add_le_add_right'⟩

instance covariant_class_add_le : CovariantClass Pgame Pgame (· + ·) (· ≤ ·) :=
  ⟨fun x y z h => (add_comm_le.trans (add_le_add_right h x)).trans add_comm_le⟩

theorem add_lf_add_right {y z : Pgame} (h : y ⧏ z) (x) : y + x ⧏ z + x :=
  suffices z + x ≤ y + x → z ≤ y by
    rw [← Pgame.not_le] at h⊢
    exact mt this h
  fun w =>
  calc
    z ≤ z + 0 := (addZeroRelabelling _).symm.le
    _ ≤ z + (x + -x) := add_le_add_left (zero_le_add_right_neg x) _
    _ ≤ z + x + -x := (addAssocRelabelling _ _ _).symm.le
    _ ≤ y + x + -x := add_le_add_right w _
    _ ≤ y + (x + -x) := (addAssocRelabelling _ _ _).le
    _ ≤ y + 0 := add_le_add_left (add_right_neg_le_zero x) _
    _ ≤ y := (addZeroRelabelling _).le
    

theorem add_lf_add_left {y z : Pgame} (h : y ⧏ z) (x) : x + y ⧏ x + z := by
  rw [lf_congr add_comm_equiv add_comm_equiv]
  apply add_lf_add_right h

instance covariant_class_swap_add_lt : CovariantClass Pgame Pgame (swap (· + ·)) (· < ·) :=
  ⟨fun x y z h => ⟨add_le_add_right h.1 x, add_lf_add_right h.2 x⟩⟩

instance covariant_class_add_lt : CovariantClass Pgame Pgame (· + ·) (· < ·) :=
  ⟨fun x y z h => ⟨add_le_add_left h.1 x, add_lf_add_left h.2 x⟩⟩

theorem add_lf_add_of_lf_of_le {w x y z : Pgame} (hwx : w ⧏ x) (hyz : y ≤ z) : w + y ⧏ x + z :=
  lf_of_lf_of_le (add_lf_add_right hwx y) (add_le_add_left hyz x)

theorem add_lf_add_of_le_of_lf {w x y z : Pgame} (hwx : w ≤ x) (hyz : y ⧏ z) : w + y ⧏ x + z :=
  lf_of_le_of_lf (add_le_add_right hwx y) (add_lf_add_left hyz x)

theorem add_congr {w x y z : Pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w + y ≈ x + z :=
  ⟨(add_le_add_left h₂.1 w).trans (add_le_add_right h₁.1 z), (add_le_add_left h₂.2 x).trans (add_le_add_right h₁.2 y)⟩

theorem add_congr_left {x y z : Pgame} (h : x ≈ y) : x + z ≈ y + z :=
  add_congr h equiv_rfl

theorem add_congr_right {x y z : Pgame} : y ≈ z → x + y ≈ x + z :=
  add_congr equiv_rfl

theorem sub_congr {w x y z : Pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w - y ≈ x - z :=
  add_congr h₁ (neg_equiv_neg_iff.2 h₂)

theorem sub_congr_left {x y z : Pgame} (h : x ≈ y) : x - z ≈ y - z :=
  sub_congr h equiv_rfl

theorem sub_congr_right {x y z : Pgame} : y ≈ z → x - y ≈ x - z :=
  sub_congr equiv_rfl

theorem le_iff_sub_nonneg {x y : Pgame} : x ≤ y ↔ 0 ≤ y - x :=
  ⟨fun h => (zero_le_add_right_neg x).trans (add_le_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (zeroAddRelabelling x).symm.le
      _ ≤ y - x + x := add_le_add_right h _
      _ ≤ y + (-x + x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (add_left_neg_le_zero x) _
      _ ≤ y := (addZeroRelabelling y).le
      ⟩

theorem lf_iff_sub_zero_lf {x y : Pgame} : x ⧏ y ↔ 0 ⧏ y - x :=
  ⟨fun h => (zero_le_add_right_neg x).trans_lf (add_lf_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (zeroAddRelabelling x).symm.le
      _ ⧏ y - x + x := add_lf_add_right h _
      _ ≤ y + (-x + x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (add_left_neg_le_zero x) _
      _ ≤ y := (addZeroRelabelling y).le
      ⟩

theorem lt_iff_sub_pos {x y : Pgame} : x < y ↔ 0 < y - x :=
  ⟨fun h => lt_of_le_of_ltₓ (zero_le_add_right_neg x) (add_lt_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (zeroAddRelabelling x).symm.le
      _ < y - x + x := add_lt_add_right h _
      _ ≤ y + (-x + x) := (addAssocRelabelling _ _ _).le
      _ ≤ y + 0 := add_le_add_left (add_left_neg_le_zero x) _
      _ ≤ y := (addZeroRelabelling y).le
      ⟩

/-! ### Special pre-games -/


/-- The pre-game `star`, which is fuzzy with zero. -/
def star : Pgame.{u} :=
  ⟨PUnit, PUnit, fun _ => 0, fun _ => 0⟩

@[simp]
theorem star_left_moves : star.LeftMoves = PUnit :=
  rfl

@[simp]
theorem star_right_moves : star.RightMoves = PUnit :=
  rfl

@[simp]
theorem star_move_left (x) : star.moveLeft x = 0 :=
  rfl

@[simp]
theorem star_move_right (x) : star.moveRight x = 0 :=
  rfl

instance uniqueStarLeftMoves : Unique star.LeftMoves :=
  PUnit.unique

instance uniqueStarRightMoves : Unique star.RightMoves :=
  PUnit.unique

theorem star_fuzzy_zero : star ∥ 0 :=
  ⟨by
    rw [lf_zero]
    use default
    rintro ⟨⟩, by
    rw [zero_lf]
    use default
    rintro ⟨⟩⟩

@[simp]
theorem neg_star : -star = star := by
  simp [← star]

@[simp]
theorem zero_lt_one : (0 : Pgame) < 1 :=
  lt_of_le_of_lf (zero_le_of_is_empty_right_moves 1) (zero_lf_le.2 ⟨default, le_rfl⟩)

instance : ZeroLeOneClass Pgame :=
  ⟨zero_lt_one.le⟩

@[simp]
theorem zero_lf_one : (0 : Pgame) ⧏ 1 :=
  zero_lt_one.Lf

end Pgame


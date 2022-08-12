/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Ordmap.Ordnode
import Mathbin.Algebra.Order.Ring
import Mathbin.Data.Nat.Dist
import Mathbin.Tactic.Linarith.Default

/-!
# Verification of the `ordnode α` datatype

This file proves the correctness of the operations in `data.ordmap.ordnode`.
The public facing version is the type `ordset α`, which is a wrapper around
`ordnode α` which includes the correctness invariant of the type, and it exposes
parallel operations like `insert` as functions on `ordset` that do the same
thing but bundle the correctness proofs. The advantage is that it is possible
to, for example, prove that the result of `find` on `insert` will actually find
the element, while `ordnode` cannot guarantee this if the input tree did not
satisfy the type invariants.

## Main definitions

* `ordset α`: A well formed set of values of type `α`

## Implementation notes

The majority of this file is actually in the `ordnode` namespace, because we first
have to prove the correctness of all the operations (and defining what correctness
means here is actually somewhat subtle). So all the actual `ordset` operations are
at the very end, once we have all the theorems.

An `ordnode α` is an inductive type which describes a tree which stores the `size` at
internal nodes. The correctness invariant of an `ordnode α` is:

* `ordnode.sized t`: All internal `size` fields must match the actual measured
  size of the tree. (This is not hard to satisfy.)
* `ordnode.balanced t`: Unless the tree has the form `()` or `((a) b)` or `(a (b))`
  (that is, nil or a single singleton subtree), the two subtrees must satisfy
  `size l ≤ δ * size r` and `size r ≤ δ * size l`, where `δ := 3` is a global
  parameter of the data structure (and this property must hold recursively at subtrees).
  This is why we say this is a "size balanced tree" data structure.
* `ordnode.bounded lo hi t`: The members of the tree must be in strictly increasing order,
  meaning that if `a` is in the left subtree and `b` is the root, then `a ≤ b` and
  `¬ (b ≤ a)`. We enforce this using `ordnode.bounded` which includes also a global
  upper and lower bound.

Because the `ordnode` file was ported from Haskell, the correctness invariants of some
of the functions have not been spelled out, and some theorems like
`ordnode.valid'.balance_l_aux` show very intricate assumptions on the sizes,
which may need to be revised if it turns out some operations violate these assumptions,
because there is a decent amount of slop in the actual data structure invariants, so the
theorem will go through with multiple choices of assumption.

**Note:** This file is incomplete, in the sense that the intent is to have verified
versions and lemmas about all the definitions in `ordnode.lean`, but at the moment only
a few operations are verified (the hard part should be out of the way, but still).
Contributors are encouraged to pick this up and finish the job, if it appeals to you.

## Tags

ordered map, ordered set, data structure, verified programming

-/


variable {α : Type _}

namespace Ordnode

/-! ### delta and ratio -/


theorem not_le_delta {s} (H : 1 ≤ s) : ¬s ≤ delta * 0 :=
  not_le_of_gtₓ H

theorem delta_lt_false {a b : ℕ} (h₁ : delta * a < b) (h₂ : delta * b < a) : False :=
  not_le_of_lt
      (lt_transₓ
        ((mul_lt_mul_left
              (by
                decide)).2
          h₁)
        h₂) <|
    by
    simpa [← mul_assoc] using
      Nat.mul_le_mul_rightₓ a
        (by
          decide : 1 ≤ delta * delta)

/-! ### `singleton` -/


/-! ### `size` and `empty` -/


/-- O(n). Computes the actual number of elements in the set, ignoring the cached `size` field. -/
def realSize : Ordnode α → ℕ
  | nil => 0
  | node _ l _ r => real_size l + real_size r + 1

/-! ### `sized` -/


/-- The `sized` property asserts that all the `size` fields in nodes match the actual size of the
respective subtrees. -/
def Sized : Ordnode α → Prop
  | nil => True
  | node s l _ r => s = size l + size r + 1 ∧ sized l ∧ sized r

theorem Sized.node' {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (node' l x r) :=
  ⟨rfl, hl, hr⟩

theorem Sized.eq_node' {s l x r} (h : @Sized α (node s l x r)) : node s l x r = node' l x r := by
  rw [h.1] <;> rfl

theorem Sized.size_eq {s l x r} (H : Sized (@node α s l x r)) : size (@node α s l x r) = size l + size r + 1 :=
  H.1

@[elab_as_eliminator]
theorem Sized.induction {t} (hl : @Sized α t) {C : Ordnode α → Prop} (H0 : C nil)
    (H1 : ∀ l x r, C l → C r → C (node' l x r)) : C t := by
  induction t
  · exact H0
    
  rw [hl.eq_node']
  exact H1 _ _ _ (t_ih_l hl.2.1) (t_ih_r hl.2.2)

theorem size_eq_real_size : ∀ {t : Ordnode α}, Sized t → size t = realSize t
  | nil, _ => rfl
  | node s l x r, ⟨h₁, h₂, h₃⟩ => by
    rw [size, h₁, size_eq_real_size h₂, size_eq_real_size h₃] <;> rfl

@[simp]
theorem Sized.size_eq_zero {t : Ordnode α} (ht : Sized t) : size t = 0 ↔ t = nil := by
  cases t <;> [simp , simp [← ht.1]]

theorem Sized.pos {s l x r} (h : Sized (@node α s l x r)) : 0 < s := by
  rw [h.1] <;> apply Nat.le_add_leftₓ

/-! `dual` -/


theorem dual_dual : ∀ t : Ordnode α, dual (dual t) = t
  | nil => rfl
  | node s l x r => by
    rw [dual, dual, dual_dual, dual_dual]

@[simp]
theorem size_dual (t : Ordnode α) : size (dual t) = size t := by
  cases t <;> rfl

/-! `balanced` -/


/-- The `balanced_sz l r` asserts that a hypothetical tree with children of sizes `l` and `r` is
balanced: either `l ≤ δ * r` and `r ≤ δ * r`, or the tree is trivial with a singleton on one side
and nothing on the other. -/
def BalancedSz (l r : ℕ) : Prop :=
  l + r ≤ 1 ∨ l ≤ delta * r ∧ r ≤ delta * l

instance BalancedSz.dec : DecidableRel BalancedSz := fun l r => Or.decidable

/-- The `balanced t` asserts that the tree `t` satisfies the balance invariants
(at every level). -/
def Balanced : Ordnode α → Prop
  | nil => True
  | node _ l _ r => BalancedSz (size l) (size r) ∧ balanced l ∧ balanced r

instance Balanced.dec : DecidablePred (@Balanced α)
  | t => by
    induction t <;> unfold balanced <;> skip <;> infer_instance

theorem BalancedSz.symm {l r : ℕ} : BalancedSz l r → BalancedSz r l :=
  Or.imp
    (by
      rw [add_commₓ] <;> exact id)
    And.symm

theorem balanced_sz_zero {l : ℕ} : BalancedSz l 0 ↔ l ≤ 1 := by
  simp (config := { contextual := true })[← balanced_sz]

theorem balanced_sz_up {l r₁ r₂ : ℕ} (h₁ : r₁ ≤ r₂) (h₂ : l + r₂ ≤ 1 ∨ r₂ ≤ delta * l) (H : BalancedSz l r₁) :
    BalancedSz l r₂ := by
  refine' or_iff_not_imp_left.2 fun h => _
  refine' ⟨_, h₂.resolve_left h⟩
  cases H
  · cases r₂
    · cases h (le_transₓ (Nat.add_le_add_leftₓ (Nat.zero_leₓ _) _) H)
      
    · exact le_transₓ (le_transₓ (Nat.le_add_rightₓ _ _) H) (Nat.le_add_leftₓ 1 _)
      
    
  · exact le_transₓ H.1 (Nat.mul_le_mul_leftₓ _ h₁)
    

theorem balanced_sz_down {l r₁ r₂ : ℕ} (h₁ : r₁ ≤ r₂) (h₂ : l + r₂ ≤ 1 ∨ l ≤ delta * r₁) (H : BalancedSz l r₂) :
    BalancedSz l r₁ :=
  have : l + r₂ ≤ 1 → BalancedSz l r₁ := fun H => Or.inl (le_transₓ (Nat.add_le_add_leftₓ h₁ _) H)
  Or.cases_on H this fun H => Or.cases_on h₂ this fun h₂ => Or.inr ⟨h₂, le_transₓ h₁ H.2⟩

theorem Balanced.dual : ∀ {t : Ordnode α}, Balanced t → Balanced (dual t)
  | nil, h => ⟨⟩
  | node s l x r, ⟨b, bl, br⟩ =>
    ⟨by
      rw [size_dual, size_dual] <;> exact b.symm, br.dual, bl.dual⟩

/-! ### `rotate` and `balance` -/


/-- Build a tree from three nodes, left associated (ignores the invariants). -/
def node3L (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) : Ordnode α :=
  node' (node' l x m) y r

/-- Build a tree from three nodes, right associated (ignores the invariants). -/
def node3R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) : Ordnode α :=
  node' l x (node' m y r)

/-- Build a tree from three nodes, with `a () b -> (a ()) b` and `a (b c) d -> ((a b) (c d))`. -/
def node4L : Ordnode α → α → Ordnode α → α → Ordnode α → Ordnode α
  | l, x, node _ ml y mr, z, r => node' (node' l x ml) y (node' mr z r)
  | l, x, nil, z, r => node3L l x nil z r

/-- Build a tree from three nodes, with `a () b -> a (() b)` and `a (b c) d -> ((a b) (c d))`. -/
-- should not happen
def node4R : Ordnode α → α → Ordnode α → α → Ordnode α → Ordnode α
  | l, x, node _ ml y mr, z, r => node' (node' l x ml) y (node' mr z r)
  | l, x, nil, z, r => node3R l x nil z r

/-- Concatenate two nodes, performing a left rotation `x (y z) -> ((x y) z)`
if balance is upset. -/
-- should not happen
def rotateL : Ordnode α → α → Ordnode α → Ordnode α
  | l, x, node _ m y r => if size m < ratio * size r then node3L l x m y r else node4L l x m y r
  | l, x, nil => node' l x nil

/-- Concatenate two nodes, performing a right rotation `(x y) z -> (x (y z))`
if balance is upset. -/
-- should not happen
def rotateR : Ordnode α → α → Ordnode α → Ordnode α
  | node _ l x m, y, r => if size m < ratio * size l then node3R l x m y r else node4R l x m y r
  | nil, y, r => node' nil y r

/-- A left balance operation. This will rebalance a concatenation, assuming the original nodes are
not too far from balanced. -/
-- should not happen
def balanceL' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if size l + size r ≤ 1 then node' l x r else if size l > delta * size r then rotateR l x r else node' l x r

/-- A right balance operation. This will rebalance a concatenation, assuming the original nodes are
not too far from balanced. -/
def balanceR' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if size l + size r ≤ 1 then node' l x r else if size r > delta * size l then rotateL l x r else node' l x r

/-- The full balance operation. This is the same as `balance`, but with less manual inlining.
It is somewhat easier to work with this version in proofs. -/
def balance' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if size l + size r ≤ 1 then node' l x r
  else if size r > delta * size l then rotateL l x r else if size l > delta * size r then rotateR l x r else node' l x r

theorem dual_node' (l : Ordnode α) (x : α) (r : Ordnode α) : dual (node' l x r) = node' (dual r) x (dual l) := by
  simp [← node', ← add_commₓ]

theorem dual_node3_l (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node3L l x m y r) = node3R (dual r) y (dual m) x (dual l) := by
  simp [← node3_l, ← node3_r, ← dual_node']

theorem dual_node3_r (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node3R l x m y r) = node3L (dual r) y (dual m) x (dual l) := by
  simp [← node3_l, ← node3_r, ← dual_node']

theorem dual_node4_l (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node4L l x m y r) = node4R (dual r) y (dual m) x (dual l) := by
  cases m <;> simp [← node4_l, ← node4_r, ← dual_node3_l, ← dual_node']

theorem dual_node4_r (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node4R l x m y r) = node4L (dual r) y (dual m) x (dual l) := by
  cases m <;> simp [← node4_l, ← node4_r, ← dual_node3_r, ← dual_node']

theorem dual_rotate_l (l : Ordnode α) (x : α) (r : Ordnode α) : dual (rotateL l x r) = rotateR (dual r) x (dual l) := by
  cases r <;> simp [← rotate_l, ← rotate_r, ← dual_node'] <;> split_ifs <;> simp [← dual_node3_l, ← dual_node4_l]

theorem dual_rotate_r (l : Ordnode α) (x : α) (r : Ordnode α) : dual (rotateR l x r) = rotateL (dual r) x (dual l) := by
  rw [← dual_dual (rotate_l _ _ _), dual_rotate_l, dual_dual, dual_dual]

theorem dual_balance' (l : Ordnode α) (x : α) (r : Ordnode α) : dual (balance' l x r) = balance' (dual r) x (dual l) :=
  by
  simp [← balance', ← add_commₓ]
  split_ifs <;> simp [← dual_node', ← dual_rotate_l, ← dual_rotate_r]
  cases delta_lt_false h_1 h_2

theorem dual_balance_l (l : Ordnode α) (x : α) (r : Ordnode α) : dual (balanceL l x r) = balanceR (dual r) x (dual l) :=
  by
  unfold balance_l balance_r
  cases' r with rs rl rx rr
  · cases' l with ls ll lx lr
    · rfl
      
    cases' ll with lls lll llx llr <;>
      cases' lr with lrs lrl lrx lrr <;>
        dsimp' only [← dual] <;>
          try
            rfl
    split_ifs <;>
      repeat'
        simp [← h, ← add_commₓ]
    
  · cases' l with ls ll lx lr
    · rfl
      
    dsimp' only [← dual]
    split_ifs
    swap
    · simp [← add_commₓ]
      
    cases' ll with lls lll llx llr <;>
      cases' lr with lrs lrl lrx lrr <;>
        try
          rfl
    dsimp' only [← dual]
    split_ifs <;> simp [← h, ← add_commₓ]
    

theorem dual_balance_r (l : Ordnode α) (x : α) (r : Ordnode α) : dual (balanceR l x r) = balanceL (dual r) x (dual l) :=
  by
  rw [← dual_dual (balance_l _ _ _), dual_balance_l, dual_dual, dual_dual]

theorem Sized.node3_l {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r) : Sized (node3L l x m y r) :=
  (hl.node' hm).node' hr

theorem Sized.node3_r {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r) : Sized (node3R l x m y r) :=
  hl.node' (hm.node' hr)

theorem Sized.node4_l {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r) : Sized (node4L l x m y r) := by
  cases m <;> [exact (hl.node' hm).node' hr, exact (hl.node' hm.2.1).node' (hm.2.2.node' hr)]

theorem node3_l_size {l x m y r} : size (@node3L α l x m y r) = size l + size m + size r + 2 := by
  dsimp' [← node3_l, ← node', ← size] <;> rw [add_right_commₓ _ 1]

theorem node3_r_size {l x m y r} : size (@node3R α l x m y r) = size l + size m + size r + 2 := by
  dsimp' [← node3_r, ← node', ← size] <;> rw [← add_assocₓ, ← add_assocₓ]

theorem node4_l_size {l x m y r} (hm : Sized m) : size (@node4L α l x m y r) = size l + size m + size r + 2 := by
  cases m <;>
    simp [← node4_l, ← node3_l, ← node', ← add_commₓ, ← add_left_commₓ] <;> [skip, simp [← size, ← hm.1]] <;>
      rw [← add_assocₓ, ← bit0] <;> simp [← add_commₓ, ← add_left_commₓ]

theorem Sized.dual : ∀ {t : Ordnode α} (h : Sized t), Sized (dual t)
  | nil, h => ⟨⟩
  | node s l x r, ⟨rfl, sl, sr⟩ =>
    ⟨by
      simp [← size_dual, ← add_commₓ], sized.dual sr, sized.dual sl⟩

theorem Sized.dual_iff {t : Ordnode α} : Sized (dual t) ↔ Sized t :=
  ⟨fun h => by
    rw [← dual_dual t] <;> exact h.dual, Sized.dual⟩

theorem Sized.rotate_l {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (rotateL l x r) := by
  cases r
  · exact hl.node' hr
    
  rw [rotate_l]
  split_ifs
  · exact hl.node3_l hr.2.1 hr.2.2
    
  · exact hl.node4_l hr.2.1 hr.2.2
    

theorem Sized.rotate_r {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (rotateR l x r) :=
  Sized.dual_iff.1 <| by
    rw [dual_rotate_r] <;> exact hr.dual.rotate_l hl.dual

theorem Sized.rotate_l_size {l x r} (hm : Sized r) : size (@rotateL α l x r) = size l + size r + 1 := by
  cases r <;> simp [← rotate_l]
  simp [← size, ← hm.1, ← add_commₓ, ← add_left_commₓ]
  rw [← add_assocₓ, ← bit0]
  simp
  split_ifs <;> simp [← node3_l_size, ← node4_l_size hm.2.1, ← add_commₓ, ← add_left_commₓ]

theorem Sized.rotate_r_size {l x r} (hl : Sized l) : size (@rotateR α l x r) = size l + size r + 1 := by
  rw [← size_dual, dual_rotate_r, hl.dual.rotate_l_size, size_dual, size_dual, add_commₓ (size l)]

theorem Sized.balance' {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (balance' l x r) := by
  unfold balance'
  split_ifs
  · exact hl.node' hr
    
  · exact hl.rotate_l hr
    
  · exact hl.rotate_r hr
    
  · exact hl.node' hr
    

theorem size_balance' {l x r} (hl : @Sized α l) (hr : Sized r) : size (@balance' α l x r) = size l + size r + 1 := by
  unfold balance'
  split_ifs
  · rfl
    
  · exact hr.rotate_l_size
    
  · exact hl.rotate_r_size
    
  · rfl
    

/-! ## `all`, `any`, `emem`, `amem` -/


theorem All.imp {P Q : α → Prop} (H : ∀ a, P a → Q a) : ∀ {t}, All P t → All Q t
  | nil, h => ⟨⟩
  | node _ l x r, ⟨h₁, h₂, h₃⟩ => ⟨h₁.imp, H _ h₂, h₃.imp⟩

theorem Any.imp {P Q : α → Prop} (H : ∀ a, P a → Q a) : ∀ {t}, Any P t → Any Q t
  | nil => id
  | node _ l x r => Or.imp any.imp <| Or.imp (H _) any.imp

theorem all_singleton {P : α → Prop} {x : α} : All P (singleton x) ↔ P x :=
  ⟨fun h => h.2.1, fun h => ⟨⟨⟩, h, ⟨⟩⟩⟩

theorem any_singleton {P : α → Prop} {x : α} : Any P (singleton x) ↔ P x :=
  ⟨by
    rintro (⟨⟨⟩⟩ | h | ⟨⟨⟩⟩) <;> exact h, fun h => Or.inr (Or.inl h)⟩

theorem all_dual {P : α → Prop} : ∀ {t : Ordnode α}, All P (dual t) ↔ All P t
  | nil => Iff.rfl
  | node s l x r =>
    ⟨fun ⟨hr, hx, hl⟩ => ⟨all_dual.1 hl, hx, all_dual.1 hr⟩, fun ⟨hl, hx, hr⟩ => ⟨all_dual.2 hr, hx, all_dual.2 hl⟩⟩

theorem all_iff_forall {P : α → Prop} : ∀ {t}, All P t ↔ ∀ x, Emem x t → P x
  | nil =>
    (iff_true_intro <| by
        rintro _ ⟨⟩).symm
  | node _ l x r => by
    simp [← all, ← emem, ← all_iff_forall, ← any, ← or_imp_distrib, ← forall_and_distrib]

theorem any_iff_exists {P : α → Prop} : ∀ {t}, Any P t ↔ ∃ x, Emem x t ∧ P x
  | nil =>
    ⟨by
      rintro ⟨⟩, by
      rintro ⟨_, ⟨⟩, _⟩⟩
  | node _ l x r => by
    simp [← any, ← emem, ← any_iff_exists, ← or_and_distrib_right, ← exists_or_distrib]

theorem emem_iff_all {x : α} {t} : Emem x t ↔ ∀ P, All P t → P x :=
  ⟨fun h P al => all_iff_forall.1 al _ h, fun H => H _ <| all_iff_forall.2 fun _ => id⟩

theorem all_node' {P l x r} : @All α P (node' l x r) ↔ All P l ∧ P x ∧ All P r :=
  Iff.rfl

theorem all_node3_l {P l x m y r} : @All α P (node3L l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r := by
  simp [← node3_l, ← all_node', ← and_assoc]

theorem all_node3_r {P l x m y r} : @All α P (node3R l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r :=
  Iff.rfl

theorem all_node4_l {P l x m y r} : @All α P (node4L l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r := by
  cases m <;> simp [← node4_l, ← all_node', ← all, ← all_node3_l, ← and_assoc]

theorem all_node4_r {P l x m y r} : @All α P (node4R l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r := by
  cases m <;> simp [← node4_r, ← all_node', ← all, ← all_node3_r, ← and_assoc]

theorem all_rotate_l {P l x r} : @All α P (rotateL l x r) ↔ All P l ∧ P x ∧ All P r := by
  cases r <;> simp [← rotate_l, ← all_node'] <;> split_ifs <;> simp [← all_node3_l, ← all_node4_l, ← all]

theorem all_rotate_r {P l x r} : @All α P (rotateR l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [← all_dual, dual_rotate_r, all_rotate_l] <;> simp [← all_dual, ← and_comm, ← And.left_comm]

theorem all_balance' {P l x r} : @All α P (balance' l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [balance'] <;> split_ifs <;> simp [← all_node', ← all_rotate_l, ← all_rotate_r]

/-! ### `to_list` -/


theorem foldr_cons_eq_to_list : ∀ (t : Ordnode α) (r : List α), t.foldr List.cons r = toList t ++ r
  | nil, r => rfl
  | node _ l x r, r' => by
    rw [foldr, foldr_cons_eq_to_list, foldr_cons_eq_to_list, ← List.cons_append, ← List.append_assoc, ←
        foldr_cons_eq_to_list] <;>
      rfl

@[simp]
theorem to_list_nil : toList (@nil α) = [] :=
  rfl

@[simp]
theorem to_list_node (s l x r) : toList (@node α s l x r) = toList l ++ x :: toList r := by
  rw [to_list, foldr, foldr_cons_eq_to_list] <;> rfl

theorem emem_iff_mem_to_list {x : α} {t} : Emem x t ↔ x ∈ toList t := by
  unfold emem <;> induction t <;> simp [← any, *, ← or_assoc]

theorem length_to_list' : ∀ t : Ordnode α, (toList t).length = t.realSize
  | nil => rfl
  | node _ l _ r => by
    rw [to_list_node, List.length_append, List.length_cons, length_to_list', length_to_list'] <;> rfl

theorem length_to_list {t : Ordnode α} (h : Sized t) : (toList t).length = t.size := by
  rw [length_to_list', size_eq_real_size h]

theorem equiv_iff {t₁ t₂ : Ordnode α} (h₁ : Sized t₁) (h₂ : Sized t₂) : Equiv t₁ t₂ ↔ toList t₁ = toList t₂ :=
  and_iff_right_of_imp fun h => by
    rw [← length_to_list h₁, h, length_to_list h₂]

/-! ### `mem` -/


theorem pos_size_of_mem [LE α] [@DecidableRel α (· ≤ ·)] {x : α} {t : Ordnode α} (h : Sized t) (h_mem : x ∈ t) :
    0 < size t := by
  cases t
  · contradiction
    
  · simp [← h.1]
    

/-! ### `(find/erase/split)_(min/max)` -/


theorem find_min'_dual : ∀ (t) (x : α), findMin' (dual t) x = findMax' x t
  | nil, x => rfl
  | node _ l x r, _ => find_min'_dual r x

theorem find_max'_dual (t) (x : α) : findMax' x (dual t) = findMin' t x := by
  rw [← find_min'_dual, dual_dual]

theorem find_min_dual : ∀ t : Ordnode α, findMin (dual t) = findMax t
  | nil => rfl
  | node _ l x r => congr_arg some <| find_min'_dual _ _

theorem find_max_dual (t : Ordnode α) : findMax (dual t) = findMin t := by
  rw [← find_min_dual, dual_dual]

theorem dual_erase_min : ∀ t : Ordnode α, dual (eraseMin t) = eraseMax (dual t)
  | nil => rfl
  | node _ nil x r => rfl
  | node _ (l@(node _ _ _ _)) x r => by
    rw [erase_min, dual_balance_r, dual_erase_min, dual, dual, dual, erase_max]

theorem dual_erase_max (t : Ordnode α) : dual (eraseMax t) = eraseMin (dual t) := by
  rw [← dual_dual (erase_min _), dual_erase_min, dual_dual]

theorem split_min_eq : ∀ (s l) (x : α) (r), splitMin' l x r = (findMin' l x, eraseMin (node s l x r))
  | _, nil, x, r => rfl
  | _, node ls ll lx lr, x, r => by
    rw [split_min', split_min_eq, split_min', find_min', erase_min]

theorem split_max_eq : ∀ (s l) (x : α) (r), splitMax' l x r = (eraseMax (node s l x r), findMax' x r)
  | _, l, x, nil => rfl
  | _, l, x, node ls ll lx lr => by
    rw [split_max', split_max_eq, split_max', find_max', erase_max]

@[elab_as_eliminator]
theorem find_min'_all {P : α → Prop} : ∀ (t) (x : α), All P t → P x → P (findMin' t x)
  | nil, x, h, hx => hx
  | node _ ll lx lr, x, ⟨h₁, h₂, h₃⟩, hx => find_min'_all _ _ h₁ h₂

@[elab_as_eliminator]
theorem find_max'_all {P : α → Prop} : ∀ (x : α) (t), P x → All P t → P (findMax' x t)
  | x, nil, hx, h => hx
  | x, node _ ll lx lr, hx, ⟨h₁, h₂, h₃⟩ => find_max'_all _ _ h₂ h₃

/-! ### `glue` -/


/-! ### `merge` -/


@[simp]
theorem merge_nil_left (t : Ordnode α) : merge t nil = t := by
  cases t <;> rfl

@[simp]
theorem merge_nil_right (t : Ordnode α) : merge nil t = t :=
  rfl

@[simp]
theorem merge_node {ls ll lx lr rs rl rx rr} :
    merge (@node α ls ll lx lr) (node rs rl rx rr) =
      if delta * ls < rs then balanceL (merge (node ls ll lx lr) rl) rx rr
      else
        if delta * rs < ls then balanceR ll lx (merge lr (node rs rl rx rr))
        else glue (node ls ll lx lr) (node rs rl rx rr) :=
  rfl

/-! ### `insert` -/


theorem dual_insert [Preorderₓ α] [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) :
    ∀ t : Ordnode α, dual (Ordnode.insert x t) = @Ordnode.insert αᵒᵈ _ _ x (dual t)
  | nil => rfl
  | node _ l y r => by
    have : @cmpLe αᵒᵈ _ _ x y = cmpLe y x := rfl
    rw [Ordnode.insert, dual, Ordnode.insert, this, ← cmp_le_swap x y]
    cases cmpLe x y <;> simp [← Ordering.swap, ← Ordnode.insert, ← dual_balance_l, ← dual_balance_r, ← dual_insert]

/-! ### `balance` properties -/


theorem balance_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r) :
    @balance α l x r = balance' l x r := by
  cases' l with ls ll lx lr
  · cases' r with rs rl rx rr
    · rfl
      
    · rw [sr.eq_node'] at hr⊢
      cases' rl with rls rll rlx rlr <;> cases' rr with rrs rrl rrx rrr <;> dsimp' [← balance, ← balance']
      · rfl
        
      · have : size rrl = 0 ∧ size rrr = 0 := by
          have := balanced_sz_zero.1 hr.1.symm
          rwa [size, sr.2.2.1, Nat.succ_le_succ_iff, Nat.le_zero_iffₓ, add_eq_zero_iff] at this
        cases sr.2.2.2.1.size_eq_zero.1 this.1
        cases sr.2.2.2.2.size_eq_zero.1 this.2
        obtain rfl : rrs = 1 := sr.2.2.1
        rw [if_neg, if_pos, rotate_l, if_pos]
        · rfl
          
        all_goals
          exact by
            decide
        
      · have : size rll = 0 ∧ size rlr = 0 := by
          have := balanced_sz_zero.1 hr.1
          rwa [size, sr.2.1.1, Nat.succ_le_succ_iff, Nat.le_zero_iffₓ, add_eq_zero_iff] at this
        cases sr.2.1.2.1.size_eq_zero.1 this.1
        cases sr.2.1.2.2.size_eq_zero.1 this.2
        obtain rfl : rls = 1 := sr.2.1.1
        rw [if_neg, if_pos, rotate_l, if_neg]
        · rfl
          
        all_goals
          exact by
            decide
        
      · symm
        rw [zero_addₓ, if_neg, if_pos, rotate_l]
        · split_ifs
          · simp [← node3_l, ← node', ← add_commₓ, ← add_left_commₓ]
            
          · simp [← node4_l, ← node', ← sr.2.1.1, ← add_commₓ, ← add_left_commₓ]
            
          
        · exact by
            decide
          
        · exact not_le_of_gtₓ (Nat.succ_lt_succₓ (add_pos sr.2.1.Pos sr.2.2.Pos))
          
        
      
    
  · cases' r with rs rl rx rr
    · rw [sl.eq_node'] at hl⊢
      cases' ll with lls lll llx llr <;> cases' lr with lrs lrl lrx lrr <;> dsimp' [← balance, ← balance']
      · rfl
        
      · have : size lrl = 0 ∧ size lrr = 0 := by
          have := balanced_sz_zero.1 hl.1.symm
          rwa [size, sl.2.2.1, Nat.succ_le_succ_iff, Nat.le_zero_iffₓ, add_eq_zero_iff] at this
        cases sl.2.2.2.1.size_eq_zero.1 this.1
        cases sl.2.2.2.2.size_eq_zero.1 this.2
        obtain rfl : lrs = 1 := sl.2.2.1
        rw [if_neg, if_neg, if_pos, rotate_r, if_neg]
        · rfl
          
        all_goals
          exact by
            decide
        
      · have : size lll = 0 ∧ size llr = 0 := by
          have := balanced_sz_zero.1 hl.1
          rwa [size, sl.2.1.1, Nat.succ_le_succ_iff, Nat.le_zero_iffₓ, add_eq_zero_iff] at this
        cases sl.2.1.2.1.size_eq_zero.1 this.1
        cases sl.2.1.2.2.size_eq_zero.1 this.2
        obtain rfl : lls = 1 := sl.2.1.1
        rw [if_neg, if_neg, if_pos, rotate_r, if_pos]
        · rfl
          
        all_goals
          exact by
            decide
        
      · symm
        rw [if_neg, if_neg, if_pos, rotate_r]
        · split_ifs
          · simp [← node3_r, ← node', ← add_commₓ, ← add_left_commₓ]
            
          · simp [← node4_r, ← node', ← sl.2.2.1, ← add_commₓ, ← add_left_commₓ]
            
          
        · exact by
            decide
          
        · exact by
            decide
          
        · exact not_le_of_gtₓ (Nat.succ_lt_succₓ (add_pos sl.2.1.Pos sl.2.2.Pos))
          
        
      
    · simp [← balance, ← balance']
      symm
      rw [if_neg]
      · split_ifs
        · have rd : delta ≤ size rl + size rr := by
            have := lt_of_le_of_ltₓ (Nat.mul_le_mul_leftₓ _ sl.pos) h
            rwa [sr.1, Nat.lt_succ_iffₓ] at this
          cases' rl with rls rll rlx rlr
          · rw [size, zero_addₓ] at rd
            exact
              absurd (le_transₓ rd (balanced_sz_zero.1 hr.1.symm))
                (by
                  decide)
            
          cases' rr with rrs rrl rrx rrr
          · exact
              absurd (le_transₓ rd (balanced_sz_zero.1 hr.1))
                (by
                  decide)
            
          dsimp' [← rotate_l]
          split_ifs
          · simp [← node3_l, ← node', ← sr.1, ← add_commₓ, ← add_left_commₓ]
            
          · simp [← node4_l, ← node', ← sr.1, ← sr.2.1.1, ← add_commₓ, ← add_left_commₓ]
            
          
        · have ld : delta ≤ size ll + size lr := by
            have := lt_of_le_of_ltₓ (Nat.mul_le_mul_leftₓ _ sr.pos) h_1
            rwa [sl.1, Nat.lt_succ_iffₓ] at this
          cases' ll with lls lll llx llr
          · rw [size, zero_addₓ] at ld
            exact
              absurd (le_transₓ ld (balanced_sz_zero.1 hl.1.symm))
                (by
                  decide)
            
          cases' lr with lrs lrl lrx lrr
          · exact
              absurd (le_transₓ ld (balanced_sz_zero.1 hl.1))
                (by
                  decide)
            
          dsimp' [← rotate_r]
          split_ifs
          · simp [← node3_r, ← node', ← sl.1, ← add_commₓ, ← add_left_commₓ]
            
          · simp [← node4_r, ← node', ← sl.1, ← sl.2.2.1, ← add_commₓ, ← add_left_commₓ]
            
          
        · simp [← node']
          
        
      · exact not_le_of_gtₓ (add_le_add sl.pos sr.pos : 2 ≤ ls + rs)
        
      
    

theorem balance_l_eq_balance {l x r} (sl : Sized l) (sr : Sized r) (H1 : size l = 0 → size r ≤ 1)
    (H2 : 1 ≤ size l → 1 ≤ size r → size r ≤ delta * size l) : @balanceL α l x r = balance l x r := by
  cases' r with rs rl rx rr
  · rfl
    
  · cases' l with ls ll lx lr
    · have : size rl = 0 ∧ size rr = 0 := by
        have := H1 rfl
        rwa [size, sr.1, Nat.succ_le_succ_iff, Nat.le_zero_iffₓ, add_eq_zero_iff] at this
      cases sr.2.1.size_eq_zero.1 this.1
      cases sr.2.2.size_eq_zero.1 this.2
      rw [sr.eq_node']
      rfl
      
    · replace H2 : ¬rs > delta * ls := not_lt_of_le (H2 sl.pos sr.pos)
      simp [← balance_l, ← balance, ← H2] <;> split_ifs <;> simp [← add_commₓ]
      
    

/-- `raised n m` means `m` is either equal or one up from `n`. -/
def Raised (n m : ℕ) : Prop :=
  m = n ∨ m = n + 1

theorem raised_iff {n m} : Raised n m ↔ n ≤ m ∧ m ≤ n + 1 := by
  constructor
  rintro (rfl | rfl)
  · exact ⟨le_rfl, Nat.le_succₓ _⟩
    
  · exact ⟨Nat.le_succₓ _, le_rfl⟩
    
  · rintro ⟨h₁, h₂⟩
    rcases eq_or_lt_of_le h₁ with (rfl | h₁)
    · exact Or.inl rfl
      
    · exact Or.inr (le_antisymmₓ h₂ h₁)
      
    

theorem Raised.dist_le {n m} (H : Raised n m) : Nat.dist n m ≤ 1 := by
  cases' raised_iff.1 H with H1 H2 <;> rwa [Nat.dist_eq_sub_of_le H1, tsub_le_iff_left]

theorem Raised.dist_le' {n m} (H : Raised n m) : Nat.dist m n ≤ 1 := by
  rw [Nat.dist_comm] <;> exact H.dist_le

theorem Raised.add_left (k) {n m} (H : Raised n m) : Raised (k + n) (k + m) := by
  rcases H with (rfl | rfl)
  · exact Or.inl rfl
    
  · exact Or.inr rfl
    

theorem Raised.add_right (k) {n m} (H : Raised n m) : Raised (n + k) (m + k) := by
  rw [add_commₓ, add_commₓ m] <;> exact H.add_left _

theorem Raised.right {l x₁ x₂ r₁ r₂} (H : Raised (size r₁) (size r₂)) :
    Raised (size (@node' α l x₁ r₁)) (size (@node' α l x₂ r₂)) := by
  dsimp' [← node', ← size]
  generalize size r₂ = m  at H⊢
  rcases H with (rfl | rfl)
  · exact Or.inl rfl
    
  · exact Or.inr rfl
    

theorem balance_l_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H : (∃ l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨ ∃ r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    @balanceL α l x r = balance' l x r := by
  rw [← balance_eq_balance' hl hr sl sr, balance_l_eq_balance sl sr]
  · intro l0
    rw [l0] at H
    rcases H with (⟨_, ⟨⟨⟩⟩ | ⟨⟨⟩⟩, H⟩ | ⟨r', e, H⟩)
    · exact balanced_sz_zero.1 H.symm
      
    exact le_transₓ (raised_iff.1 e).1 (balanced_sz_zero.1 H.symm)
    
  · intro l1 r1
    rcases H with (⟨l', e, H | ⟨H₁, H₂⟩⟩ | ⟨r', e, H | ⟨H₁, H₂⟩⟩)
    · exact
        le_transₓ (le_transₓ (Nat.le_add_leftₓ _ _) H)
          (mul_pos
            (by
              decide)
            l1 :
            (0 : ℕ) < _)
      
    · exact le_transₓ H₂ (Nat.mul_le_mul_leftₓ _ (raised_iff.1 e).1)
      
    · cases raised_iff.1 e
      unfold delta
      linarith
      
    · exact le_transₓ (raised_iff.1 e).1 H₂
      
    

theorem balance_sz_dual {l r}
    (H :
      (∃ l', Raised (@size α l) l' ∧ BalancedSz l' (@size α r)) ∨ ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    (∃ l', Raised l' (size (dual r)) ∧ BalancedSz l' (size (dual l))) ∨
      ∃ r', Raised (size (dual l)) r' ∧ BalancedSz (size (dual r)) r' :=
  by
  rw [size_dual, size_dual]
  exact
    H.symm.imp (Exists.imp fun _ => And.imp_right balanced_sz.symm) (Exists.imp fun _ => And.imp_right balanced_sz.symm)

theorem size_balance_l {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H : (∃ l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨ ∃ r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    size (@balanceL α l x r) = size l + size r + 1 := by
  rw [balance_l_eq_balance' hl hr sl sr H, size_balance' sl sr]

theorem all_balance_l {P l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H : (∃ l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨ ∃ r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    All P (@balanceL α l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [balance_l_eq_balance' hl hr sl sr H, all_balance']

theorem balance_r_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H : (∃ l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨ ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    @balanceR α l x r = balance' l x r := by
  rw [← dual_dual (balance_r l x r), dual_balance_r,
    balance_l_eq_balance' hr.dual hl.dual sr.dual sl.dual (balance_sz_dual H), ← dual_balance', dual_dual]

theorem size_balance_r {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H : (∃ l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨ ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    size (@balanceR α l x r) = size l + size r + 1 := by
  rw [balance_r_eq_balance' hl hr sl sr H, size_balance' sl sr]

theorem all_balance_r {P l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H : (∃ l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨ ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    All P (@balanceR α l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [balance_r_eq_balance' hl hr sl sr H, all_balance']

/-! ### `bounded` -/


section

variable [Preorderₓ α]

/-- `bounded t lo hi` says that every element `x ∈ t` is in the range `lo < x < hi`, and also this
property holds recursively in subtrees, making the full tree a BST. The bounds can be set to
`lo = ⊥` and `hi = ⊤` if we care only about the internal ordering constraints. -/
def Bounded : Ordnode α → WithBot α → WithTop α → Prop
  | nil, some a, some b => a < b
  | nil, _, _ => True
  | node _ l x r, o₁, o₂ => bounded l o₁ ↑x ∧ bounded r (↑x) o₂

theorem Bounded.dual : ∀ {t : Ordnode α} {o₁ o₂} (h : Bounded t o₁ o₂), @Bounded αᵒᵈ _ (dual t) o₂ o₁
  | nil, o₁, o₂, h => by
    cases o₁ <;>
      cases o₂ <;>
        try
            trivial <;>
          exact h
  | node s l x r, _, _, ⟨ol, Or⟩ => ⟨Or.dual, ol.dual⟩

theorem Bounded.dual_iff {t : Ordnode α} {o₁ o₂} : Bounded t o₁ o₂ ↔ @Bounded αᵒᵈ _ (dual t) o₂ o₁ :=
  ⟨Bounded.dual, fun h => by
    have := bounded.dual h <;> rwa [dual_dual, OrderDual.preorder.dual_dual] at this⟩

theorem Bounded.weak_left : ∀ {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ → Bounded t ⊥ o₂
  | nil, o₁, o₂, h => by
    cases o₂ <;>
      try
          trivial <;>
        exact h
  | node s l x r, _, _, ⟨ol, Or⟩ => ⟨ol.weak_left, Or⟩

theorem Bounded.weak_right : ∀ {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ → Bounded t o₁ ⊤
  | nil, o₁, o₂, h => by
    cases o₁ <;>
      try
          trivial <;>
        exact h
  | node s l x r, _, _, ⟨ol, Or⟩ => ⟨ol, Or.weak_right⟩

theorem Bounded.weak {t : Ordnode α} {o₁ o₂} (h : Bounded t o₁ o₂) : Bounded t ⊥ ⊤ :=
  h.weak_left.weak_right

theorem Bounded.mono_left {x y : α} (xy : x ≤ y) : ∀ {t : Ordnode α} {o}, Bounded t (↑y) o → Bounded t (↑x) o
  | nil, none, h => ⟨⟩
  | nil, some z, h => lt_of_le_of_ltₓ xy h
  | node s l z r, o, ⟨ol, Or⟩ => ⟨ol.mono_left, Or⟩

theorem Bounded.mono_right {x y : α} (xy : x ≤ y) : ∀ {t : Ordnode α} {o}, Bounded t o ↑x → Bounded t o ↑y
  | nil, none, h => ⟨⟩
  | nil, some z, h => lt_of_lt_of_leₓ h xy
  | node s l z r, o, ⟨ol, Or⟩ => ⟨ol, Or.mono_right⟩

theorem Bounded.to_lt : ∀ {t : Ordnode α} {x y : α}, Bounded t x y → x < y
  | nil, x, y, h => h
  | node _ l y r, x, z, ⟨h₁, h₂⟩ => lt_transₓ h₁.to_lt h₂.to_lt

theorem Bounded.to_nil {t : Ordnode α} : ∀ {o₁ o₂}, Bounded t o₁ o₂ → Bounded nil o₁ o₂
  | none, _, h => ⟨⟩
  | some _, none, h => ⟨⟩
  | some x, some y, h => h.to_lt

theorem Bounded.trans_left {t₁ t₂ : Ordnode α} {x : α} :
    ∀ {o₁ o₂}, Bounded t₁ o₁ ↑x → Bounded t₂ (↑x) o₂ → Bounded t₂ o₁ o₂
  | none, o₂, h₁, h₂ => h₂.weak_left
  | some y, o₂, h₁, h₂ => h₂.mono_left (le_of_ltₓ h₁.to_lt)

theorem Bounded.trans_right {t₁ t₂ : Ordnode α} {x : α} :
    ∀ {o₁ o₂}, Bounded t₁ o₁ ↑x → Bounded t₂ (↑x) o₂ → Bounded t₁ o₁ o₂
  | o₁, none, h₁, h₂ => h₁.weak_right
  | o₁, some y, h₁, h₂ => h₁.mono_right (le_of_ltₓ h₂.to_lt)

theorem Bounded.mem_lt : ∀ {t o} {x : α}, Bounded t o ↑x → All (· < x) t
  | nil, o, x, _ => ⟨⟩
  | node _ l y r, o, x, ⟨h₁, h₂⟩ => ⟨h₁.mem_lt.imp fun z h => lt_transₓ h h₂.to_lt, h₂.to_lt, h₂.mem_lt⟩

theorem Bounded.mem_gt : ∀ {t o} {x : α}, Bounded t (↑x) o → All (· > x) t
  | nil, o, x, _ => ⟨⟩
  | node _ l y r, o, x, ⟨h₁, h₂⟩ => ⟨h₁.mem_gt, h₁.to_lt, h₂.mem_gt.imp fun z => lt_transₓ h₁.to_lt⟩

theorem Bounded.of_lt : ∀ {t o₁ o₂} {x : α}, Bounded t o₁ o₂ → Bounded nil o₁ ↑x → All (· < x) t → Bounded t o₁ ↑x
  | nil, o₁, o₂, x, _, hn, _ => hn
  | node _ l y r, o₁, o₂, x, ⟨h₁, h₂⟩, hn, ⟨al₁, al₂, al₃⟩ => ⟨h₁, h₂.of_lt al₂ al₃⟩

theorem Bounded.of_gt : ∀ {t o₁ o₂} {x : α}, Bounded t o₁ o₂ → Bounded nil (↑x) o₂ → All (· > x) t → Bounded t (↑x) o₂
  | nil, o₁, o₂, x, _, hn, _ => hn
  | node _ l y r, o₁, o₂, x, ⟨h₁, h₂⟩, hn, ⟨al₁, al₂, al₃⟩ => ⟨h₁.of_gt al₂ al₁, h₂⟩

theorem Bounded.to_sep {t₁ t₂ o₁ o₂} {x : α} (h₁ : Bounded t₁ o₁ ↑x) (h₂ : Bounded t₂ (↑x) o₂) :
    t₁.all fun y => t₂.all fun z : α => y < z :=
  h₁.mem_lt.imp fun y yx => h₂.mem_gt.imp fun z xz => lt_transₓ yx xz

end

/-! ### `valid` -/


section

variable [Preorderₓ α]

/-- The validity predicate for an `ordnode` subtree. This asserts that the `size` fields are
correct, the tree is balanced, and the elements of the tree are organized according to the
ordering. This version of `valid` also puts all elements in the tree in the interval `(lo, hi)`. -/
structure Valid' (lo : WithBot α) (t : Ordnode α) (hi : WithTop α) : Prop where
  ord : t.Bounded lo hi
  sz : t.Sized
  bal : t.Balanced

/-- The validity predicate for an `ordnode` subtree. This asserts that the `size` fields are
correct, the tree is balanced, and the elements of the tree are organized according to the
ordering. -/
def Valid (t : Ordnode α) : Prop :=
  Valid' ⊥ t ⊤

theorem Valid'.mono_left {x y : α} (xy : x ≤ y) {t : Ordnode α} {o} (h : Valid' (↑y) t o) : Valid' (↑x) t o :=
  ⟨h.1.mono_left xy, h.2, h.3⟩

theorem Valid'.mono_right {x y : α} (xy : x ≤ y) {t : Ordnode α} {o} (h : Valid' o t ↑x) : Valid' o t ↑y :=
  ⟨h.1.mono_right xy, h.2, h.3⟩

theorem Valid'.trans_left {t₁ t₂ : Ordnode α} {x : α} {o₁ o₂} (h : Bounded t₁ o₁ ↑x) (H : Valid' (↑x) t₂ o₂) :
    Valid' o₁ t₂ o₂ :=
  ⟨h.trans_left H.1, H.2, H.3⟩

theorem Valid'.trans_right {t₁ t₂ : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t₁ ↑x) (h : Bounded t₂ (↑x) o₂) :
    Valid' o₁ t₁ o₂ :=
  ⟨H.1.trans_right h, H.2, H.3⟩

theorem Valid'.of_lt {t : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t o₂) (h₁ : Bounded nil o₁ ↑x)
    (h₂ : All (· < x) t) : Valid' o₁ t ↑x :=
  ⟨H.1.of_lt h₁ h₂, H.2, H.3⟩

theorem Valid'.of_gt {t : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t o₂) (h₁ : Bounded nil (↑x) o₂)
    (h₂ : All (· > x) t) : Valid' (↑x) t o₂ :=
  ⟨H.1.of_gt h₁ h₂, H.2, H.3⟩

theorem Valid'.valid {t o₁ o₂} (h : @Valid' α _ o₁ t o₂) : Valid t :=
  ⟨h.1.weak, h.2, h.3⟩

theorem valid'_nil {o₁ o₂} (h : Bounded nil o₁ o₂) : Valid' o₁ (@nil α) o₂ :=
  ⟨h, ⟨⟩, ⟨⟩⟩

theorem valid_nil : Valid (@nil α) :=
  valid'_nil ⟨⟩

theorem Valid'.node {s l x r o₁ o₂} (hl : Valid' o₁ l ↑x) (hr : Valid' (↑x) r o₂) (H : BalancedSz (size l) (size r))
    (hs : s = size l + size r + 1) : Valid' o₁ (@node α s l x r) o₂ :=
  ⟨⟨hl.1, hr.1⟩, ⟨hs, hl.2, hr.2⟩, ⟨H, hl.3, hr.3⟩⟩

theorem Valid'.dual : ∀ {t : Ordnode α} {o₁ o₂} (h : Valid' o₁ t o₂), @Valid' αᵒᵈ _ o₂ (dual t) o₁
  | nil, o₁, o₂, h => valid'_nil h.1.dual
  | node s l x r, o₁, o₂, ⟨⟨ol, Or⟩, ⟨rfl, sl, sr⟩, ⟨b, bl, br⟩⟩ =>
    let ⟨ol', sl', bl'⟩ := valid'.dual ⟨ol, sl, bl⟩
    let ⟨or', sr', br'⟩ := valid'.dual ⟨Or, sr, br⟩
    ⟨⟨or', ol'⟩,
      ⟨by
        simp [← size_dual, ← add_commₓ], sr', sl'⟩,
      ⟨by
        rw [size_dual, size_dual] <;> exact b.symm, br', bl'⟩⟩

theorem Valid'.dual_iff {t : Ordnode α} {o₁ o₂} : Valid' o₁ t o₂ ↔ @Valid' αᵒᵈ _ o₂ (dual t) o₁ :=
  ⟨Valid'.dual, fun h => by
    have := valid'.dual h <;> rwa [dual_dual, OrderDual.preorder.dual_dual] at this⟩

theorem Valid.dual {t : Ordnode α} : Valid t → @Valid αᵒᵈ _ (dual t) :=
  valid'.dual

theorem Valid.dual_iff {t : Ordnode α} : Valid t ↔ @Valid αᵒᵈ _ (dual t) :=
  valid'.dual_iff

theorem Valid'.left {s l x r o₁ o₂} (H : Valid' o₁ (@node α s l x r) o₂) : Valid' o₁ l x :=
  ⟨H.1.1, H.2.2.1, H.3.2.1⟩

theorem Valid'.right {s l x r o₁ o₂} (H : Valid' o₁ (@node α s l x r) o₂) : Valid' (↑x) r o₂ :=
  ⟨H.1.2, H.2.2.2, H.3.2.2⟩

theorem Valid.left {s l x r} (H : Valid (@node α s l x r)) : Valid l :=
  H.left.valid

theorem Valid.right {s l x r} (H : Valid (@node α s l x r)) : Valid r :=
  H.right.valid

theorem Valid.size_eq {s l x r} (H : Valid (@node α s l x r)) : size (@node α s l x r) = size l + size r + 1 :=
  H.2.1

theorem Valid'.node' {l x r o₁ o₂} (hl : Valid' o₁ l ↑x) (hr : Valid' (↑x) r o₂) (H : BalancedSz (size l) (size r)) :
    Valid' o₁ (@node' α l x r) o₂ :=
  hl.node hr H rfl

theorem valid'_singleton {x : α} {o₁ o₂} (h₁ : Bounded nil o₁ ↑x) (h₂ : Bounded nil (↑x) o₂) :
    Valid' o₁ (singleton x : Ordnode α) o₂ :=
  (valid'_nil h₁).node (valid'_nil h₂) (Or.inl zero_le_one) rfl

theorem valid_singleton {x : α} : Valid (singleton x : Ordnode α) :=
  valid'_singleton ⟨⟩ ⟨⟩

theorem Valid'.node3_l {l x m y r o₁ o₂} (hl : Valid' o₁ l ↑x) (hm : Valid' (↑x) m ↑y) (hr : Valid' (↑y) r o₂)
    (H1 : BalancedSz (size l) (size m)) (H2 : BalancedSz (size l + size m + 1) (size r)) :
    Valid' o₁ (@node3L α l x m y r) o₂ :=
  (hl.node' hm H1).node' hr H2

theorem Valid'.node3_r {l x m y r o₁ o₂} (hl : Valid' o₁ l ↑x) (hm : Valid' (↑x) m ↑y) (hr : Valid' (↑y) r o₂)
    (H1 : BalancedSz (size l) (size m + size r + 1)) (H2 : BalancedSz (size m) (size r)) :
    Valid' o₁ (@node3R α l x m y r) o₂ :=
  hl.node' (hm.node' hr H2) H1

theorem Valid'.node4_l_lemma₁ {a b c d : ℕ} (lr₂ : 3 * (b + c + 1 + d) ≤ 16 * a + 9) (mr₂ : b + c + 1 ≤ 3 * d)
    (mm₁ : b ≤ 3 * c) : b < 3 * a + 1 := by
  linarith

theorem Valid'.node4_l_lemma₂ {b c d : ℕ} (mr₂ : b + c + 1 ≤ 3 * d) : c ≤ 3 * d := by
  linarith

theorem Valid'.node4_l_lemma₃ {b c d : ℕ} (mr₁ : 2 * d ≤ b + c + 1) (mm₁ : b ≤ 3 * c) : d ≤ 3 * c := by
  linarith

theorem Valid'.node4_l_lemma₄ {a b c d : ℕ} (lr₁ : 3 * a ≤ b + c + 1 + d) (mr₂ : b + c + 1 ≤ 3 * d) (mm₁ : b ≤ 3 * c) :
    a + b + 1 ≤ 3 * (c + d + 1) := by
  linarith

theorem Valid'.node4_l_lemma₅ {a b c d : ℕ} (lr₂ : 3 * (b + c + 1 + d) ≤ 16 * a + 9) (mr₁ : 2 * d ≤ b + c + 1)
    (mm₂ : c ≤ 3 * b) : c + d + 1 ≤ 3 * (a + b + 1) := by
  linarith

theorem Valid'.node4_l {l x m y r o₁ o₂} (hl : Valid' o₁ l ↑x) (hm : Valid' (↑x) m ↑y) (hr : Valid' (↑y) r o₂)
    (Hm : 0 < size m)
    (H :
      size l = 0 ∧ size m = 1 ∧ size r ≤ 1 ∨
        0 < size l ∧
          ratio * size r ≤ size m ∧
            delta * size l ≤ size m + size r ∧ 3 * (size m + size r) ≤ 16 * size l + 9 ∧ size m ≤ delta * size r) :
    Valid' o₁ (@node4L α l x m y r) o₂ := by
  cases' m with s ml z mr
  · cases Hm
    
  suffices :
    balanced_sz (size l) (size ml) ∧
      balanced_sz (size mr) (size r) ∧ balanced_sz (size l + size ml + 1) (size mr + size r + 1)
  exact valid'.node' (hl.node' hm.left this.1) (hm.right.node' hr this.2.1) this.2.2
  rcases H with (⟨l0, m1, r0⟩ | ⟨l0, mr₁, lr₁, lr₂, mr₂⟩)
  · rw [hm.2.size_eq, Nat.succ_inj', add_eq_zero_iff] at m1
    rw [l0, m1.1, m1.2]
    rcases size r with (_ | _ | _) <;>
      exact by
        decide
    
  · cases' Nat.eq_zero_or_posₓ (size r) with r0 r0
    · rw [r0] at mr₂
      cases not_le_of_lt Hm mr₂
      
    rw [hm.2.size_eq] at lr₁ lr₂ mr₁ mr₂
    by_cases' mm : size ml + size mr ≤ 1
    · have r1 :=
        le_antisymmₓ
          ((mul_le_mul_left
                (by
                  decide)).1
            (le_transₓ mr₁ (Nat.succ_le_succₓ mm) : _ ≤ ratio * 1))
          r0
      rw [r1, add_assocₓ] at lr₁
      have l1 :=
        le_antisymmₓ
          ((mul_le_mul_left
                (by
                  decide)).1
            (le_transₓ lr₁ (add_le_add_right mm 2) : _ ≤ delta * 1))
          l0
      rw [l1, r1]
      cases size ml <;> cases size mr
      · exact by
          decide
        
      · rw [zero_addₓ] at mm
        rcases mm with (_ | ⟨_, ⟨⟩⟩)
        exact by
          decide
        
      · rcases mm with (_ | ⟨_, ⟨⟩⟩)
        exact by
          decide
        
      · rw [Nat.succ_add] at mm
        rcases mm with (_ | ⟨_, ⟨⟩⟩)
        
      
    rcases hm.3.1.resolve_left mm with ⟨mm₁, mm₂⟩
    cases' Nat.eq_zero_or_posₓ (size ml) with ml0 ml0
    · rw [ml0, mul_zero, Nat.le_zero_iffₓ] at mm₂
      rw [ml0, mm₂] at mm
      cases
        mm
          (by
            decide)
      
    have : 2 * size l ≤ size ml + size mr + 1 := by
      have := Nat.mul_le_mul_leftₓ _ lr₁
      rw [mul_left_commₓ, mul_addₓ] at this
      have := le_transₓ this (add_le_add_left mr₁ _)
      rw [← Nat.succ_mul] at this
      exact
        (mul_le_mul_left
              (by
                decide)).1
          this
    refine' ⟨Or.inr ⟨_, _⟩, Or.inr ⟨_, _⟩, Or.inr ⟨_, _⟩⟩
    · refine'
        (mul_le_mul_left
              (by
                decide)).1
          (le_transₓ this _)
      rw [two_mul, Nat.succ_le_iff]
      refine' add_lt_add_of_lt_of_le _ mm₂
      simpa using
        (mul_lt_mul_right ml0).2
          (by
            decide : 1 < 3)
      
    · exact Nat.le_of_lt_succₓ (valid'.node4_l_lemma₁ lr₂ mr₂ mm₁)
      
    · exact valid'.node4_l_lemma₂ mr₂
      
    · exact valid'.node4_l_lemma₃ mr₁ mm₁
      
    · exact valid'.node4_l_lemma₄ lr₁ mr₂ mm₁
      
    · exact valid'.node4_l_lemma₅ lr₂ mr₁ mm₂
      
    

theorem Valid'.rotate_l_lemma₁ {a b c : ℕ} (H2 : 3 * a ≤ b + c) (hb₂ : c ≤ 3 * b) : a ≤ 3 * b := by
  linarith

theorem Valid'.rotate_l_lemma₂ {a b c : ℕ} (H3 : 2 * (b + c) ≤ 9 * a + 3) (h : b < 2 * c) : b < 3 * a + 1 := by
  linarith

theorem Valid'.rotate_l_lemma₃ {a b c : ℕ} (H2 : 3 * a ≤ b + c) (h : b < 2 * c) : a + b < 3 * c := by
  linarith

theorem Valid'.rotate_l_lemma₄ {a b : ℕ} (H3 : 2 * b ≤ 9 * a + 3) : 3 * b ≤ 16 * a + 9 := by
  linarith

theorem Valid'.rotate_l {l x r o₁ o₂} (hl : Valid' o₁ l ↑x) (hr : Valid' (↑x) r o₂) (H1 : ¬size l + size r ≤ 1)
    (H2 : delta * size l < size r) (H3 : 2 * size r ≤ 9 * size l + 5 ∨ size r ≤ 3) : Valid' o₁ (@rotateL α l x r) o₂ :=
  by
  cases' r with rs rl rx rr
  · cases H2
    
  rw [hr.2.size_eq, Nat.lt_succ_iffₓ] at H2
  rw [hr.2.size_eq] at H3
  replace H3 : 2 * (size rl + size rr) ≤ 9 * size l + 3 ∨ size rl + size rr ≤ 2 :=
    H3.imp (@Nat.le_of_add_le_add_rightₓ 2 _ _) Nat.le_of_succ_le_succₓ
  have H3_0 : size l = 0 → size rl + size rr ≤ 2 := by
    intro l0
    rw [l0] at H3
    exact
      (or_iff_right_of_imp fun h =>
            (mul_le_mul_left
                  (by
                    decide)).1
              (le_transₓ h
                (by
                  decide))).1
        H3
  have H3p : size l > 0 → 2 * (size rl + size rr) ≤ 9 * size l + 3 := fun l0 : 1 ≤ size l =>
    (or_iff_left_of_imp <| by
          intro <;> linarith).1
      H3
  have ablem : ∀ {a b : ℕ}, 1 ≤ a → a + b ≤ 2 → b ≤ 1 := by
    intros
    linarith
  have hlp : size l > 0 → ¬size rl + size rr ≤ 1 := fun l0 hb =>
    absurd (le_transₓ (le_transₓ (Nat.mul_le_mul_leftₓ _ l0) H2) hb)
      (by
        decide)
  rw [rotate_l]
  split_ifs
  · have rr0 : size rr > 0 :=
      (mul_lt_mul_left
            (by
              decide)).1
        (lt_of_le_of_ltₓ (Nat.zero_leₓ _) h : ratio * 0 < _)
    suffices balanced_sz (size l) (size rl) ∧ balanced_sz (size l + size rl + 1) (size rr) by
      exact hl.node3_l hr.left hr.right this.1 this.2
    cases' Nat.eq_zero_or_posₓ (size l) with l0 l0
    · rw [l0]
      replace H3 := H3_0 l0
      have := hr.3.1
      cases' Nat.eq_zero_or_posₓ (size rl) with rl0 rl0
      · rw [rl0] at this⊢
        rw [le_antisymmₓ (balanced_sz_zero.1 this.symm) rr0]
        exact by
          decide
        
      have rr1 : size rr = 1 := le_antisymmₓ (ablem rl0 H3) rr0
      rw [add_commₓ] at H3
      rw [rr1, show size rl = 1 from le_antisymmₓ (ablem rr0 H3) rl0]
      exact by
        decide
      
    replace H3 := H3p l0
    rcases hr.3.1.resolve_left (hlp l0) with ⟨hb₁, hb₂⟩
    refine' ⟨Or.inr ⟨_, _⟩, Or.inr ⟨_, _⟩⟩
    · exact valid'.rotate_l_lemma₁ H2 hb₂
      
    · exact Nat.le_of_lt_succₓ (valid'.rotate_l_lemma₂ H3 h)
      
    · exact valid'.rotate_l_lemma₃ H2 h
      
    · exact le_transₓ hb₂ (Nat.mul_le_mul_leftₓ _ <| le_transₓ (Nat.le_add_leftₓ _ _) (Nat.le_add_rightₓ _ _))
      
    
  · cases' Nat.eq_zero_or_posₓ (size rl) with rl0 rl0
    · rw [rl0, not_ltₓ, Nat.le_zero_iffₓ, Nat.mul_eq_zero] at h
      replace h :=
        h.resolve_left
          (by
            decide)
      rw [rl0, h, Nat.le_zero_iffₓ, Nat.mul_eq_zero] at H2
      rw [hr.2.size_eq, rl0, h,
        H2.resolve_left
          (by
            decide)] at
        H1
      cases
        H1
          (by
            decide)
      
    refine' hl.node4_l hr.left hr.right rl0 _
    cases' Nat.eq_zero_or_posₓ (size l) with l0 l0
    · replace H3 := H3_0 l0
      cases' Nat.eq_zero_or_posₓ (size rr) with rr0 rr0
      · have := hr.3.1
        rw [rr0] at this
        exact Or.inl ⟨l0, le_antisymmₓ (balanced_sz_zero.1 this) rl0, rr0.symm ▸ zero_le_one⟩
        
      exact
        Or.inl
          ⟨l0,
            le_antisymmₓ
              (ablem rr0 <| by
                rwa [add_commₓ])
              rl0,
            ablem rl0 H3⟩
      
    exact Or.inr ⟨l0, not_ltₓ.1 h, H2, valid'.rotate_l_lemma₄ (H3p l0), (hr.3.1.resolve_left (hlp l0)).1⟩
    

theorem Valid'.rotate_r {l x r o₁ o₂} (hl : Valid' o₁ l ↑x) (hr : Valid' (↑x) r o₂) (H1 : ¬size l + size r ≤ 1)
    (H2 : delta * size r < size l) (H3 : 2 * size l ≤ 9 * size r + 5 ∨ size l ≤ 3) : Valid' o₁ (@rotateR α l x r) o₂ :=
  by
  refine' valid'.dual_iff.2 _
  rw [dual_rotate_r]
  refine' hr.dual.rotate_l hl.dual _ _ _
  · rwa [size_dual, size_dual, add_commₓ]
    
  · rwa [size_dual, size_dual]
    
  · rwa [size_dual, size_dual]
    

theorem Valid'.balance'_aux {l x r o₁ o₂} (hl : Valid' o₁ l ↑x) (hr : Valid' (↑x) r o₂)
    (H₁ : 2 * @size α r ≤ 9 * size l + 5 ∨ size r ≤ 3) (H₂ : 2 * @size α l ≤ 9 * size r + 5 ∨ size l ≤ 3) :
    Valid' o₁ (@balance' α l x r) o₂ := by
  rw [balance']
  split_ifs
  · exact hl.node' hr (Or.inl h)
    
  · exact hl.rotate_l hr h h_1 H₁
    
  · exact hl.rotate_r hr h h_2 H₂
    
  · exact hl.node' hr (Or.inr ⟨not_ltₓ.1 h_2, not_ltₓ.1 h_1⟩)
    

theorem Valid'.balance'_lemma {α l l' r r'} (H1 : BalancedSz l' r')
    (H2 : Nat.dist (@size α l) l' ≤ 1 ∧ size r = r' ∨ Nat.dist (size r) r' ≤ 1 ∧ size l = l') :
    2 * @size α r ≤ 9 * size l + 5 ∨ size r ≤ 3 := by
  suffices @size α r ≤ 3 * (size l + 1) by
    cases' Nat.eq_zero_or_posₓ (size l) with l0 l0
    · apply Or.inr
      rwa [l0] at this
      
    change 1 ≤ _ at l0
    apply Or.inl
    linarith
  rcases H2 with (⟨hl, rfl⟩ | ⟨hr, rfl⟩) <;> rcases H1 with (h | ⟨h₁, h₂⟩)
  · exact le_transₓ (Nat.le_add_leftₓ _ _) (le_transₓ h (Nat.le_add_leftₓ _ _))
    
  · exact le_transₓ h₂ (Nat.mul_le_mul_leftₓ _ <| le_transₓ (Nat.dist_tri_right _ _) (Nat.add_le_add_leftₓ hl _))
    
  · exact
      le_transₓ (Nat.dist_tri_left' _ _)
        (le_transₓ (add_le_add hr (le_transₓ (Nat.le_add_leftₓ _ _) h))
          (by
            decide))
    
  · rw [Nat.mul_succ]
    exact
      le_transₓ (Nat.dist_tri_right' _ _)
        (add_le_add h₂
          (le_transₓ hr
            (by
              decide)))
    

theorem Valid'.balance' {l x r o₁ o₂} (hl : Valid' o₁ l ↑x) (hr : Valid' (↑x) r o₂)
    (H :
      ∃ l' r', BalancedSz l' r' ∧ (Nat.dist (size l) l' ≤ 1 ∧ size r = r' ∨ Nat.dist (size r) r' ≤ 1 ∧ size l = l')) :
    Valid' o₁ (@balance' α l x r) o₂ :=
  let ⟨l', r', H1, H2⟩ := H
  Valid'.balance'_aux hl hr (Valid'.balance'_lemma H1 H2) (Valid'.balance'_lemma H1.symm H2.symm)

theorem Valid'.balance {l x r o₁ o₂} (hl : Valid' o₁ l ↑x) (hr : Valid' (↑x) r o₂)
    (H :
      ∃ l' r', BalancedSz l' r' ∧ (Nat.dist (size l) l' ≤ 1 ∧ size r = r' ∨ Nat.dist (size r) r' ≤ 1 ∧ size l = l')) :
    Valid' o₁ (@balance α l x r) o₂ := by
  rw [balance_eq_balance' hl.3 hr.3 hl.2 hr.2] <;> exact hl.balance' hr H

theorem Valid'.balance_l_aux {l x r o₁ o₂} (hl : Valid' o₁ l ↑x) (hr : Valid' (↑x) r o₂) (H₁ : size l = 0 → size r ≤ 1)
    (H₂ : 1 ≤ size l → 1 ≤ size r → size r ≤ delta * size l) (H₃ : 2 * @size α l ≤ 9 * size r + 5 ∨ size l ≤ 3) :
    Valid' o₁ (@balanceL α l x r) o₂ := by
  rw [balance_l_eq_balance hl.2 hr.2 H₁ H₂, balance_eq_balance' hl.3 hr.3 hl.2 hr.2]
  refine' hl.balance'_aux hr (Or.inl _) H₃
  cases' Nat.eq_zero_or_posₓ (size r) with r0 r0
  · rw [r0]
    exact Nat.zero_leₓ _
    
  cases' Nat.eq_zero_or_posₓ (size l) with l0 l0
  · rw [l0]
    exact
      le_transₓ (Nat.mul_le_mul_leftₓ _ (H₁ l0))
        (by
          decide)
    
  replace H₂ : _ ≤ 3 * _ := H₂ l0 r0
  linarith

theorem Valid'.balance_l {l x r o₁ o₂} (hl : Valid' o₁ l ↑x) (hr : Valid' (↑x) r o₂)
    (H : (∃ l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨ ∃ r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    Valid' o₁ (@balanceL α l x r) o₂ := by
  rw [balance_l_eq_balance' hl.3 hr.3 hl.2 hr.2 H]
  refine' hl.balance' hr _
  rcases H with (⟨l', e, H⟩ | ⟨r', e, H⟩)
  · exact ⟨_, _, H, Or.inl ⟨e.dist_le', rfl⟩⟩
    
  · exact ⟨_, _, H, Or.inr ⟨e.dist_le, rfl⟩⟩
    

theorem Valid'.balance_r_aux {l x r o₁ o₂} (hl : Valid' o₁ l ↑x) (hr : Valid' (↑x) r o₂) (H₁ : size r = 0 → size l ≤ 1)
    (H₂ : 1 ≤ size r → 1 ≤ size l → size l ≤ delta * size r) (H₃ : 2 * @size α r ≤ 9 * size l + 5 ∨ size r ≤ 3) :
    Valid' o₁ (@balanceR α l x r) o₂ := by
  rw [valid'.dual_iff, dual_balance_r]
  have := hr.dual.balance_l_aux hl.dual
  rw [size_dual, size_dual] at this
  exact this H₁ H₂ H₃

theorem Valid'.balance_r {l x r o₁ o₂} (hl : Valid' o₁ l ↑x) (hr : Valid' (↑x) r o₂)
    (H : (∃ l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨ ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    Valid' o₁ (@balanceR α l x r) o₂ := by
  rw [valid'.dual_iff, dual_balance_r] <;> exact hr.dual.balance_l hl.dual (balance_sz_dual H)

theorem Valid'.erase_max_aux {s l x r o₁ o₂} (H : Valid' o₁ (node s l x r) o₂) :
    Valid' o₁ (@eraseMax α (node' l x r)) ↑(findMax' x r) ∧ size (node' l x r) = size (eraseMax (node' l x r)) + 1 := by
  have := H.2.eq_node'
  rw [this] at H
  clear this
  induction' r with rs rl rx rr IHrl IHrr generalizing l x o₁
  · exact ⟨H.left, rfl⟩
    
  have := H.2.2.2.eq_node'
  rw [this] at H⊢
  rcases IHrr H.right with ⟨h, e⟩
  refine' ⟨valid'.balance_l H.left h (Or.inr ⟨_, Or.inr e, H.3.1⟩), _⟩
  rw [erase_max, size_balance_l H.3.2.1 h.3 H.2.2.1 h.2 (Or.inr ⟨_, Or.inr e, H.3.1⟩)]
  rw [size, e]
  rfl

theorem Valid'.erase_min_aux {s l x r o₁ o₂} (H : Valid' o₁ (node s l x r) o₂) :
    Valid' (↑(findMin' l x)) (@eraseMin α (node' l x r)) o₂ ∧ size (node' l x r) = size (eraseMin (node' l x r)) + 1 :=
  by
  have := H.dual.erase_max_aux <;>
    rwa [← dual_node', size_dual, ← dual_erase_min, size_dual, ← valid'.dual_iff, find_max'_dual] at this

theorem eraseMin.valid : ∀ {t} (h : @Valid α _ t), Valid (eraseMin t)
  | nil, _ => valid_nil
  | node _ l x r, h => by
    rw [h.2.eq_node'] <;> exact h.erase_min_aux.1.valid

theorem eraseMax.valid {t} (h : @Valid α _ t) : Valid (eraseMax t) := by
  rw [valid.dual_iff, dual_erase_max] <;> exact erase_min.valid h.dual

theorem Valid'.glue_aux {l r o₁ o₂} (hl : Valid' o₁ l o₂) (hr : Valid' o₁ r o₂)
    (sep : l.all fun x => r.all fun y => x < y) (bal : BalancedSz (size l) (size r)) :
    Valid' o₁ (@glue α l r) o₂ ∧ size (glue l r) = size l + size r := by
  cases' l with ls ll lx lr
  · exact ⟨hr, (zero_addₓ _).symm⟩
    
  cases' r with rs rl rx rr
  · exact ⟨hl, rfl⟩
    
  dsimp' [← glue]
  split_ifs
  · rw [split_max_eq, glue]
    cases' valid'.erase_max_aux hl with v e
    suffices H
    refine' ⟨valid'.balance_r v (hr.of_gt _ _) H, _⟩
    · refine' find_max'_all lx lr hl.1.2.to_nil (sep.2.2.imp _)
      exact fun x h => hr.1.2.to_nil.mono_left (le_of_ltₓ h.2.1)
      
    · exact @find_max'_all _ (fun a => all (· > a) (node rs rl rx rr)) lx lr sep.2.1 sep.2.2
      
    · rw [size_balance_r v.3 hr.3 v.2 hr.2 H, add_right_commₓ, ← e, hl.2.1]
      rfl
      
    · refine' Or.inl ⟨_, Or.inr e, _⟩
      rwa [hl.2.eq_node'] at bal
      
    
  · rw [split_min_eq, glue]
    cases' valid'.erase_min_aux hr with v e
    suffices H
    refine' ⟨valid'.balance_l (hl.of_lt _ _) v H, _⟩
    · refine' @find_min'_all _ (fun a => bounded nil o₁ ↑a) rl rx (sep.2.1.1.imp _) hr.1.1.to_nil
      exact fun y h => hl.1.1.to_nil.mono_right (le_of_ltₓ h)
      
    · exact
        @find_min'_all _ (fun a => all (· < a) (node ls ll lx lr)) rl rx
          (all_iff_forall.2 fun x hx => sep.imp fun y hy => all_iff_forall.1 hy.1 _ hx) (sep.imp fun y hy => hy.2.1)
      
    · rw [size_balance_l hl.3 v.3 hl.2 v.2 H, add_assocₓ, ← e, hr.2.1]
      rfl
      
    · refine' Or.inr ⟨_, Or.inr e, _⟩
      rwa [hr.2.eq_node'] at bal
      
    

theorem Valid'.glue {l x r o₁ o₂} (hl : Valid' o₁ l ↑(x : α)) (hr : Valid' (↑x) r o₂) :
    BalancedSz (size l) (size r) → Valid' o₁ (@glue α l r) o₂ ∧ size (@glue α l r) = size l + size r :=
  Valid'.glue_aux (hl.trans_right hr.1) (hr.trans_left hl.1) (hl.1.to_sep hr.1)

theorem Valid'.merge_lemma {a b c : ℕ} (h₁ : 3 * a < b + c + 1) (h₂ : b ≤ 3 * c) : 2 * (a + b) ≤ 9 * c + 5 := by
  linarith

theorem Valid'.merge_aux₁ {o₁ o₂ ls ll lx lr rs rl rx rr t} (hl : Valid' o₁ (@node α ls ll lx lr) o₂)
    (hr : Valid' o₁ (node rs rl rx rr) o₂) (h : delta * ls < rs) (v : Valid' o₁ t ↑rx) (e : size t = ls + size rl) :
    Valid' o₁ (balanceL t rx rr) o₂ ∧ size (balanceL t rx rr) = ls + rs := by
  rw [hl.2.1] at e
  rw [hl.2.1, hr.2.1, delta] at h
  rcases hr.3.1 with (H | ⟨hr₁, hr₂⟩)
  · linarith
    
  suffices H₂
  suffices H₁
  refine' ⟨valid'.balance_l_aux v hr.right H₁ H₂ _, _⟩
  · rw [e]
    exact Or.inl (valid'.merge_lemma h hr₁)
    
  · rw [balance_l_eq_balance v.2 hr.2.2.2 H₁ H₂, balance_eq_balance' v.3 hr.3.2.2 v.2 hr.2.2.2,
      size_balance' v.2 hr.2.2.2, e, hl.2.1, hr.2.1]
    simp [← add_commₓ, ← add_left_commₓ]
    
  · rw [e, add_right_commₓ]
    rintro ⟨⟩
    
  · intro _ h₁
    rw [e]
    unfold delta  at hr₂⊢
    linarith
    

theorem Valid'.merge_aux {l r o₁ o₂} (hl : Valid' o₁ l o₂) (hr : Valid' o₁ r o₂)
    (sep : l.all fun x => r.all fun y => x < y) : Valid' o₁ (@merge α l r) o₂ ∧ size (merge l r) = size l + size r := by
  induction' l with ls ll lx lr IHll IHlr generalizing o₁ o₂ r
  · exact ⟨hr, (zero_addₓ _).symm⟩
    
  induction' r with rs rl rx rr IHrl IHrr generalizing o₁ o₂
  · exact ⟨hl, rfl⟩
    
  rw [merge_node]
  split_ifs
  · cases' IHrl (sep.imp fun x h => h.1) (hl.of_lt hr.1.1.to_nil <| sep.imp fun x h => h.2.1) hr.left with v e
    exact valid'.merge_aux₁ hl hr h v e
    
  · cases' IHlr hl.right (hr.of_gt hl.1.2.to_nil sep.2.1) sep.2.2 with v e
    have := valid'.merge_aux₁ hr.dual hl.dual h_1 v.dual
    rw [size_dual, add_commₓ, size_dual, ← dual_balance_r, ← valid'.dual_iff, size_dual, add_commₓ rs] at this
    exact this e
    
  · refine' valid'.glue_aux hl hr sep (Or.inr ⟨not_ltₓ.1 h_1, not_ltₓ.1 h⟩)
    

theorem Valid.merge {l r} (hl : Valid l) (hr : Valid r) (sep : l.all fun x => r.all fun y => x < y) :
    Valid (@merge α l r) :=
  (Valid'.merge_aux hl hr sep).1

theorem insertWith.valid_aux [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (f : α → α) (x : α)
    (hf : ∀ y, x ≤ y ∧ y ≤ x → x ≤ f y ∧ f y ≤ x) :
    ∀ {t o₁ o₂},
      Valid' o₁ t o₂ →
        Bounded nil o₁ ↑x →
          Bounded nil (↑x) o₂ → Valid' o₁ (insertWith f x t) o₂ ∧ Raised (size t) (size (insertWith f x t))
  | nil, o₁, o₂, _, bl, br => ⟨valid'_singleton bl br, Or.inr rfl⟩
  | node sz l y r, o₁, o₂, h, bl, br => by
    rw [insert_with, cmpLe]
    split_ifs <;> rw [insert_with]
    · rcases h with ⟨⟨lx, xr⟩, hs, hb⟩
      rcases hf _ ⟨h_1, h_2⟩ with ⟨xf, fx⟩
      refine' ⟨⟨⟨lx.mono_right (le_transₓ h_2 xf), xr.mono_left (le_transₓ fx h_1)⟩, hs, hb⟩, Or.inl rfl⟩
      
    · rcases insert_with.valid_aux h.left bl (lt_of_le_not_leₓ h_1 h_2) with ⟨vl, e⟩
      suffices H
      · refine' ⟨vl.balance_l h.right H, _⟩
        rw [size_balance_l vl.3 h.3.2.2 vl.2 h.2.2.2 H, h.2.size_eq]
        refine' (e.add_right _).add_right _
        
      · exact Or.inl ⟨_, e, h.3.1⟩
        
      
    · have : y < x := lt_of_le_not_leₓ ((total_of (· ≤ ·) _ _).resolve_left h_1) h_1
      rcases insert_with.valid_aux h.right this br with ⟨vr, e⟩
      suffices H
      · refine' ⟨h.left.balance_r vr H, _⟩
        rw [size_balance_r h.3.2.1 vr.3 h.2.2.1 vr.2 H, h.2.size_eq]
        refine' (e.add_left _).add_right _
        
      · exact Or.inr ⟨_, e, h.3.1⟩
        
      

theorem insertWith.valid [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (f : α → α) (x : α)
    (hf : ∀ y, x ≤ y ∧ y ≤ x → x ≤ f y ∧ f y ≤ x) {t} (h : Valid t) : Valid (insertWith f x t) :=
  (insertWith.valid_aux _ _ hf h ⟨⟩ ⟨⟩).1

theorem insert_eq_insert_with [@DecidableRel α (· ≤ ·)] (x : α) : ∀ t, Ordnode.insert x t = insertWith (fun _ => x) x t
  | nil => rfl
  | node _ l y r => by
    unfold Ordnode.insert insert_with <;>
      cases cmpLe x y <;> unfold Ordnode.insert insert_with <;> simp [← insert_eq_insert_with]

theorem insert.valid [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) {t} (h : Valid t) :
    Valid (Ordnode.insert x t) := by
  rw [insert_eq_insert_with] <;> exact insert_with.valid _ _ (fun _ _ => ⟨le_rfl, le_rfl⟩) h

theorem insert'_eq_insert_with [@DecidableRel α (· ≤ ·)] (x : α) : ∀ t, insert' x t = insertWith id x t
  | nil => rfl
  | node _ l y r => by
    unfold insert' insert_with <;> cases cmpLe x y <;> unfold insert' insert_with <;> simp [← insert'_eq_insert_with]

theorem insert'.valid [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) {t} (h : Valid t) : Valid (insert' x t) :=
  by
  rw [insert'_eq_insert_with] <;> exact insert_with.valid _ _ (fun _ => id) h

theorem Valid'.map_aux {β} [Preorderₓ β] {f : α → β} (f_strict_mono : StrictMono f) {t a₁ a₂} (h : Valid' a₁ t a₂) :
    Valid' (Option.map f a₁) (mapₓ f t) (Option.map f a₂) ∧ (mapₓ f t).size = t.size := by
  induction t generalizing a₁ a₂
  · simp [← map]
    apply valid'_nil
    cases a₁
    · trivial
      
    cases a₂
    · trivial
      
    simp [← bounded]
    exact f_strict_mono h.ord
    
  · have t_ih_l' := t_ih_l h.left
    have t_ih_r' := t_ih_r h.right
    clear t_ih_l t_ih_r
    cases' t_ih_l' with t_l_valid t_l_size
    cases' t_ih_r' with t_r_valid t_r_size
    simp [← map]
    constructor
    · exact And.intro t_l_valid.ord t_r_valid.ord
      
    · repeat'
        constructor
      · rw [t_l_size, t_r_size]
        exact h.sz.1
        
      · exact t_l_valid.sz
        
      · exact t_r_valid.sz
        
      
    · repeat'
        constructor
      · rw [t_l_size, t_r_size]
        exact h.bal.1
        
      · exact t_l_valid.bal
        
      · exact t_r_valid.bal
        
      
    

theorem mapₓ.valid {β} [Preorderₓ β] {f : α → β} (f_strict_mono : StrictMono f) {t} (h : Valid t) : Valid (mapₓ f t) :=
  (Valid'.map_aux f_strict_mono h).1

theorem Valid'.erase_aux [@DecidableRel α (· ≤ ·)] (x : α) {t a₁ a₂} (h : Valid' a₁ t a₂) :
    Valid' a₁ (erase x t) a₂ ∧ Raised (erase x t).size t.size := by
  induction t generalizing a₁ a₂
  · simp [← erase, ← raised]
    exact h
    
  · simp [← erase]
    have t_ih_l' := t_ih_l h.left
    have t_ih_r' := t_ih_r h.right
    clear t_ih_l t_ih_r
    cases' t_ih_l' with t_l_valid t_l_size
    cases' t_ih_r' with t_r_valid t_r_size
    cases cmpLe x t_x <;> simp [← erase._match_1] <;> rw [h.sz.1]
    · suffices h_balanceable
      constructor
      · exact valid'.balance_r t_l_valid h.right h_balanceable
        
      · rw [size_balance_r t_l_valid.bal h.right.bal t_l_valid.sz h.right.sz h_balanceable]
        repeat'
          apply raised.add_right
        exact t_l_size
        
      · left
        exists t_l.size
        exact And.intro t_l_size h.bal.1
        
      
    · have h_glue := valid'.glue h.left h.right h.bal.1
      cases' h_glue with h_glue_valid h_glue_sized
      constructor
      · exact h_glue_valid
        
      · right
        rw [h_glue_sized]
        
      
    · suffices h_balanceable
      constructor
      · exact valid'.balance_l h.left t_r_valid h_balanceable
        
      · rw [size_balance_l h.left.bal t_r_valid.bal h.left.sz t_r_valid.sz h_balanceable]
        apply raised.add_right
        apply raised.add_left
        exact t_r_size
        
      · right
        exists t_r.size
        exact And.intro t_r_size h.bal.1
        
      
    

theorem erase.valid [@DecidableRel α (· ≤ ·)] (x : α) {t} (h : Valid t) : Valid (erase x t) :=
  (Valid'.erase_aux x h).1

theorem size_erase_of_mem [@DecidableRel α (· ≤ ·)] {x : α} {t a₁ a₂} (h : Valid' a₁ t a₂) (h_mem : x ∈ t) :
    size (erase x t) = size t - 1 := by
  induction t generalizing a₁ a₂ h h_mem
  · contradiction
    
  · have t_ih_l' := t_ih_l h.left
    have t_ih_r' := t_ih_r h.right
    clear t_ih_l t_ih_r
    unfold HasMem.Mem mem  at h_mem
    unfold erase
    cases cmpLe x t_x <;> simp [← mem._match_1] at h_mem <;> simp [← erase._match_1]
    · have t_ih_l := t_ih_l' h_mem
      clear t_ih_l' t_ih_r'
      have t_l_h := valid'.erase_aux x h.left
      cases' t_l_h with t_l_valid t_l_size
      rw
        [size_balance_r t_l_valid.bal h.right.bal t_l_valid.sz h.right.sz
          (Or.inl (Exists.introₓ t_l.size (And.intro t_l_size h.bal.1)))]
      rw [t_ih_l, h.sz.1]
      have h_pos_t_l_size := pos_size_of_mem h.left.sz h_mem
      cases' t_l.size with t_l_size
      · cases h_pos_t_l_size
        
      simp [← Nat.succ_add]
      
    · rw [(valid'.glue h.left h.right h.bal.1).2, h.sz.1]
      rfl
      
    · have t_ih_r := t_ih_r' h_mem
      clear t_ih_l' t_ih_r'
      have t_r_h := valid'.erase_aux x h.right
      cases' t_r_h with t_r_valid t_r_size
      rw
        [size_balance_l h.left.bal t_r_valid.bal h.left.sz t_r_valid.sz
          (Or.inr (Exists.introₓ t_r.size (And.intro t_r_size h.bal.1)))]
      rw [t_ih_r, h.sz.1]
      have h_pos_t_r_size := pos_size_of_mem h.right.sz h_mem
      cases' t_r.size with t_r_size
      · cases h_pos_t_r_size
        
      simp [← Nat.succ_add, ← Nat.add_succ]
      
    

end

end Ordnode

/-- An `ordset α` is a finite set of values, represented as a tree. The operations on this type
maintain that the tree is balanced and correctly stores subtree sizes at each level. The
correctness property of the tree is baked into the type, so all operations on this type are correct
by construction. -/
def Ordset (α : Type _) [Preorderₓ α] :=
  { t : Ordnode α // t.valid }

namespace Ordset

open Ordnode

variable [Preorderₓ α]

/-- O(1). The empty set. -/
def nil : Ordset α :=
  ⟨nil, ⟨⟩, ⟨⟩, ⟨⟩⟩

/-- O(1). Get the size of the set. -/
def size (s : Ordset α) : ℕ :=
  s.1.size

/-- O(1). Construct a singleton set containing value `a`. -/
protected def singleton (a : α) : Ordset α :=
  ⟨singleton a, valid_singleton⟩

instance : HasEmptyc (Ordset α) :=
  ⟨nil⟩

instance : Inhabited (Ordset α) :=
  ⟨nil⟩

instance : HasSingleton α (Ordset α) :=
  ⟨Ordset.singleton⟩

/-- O(1). Is the set empty? -/
def Empty (s : Ordset α) : Prop :=
  s = ∅

theorem empty_iff {s : Ordset α} : s = ∅ ↔ s.1.Empty :=
  ⟨fun h => by
    cases h <;> exact rfl, fun h => by
    cases s <;> cases s_val <;> [exact rfl, cases h]⟩

instance : DecidablePred (@Empty α _) := fun s => decidableOfIff' _ empty_iff

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
  If an equivalent element is already in the set, this replaces it. -/
protected def insert [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) (s : Ordset α) : Ordset α :=
  ⟨Ordnode.insert x s.1, insert.valid _ s.2⟩

instance [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] : HasInsert α (Ordset α) :=
  ⟨Ordset.insert⟩

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
  If an equivalent element is already in the set, the set is returned as is. -/
def insert' [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) (s : Ordset α) : Ordset α :=
  ⟨insert' x s.1, insert'.valid _ s.2⟩

section

variable [@DecidableRel α (· ≤ ·)]

/-- O(log n). Does the set contain the element `x`? That is,
  is there an element that is equivalent to `x` in the order? -/
def mem (x : α) (s : Ordset α) : Bool :=
  x ∈ s.val

/-- O(log n). Retrieve an element in the set that is equivalent to `x` in the order,
  if it exists. -/
def find (x : α) (s : Ordset α) : Option α :=
  Ordnode.find x s.val

instance : HasMem α (Ordset α) :=
  ⟨fun x s => mem x s⟩

instance mem.decidable (x : α) (s : Ordset α) : Decidable (x ∈ s) :=
  Bool.decidableEq _ _

theorem pos_size_of_mem {x : α} {t : Ordset α} (h_mem : x ∈ t) : 0 < size t := by
  simp [← HasMem.Mem, ← mem] at h_mem
  apply Ordnode.pos_size_of_mem t.property.sz h_mem

end

/-- O(log n). Remove an element from the set equivalent to `x`. Does nothing if there
is no such element. -/
def erase [@DecidableRel α (· ≤ ·)] (x : α) (s : Ordset α) : Ordset α :=
  ⟨Ordnode.erase x s.val, Ordnode.erase.valid x s.property⟩

/-- O(n). Map a function across a tree, without changing the structure. -/
def map {β} [Preorderₓ β] (f : α → β) (f_strict_mono : StrictMono f) (s : Ordset α) : Ordset β :=
  ⟨Ordnode.mapₓ f s.val, Ordnode.mapₓ.valid f_strict_mono s.property⟩

end Ordset


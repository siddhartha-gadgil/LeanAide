import Aesop

/-!
Source: https://github.com/IPDSnelting/tba-2022/blob/master/TBA/AesopSort.lean
-/


variable [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)]

@[aesop safe constructors]
inductive Sorted : List α → Prop where
  | nil : Sorted []
  | single : Sorted [x]
  | cons_cons : x ≤ x' → Sorted (x' :: xs) → Sorted (x :: x' :: xs)

@[simp] def insertInOrder (a : α) : List α → List α
  | [] => [a]
  | x :: xs =>
    if a ≤ x then
      a :: x :: xs
    else
      x :: insertInOrder a xs

@[simp] def insertionSort : List α → List α
  | []      => []
  | x :: xs => insertInOrder x (insertionSort xs)

variable (antisymm : ∀ {x y : α}, ¬ (x ≤ y) → y ≤ x)

theorem sorted_insertInOrder {xs : List α} (h : Sorted xs) : Sorted (insertInOrder x xs) := by
  induction h <;> aesop

theorem sorted_insertionSort {xs : List α} : Sorted (insertionSort xs) := by
  induction xs <;> aesop (add safe sorted_insertInOrder)

inductive Perm : List α → List α → Prop where
  | nil : Perm [] []
  | cons : Perm xs xs' → Perm (x :: xs) (x :: xs')
  | swap : Perm (x :: y :: xs) (y :: x :: xs)
  | trans : Perm xs ys → Perm ys zs → Perm xs zs

attribute [aesop safe] Perm.nil
attribute [aesop unsafe] Perm.cons
attribute [aesop unsafe] Perm.swap
attribute [aesop unsafe] Perm.trans

theorem Perm.symm : Perm xs ys → Perm ys xs := by
  intro h
  induction h <;> aesop

@[aesop safe]
theorem perm_insertInOrder {xs : List α} : Perm (x :: xs) (insertInOrder x xs) := by
  induction xs <;> aesop

theorem perm_insertionSort {xs : List α} : Perm xs (insertionSort xs) := by
  induction xs with
  | nil => aesop
  | cons x xs =>
    cases xs with
    | nil => aesop
    | cons x' xs =>
      apply Perm.trans (ys := x :: insertInOrder x' xs)
      · exact Perm.cons perm_insertInOrder
      · apply Perm.trans (ys := x :: insertionSort (x' :: xs))
        · aesop (add safe Perm.cons, unsafe [cases List, Perm.symm])
        · aesop

def IsSortingAlgorithm (f : List α → List α) := ∀ xs, Perm xs (f xs) ∧ Sorted (f xs)

theorem isSortingAlgorithm_insertionSort : IsSortingAlgorithm (insertionSort (α := α)) :=
  fun _xs => ⟨perm_insertionSort, sorted_insertionSort @antisymm⟩

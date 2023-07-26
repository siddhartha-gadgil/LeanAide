import LeanAide.RunAsync
import Aesop
import Mathlib
import Std.Tactic.TryThis

opaque sillyN : Nat

axiom silly : sillyN = 2

example : sillyN ≤ 3 := by
  with_auto aesop? do
  rw [silly]

example : 3 ≤ 4 := by# 

example : sillyN ≤ 4 := by#
  rw [silly]
  
example: 1 = 1 := by aesop?

example : 1 ≤ 2 := by
   decide

-- c

example (n : Nat) : n ≤ n := by
   aesop?
  
example : 2 ≤ 2 := by
   apply?

example : 2 ≤ 2 := by#

example : 2 ≤ 2 := by
  with_auto aesop? do

example : 2 ≤ 2 := by#
   skip

macro "by!" tacs:tacticSeq : term =>
  `(by 
  with_auto from_by apply? do $tacs)

macro "by!"  : term =>
  `(by 
  with_auto from_by apply? do)


example : 2 ≤ 2 := by!
     skip


def prop := 2 ≤ 3

example : prop := by!
    rw [prop]

example : 1 = 1 := by!


example : sillyN ≤ 4 := by#
  rw [silly]

example : 1 = 1 := by#
  skip
  
example : 1 = 1 := by
  simp?

def sum : ℕ → ℕ
| 0 => 0
| n + 1 => n + 1 + sum n

theorem sum_formula (n: ℕ) :  sum n = (n * (n + 1) : ℚ) / 2  := by 
  induction n with
  | zero => rfl
  | succ n ih => 
    with_auto linarith do
    simp [sum]
    
    


open leanaide.auto

-- To be avoided

example : sillyN ≤ 4 := by
  rw [silly]
  

example : 1 = 1 := by


  


  


  

  


  


  


  

  


  


  


  

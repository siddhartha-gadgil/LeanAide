import LeanAide.Async
import LeanAide.AsyncCodeAction
import Aesop
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.TryThis

opaque sillyN : Nat

axiom silly : sillyN = 2

example : sillyN ≤ 3 := by
  with_auto
  rw [silly]
  -- simp_all only

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

example : 2 ≤ 2 := by
   auto?

example : 2 ≤ 2 := by
  with_auto

example : 2 ≤ 2 := by#
   skip

macro_rules
| `(tactic|auto?) => `(tactic|apply?)

example : 2 ≤ 2 := by#
   skip

def prop := 2 ≤ 3

example : prop := by
  with_auto
  rw [prop]

example : 1 = 1 := by#

macro_rules
| `(tactic|auto?) => `(tactic|aesop?)

example : sillyN ≤ 4 := by#
  rw [silly]

example : 1 = 1 := by#
  skip
  
example : 1 = 1 := by
  simp?

open leanaide.auto

example : sillyN ≤ 4 := by
  rw [silly]
  

example : 1 = 1 := by


  


  


  

  


  


  


  

  


  


  


  

import LeanCodePrompts.Async
import LeanCodePrompts.AsyncCodeAction
import Aesop
import Mathlib.Tactic.LibrarySearch

opaque sillyN : Nat

axiom silly : sillyN = 2

example : sillyN ≤ 3 := by
  with_auto
  rw [silly]
  -- check_auto
  skip
  -- auto

/-
example : 1 ≤ 2 := by
  bg decide
  
example (n : Nat) : n ≤ n := by
  bg aesop?
  
example : 2 ≤ 2 := by
  bg library_search

example : 2 ≤ 2 := by
  bg auto



example : 2 ≤ 2 := by
  with_auto

macro_rules
| `(tactic|auto) => `(tactic|library_search)

example : 2 ≤ 2 := by
  bg auto

def prop := 2 ≤ 2

-- example : prop := by
--   with_auto
--   rw [prop]



  


  

-/
  

  


  


  


  

  


  


  


  

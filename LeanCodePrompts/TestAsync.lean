import LeanCodePrompts.Async
import LeanCodePrompts.AsyncCodeAction
import Aesop
import Mathlib.Tactic.LibrarySearch

example : 1 ≤ 2 := by
  bg decide
  
example (n : Nat) : n ≤ n := by
  bg aesop?
  
example : 2 ≤ 2 := by
  bg library_search

example : 2 ≤ 2 := by
  bg auto
  
macro_rules
| `(tactic|auto) => `(tactic|library_search)

example : 2 ≤ 2 := by
  bg auto

def prop := 2 ≤ 2

example : prop := by
  with_auto
  rw [prop]

  


  


  


  

  


  


  


  

  


  


  


  

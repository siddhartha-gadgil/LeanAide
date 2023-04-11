import LeanCodePrompts.Async
import LeanCodePrompts.AsyncCodeAction
import Aesop
import Mathlib.Tactic.LibrarySearch

example : 1 ≤ 2 := by
  bg decide

example : 1 = 1 := by bg rfl
  
example (n : Nat) : n ≤ n := by
  bg aesop?
  
example : 2 ≤ 2 := by
  bg library_search

  


  

  


  


  


  

  


  


  


  

  


  


  


  

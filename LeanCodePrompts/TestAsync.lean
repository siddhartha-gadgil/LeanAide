import LeanCodePrompts.Async
import LeanCodePrompts.AsyncCodeAction


example : 1 ≤ 2 := by
  launch rfl
  launch (apply Nat.le_step)
  launch decide
  fetch_proof

-- example : 1  = 1 := by launch rfl

  

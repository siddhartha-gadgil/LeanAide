import LeanCodePrompts.Async
import LeanCodePrompts.AsyncCodeAction


example : 1 ≤ 2 := by
  launch rfl
  launch (apply Nat.le_step)
  decide
  

  

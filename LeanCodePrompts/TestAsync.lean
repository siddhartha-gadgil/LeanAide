import LeanCodePrompts.Async

example : 1 ≤ 2 := by
  launch rfl
  launch (apply Nat.le_step)
  launch decide
  fetch_proof


import LeanAide.AddDocs

example : True := by trivial

theorem eg₀ (x: Nat) : x + 0 = x := by
  simp

/-- With a doc -/
theorem eg₁ (x: Nat) : x + 0 = x := by
  simp

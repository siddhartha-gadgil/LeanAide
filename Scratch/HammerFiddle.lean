import Hammer
example (a b : Nat) : a + b = b + a := by
  hammer


example {P Q: Prop} : Q := by
  have h : P := by
    sorry
  have h' : P → Q := by
    sorry
  hammer

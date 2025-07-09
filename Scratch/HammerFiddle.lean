import Hammer
example (a b : Nat) : a + b = b + a := by
  hammer {aesopPremises := 0, autoPremises := 0}


example {P Q: Prop} : Q := by
  have h : P := by
    sorry
  have h' : P → Q := by
    sorry
  hammer {aesopPremises := 0, autoPremises := 0}

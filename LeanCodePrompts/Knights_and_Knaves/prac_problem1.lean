import basic

--link : https://www.cut-the-knot.org/Outline/Logic/KnightKnave1.shtml

/-
On an island, the populace is of two kinds: knights and knaves. Knights always tell the truth, knaves always lie. An islander - call him `A` - made a statement about himself and a friend, call him `B`: "At least one of us is a knave." What are `A` and `B`?
-/
theorem who_is_who_1 (A : Islander) (B : Islander) (h1 : (says A (is_Knave A ∨ is_Knave B))) : (is_Knight A) ∧ (is_Knave B) :=
begin
split,
{
  induction A,
  {
    induction B,
    repeat {unfold is_Knight,},
  },
  {
    exfalso,
    apply h1,
    induction B,
    repeat {left, unfold is_Knave,}, 
  }
},
{
  induction A,
  {
    induction B,
    cases h1,
    exact h1,
    exact h1,
    unfold is_Knave,
  },
  {
    induction B,
    exfalso,
    apply h1,
    left,
    repeat {unfold is_Knave},
  },
}
end


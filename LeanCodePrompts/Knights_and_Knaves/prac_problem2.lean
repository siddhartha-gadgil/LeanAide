import basic

--link: https://www.cut-the-knot.org/Outline/Logic/KnightKnave2.shtml

/-
On an island, the populace is of two kinds: knights and knaves. Knights always tell the truth, knaves always lie. An islander - call him `A` - made a statement about himself and a friend, call him `B`: "Either I am a knave or `B` is a knight." What are `A` and `B`?
-/ 
theorem who_is_who_2 (A : Islander) (B : Islander) (h1 : says A (is_Knave A ∨ is_Knight B )) : is_Knight A ∧ is_Knight B :=
begin
split,
{
  induction A,
  unfold is_Knight,
  exfalso,
  apply h1,
  left,
  unfold is_Knave,
},
{
  induction A,
  induction B,
  unfold is_Knight,
  cases h1,
  repeat {trivial},
  induction B,
  unfold is_Knight,
  exfalso,
  apply h1,
  left,
}
end
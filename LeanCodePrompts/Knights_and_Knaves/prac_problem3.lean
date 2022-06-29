import basic
--link: https://www.cut-the-knot.org/Outline/Logic/KnightKnave3.shtml

/-
On an island, the populace is of two kinds: knights and knaves. Knights always tell the truth, knaves always lie. An islander - call him `A` - made a statement: "Either I am a knave or 2 + 2 = 5." What can we conclude?
-/
theorem who_is_who_3 (A : Islander) (h1 : says A (is_Knave A ∨ (2+2=5))) : false:=
begin
  induction A,
  cases h1,
  unfold is_Knave at h1,
  trivial,
  have h2 : 2 + 2 = 4 + 0, from rfl,
  rw h2 at h1,
  have h3 : 4 + 1 = 5, from rfl,
  rw ← h3 at h1,
  have h4 := nat.add_left_cancel h1,
  apply nat.one_ne_zero,
  rw h4,
  apply h1,
  left,
  unfold is_Knave,
end

/-
Some Basic Definitions for Knights and Knaves Problems
-/

/-
An Islander is either Knight or Knave
-/
inductive Islander 
| Knight : Islander
| Knave : Islander

/-
`a` is Knight
-/
def is_Knight (a : Islander) : Prop :=
a = Islander.Knight

/-
`a` is Knave
-/
def is_Knave (a : Islander) : Prop :=
a = Islander.Knave

/-
`a` is Knight if and only if `a` is not Knave
-/
lemma Knight_is_not_Knave_iff (a : Islander) : (is_Knight a) ↔ (¬ is_Knave a) :=
begin
  split,
  intro h1,
  induction a,
  repeat {trivial},
  induction a,
  intro h1,
  unfold is_Knight,
  intro h1,
  exfalso,
  apply h1,
  unfold is_Knave,
end

/-
Knight says truth and Knave says false 
-/
def says (a : Islander) (h1 : Prop) : Prop :=
begin
induction a with h,
{exact h1},
{exact (h1 -> false)},
end
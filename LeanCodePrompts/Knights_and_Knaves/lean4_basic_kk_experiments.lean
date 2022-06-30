/-
Some experiments with (partially) formalising Knights and Knaves puzzles using macros.
-/

inductive Islander
  | Knight
  | Knave
deriving BEq, DecidableEq

@[reducible, simp] def Islander.isKnight : Islander → Prop
  | Knight => True
  | Knave  => False

@[reducible, simp] def Islander.isKnave : Islander → Prop
  | Knight => False
  | Knave  => True

@[reducible, simp] def Islander.says (p : Prop) : Islander → Prop
  | Knight => p
  | Knave  => ¬p

syntax:160 ident " is an islander, " term:60 : term
syntax:160 ident " is a knight" : term
syntax:160 ident " is a knave" : term
syntax:150 ident " says " term:121 : term

syntax:120 term " and " term : term
syntax:110 term " or " term : term

syntax:100 term:101 ". " term:100 : term

macro_rules
  | `($k:ident is an islander, $p:term) => `(($k : Islander) -> $p)
  | `($k:ident is a knight) => `(Islander.isKnight $k)
  | `($k:ident is a knave) => `(Islander.isKnave $k)
  | `($k:ident says $p:term) => `(Islander.says $p $k)
  | `($p:term and $q:term) => `($p ∧ $q)
  | `($p:term or $q:term) => `($p ∨ $q)
  | `($a:term. $b:term) => `(($a) -> ($b))

theorem problem1 : A is an islander, B is an islander, (A says (A is a knave or B is a knave)). A is a knight and B is a knave := by
  intros A B; cases A <;> cases B <;> simp

theorem problem2 : A is an islander, B is an islander, (A says (A is a knave or B is a knight)). A is a knight and B is a knight := by
  intros A B; cases A <;> cases B <;> simp

theorem problem3 : A is an islander, (A says (A is a knave or (2 + 2 = 5))). False := by
  intro A; cases A <;> simp

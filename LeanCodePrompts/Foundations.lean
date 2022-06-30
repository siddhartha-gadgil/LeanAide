import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Logic

/-
Basic examples of Lean's dependent type theory, including
- Functions (`λ` notation, `fun` notation, `def` notation, etc)
- Sum and product types (and their `Prop` versions)
- Dependent sum and product types (and their `Prop` versions)
- `Unit` and `Empty` types (and their `Prop` versions, including a few examples of negation)
- Some basic proofs in the style of the introductory chapters of TPiL

The aim is to introduce most of the basic constructions in Lean along with their notational nuances.
-/

/-
`m` is a natural number.
-/
def m : Nat := 1

/-
`n` is a natural number equal to `0`.
-/
def n := (0 : ℕ)

/-
`b₁` is a Boolean whose value is `true`.
-/
def b₁ := true

/-
`b₂` is a Boolean.
-/
abbrev b₂ : Bool := false

/-
`identℕ` is a function that takes in a natural number and returns it back.
-/
def identℕ : ℕ → ℕ := fun (n : Nat) => n

/-
The identity function on the type of natural numbers.
-/
def idℕ : ℕ → ℕ := id

/-
`const0` is a constant function mapping to `0`.
-/
def const0 : ℕ → ℕ := λ _ => 0

/-
`const3` is the constant function taking the value `3`.
-/
def const3 (a : ℕ) : Nat := 3

/-
`addOne` is a function that adds one to a natural number.
-/
def addOne : ℕ → ℕ := (· + 1)

/-
A function taking a natural number to its successor.
-/
def succℕ := Nat.succ

/-
The type of all functions from natural numbers to natural numbers.

The type of all sequences of natural numbers.
-/
def Seqℕ : Type := ℕ → ℕ

/-
The type of all ordered pairs of Booleans.
-/
def BoolProd : Type := Bool × Bool

/-
The product of `Nat` and `Bool`.
-/
def prodℕBool := Prod.mk ℕ Bool

/-
An element of the product type `Bool × Bool`.

`bb` is an ordered pair of Booleans.
-/
def bb : Bool × Bool := (true, false)

/-
An element of the product type `Nat × Bool`.
-/
def nb : ℕ × Bool := (1, true)

/-
An ordered pair of floats.
-/
def fp : Float × Float := (1.0, 2.0)

/-
Projection onto the first element of an ordered pair.
-/
def proj₁ {α β : Type _} : α × β → α := Prod.fst

/-
Projection onto the second element of an ordered pair.
-/
def proj₂ {α β : Type _} : α × β → β := Prod.snd

/-
The first element of the ordered pair `bb`.
-/
def bb₁ : Bool := Prod.fst bb

/-
The second element of the ordered pair `nb`.
-/
def nb₂ : Bool := Prod.snd nb

/-
`boolToNat` is a function that takes a Boolean and returns a natural number.  
-/
def boolToNat : Bool → ℕ := λ b => if b then 1 else 0

/-
The sum of two natural numbers.
-/
def addℕ : ℕ → (ℕ → ℕ) := (· + ·)

/-
The type of all Boolean sequences.

The type of subsets of natural numbers.
-/
abbrev SeqBool := ℕ → Bool

/-
The constant false sequence.
-/
def constFalse : SeqBool := λ _ => false

/-
`indicatorℕ` is a function that takes a natural number and returns the Boolean sequence that is `true` at that number and `false` everywhere else.
-/
def indicatorℕ (n : Nat) : SeqBool := λ i => if i = n then true else false

/-
The function `indicatorℕ` applied to the argument `5`.
-/
def indicator5 := indicatorℕ 5

/-
The function `indicatorℕ` applied to the argument `3`.
-/
def indicator3 := (λ i => if i = n then true else false) 3
-- indicatorℕ 3

/-
The function `addℕ` applied to the arguments `1` and `2`.
-/
def add1_2 := addℕ 1 2

/-
The function `addℕ` partially applied to the argument `1`.
-/
def add1 := addℕ 1

/-
The type of all functions from natural numbers to sequences of natural numbers.
-/
def SeqSeqℕ : Type := ℕ → (ℕ → ℕ)

/-
The product of `Nat` and `Seqℕ`.
-/
def prodℕSeqℕ := Prod ℕ Seqℕ

/-
The composition of `add1` and `indicator5`.
-/
def add1_indicator5 := indicator5 ∘ add1

/-
The composition of two functions from natural numbers to natural numbers.
-/
def compℕ : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ := λ f g n => f (g n)

/-
A function on natural numbers that doubles its input.
-/
def double (x : ℕ) : ℕ := x + x

/-
A function that takes a function and a natural number argument and applies it twice to the argument.
-/
def twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)

/-
A function that squares its input and adds one.
-/
def square_add_one (x : ℕ) : ℕ := 
  let sq := x * x
  let sq_plus_one := sq + 1
  sq_plus_one

/-
A two-argument function that returns an ordered pair of its arguments.
-/
def pair {α β : Type _} (x : α) (y : β) : α × β := (x, y)

/-
Every proposition implies itself.
-/
theorem prop_implies_self : ∀ {P : Prop}, P → P := λ {P} h => h

/-
There is a function from any type to itself (namely `id`).
-/
theorem type_to_self : ∀ {α : Type _}, α → α := λ {α} => id

/-
Every proposition implies the proposition `True`.
-/
theorem prop_implies_true : ∀ {P : Prop}, P → True := λ {P} h => trivial

/-
There is always a function from any type to `Unit`.
-/
theorem type_to_unit : ∀ {α : Type _}, α → Unit := λ {α} => fun _ => ()

/-
Every proposition follows from `False`.
-/
theorem false_implies_prop : ∀ {P : Prop}, False → P := λ {P} h => False.elim h 

/-
There is always a function from `Empty` to any type.
-/
theorem empty_to_type : ∀ {α : Type _}, Empty → α := λ {α} => Empty.rec _

/-
For any propositions `P` and `Q`, `P` follows from `Q` under the assumption that `P` is true.
-/
theorem implies_assumption : ∀ {P Q : Prop}, P → Q → P := λ {P Q} (h₁ : P) (h₂ : Q) => h₁

/-
For any types `α` and `β`, there is a function from `α` to the type of functions from `β` to `α`.

This is the two-argument function that takes in terms of types `α` and `β` and discards the second argument.
-/
def arg₁ : ∀ {α β : Type _}, α → (β → α) := λ {α β} => fun (a : α) (b : β) => a

/-
The negation of a proposition `P` is equivalent to the proposition that `P` implies `False`.
-/
theorem neg_prop {P : Prop} : ¬ P ↔ (P → False) := Iff.rfl

/-
Every proposition implies its double negation.
-/
theorem prop_implies_double_neg : ∀ {P : Prop}, P → ¬¬P := λ {P} hp hnnp => hnnp hp

/-
There is a function from every type to its double dual function space with another type.
-/
def double_dual_empty : ∀ {α β : Type _}, α → ((α → β) → β)  := λ {α β} => fun (a : α) (f : α → β) => f a 

/-
An implication implies its contraposition.
-/
theorem implies_contraposition : ∀ {P Q : Prop}, (P → Q) → ¬Q → ¬P := λ {P Q} (h₁ : P → Q) (h₂ : ¬Q) (h₃ : P) => h₂ (h₁ h₃)

/-
Given a function between two types, there is a function in the opposite direction between the two dual function spaces with a third type.
-/
def op_dual {α β γ : Type _} (f : α → β) : (β → γ) → (α → γ) := λ (g : β → γ) => fun (a : α) => g (f a)

/-
Transitivity of implication.
-/
theorem implies_transitive : ∀ {P Q R : Prop}, (P → Q) → (Q → R) → (P → R) := λ {P Q R} (h₁ : P → Q) (h₂ : Q → R) (h₃ : P) => h₂ (h₁ h₃)

/-
If propositions `P` and `Q` are individually true, their conjunction is also true.
-/
theorem individual_implies_conjunction : ∀ {P Q : Prop}, P → Q → P ∧ Q := λ {P Q} (h₁ : P) (h₂ : Q) => ⟨h₁, h₂⟩

/-
Conjunction is commutative.
-/
theorem conjunction_commutative : ∀ {P Q : Prop}, P ∧ Q → Q ∧ P := λ {P Q} (h : P ∧ Q) => ⟨h.2, h.1⟩

/-
Conjunction is associative.
-/
theorem conjunction_associative {P Q R : Prop} : P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R := 
  Iff.intro (λ (⟨hp, ⟨hq, hr⟩⟩ : P ∧ (Q ∧ R)) => ⟨⟨hp, hq⟩, hr⟩) (λ (⟨⟨hp, hq⟩, hr⟩ : (P ∧ Q) ∧ R) => ⟨hp, ⟨hq, hr⟩⟩)

/-
If the conjunction of two propositions is true, then one of the individual propositions is true.
-/
def conjunction_implies_individual : P ∧ Q → P ∨ Q := λ ⟨hp, hq⟩ => Or.inl hp 

/-
Disjunction is commutative.
-/
theorem disjunction_commutative {P Q : Prop} : P ∨ Q → Q ∨ P :=
  λ h : P ∨ Q =>
  match h with
    | Or.inl hp => Or.inr hp
    | Or.inr hq => Or.inl hq

/-
Disjunction is associative.
-/
theorem disjunction_associative {P Q R : Prop} : P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R :=
  Iff.intro (Or.rec (Or.inl ∘ Or.inl) (Or.rec (Or.inl ∘ Or.inr) Or.inr)) (Or.rec (Or.rec Or.inl (Or.inr ∘ Or.inl)) (Or.inr ∘ Or.inr))

/-
For propositions `P` and `Q`, if `P` is true, then the disjunction of `P` and `Q` is true. 
-/
theorem fst_implies_disj : ∀ {P Q : Prop}, P → P ∨ Q := λ {P Q} (hp : P) => Or.inl hp

/-
For propositions `P` and `Q`, if `Q` is true, then the disjunction of `P` and `Q` is true.
-/
theorem snd_implies_disj : ∀ {P Q : Prop}, Q → P ∨ Q := λ {P Q} (hq : Q) => Or.inr hq

/-
Conjunction left-distributes over disjunction.
-/
theorem conjunction_left_distributes {P Q R : Prop} : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
  Iff.intro (λ (⟨hp, hqr⟩ : P ∧ (Q ∨ R)) => match hqr with | Or.inl hq => Or.inl ⟨hp, hq⟩ | Or.inr hr => Or.inr ⟨hp, hr⟩) (Or.rec (λ ⟨hp, hq⟩ => ⟨hp, Or.inl hq⟩) (λ ⟨hp, hr⟩ => ⟨hp, Or.inr hr⟩))

/-
Conjunction right-distributes over disjunction.
-/
theorem conjunction_right_distributes {P Q R : Prop} : (P ∨ Q) ∧ R ↔ (P ∧ R) ∨ (Q ∧ R) :=
  Iff.intro (λ (⟨hpq, hr⟩ : (P ∨ Q) ∧ R) => match hpq with | Or.inl hp => Or.inl ⟨hp, hr⟩ | Or.inr hq => Or.inr ⟨hq, hr⟩) (Or.rec (λ ⟨hp, hr⟩ => ⟨Or.inl hp, hr⟩) (λ ⟨hq, hr⟩ => ⟨Or.inr hq, hr⟩))

/-
Disjunction left-distributes over conjunction.
-/
theorem disjunction_left_distributes {P Q R : Prop} : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
  Iff.intro (Or.rec (λ hp => ⟨Or.inl hp, Or.inl hp⟩) (λ ⟨hq, hr⟩ => ⟨Or.inr hq, Or.inr hr⟩)) 
  (λ ⟨hpq, hpr⟩ => 
    match hpq, hpr with
      | Or.inl hp, Or.inl hq => Or.inl hp
      | Or.inl hp, Or.inr hr => Or.inl hp
      | Or.inr hq, Or.inl hp => Or.inl hp
      | Or.inr hq, Or.inr hr => Or.inr ⟨hq, hr⟩
  )

/-
Disjunction right-distributes over conjunction.
-/
theorem disjunction_right_distributes {P Q R : Prop} : (P ∧ Q) ∨ R ↔ (P ∨ R) ∧ (Q ∨ R) :=
  Iff.intro (Or.rec (λ ⟨hp, hq⟩ => ⟨Or.inl hp, Or.inl hq⟩) (λ hr => ⟨Or.inr hr, Or.inr hr⟩)) 
  (λ ⟨hpr, hqr⟩ =>
    match hpr, hqr with
      | Or.inl hp, Or.inl hq => Or.inl ⟨hp, hq⟩
      | Or.inl hp, Or.inr hr => Or.inr hr
      | Or.inr hr, Or.inl hq => Or.inr hr
      | Or.inr hr, Or.inr hq => Or.inr hr
  )
  
/-
The proposition `False` is a left identity for disjunction.
-/
theorem false_disjunction_left_ident {P : Prop} : False ∨ P ↔ P := Iff.intro (Or.rec (λ f => False.elim f) (λ hp => hp)) (λ hp => Or.inr hp)

/-
The proposition `False` is a right identity for disjunction.
-/
theorem false_disjunction_right_ident {P : Prop} : P ∨ False ↔ P := Iff.intro (Or.rec (λ hp => hp) (λ f => False.elim f)) (λ hp => Or.inl hp)

/-
The proposition `True` is a left identity for conjunction.
-/
theorem true_conjunction_left_ident {P : Prop} : True ∧ P ↔ P := Iff.intro (λ ⟨h, hp⟩ => hp) (λ hp => ⟨trivial, hp⟩)

/-
The proposition `True` is a right identity for conjunction.
-/
theorem true_conjunction_right_ident {P : Prop} : P ∧ True ↔ P := Iff.intro (λ ⟨hp, h⟩ => hp) (λ hp => ⟨hp, trivial⟩)

/-
The proposition `True` is a left annihilator for disjunction.
-/
theorem true_disjunction_left_annihilator {P : Prop} : True ∨ P ↔ True := Iff.intro (Or.rec (λ t => trivial) (λ hp => trivial)) (λ hp => Or.inl hp)

/-
The proposition `True` is a right annihilator for disjunction.
-/
theorem true_disjunction_right_annihilator {P : Prop} : P ∨ True ↔ True := Iff.intro (Or.rec (λ hp => trivial) (λ t => trivial)) (λ t => Or.inr t)

/-
The proposition `False` is a left annihilator for conjunction.
-/
theorem false_conjunction_left_annihilator {P : Prop} : False ∧ P ↔ False := Iff.intro (λ ⟨h, hp⟩ => h) (λ h => False.elim h)

/-
The proposition `False` is a right annihilator for conjunction.
-/
theorem false_conjunction_right_annihilator {P : Prop} : P ∧ False ↔ False := Iff.intro (λ ⟨hp, h⟩ => h) (λ h => False.elim h)

/-
Every proposition is equivalent to itself.
-/
theorem equivalent_self {P : Prop} : P ↔ P := Iff.intro (λ hp => hp) (λ hp => hp)

/-
Every proposition is equivalent to the conjunction with itself.
-/
theorem equivalent_conjunction_self {P : Prop} : P ↔ P ∧ P := Iff.intro (λ hp => ⟨hp, hp⟩) (λ ⟨hp, hq⟩ => hp)

/-
Every proposition is equivalent to the disjunction with itself.
-/
theorem equivalent_disjunction_self {P : Prop} : P ↔ P ∨ P := Iff.intro (λ hp => Or.inl hp) (Or.rec (λ hp => hp) (λ hp => hp))

/-
Equivalence of propositions is a reflexive relation.
-/
theorem equivalence_reflexive {P : Prop} : P ↔ P := Iff.intro (λ hp => hp) (λ hp => hp)

/-
Equivalence of propositions is a symmetric relation.
-/
theorem equivalence_symmetric {P Q : Prop} : (P ↔ Q) → (Q ↔ P) := λ ⟨hpq, hqp⟩ => ⟨hqp, hpq⟩

/-
Equivalence of propositions is a transitive relation.
-/
theorem equivalence_transitive {P Q R : Prop} : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := λ ⟨hpq, hqp⟩ ⟨hqr, hrq⟩ => ⟨hqr ∘ hpq, hqp ∘ hrq⟩

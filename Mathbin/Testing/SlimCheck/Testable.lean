/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Testing.SlimCheck.Sampleable

/-!
# `testable` Class

Testable propositions have a procedure that can generate counter-examples
together with a proof that they invalidate the proposition.

This is a port of the Haskell QuickCheck library.

## Creating Customized Instances

The type classes `testable` and `sampleable` are the means by which
`slim_check` creates samples and tests them. For instance, the proposition
`∀ i j : ℕ, i ≤ j` has a `testable` instance because `ℕ` is sampleable
and `i ≤ j` is decidable. Once `slim_check` finds the `testable`
instance, it can start using the instance to repeatedly creating samples
and checking whether they satisfy the property. This allows the
user to create new instances and apply `slim_check` to new situations.

### Polymorphism

The property `testable.check (∀ (α : Type) (xs ys : list α), xs ++ ys
= ys ++ xs)` shows us that type-polymorphic properties can be
tested. `α` is instantiated with `ℤ` first and then tested as normal
monomorphic properties.

The monomorphisation limits the applicability of `slim_check` to
polymorphic properties that can be stated about integers. The
limitation may be lifted in the future but, for now, if
one wishes to use a different type than `ℤ`, one has to refer to
the desired type.

### What do I do if I'm testing a property about my newly defined type?

Let us consider a type made for a new formalization:

```lean
structure my_type :=
(x y : ℕ)
(h : x ≤ y)
```

How do we test a property about `my_type`? For instance, let us consider
`testable.check $ ∀ a b : my_type, a.y ≤ b.x → a.x ≤ b.y`. Writing this
property as is will give us an error because we do not have an instance
of `sampleable my_type`. We can define one as follows:

```lean
instance : sampleable my_type :=
{ sample := do
  x ← sample ℕ,
  xy_diff ← sample ℕ,
  return { x := x, y := x + xy_diff, h := /- some proof -/ } }
```

We can see that the instance is very simple because our type is built
up from other type that have `sampleable` instances. `sampleable` also
has a `shrink` method but it is optional. We may want to implement one
for ease of testing as:

```lean
/- ... -/
  shrink := λ ⟨x,y,h⟩, (λ ⟨x,y⟩, { x := x, y := x + y, h := /- proof -/}) <$> shrink (x, y - x) }
```

Again, we take advantage of the fact that other types have useful
`shrink` implementations, in this case `prod`.

### Optimizing the sampling

Some properties are guarded by a proposition. For instance, recall this
example:

```lean
#eval testable.check (∀ x : ℕ, 2 ∣ x → x < 100)
```

When testing the above example, we generate a natural number, we check
that it is even and test it if it is even or throw it away and start
over otherwise. Statistically, we can expect half of our samples to be
thrown away by such a filter. Sometimes, the filter is more
restrictive. For instance we might need `x` to be a `prime`
number. This would cause most of our samples to be discarded.

We can help `slim_check` find good samples by providing specialized
sampleable instances. Below, we show an instance for the subtype
of even natural numbers. This means that, when producing
a sample, it is forced to produce a proof that it is even.

```lean
instance {k : ℕ} [fact (0 < k)] : sampleable { x : ℕ // k ∣ x } :=
{ sample := do { n ← sample ℕ, pure ⟨k*n, dvd_mul_right _ _⟩ },
  shrink := λ ⟨x,h⟩, (λ y, ⟨k*y, dvd_mul_right _ _⟩) <$> shrink x }
```

Such instance will be preferred when testing a proposition of the shape
`∀ x : T, p x → q`

We can observe the effect by enabling tracing:

```lean
/- no specialized sampling -/
#eval testable.check (∀ x : ℕ, 2 ∣ x → x < 100) { trace_discarded := tt }
-- discard
--  x := 1
-- discard
--  x := 41
-- discard
--  x := 3
-- discard
--  x := 5
-- discard
--  x := 5
-- discard
--  x := 197
-- discard
--  x := 469
-- discard
--  x := 9
-- discard

-- ===================
-- Found problems!

-- x := 552
-- -------------------

/- let us define a specialized sampling instance -/
instance {k : ℕ} : sampleable { x : ℕ // k ∣ x } :=
{ sample := do { n ← sample ℕ, pure ⟨k*n, dvd_mul_right _ _⟩ },
  shrink := λ ⟨x,h⟩, (λ y, ⟨k*y, dvd_mul_right _ _⟩) <$> shrink x }

#eval testable.check (∀ x : ℕ, 2 ∣ x → x < 100) { enable_tracing := tt }
-- ===================
-- Found problems!

-- x := 358
-- -------------------
```

Similarly, it is common to write properties of the form: `∀ i j, i ≤ j → ...`
as the following example show:

```lean
#eval check (∀ i j k : ℕ, j < k → i - k < i - j)
```

Without subtype instances, the above property discards many samples
because `j < k` does not hold. Fortunately, we have appropriate
instance to choose `k` intelligently.

## Main definitions
  * `testable` class
  * `testable.check`: a way to test a proposition using random examples

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/


universe u v

variable (var var' : Stringₓ)

variable (α : Type u)

variable (β : α → Prop)

variable (f : Type → Prop)

namespace SlimCheck

-- ./././Mathport/Syntax/Translate/Basic.lean:1422:30: infer kinds are unsupported in Lean 4: gave_up {}
/-- Result of trying to disprove `p`

The constructors are:
  *  `success : (psum unit p) → test_result`
     succeed when we find another example satisfying `p`
     In `success h`, `h` is an optional proof of the proposition.
     Without the proof, all we know is that we found one example
     where `p` holds. With a proof, the one test was sufficient to
     prove that `p` holds and we do not need to keep finding examples.
   * `gave_up {} : ℕ → test_result`
     give up when a well-formed example cannot be generated.
     `gave_up n` tells us that `n` invalid examples were tried.
     Above 100, we give up on the proposition and report that we
     did not find a way to properly test it.
   * `failure : ¬ p → (list string) → ℕ → test_result`
     a counter-example to `p`; the strings specify values for the relevant variables.
     `failure h vs n` also carries a proof that `p` does not hold. This way, we can
     guarantee that there will be no false positive. The last component, `n`,
     is the number of times that the counter-example was shrunk.
-/
inductive TestResultₓ (p : Prop)
  | success : PSum Unit p → test_result
  | gave_up : ℕ → test_result
  | failure : ¬p → List Stringₓ → ℕ → test_result
  deriving Inhabited

/-- format a `test_result` as a string. -/
protected def TestResultₓ.toString {p} : TestResultₓ p → Stringₓ
  | test_result.success (PSum.inl ()) => "success (without proof)"
  | test_result.success (PSum.inr h) => "success (with proof)"
  | test_result.gave_up n => s! "gave up {n} times"
  | test_result.failure a vs _ => s! "failed {vs}"

/-- configuration for testing a property -/
structure SlimCheckCfg where
  numInst : ℕ := 100
  -- number of examples
  maxSize : ℕ := 100
  -- final size argument
  traceDiscarded : Bool := false
  -- enable the printing out of discarded samples
  traceSuccess : Bool := false
  -- enable the printing out of successful tests
  traceShrink : Bool := false
  -- enable the printing out of shrinking steps
  traceShrinkCandidates : Bool := false
  -- enable the printing out of shrinking candidates
  randomSeed : Option ℕ := none
  -- specify a seed to the random number generator to
  -- obtain a deterministic behavior
  quiet : Bool := false
  deriving has_reflect, Inhabited

-- suppress success message when running `slim_check`
instance {p} : HasToString (TestResultₓ p) :=
  ⟨TestResultₓ.toString⟩

/-- `printable_prop p` allows one to print a proposition so that
`slim_check` can indicate how values relate to each other.
-/
class PrintablePropₓ (p : Prop) where
  printProp : Option Stringₓ

-- see [note priority]
instance (priority := 100) defaultPrintableProp {p} : PrintablePropₓ p :=
  ⟨none⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`run] []
/-- `testable p` uses random examples to try to disprove `p`. -/
class Testableₓ (p : Prop) where
  run (cfg : SlimCheckCfg) (minimize : Bool) : Genₓ (TestResultₓ p)

open _Root_.List

open TestResult

/-- applicative combinator proof carrying test results -/
def combine {p q : Prop} : PSum Unit (p → q) → PSum Unit p → PSum Unit q
  | PSum.inr f, PSum.inr x => PSum.inr (f x)
  | _, _ => PSum.inl ()

/-- Combine the test result for properties `p` and `q` to create a test for their conjunction. -/
def andCounterExample {p q : Prop} : TestResultₓ p → TestResultₓ q → TestResultₓ (p ∧ q)
  | failure Hce xs n, _ => failure (fun h => Hce h.1) xs n
  | _, failure Hce xs n => failure (fun h => Hce h.2) xs n
  | success xs, success ys => success <| combine (combine (PSum.inr And.intro) xs) ys
  | gave_up n, gave_up m => gave_up <| n + m
  | gave_up n, _ => gave_up n
  | _, gave_up n => gave_up n

/-- Combine the test result for properties `p` and `q` to create a test for their disjunction -/
def orCounterExample {p q : Prop} : TestResultₓ p → TestResultₓ q → TestResultₓ (p ∨ q)
  | failure Hce xs n, failure Hce' ys n' => failure (fun h => or_iff_not_and_not.1 h ⟨Hce, Hce'⟩) (xs ++ ys) (n + n')
  | success xs, _ => success <| combine (PSum.inr Or.inl) xs
  | _, success ys => success <| combine (PSum.inr Or.inr) ys
  | gave_up n, gave_up m => gave_up <| n + m
  | gave_up n, _ => gave_up n
  | _, gave_up n => gave_up n

/-- If `q → p`, then `¬ p → ¬ q` which means that testing `p` can allow us
to find counter-examples to `q`. -/
def convertCounterExample {p q : Prop} (h : q → p) :
    TestResultₓ p → optParam (PSum Unit (p → q)) (PSum.inl ()) → TestResultₓ q
  | failure Hce xs n, _ => failure (mt h Hce) xs n
  | success Hp, Hpq => success (combine Hpq Hp)
  | gave_up n, _ => gave_up n

/-- Test `q` by testing `p` and proving the equivalence between the two. -/
def convertCounterExample' {p q : Prop} (h : p ↔ q) (r : TestResultₓ p) : TestResultₓ q :=
  convertCounterExample h.2 r (PSum.inr h.1)

/-- When we assign a value to a universally quantified variable,
we record that value using this function so that our counter-examples
can be informative. -/
def addToCounterExample (x : Stringₓ) {p q : Prop} (h : q → p) :
    TestResultₓ p → optParam (PSum Unit (p → q)) (PSum.inl ()) → TestResultₓ q
  | failure Hce xs n, _ => failure (mt h Hce) (x :: xs) n
  | r, hpq => convertCounterExample h r hpq

/-- Add some formatting to the information recorded by `add_to_counter_example`. -/
def addVarToCounterExample {γ : Type v} [HasRepr γ] (var : Stringₓ) (x : γ) {p q : Prop} (h : q → p) :
    TestResultₓ p → optParam (PSum Unit (p → q)) (PSum.inl ()) → TestResultₓ q :=
  @addToCounterExample (var ++ " := " ++ reprₓ x) _ _ h

/-- Gadget used to introspect the name of bound variables.

It is used with the `testable` typeclass so that
`testable (named_binder "x" (∀ x, p x))` can use the variable name
of `x` in error messages displayed to the user. If we find that instantiating
the above quantifier with 3 falsifies it, we can print:

```
==============
Problem found!
==============
x := 3
```
 -/
@[simp, nolint unused_arguments]
def NamedBinderₓ (n : Stringₓ) (p : Prop) : Prop :=
  p

/-- Is the given test result a failure? -/
def isFailure {p} : TestResultₓ p → Bool
  | test_result.failure _ _ _ => true
  | _ => false

instance andTestable (p q : Prop) [Testableₓ p] [Testableₓ q] : Testableₓ (p ∧ q) :=
  ⟨fun cfg min => do
    let xp ← Testableₓ.run p cfg min
    let xq ← Testableₓ.run q cfg min
    pure <| and_counter_example xp xq⟩

instance orTestable (p q : Prop) [Testableₓ p] [Testableₓ q] : Testableₓ (p ∨ q) :=
  ⟨fun cfg min => do
    let xp ← Testableₓ.run p cfg min
    match xp with
      | success (PSum.inl h) => pure <| success (PSum.inl h)
      | success (PSum.inr h) => pure <| success (PSum.inr <| Or.inl h)
      | _ => do
        let xq ← testable.run q cfg min
        pure <| or_counter_example xp xq⟩

instance iffTestable (p q : Prop) [Testableₓ (p ∧ q ∨ ¬p ∧ ¬q)] : Testableₓ (p ↔ q) :=
  ⟨fun cfg min => do
    let xp ← Testableₓ.run (p ∧ q ∨ ¬p ∧ ¬q) cfg min
    return <|
        convert_counter_example'
          (by
            tauto!)
          xp⟩

open PrintableProp

instance (priority := 1000) decGuardTestable (p : Prop) [PrintablePropₓ p] [Decidable p] (β : p → Prop)
    [∀ h, Testableₓ (β h)] : Testableₓ (NamedBinderₓ var <| ∀ h, β h) :=
  ⟨fun cfg min => do
    if h : p then
        match print_prop p with
        | none => (fun r => convert_counter_example (· <| h) r (PSum.inr fun q _ => q)) <$> testable.run (β h) cfg min
        | some str =>
          (fun r => add_to_counter_example (s! "guard: {str}") (· <| h) r (PSum.inr fun q _ => q)) <$>
            testable.run (β h) cfg min
      else
        if cfg ∨ cfg then
          match print_prop p with
          | none => trace "discard" <| return <| gave_up 1
          | some str => (trace s! "discard: {str} does not hold") <| return <| gave_up 1
        else return <| gave_up 1⟩

/-- Type tag that replaces a type's `has_repr` instance with its `has_to_string` instance. -/
def UseHasToString (α : Type _) :=
  α

instance UseHasToString.inhabited [I : Inhabited α] : Inhabited (UseHasToString α) :=
  I

/-- Add the type tag `use_has_to_string` to an expression's type. -/
def UseHasToString.mk {α} (x : α) : UseHasToString α :=
  x

instance [HasToString α] : HasRepr (UseHasToString α) :=
  ⟨@toString α _⟩

instance (priority := 2000) allTypesTestable [Testableₓ (f ℤ)] : Testableₓ (NamedBinderₓ var <| ∀ x, f x) :=
  ⟨fun cfg min => do
    let r ← Testableₓ.run (f ℤ) cfg min
    return <| add_var_to_counter_example var (use_has_to_string.mk "ℤ") (· <| ℤ) r⟩

/-- Trace the value of sampled variables if the sample is discarded. -/
def traceIfGiveupₓ {p α β} [HasRepr α] (tracing_enabled : Bool) (var : Stringₓ) (val : α) : TestResultₓ p → Thunkₓ β → β
  | test_result.gave_up _ => if tracing_enabled then trace s! " {var } := {reprₓ val}" else (· <| ())
  | _ => (· <| ())

/-- testable instance for a property iterating over the element of a list -/
instance (priority := 5000) testForallInList [∀ x, Testableₓ (β x)] [HasRepr α] :
    ∀ xs : List α, Testableₓ (NamedBinderₓ var <| ∀ x, NamedBinderₓ var' <| x ∈ xs → β x)
  | [] =>
    ⟨fun tracing min =>
      return <|
        success <|
          PSum.inr
            (by
              introv x h
              cases h)⟩
  | x :: xs =>
    ⟨fun cfg min => do
      let r ← Testableₓ.run (β x) cfg min
      trace_if_giveup cfg var x r <|
          match r with
          | failure _ _ _ =>
            return <|
              add_var_to_counter_example var x
                (by
                  intro h
                  apply h
                  left
                  rfl)
                r
          | success hp => do
            let rs ← @testable.run _ (test_forall_in_list xs) cfg min
            return <|
                convert_counter_example
                  (by
                    intro h i h'
                    apply h
                    right
                    apply h')
                  rs
                  (combine
                    (PSum.inr <| by
                      intro j h
                      simp only [← ball_cons, ← named_binder]
                      constructor <;> assumption)
                    hp)
          | gave_up n => do
            let rs ← @testable.run _ (test_forall_in_list xs) cfg min
            match rs with
              | success _ => return <| gave_up n
              | failure Hce xs n =>
                return <|
                  failure
                    (by
                      simp only [← ball_cons, ← named_binder]
                      apply not_and_of_not_right _ Hce)
                    xs n
              | gave_up n' => return <| gave_up (n + n')⟩

/-- Test proposition `p` by randomly selecting one of the provided
testable instances. -/
def combineTestable (p : Prop) (t : List <| Testableₓ p) (h : 0 < t.length) : Testableₓ p :=
  ⟨fun cfg min =>
    have : 0 < length (map (fun t => @Testableₓ.run _ t cfg min) t) := by
      rw [length_map]
      apply h
    Genₓ.oneOf (List.map (fun t => @Testableₓ.run _ t cfg min) t) this⟩

open SampleableExt

/-- Format the counter-examples found in a test failure.
-/
def formatFailure (s : Stringₓ) (xs : List Stringₓ) (n : ℕ) : Stringₓ :=
  let counter_ex := Stringₓ.intercalate "\n" xs
  s! "
    ===================
    {s }
    
    {counter_ex }
    ({n} shrinks)
    -------------------
    "

/-- Format the counter-examples found in a test failure.
-/
def formatFailure' (s : Stringₓ) {p} : TestResultₓ p → Stringₓ
  | success a => ""
  | gave_up a => ""
  | test_result.failure _ xs n => formatFailure s xs n

/-- Increase the number of shrinking steps in a test result.
-/
def addShrinks {p} (n : ℕ) : TestResultₓ p → TestResultₓ p
  | r@(success a) => r
  | r@(gave_up a) => r
  | test_result.failure h vs n' => TestResultₓ.failure h vs <| n + n'

/-- Shrink a counter-example `x` by using `shrink x`, picking the first
candidate that falsifies a property and recursively shrinking that one.

The process is guaranteed to terminate because `shrink x` produces
a proof that all the values it produces are smaller (according to `sizeof`)
than `x`. -/
def minimizeAux [SampleableExtₓ α] [∀ x, Testableₓ (β x)] (cfg : SlimCheckCfg) (var : Stringₓ) :
    ProxyRepr α → ℕ → OptionTₓ Genₓ (Σx, TestResultₓ (β (interp α x))) :=
  (WellFounded.fix HasWellFounded.wf) fun x f_rec n => do
    if cfg then
        return <|
          trace
            (s! "candidates for {var } :=
              {reprₓ (sampleable_ext.shrink x).toList}
              ")
            ()
      else pure ()
    let ⟨y, r, ⟨h₁⟩⟩ ←
      (SampleableExtₓ.shrink x).mfirst fun ⟨a, h⟩ => do
          let ⟨r⟩ ←
            monadLift
                (Uliftable.up <| Testableₓ.run (β (interp α a)) cfg true :
                  Genₓ (ULift <| test_result <| β <| interp α a))
          if is_failure r then pure (⟨a, r, ⟨h⟩⟩ : Σa, test_result (β (interp α a)) × Plift (sizeof_lt a x))
            else failure
    if cfg then return <| trace ((s! "{var } := {reprₓ y}") ++ format_failure' "Shrink counter-example:" r) ()
      else pure ()
    f_rec y h₁ (n + 1) <|> pure ⟨y, add_shrinks (n + 1) r⟩

/-- Once a property fails to hold on an example, look for smaller counter-examples
to show the user. -/
def minimize [SampleableExtₓ α] [∀ x, Testableₓ (β x)] (cfg : SlimCheckCfg) (var : Stringₓ) (x : ProxyRepr α)
    (r : TestResultₓ (β (interp α x))) : Genₓ (Σx, TestResultₓ (β (interp α x))) := do
  if cfg then return <| trace ((s! "{var } := {reprₓ x}") ++ format_failure' "Shrink counter-example:" r) ()
    else pure ()
  let x' ← OptionTₓ.run <| minimizeAux α _ cfg var x 0
  pure <| x' ⟨x, r⟩

instance (priority := 2000) existsTestable (p : Prop)
    [Testableₓ (NamedBinderₓ var (∀ x, NamedBinderₓ var' <| β x → p))] :
    Testableₓ (NamedBinderₓ var' (NamedBinderₓ var (∃ x, β x) → p)) :=
  ⟨fun cfg min => do
    let x ← Testableₓ.run (NamedBinderₓ var (∀ x, NamedBinderₓ var' <| β x → p)) cfg min
    pure <| convert_counter_example' exists_imp_distrib x⟩

/-- Test a universal property by creating a sample of the right type and instantiating the
bound variable with it -/
instance varTestable [SampleableExtₓ α] [∀ x, Testableₓ (β x)] : Testableₓ (NamedBinderₓ var <| ∀ x : α, β x) :=
  ⟨fun cfg min => do
    (Uliftable.adaptDown (sampleable_ext.sample α)) fun x => do
        let r ← testable.run (β (sampleable_ext.interp α x)) cfg ff
        (Uliftable.adaptDown
              (if is_failure r ∧ min then minimize _ _ cfg var x r
              else if cfg then (trace s! "  {var } := {reprₓ x}") <| pure ⟨x, r⟩ else pure ⟨x, r⟩))
            fun ⟨x, r⟩ =>
            return <| trace_if_giveup cfg var x r (add_var_to_counter_example var x (· <| sampleable_ext.interp α x) r)⟩

/-- Test a universal property about propositions -/
instance propVarTestable (β : Prop → Prop) [I : ∀ b : Bool, Testableₓ (β b)] :
    Testableₓ (NamedBinderₓ var <| ∀ p : Prop, β p) :=
  ⟨fun cfg min => do
    (convert_counter_example fun h (b : Bool) => h b) <$> @testable.run (named_binder var <| ∀ b : Bool, β b) _ cfg min⟩

instance (priority := 3000) unusedVarTestable (β) [Inhabited α] [Testableₓ β] :
    Testableₓ (NamedBinderₓ var <| ∀ x : α, β) :=
  ⟨fun cfg min => do
    let r ← Testableₓ.run β cfg min
    pure <| convert_counter_example (· <| default) r (PSum.inr fun x _ => x)⟩

instance (priority := 2000) subtypeVarTestable {p : α → Prop} [∀ x, PrintablePropₓ (p x)] [∀ x, Testableₓ (β x)]
    [I : SampleableExtₓ (Subtype p)] : Testableₓ (NamedBinderₓ var <| ∀ x : α, NamedBinderₓ var' <| p x → β x) :=
  ⟨fun cfg min => do
    let test (x : Subtype p) : Testableₓ (β x) :=
      ⟨fun cfg min => do
        let r ← Testableₓ.run (β x.val) cfg min
        match print_prop (p x) with
          | none => pure r
          | some str => pure <| add_to_counter_example (s! "guard: {str} (by construction)") id r (PSum.inr id)⟩
    let r ← @Testableₓ.run (∀ x : Subtype p, β x.val) (@SlimCheck.varTestable var _ _ I test) cfg min
    pure <| convert_counter_example' ⟨fun (h : ∀ x : Subtype p, β x) x h' => h ⟨x, h'⟩, fun h ⟨x, h'⟩ => h x h'⟩ r⟩

instance (priority := 100) decidableTestable (p : Prop) [PrintablePropₓ p] [Decidable p] : Testableₓ p :=
  ⟨fun cfg min =>
    return <|
      if h : p then success (PSum.inr h)
      else
        match printProp p with
        | none => failure h [] 0
        | some str => failure h [s! "issue: {str} does not hold"] 0⟩

instance Eq.printablePropₓ {α} [HasRepr α] (x y : α) : PrintablePropₓ (x = y) :=
  ⟨some s!"{(reprₓ x)} = {reprₓ y}"⟩

instance Ne.printablePropₓ {α} [HasRepr α] (x y : α) : PrintablePropₓ (x ≠ y) :=
  ⟨some s!"{(reprₓ x)} ≠ {reprₓ y}"⟩

instance Le.printableProp {α} [LE α] [HasRepr α] (x y : α) : PrintablePropₓ (x ≤ y) :=
  ⟨some s!"{(reprₓ x)} ≤ {reprₓ y}"⟩

instance Lt.printableProp {α} [LT α] [HasRepr α] (x y : α) : PrintablePropₓ (x < y) :=
  ⟨some s!"{(reprₓ x)} < {reprₓ y}"⟩

instance Perm.printableProp {α} [HasRepr α] (xs ys : List α) : PrintablePropₓ (xs ~ ys) :=
  ⟨some s!"{(reprₓ xs)} ~ {reprₓ ys}"⟩

instance And.printablePropₓ (x y : Prop) [PrintablePropₓ x] [PrintablePropₓ y] : PrintablePropₓ (x ∧ y) :=
  ⟨do
    let x' ← printProp x
    let y' ← printProp y
    some s! "({x' } ∧ {y'})"⟩

instance Or.printablePropₓ (x y : Prop) [PrintablePropₓ x] [PrintablePropₓ y] : PrintablePropₓ (x ∨ y) :=
  ⟨do
    let x' ← printProp x
    let y' ← printProp y
    some s! "({x' } ∨ {y'})"⟩

instance Iff.printablePropₓ (x y : Prop) [PrintablePropₓ x] [PrintablePropₓ y] : PrintablePropₓ (x ↔ y) :=
  ⟨do
    let x' ← printProp x
    let y' ← printProp y
    some s! "({x' } ↔ {y'})"⟩

instance Imp.printablePropₓ (x y : Prop) [PrintablePropₓ x] [PrintablePropₓ y] : PrintablePropₓ (x → y) :=
  ⟨do
    let x' ← printProp x
    let y' ← printProp y
    some s! "({x' } → {y'})"⟩

instance Not.printablePropₓ (x : Prop) [PrintablePropₓ x] : PrintablePropₓ ¬x :=
  ⟨do
    let x' ← printProp x
    some s! "¬ {x'}"⟩

instance True.printablePropₓ : PrintablePropₓ True :=
  ⟨some "true"⟩

instance False.printablePropₓ : PrintablePropₓ False :=
  ⟨some "false"⟩

instance Bool.printablePropₓ (b : Bool) : PrintablePropₓ b :=
  ⟨some <| if b then "true" else "false"⟩

section Io

open _Root_.Nat

variable {p : Prop}

/-- Execute `cmd` and repeat every time the result is `gave_up` (at most
`n` times). -/
def retryₓ (cmd : Randₓ (TestResultₓ p)) : ℕ → Randₓ (TestResultₓ p)
  | 0 => return <| gave_up 1
  | succ n => do
    let r ← cmd
    match r with
      | success hp => return <| success hp
      | failure Hce xs n => return (failure Hce xs n)
      | gave_up _ => retry n

/-- Count the number of times the test procedure gave up. -/
def giveUpₓ (x : ℕ) : TestResultₓ p → TestResultₓ p
  | success (PSum.inl ()) => gave_up x
  | success (PSum.inr p) => success (PSum.inr p)
  | gave_up n => gave_up (n + x)
  | failure Hce xs n => failure Hce xs n

variable (p)

variable [Testableₓ p]

/-- Try `n` times to find a counter-example for `p`. -/
def Testableₓ.runSuiteAux (cfg : SlimCheckCfg) : TestResultₓ p → ℕ → Randₓ (TestResultₓ p)
  | r, 0 => return r
  | r, succ n => do
    let size := (cfg.numInst - n - 1) * cfg.maxSize / cfg.numInst
    when cfg <| return <| trace s!"[slim_check: sample]" ()
    let x ← retryₓ ((Testableₓ.run p cfg true).run ⟨size⟩) 10
    match x with
      | success (PSum.inl ()) => testable.run_suite_aux r n
      | success (PSum.inr Hp) => return <| success (PSum.inr Hp)
      | failure Hce xs n => return (failure Hce xs n)
      | gave_up g => testable.run_suite_aux (give_up g r) n

/-- Try to find a counter-example of `p`. -/
def Testableₓ.runSuite (cfg : SlimCheckCfg := {  }) : Randₓ (TestResultₓ p) :=
  Testableₓ.runSuiteAux p cfg (success <| PSum.inl ()) cfg.numInst

/-- Run a test suite for `p` in `io`. -/
def Testableₓ.check' (cfg : SlimCheckCfg := {  }) : Io (TestResultₓ p) :=
  match cfg.randomSeed with
  | some seed => Io.runRandWith seed (Testableₓ.runSuite p cfg)
  | none => Io.runRand (Testableₓ.runSuite p cfg)

namespace Tactic

open _Root_.Tactic Expr

/-!
## Decorations

Instances of `testable` use `named_binder` as a decoration on
propositions in order to access the name of bound variables, as in
`named_binder "x" (forall x, x < y)`.  This helps the
`testable` instances create useful error messages where variables
are matched with values that falsify a given proposition.

The following functions help support the gadget so that the user does
not have to put them in themselves.
-/


/-- `add_existential_decorations p` adds `a `named_binder` annotation at the
root of `p` if `p` is an existential quantification. -/
unsafe def add_existential_decorations : expr → expr
  | e@(quote.1 (@Exists (%%ₓα) (%%ₓlam n bi d b))) =>
    let n := toString n
    const `` named_binder [] (quote.1 n : expr) e
  | e => e

/-- Traverse the syntax of a proposition to find universal quantifiers
and existential quantifiers and add `named_binder` annotations next to
them. -/
unsafe def add_decorations : expr → expr
  | e =>
    e.replace fun e _ =>
      match e with
      | pi n bi d b =>
        let n := toString n
        some <|
          const `` named_binder [] (quote.1 n : expr) (pi n bi (add_existential_decorations d) (add_decorations b))
      | e => none

/-- `decorations_of p` is used as a hint to `mk_decorations` to specify
that the goal should be satisfied with a proposition equivalent to `p`
with added annotations. -/
@[reducible, nolint unused_arguments]
def DecorationsOf (p : Prop) :=
  Prop

/-- In a goal of the shape `⊢ tactic.decorations_of p`, `mk_decoration` examines
the syntax of `p` and add `named_binder` around universal quantifications and
existential quantifications to improve error messages.

This tool can be used in the declaration of a function as follows:

```lean
def foo (p : Prop) (p' : tactic.decorations_of p . mk_decorations) [testable p'] : ...
```

`p` is the parameter given by the user, `p'` is an equivalent proposition where
the quantifiers are annotated with `named_binder`.
-/
unsafe def mk_decorations : tactic Unit := do
  let quote.1 (Tactic.DecorationsOf (%%ₓp)) ← target
  exact <| add_decorations p

end Tactic

/-- Run a test suite for `p` and return true or false: should we believe that `p` holds? -/
def Testableₓ.check (p : Prop) (cfg : SlimCheckCfg := {  })
    (p' : Tactic.DecorationsOf p := by
      run_tac
        tactic.mk_decorations)
    [Testableₓ p'] : Io PUnit := do
  let x ←
    match cfg.randomSeed with
      | some seed => Io.runRandWith seed (Testableₓ.runSuite p' cfg)
      | none => Io.runRand (Testableₓ.runSuite p' cfg)
  match x with
    | success _ => when ¬cfg <| Io.putStrLn "Success"
    | gave_up n => Io.fail s! "Gave up {reprₓ n} times"
    | failure _ xs n => do
      Io.fail <| format_failure "Found problems!" xs n

end Io

end SlimCheck


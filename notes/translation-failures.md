# Translation failures

We gather here failures in translation with target a single theorem or definition.

* Each section should have
  * A level two heading `## ...` with the nature of the failure. 
  * At least one example.
  * We add suggested fixes as we think of them.
  * Note the result of manually attempted fix.
  * Note ideas for automated fixes.
* Use subheadings `### ...` and below for different parts of the analysis.
* When in doubt, split into multiple sections.

## Lean Syntax Error: `∃!` with multiple arguments

## Example

* Text: "Let $p > 1$ be an integer with the property that $x^2 - x + p$ is prime for all $x$ in the range $0 < x < p$. Show there exists exactly one triple of integers $a,b,c$ satisfying $b^2 - 4ac = 1 - 4p$, $0 < a \\leq c$, and $-a \\leq b < a$."
* Lean translation: `∀ {p : ℤ}, 1 < p → (∀ x, 0 < x ∧ x < p → Nat.Prime (x ^ 2 - x + p)) → ∃! (a b c : ℤ), b ^ 2 - 4 * a * c = 1 - 4 * p ∧ 0 < a ∧ a ≤ c ∧ -a ≤ b ∧ b < a`
* Error message:"The `ExistsUnique` notation should not be used with more than one binder.\n\nThe reason for this is that `∃! (x : α), ∃! (y : β), p x y` has a completely different meaning from `∃! q : α × β, p q.1 q.2`. To prevent confusion, this notation requires that you be explicit and use one with the correct interpretation."

## Recognizing the error

This is easy to recognize from the error message.

## Fixing the error

* Write a parser in Lean to recognize the pattern - this may already exist for reporting the error (not needed?).
* Match in the syntax tree and replace with the correct form.
* One can even do this with strings and regular expressions.

## Manual fix

Easy here but should be done for completeness.
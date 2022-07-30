def Nat.divides (a b : Nat) : Prop := b % a = 0

infix:65 "|" => Nat.divides

def prime(n: Nat): Prop := (n > 1) ∧ (∀ d: Nat, d | n → d = 1 ∨ d = n)

/- Text: Every natural number is greater or equal to than $0$  -/
example : Prop := ∀ n : Nat, n ≥ 0

/- 
* Text: Every natural number $n$, where $n$ is greater than $1$, is divisible by a prime number 

* Text: Every natural number $n$ which is greater than $1$ is divisible by a prime number
-/
example : Prop := ∀ n : Nat, n > 1 → ∃ p : Nat, prime p ∧  p | n

/-
Text: if a prime number $p$ divides the product of $m$ and $n$,  $p$ divides one of $m$ and $n$

Text: if a prime number $p$ divides the product of $m$ and $n$,  $p$ divides $m$ or $n$"

Text: if a prime number $p$ divides $mn$, $p$ divides $m$ or $n$
-/
example : Prop := ∀ p : Nat, prime p → ∀ m n : Nat, p | m * n → p | m ∨ p | n

/-
* Text: Six is not the sum of two distinct primes
* Text: $6$ is not the sum of two distinct prime numbers
-/
example : Prop := ¬ (∃ n m: Nat, prime n ∧ prime m ∧ n ≠ m ∧ 6 = n + m)

/- 
* Text: Six is not a square 
* Text: $6$ is not a perfect square
-/
example : Prop := ¬(∃ n: Nat, n * n = 6)

-- Background for the next example:
variable (A B : Type)(φ : A → B)(e: B)
/-
Text: $\ker \phi$ is the set of all $a\in A$ that map to the identity element in $B$
-/
def ker :=  {a : A // φ a = e}

example : 1 = 1 := by simp_arith

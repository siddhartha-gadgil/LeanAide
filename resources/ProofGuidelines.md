Please write the proof in a style suitable for formalization in the Lean Theorem Prover. Concretely, follow the following guidelines:

### **Declarative over imperative**: focusing on what is true, not instructing the reader.
  
### **Explicit naming of quantities**: introducing objects with clear, reusable identifiers.

###  State All Assumptions and Types Upfront

A formal proof operates within a specific **context**. Clearly stating everything you're assuming at the beginning makes this context explicit.
* **Instead of:** "In this proof, $n$ is a natural number greater than 1."
* **Do this:** "Assume $n$ is a natural number and $n > 1$."


###  Justify Every Step, Citing Its Premises

Every new conclusion must logically follow from previous statements. In an informal proof, we often combine steps. For formalization, it's better to make each logical leap a separate, justified statement.
* **Instead of:** "Since $p$ is the smallest prime factor of $n$, and $d$ divides $n$ with $d < p$, $d$ must be 1."
* **Do this:** "Let $p$ be the smallest prime factor of $n$. Assume $d$ is a divisor of $n$ and $d < p$. By the definition of a prime factor, any divisor of $n$ other than 1 must be greater than or equal to the smallest prime factor $p$. Since $d < p$, $d$ cannot be a prime factor. Since $d$ divides $n$, this leaves $d=1$."
* In case something is true *by definition*, spell out by definition of what. For instance, numbers $p$ and $q$ could be equal because of the definition of $p$ or the definition of $q$.

###  Decompose the Proof into Lemmas

Complex proofs are rarely formalized in one go. Breaking a large proof into smaller, self-contained **lemmas** is standard practice and highly encouraged. This makes the proof modular, easier to read, and promotes reusability.

Before starting the main proof, state and prove the small, intermediate results you'll need.
* **Example:** When proving that every integer $n > 1$ has a prime factor, you might first prove a lemma:

    * **Lemma 1:** If an integer $k > 1$ is not prime, it has a divisor $d$ such that $1 < d < k$.

    * **Main Proof:** "Proceed by strong induction on $n$. ... If $n$ is not prime, by Lemma 1, there exists a divisor $d$ such that $1 < d < n$. By the induction hypothesis, $d$ has a prime factor, which is also a prime factor of $n$."

###  Be Explicit with Case Analysis

When a proof splits into cases, state the justification for the case split and ensure the cases are exhaustive.
* **Instead of:** "Now consider if $n$ is even or odd."
* **Do this:** "Every integer $n$ is either even or odd. We proceed by case analysis.

    * **Case 1:** Assume $n$ is even. Then by definition, $n = 2k$ for some integer $k$. ...

    * **Case 2:** Assume $n$ is odd. Then by definition, $n = 2k + 1$ for some integer $k$. ...

    Since we have proven the result in all cases, the statement holds for all integers $n$."

### Prefer Constructive Arguments

When proving an existence statement (e.g., "there exists an $x$ such that $P(x)$"), a proof that provides the object $x$ (a "witness") is **constructive**. A proof that shows the non-existence of $x$ leads to a contradiction is **non-constructive**.

While Lean can handle non-constructive proofs, constructive proofs are often more direct and simpler to formalize.
* **Non-constructive:** "Assume for contradiction that no such $x$ exists. ... This leads to a contradiction. Therefore, such an $x$ must exist."
* **Constructive:** "Let $x_0 = f(y)$. We now show that $P(x_0)$ holds. ... Thus, an $x$ satisfying $P(x)$ exists."

### Be Fully Explicit About Assumptions and Quantifiers

Avoid relying on "it is clear that..." or implicit assumptions. Instead:
* State all hypotheses explicitly before using them.
  
* For example, instead of "this holds because a < b", write:
  "Since a<ba < b, and ff is monotonic by hypothesis hh, we have f(a)<f(b)f(a) < f(b)."
  

In Lean, every assumption must be named and passed to functions or lemmas.
* * *

###  Use Modular Lemmas and Definitions

Structure proofs so that each step can, in principle, be factored into a lemma:
* If a proof uses an idea more than once, define it as a named helper.
  
* Prefer referring to known lemmas (e.g., "by the triangle inequality") rather than rederiving facts.
  

In Lean, this encourages reuse and better composability.
* * *

###  Avoid Ambiguity in Notation or Scope

Human readers disambiguate easily; Lean does not.
* Clarify the scope of variables and the domains of quantification.
  
* Prefer “Let x∈X \in X” over “Take x”.
  

In Lean, `x : X` is always the form in contexts and proofs.
* * *

###  Avoid Pronouns and Natural Language Shortcuts

Expressions like “this”, “that one”, or “the former” create ambiguity.
* Instead of "this function", say "the function ff".
  
* Instead of "it follows", say "it follows from hypothesis h1h_1 and lemma foofoo".
  
* * *

### Use Definitions When Needed

* Instead of “the set of all xx such that ...”, say
  “Let S:={x∈N∣P(x)}S := \{ x \in \mathbb{N} \mid P(x) \}.”
  
### Define only ONE object per definition

* Avoid a chain of definitions in a single statement, such as "let $p(x)$ be the minimal polynomial of the field $F$ and let $a$ be its root". Instead split into two or more definitions.
* Do not include assertions about the object being defined as part of the definition. Instead make a separate assertion/lemma/theorem.

### Avoid Overloaded Language

Many words (e.g., “is trivial”, “clearly”, “obviously”) are informal and vague.
* Instead of “the result is trivial”, say what the result is and *why* it follows directly.
  

### State the Goal Clearly at Each Step

Break long arguments into intermediate goals.
* Use "We aim to show that..." or "It suffices to prove..." with precision.
  
###  Respect the Order of Dependencies

Only use objects after they are introduced.

### Use Consistent Naming for Hypotheses and Objects

You can adopt Lean's naming conventions:
* Use lowercase for objects (`x`, `n`, `f`)
  
* Prefix hypotheses (`h1`, `hf`, `hp`) consistently
  

### Minimize Appeals to Intuition or Visual Reasoning

If the step relies on a diagram or an appeal to intuition (e.g., “as can be seen from the graph”), wherever possible replace it with a precise statement or lemma.

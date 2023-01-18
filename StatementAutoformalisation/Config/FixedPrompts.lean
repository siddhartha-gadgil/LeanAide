import StatementAutoformalisation.Declaration

/-- The fixed `Declaration`s that will be added to the beginning of the prompt. 
  The `Mathlib` import is required to parse the specialised notation. -/
def leanChatPrompts : Lean.MetaM <| Array DeclarationWithDocstring := 
return #[
  {
    kind := "theorem",
    name := "abs_sum_leq_sum_abs",
    args := "(n : ℕ) (f : ℕ → ℂ)",
    type := "abs (∑ i in finset.range n, f i) ≤ ∑ i in finset.range n, abs (f i)",
    docstring := "If $z_1, \\dots, z_n$ are complex, then $|z_1 + z_2 + \\dots + z_n|\\leq |z_1| + |z_2| + \\dots + |z_n|$."
  },
  {
    kind := "theorem",
    name := "sum_add_square_sub_square_eq_sum_square",
    args := "(n : ℕ) (x y : euclidean_space ℝ (fin n))",
    type := "∥x + y∥^2 + ∥x - y∥^2 = 2*∥x∥^2 + 2*∥y∥^2",
    docstring := "If x and y are in $\\mathbb{R}^n$, then $|x+y|^2 + |x-y|^2 = 2|x|^2 + 2|y|^2$."
  },
  {
    kind := "theorem",
    name := "distinct_powers_of_infinite_order_element",
    args := "(G : Type*) [group G] (x : G) (hx : x ≠ 1) (hx_inf : ∀ n : ℕ, x ^ n ≠ 1)",
    type := "∀ m n : ℤ, m ≠ n → x ^ m ≠ x ^ n",
    docstring := "If $x$ is an element of infinite order in $G$, prove that the elements $x^n$, $n\\in\\mathbb{Z}$ are all distinct."
  },
  {
    kind := "theorem",
    name := "subset_of_open_subset_is_open",
    args := "(X : Type*) [topological_space X] (A : set X) (hA : ∀ x ∈ A, ∃ U : set X, is_open U ∧ x ∈ U ∧ U ⊆ A)",
    type := "is_open A",
    docstring := "Let $X$ be a topological space; let $A$ be a subset of $X$. Suppose that for each $x\\in A$ there is an open set $U$ containing $x$ such that $U\\subset A$. Show that $A$ is open in $X$."
  }
]
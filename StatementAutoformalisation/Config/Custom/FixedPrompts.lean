import StatementAutoformalisation.Declaration

/-- The fixed `Declaration`s that will be added to the beginning of the prompt. 
  The `Mathbin.All` import is required to parse the specialised notation. -/
def fixedPrompts : Lean.MetaM <| Array DeclarationWithDocstring := 
#["/-- If $z_1, \\dots, z_n$ are complex, then $|z_1 + z_2 + \\dots + z_n|\\leq |z_1| + |z_2| + \\dots + |z_n|$. -/
  theorem abs_sum_leq_sum_abs (n : ℕ) (f : ℕ → ℂ) :
    abs (∑ i in finset.range n, f i) ≤ ∑ i in finset.range n, abs (f i)",

  "/-- If x and y are in $\\mathbb{R}^n$, then $|x+y|^2 + |x-y|^2 = 2|x|^2 + 2|y|^2$. -/
  theorem sum_add_square_sub_square_eq_sum_square (n : ℕ) (x y : euclidean_space ℝ (fin n)) :
    ∥x + y∥^2 + ∥x - y∥^2 = 2*∥x∥^2 + 2*∥y∥^2",

  "/-- If $x$ is an element of infinite order in $G$, prove that the elements $x^n$, $n\\in\\mathbb{Z}$ are all distinct. -/
  theorem distinct_powers_of_infinite_order_element (G : Type*) [group G] (x : G)
  (hx : x ≠ 1) (hx_inf : ∀ n : ℕ, x ^ n ≠ 1) :
  ∀ m n : ℤ, m ≠ n → x ^ m ≠ x ^ n",

  "/-- Let $X$ be a topological space; let $A$ be a subset of $X$. Suppose that for each $x\\in A$ there is an open set $U$ containing $x$ such that $U\\subset A$. Show that $A$ is open in $X$. -/
    theorem subset_of_open_subset_is_open (X : Type*) [topological_space X] 
  (A : set X) (hA : ∀ x ∈ A, ∃ U : set X, is_open U ∧ x ∈ U ∧ U ⊆ A): 
  is_open A "] 
    |>.filterMapM' DeclarationWithDocstring.fromString?
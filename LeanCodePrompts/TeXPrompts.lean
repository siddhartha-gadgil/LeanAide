def teXPrompts := #[
  ("\\forall a, b \\in G, ab = ba", "∀ a b : G, a * b = b * a"),
  ("\\int_{x = a}^b f(x) dx", "∫ (x : ℝ) in a..b, f x"),
  ("\\sin x = x - \\frac{x^3}{3!} + \\frac{x^5}{5!} - \\frac{x^7}{7!} + \\cdots = \\sum_{n=0}^\\infty \\frac{(-1)^n}{(2n+1)!}x^{2n+1}", "real.sin x = ∑' (n : ℕ), (-1)^n / (2 * n + 1)! * x^(2 * n + 1))"),
  ("\\forall n, k \\in \\mathbb{N}, k \\leq n \\implies 0 \\lt \\binom{n}{k}", "∀ {n k : ℕ}, k ≤ n → 0 < n.choose k"),
  ("\\frac{1}{|G|} \\sum_{g \\in G} g⁻¹ • π(g • -)", "⅟(fintype.card G : k) • (π.sum_of_conjugates_equivariant G)"),
  ("\\sigma_k(n)=\\sum_{d\\mid n} d^k", "σ k n = ∑ d in divisors n, d ^ k"),
  ("\\lim_{t \\to \\infty} \\int_{x=0}^t x dx = \\infty", "tendsto (λ t, ∫ x in 0..t, x) at_top at_top"),
  ("\\lim_{t \\to -\\infty} \\int_{x=0}^t x dx = -\\infty", "tendsto (λ t, ∫ x in 0..t, x) at_bot at_bot"),
  ("\\mu\\left(\\overline{\\{a \\vert f(a) \\leq g(a) \\}}\\right) = \\mu\\left(s\\right)", "μ (closure {a | f a ≤ g a}) = μ s"),
  ("\\prod_{i=0}^m \\frac {1}{1-X^{2i+1}}$$", "∏ i in range m, (1 - (X : power_series α)^(2*i+1))⁻¹"),
  ("\\left|exp^{a\\left(e^{z}+e^{-z}\right)}\\right| \\le e^{a\\cos b \\exp^{|re z|}}", "abs (exp (a * (exp z + exp (-z)))) ≤ real.exp (a * real.cos b * real.exp (|z.re|))"),
  ("d + 1) (1 + y)^d - (d + 1)y^d = \\sum_{i = 0}^d {d + 1 \\choose i} \\cdot i \\cdot y^{i - 1}", "eval (1 + y) (monomial d (d + 1 : S)) - eval y (monomial d (d + 1 : S)) =
  ∑ (i : ℕ) in range (d + 1), ↑((d + 1).choose i) * (↑i * y ^ (i - 1))"),
  ("\\left| ab(a^2 - b^2) + bc(b^2 - c^2) + ca(c^2 - a^2) \\right|
≤ M (a^2 + b^2 + c^2)^2", "|a * b * (a^2 - b^2) + b * c * (b^2 - c^2) + c * a * (c^2 - a^2)| ≤ M * (a^2 + b^2 + c^2)^2)")
]
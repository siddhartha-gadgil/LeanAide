## Rule-based translations

- Inequalities ($\le$, $\leq$, $a \leq b \leq c$)
- Subsets ($A \subset B$, $A \subset B \subset C$)
- Binomial coefficients ($\binom{n}{k}$, $n \choose k$)
- Factorials
- Fractions ($\frac{1}{2}$)
- Roots ($\sqrt{4}$, $\sqrt[3]{5}$)
- Powers, exponents
- Floor, ceiling, absolute value functions
- Intervals ($[0, 1]$, $(2, 3]$)
- Unions and intersections (both finite and infinite)
- Embellished names ($\mathbb{R}, $\Hom$, $\operatorname{Int}$)

## Input-dependent prompting

- Finite sums and products ($\sum_{n = 1}^{10} n^2$, $x_{1} \cdot x_{2} \cdot \cdots \cdot x_{n}$)
- Infinite sums and products ($\sum_{n=1}^{\infty} \frac{1}{n^2}$)
- Limits ($\lim_{n \to \infty} \frac{1}{n}$)
- Multiplication without dot ($ab = ba$) (**Comment:** Since this is based on the _lack of_ a pattern, there is no clear way to do input-dependent prompting. We can just include a few fixed prompts to handle this kind of syntax) 
- Finite sequences ($a_{1}, a_{2}, \ldots, a_{n}$)
- Big O notation
- Integrals ($\int_{0}^{5} 2x dx$)
- Subscripts (for $t \in [0, 1]$, $f_{t}$ is a continuous map from $X$ to $Y$)
- Modular arithmetic/Congruence ($2 \equiv 7 \pmod 5$)
- Exists unique ($\exists!$)

## Examples

- Stirling formula
- Bayes' theorem
- e limit

## Nice to have

- special summation
- ldots with patterns
- casewise functions
- approx eq
- Matrices

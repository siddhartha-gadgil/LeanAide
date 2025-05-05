Okay, here is the extracted core content focusing on the proof that the limit $\lambda_k$ is strictly positive, first in Markdown and then in JSON format.

## Core Mathematical Content (Markdown)

Let $k \ge 2$. Consider a random word $X = X^{(n)} = (X_1, ..., X_n)$ of length $n$ where each $X_i$ is chosen uniformly and independently from the alphabet $A_k = \{\alpha_1, \bar{\alpha}_1, ..., \alpha_k, \bar{\alpha}_k\}$, where $\bar{\alpha}_i$ denotes the inverse of $\alpha_i$.

**Definition (Non-Crossing Matching)**
A *non-crossing matching* for $X$ is a set $P$ of pairs of indices $(i, j)$ with $1 \le i < j \le n$ such that:
(a) Each index $i \in \{1, ..., n\}$ belongs to at most one pair in $P$.
(b) If $(i, k) \in P$ and $(j, l) \in P$ with $i < j < k < l$, this configuration is forbidden (no crossings).
(c) If $(i, j) \in P$, then $X_i = \bar{X}_j$.

**Definition (Length Function $l$)**
The length $l(X)$ is the minimum number of *unmatched* indices over all possible non-crossing matchings $P$ for the word $X$.

**Definition ($L_k(n)$, $p_k(n)$, $\lambda_k$)**
Let $L_k(n) = E[l(X^{(n)})]$ where the expectation is over the uniform distribution on words of length $n$. Let $p_k(n) = L_k(n)/n$.

**Lemma 12.** For $m, n > 0$, $L_k(m+n) \le L_k(m) + L_k(n)$.

**Corollary 13.** The sequence $p_k(n) = L_k(n)/n$ converges to $\lambda_k := \inf_n p_k(n)$.

**Theorem 1 (Main Result - Positivity).** With the above notations, $\lambda_k > 0$.

**Lemma 14.** We have $\lambda_k > 0$.

*Proof of Lemma 14 (and Theorem 1 Positivity):*
Fix $\delta > 0$. Observe that
$$ L_k(n) \ge n\delta \cdot P(l(X^{(n)}) \ge n\delta) $$
and hence
$$ p_k(n) \ge \delta P(l(X^{(n)}) \ge n\delta). $$
To show $\lambda_k > 0$, it suffices to find a $\delta > 0$ such that $P(l(X^{(n)}) \ge n\delta) \to 1$ as $n \to \infty$, or equivalently, $P(l(X^{(n)}) < n\delta) \to 0$.

Let $W(n, \delta)$ be the number of words $X$ of length $n$ such that $l(X) < n\delta$. Then
$$ P(l(X^{(n)}) < n\delta) = \frac{W(n, \delta)}{(2k)^n}. $$
If $l(X^{(n)}) < n\delta$, then $X=X^{(n)}$ has a non-crossing matching with at least $n - n\delta$ matched indices, which means at least $m = \lceil (n-n\delta)/2 \rceil$ pairs. We can consider a matching $M$ with exactly $m' = \lfloor (n-n\delta)/2 \rfloor$ pairs (by dropping pairs if necessary). Let $r = n - 2m'$. Note $r \approx n\delta$.
Such a word $X$ can be determined by:
1.  The set $s$ of $r$ unmatched indices ($|s|=r$).
2.  The word $Y$ (length $r$) of unmatched letters in order.
3.  The word $Z$ (length $2m'$) of matched letters in order.
The matching $M$ provides a complete non-crossing matching on $Z$, meaning $Z$ represents the trivial element in the free group $F_k = \langle \alpha_1, ..., \alpha_k \rangle$.

Let $T_p$ be the set of words of length $p$ in $A_k$ that represent the trivial element in $F_k$. The number of triples $(Y, Z, s)$ is bounded by $\binom{n}{r} (2k)^r |T_{2m'}|$. Thus,
$$ W(n, \delta) \le \binom{n}{r} (2k)^r |T_{2m'}|. $$
Let $\tau_p = |T_p| / (2k)^p$ be the probability that a random word of length $p$ is trivial. We have $\tau_p \le \theta_k^p$ where $\theta_k = \sup_p \tau_p^{1/p} = \frac{\sqrt{2k-1}}{k}$ (Kesten, 1959).
Substituting this into the probability bound:
$$ P(l(X^{(n)}) < n\delta) \le \binom{n}{r} (2k)^r \tau_{2m'} (2k)^{2m'} (2k)^{-n} = \binom{n}{r} \tau_{2m'} $$
$$ \le \binom{n}{r} \theta_k^{2m'} $$
Using the approximation $r \approx n\delta$, $2m' \approx n(1-\delta)$ and the standard bound $\binom{n}{r} \le e^{n h(\delta)}$ where $h(\delta) = -\delta \log \delta - (1-\delta)\log(1-\delta)$ is the binary entropy function, we get:
$$ P(l(X^{(n)}) < n\delta) \le e^{n h(\delta)} \theta_k^{n(1-\delta)} = \exp(n[h(\delta) + (1-\delta)\log \theta_k]) $$
(Note: The calculation on page 11 uses $\tau_{2m} \approx \theta_k^{2m}$ and bounds $W(n,\delta)$ slightly differently leading to $\exp(n[h(\delta) + \log\theta_k])$. Let's follow the paper's final step.)

Let's re-evaluate the bound on $P(l(X^{(n)}) < n \delta)$. From (3) and the subsequent steps on page 10-11:
$|W(n, \delta)| \le \binom{n}{r} (2k)^r |T_{2m}|$ where $r = n-2m$. Assume $r=n\delta$ for simplicity.
$$ P(l(X^{(n)}) < n\delta) = \frac{W(n, \delta)}{(2k)^n} \le \binom{n}{n\delta} \frac{(2k)^{n\delta}}{(2k)^n} |T_{n(1-\delta)}| = \binom{n}{n\delta} \tau_{n(1-\delta)} $$
$$ \le e^{n h(\delta)} \theta_k^{n(1-\delta)} $$
This calculation seems correct. Let's check page 11 again.
The inequality (3) is $|W(n,\delta)| \le \binom{n}{r} (2k)^r |T_{2m}|$.
$P(l(X^{(n)}) < n\delta) = W(n,\delta)/(2k)^n \le \binom{n}{r} (2k)^r |T_{2m}| / (2k)^n = \binom{n}{r} (2k)^r \tau_{2m} (2k)^{2m} / (2k)^n = \binom{n}{r} \tau_{2m}$.
Assuming $r=n\delta$, $2m=n(1-\delta)$.
$P(l(X^{(n)}) < n\delta) \le \binom{n}{n\delta} \tau_{n(1-\delta)} \le e^{nh(\delta)} \theta_k^{n(1-\delta)}$.
This indeed seems different from the paper's expression $e^{n(h(\delta) + \log \theta_k)}$. Let's re-read the paper's derivation on p11 carefully.
It says $P(l(X^{(n)}) < n\delta) \le \exp \{ n(h(\delta) + \log \theta_k) \}$. The derivation uses (3): $|W(n,\delta)| \le \binom{n}{r}(2k)^r |T_{2m}|$.
$P = W/(2k)^n \le \binom{n}{r} (2k)^r T_{2m} / (2k)^n = \binom{n}{r} (2k)^r \tau_{2m} (2k)^{2m} / (2k)^n = \binom{n}{r} \tau_{2m}$.
Using $\tau_{2m} \le \theta_k^{2m}$ and $\binom{n}{r} \le e^{nh(\delta)}$.
$P \le e^{nh(\delta)} \theta_k^{2m}$.
Using $r=n\delta$, $2m = n-r = n(1-\delta)$.
$P \le e^{nh(\delta)} \theta_k^{n(1-\delta)} = \exp(n[h(\delta) + (1-\delta)\log\theta_k])$.

Let's re-derive the paper's version. Perhaps the bound on $W(n,\delta)$ is different.
The triple is $(Y, Z, s)$. $|Y|=r, |Z|=2m$. $|s|=r$. $r+2m=n$.
$W(n,\delta) \le (\text{# choices for } s) \times (\text{# choices for } Y) \times (\text{# choices for } Z)$.
$W(n,\delta) \le \binom{n}{r} \times (2k)^r \times |T_{2m}|$. This is Eq (3) on page 10.
$P(l(X^{(n)}) < n\delta) = W(n,\delta) / (2k)^n \le \binom{n}{r} (2k)^r |T_{2m}| / (2k)^n = \binom{n}{r} \tau_{2m}$.
Assume $r=n\delta$, $2m = n(1-\delta)$.
$P \le \binom{n}{n\delta} \tau_{n(1-\delta)} \le e^{nh(\delta)} \theta_k^{n(1-\delta)}$.

Let's re-read page 11: "Using the elementary fact that $\binom{n}{r} \le e^{nh(\delta)}$ where $h(\delta) = -\delta \log(\delta) - (1-\delta)\log(1-\delta)$ in (3), we get $P(l(X^{(n)}) < n\delta) \le \exp\{n(h(\delta) + \log \theta_k)\}$.
This seems to imply that $\tau_{2m}$ was bounded by $\theta_k^n$ perhaps?
No, the relation is $W(n,\delta) \le \binom{n}{r} (2k)^r |T_{2m}|$.
$P \le \binom{n}{r} (2k)^r \tau_{2m} (2k)^{2m} / (2k)^n = \binom{n}{r} \tau_{2m}$.
Maybe $\tau_{2m} \approx \theta_k^{2m}$ is related to $\log \theta_k$ differently?
$\log P \le n h(\delta) + 2m \log \theta_k = n h(\delta) + n(1-\delta) \log \theta_k$.
The paper states $n h(\delta) + n \log \theta_k$. There might be a typo in the paper or my understanding. Let's assume the paper's condition $h(\delta) + \log \theta_k < 0$ is the one derived somehow.

$P(l(X^{(n)}) < n\delta) \le \exp \{n (h(\delta) + \log \theta_k)\}$.
This probability goes to 0 as $n \to \infty$ provided $h(\delta) + \log \theta_k < 0$.
Since $\theta_k = \frac{\sqrt{2k-1}}{k} < 1$ for $k \ge 2$, we have $\log \theta_k < 0$.
The entropy function $h(\delta) \to 0$ as $\delta \to 0$.
Therefore, for any fixed $k \ge 2$, we can choose $\delta > 0$ small enough such that $h(\delta) < -\log \theta_k$, which means $h(\delta) + \log \theta_k < 0$.
For such a $\delta$, $P(l(X^{(n)}) < n\delta) \to 0$.
This implies $P(l(X^{(n)}) \ge n\delta) \to 1$.
From $p_k(n) \ge \delta P(l(X^{(n)}) \ge n\delta)$, taking the limit (or infimum) gives $\lambda_k = \lim p_k(n) \ge \delta \times 1 = \delta$.
Since we found a $\delta > 0$ for which $\lambda_k \ge \delta$, we must have $\lambda_k > 0$.

(For $k=2$, $\theta_2 = \sqrt{3}/2 \approx 0.866$. $\log \theta_2 \approx -0.1438$. We need $h(\delta) < 0.1438$. $h(0.03) = -0.03 \log 0.03 - 0.97 \log 0.97 \approx -0.03(-3.5) - 0.97(-0.03) \approx 0.105 + 0.029 = 0.134$. So $\delta=0.03$ works, giving $\lambda_2 \ge 0.03$).
$\square$

---

## Core Mathematical Content (JSON)

```json
{
  "document": [
    {
      "block": "Let $k \\ge 2$. Consider a random word $X = X^{(n)} = (X_1, ..., X_n)$ of length $n$ where each $X_i$ is chosen uniformly and independently from the alphabet $A_k = \\{\\alpha_1, \\bar{\\alpha}_1, ..., \\alpha_k, \\bar{\\alpha}_k\\}$, where $\\bar{\\alpha}_i$ denotes the inverse of $\\alpha_i$."
    },
    {
      "name": "Definition 1",
      "header": "Definition",
      "definition": "A *non-crossing matching* for $X$ is a set $P$ of pairs of indices $(i, j)$ with $1 \\le i < j \\le n$ such that:\n(a) Each index $i \\in \\{1, ..., n\\}$ belongs to at most one pair in $P$.\n(b) If $(i, k) \\in P$ and $(j, l) \\in P$ with $i < j < k < l$, this configuration is forbidden (no crossings).\n(c) If $(i, j) \\in P$, then $X_i = \\bar{X}_j$."
    },
    {
      "name": "Definition 2",
      "header": "Definition",
      "definition": "The length $l(X)$ is the minimum number of *unmatched* indices over all possible non-crossing matchings $P$ for the word $X$."
    },
    {
      "name": "Definition 3",
      "header": "Definition",
      "definition": "Let $L_k(n) = E[l(X^{(n)})]$ where the expectation is over the uniform distribution on words of length $n$. Let $p_k(n) = L_k(n)/n$."
    },
    {
      "name": "Lemma 12",
      "header": "Lemma",
      "claim": "For $m, n > 0$, $L_k(m+n) \\le L_k(m) + L_k(n)$."
    },
    {
      "name": "Corollary 13",
      "header": "Corollary",
      "claim": "The sequence $p_k(n) = L_k(n)/n$ converges to $\\lambda_k := \\inf_n p_k(n)$."
    },
    {
      "name": "Theorem 1",
      "header": "Theorem",
      "claim": "With the above notations, $\\lambda_k > 0$."
    },
    {
      "name": "Lemma 14",
      "header": "Lemma",
      "claim": "We have $\\lambda_k > 0$."
    },
    {
      "proof": {
        "claim_name": "Lemma 14",
        "proof_steps": [
          {
            "block": "Fix $\\delta > 0$. Observe that\n$$ L_k(n) \\ge n\\delta \\cdot P(l(X^{(n)}) \\ge n\\delta) $$ \nand hence\n$$ p_k(n) \\ge \\delta P(l(X^{(n)}) \\ge n\\delta). $$ \nTo show $\\lambda_k > 0$, it suffices to find a $\\delta > 0$ such that $P(l(X^{(n)}) \\ge n\\delta) \\to 1$ as $n \\to \\infty$, or equivalently, $P(l(X^{(n)}) < n\\delta) \\to 0$."
          },
          {
            "block": "Let $W(n, \\delta)$ be the number of words $X$ of length $n$ such that $l(X) < n\\delta$. Then $P(l(X^{(n)}) < n\\delta) = \\frac{W(n, \\delta)}{(2k)^n}$.\nIf $l(X^{(n)}) < n\\delta$, then $X$ has a non-crossing matching $M$ with $2m'$ matched pairs, where $2m' \\ge n(1-\\delta)$. Let $r = n-2m'$ be the number of unmatched letters. Note $r \\le n\\delta$. The word $X$ is determined by the set $s$ of unmatched indices ($|s|=r$), the word $Y$ of unmatched letters (length $r$), and the word $Z$ of matched letters (length $2m'$). $Z$ must represent the trivial element in the free group $F_k = \\langle \\alpha_1, ..., \\alpha_k \\rangle$."
          },
          {
            "block": "Let $T_p$ be the set of words of length $p$ in $A_k$ that represent the trivial element in $F_k$. The number of words $W(n,\\delta)$ is bounded by the number of ways to choose $s$, $Y$, and $Z$: \n$$ W(n, \\delta) \\le \\binom{n}{r} (2k)^r |T_{2m'}|. $$"
          },
          {
            "block": "Let $\\tau_p = |T_p| / (2k)^p$ be the probability that a random word of length $p$ is trivial. We have $\\tau_p \\le \\theta_k^p$ where $\\theta_k = \\sup_p \\tau_p^{1/p} = \\frac{\\sqrt{2k-1}}{k}$.\n$$ P(l(X^{(n)}) < n\\delta) = \\frac{W(n, \\delta)}{(2k)^n} \\le \\binom{n}{r} \\frac{(2k)^r |T_{2m'}|}{(2k)^n} = \\binom{n}{r} \\tau_{2m'}. $$"
          },
          {
            "block": "Using the approximation $r \\approx n\\delta$, $2m' \\approx n(1-\\delta)$, the standard bound $\\binom{n}{r} \\le e^{n h(\\delta)}$ where $h(\\delta) = -\\delta \\log \\delta - (1-\\delta)\\log(1-\\delta)$, and $\\tau_{2m'} \\le \\theta_k^{2m'}$:\n$$ P(l(X^{(n)}) < n\\delta) \\le e^{n h(\delta)} \\theta_k^{n(1-\\delta)} = \\exp(n[h(\\delta) + (1-\\delta)\\log \\theta_k]). $$ \n(Note: The paper text uses the bound $\\exp \\{n (h(\\delta) + \\log \\theta_k)\\}$ on page 11. We proceed assuming the paper's derived condition for convergence.)\n$$ P(l(X^{(n)}) < n\\delta) \\le \\exp \\{n (h(\\delta) + \\log \\theta_k)\\} $$ This probability goes to 0 as $n \\to \\infty$ provided $h(\\delta) + \\log \\theta_k < 0$."
          },
          {
            "block": "Since $\\theta_k = \\frac{\\sqrt{2k-1}}{k} < 1$ for $k \\ge 2$, we have $\\log \\theta_k < 0$. The entropy function $h(\\delta) \\to 0$ as $\\delta \\to 0$. Therefore, for any fixed $k \\ge 2$, we can choose $\\delta > 0$ small enough such that $h(\\delta) < -\\log \\theta_k$, which means $h(\\delta) + \\log \\theta_k < 0$. For such a $\\delta$, $P(l(X^{(n)}) < n\\delta) \\to 0$. This implies $P(l(X^{(n)}) \\ge n\\delta) \\to 1$."
          },
          {
            "block": "From $p_k(n) \\ge \\delta P(l(X^{(n)}) \\ge n\\delta)$, taking the limit gives $\\lambda_k = \\lim p_k(n) \\ge \\delta \\times 1 = \\delta$. Since we found a $\\delta > 0$ for which $\\lambda_k \\ge \\delta$, we must have $\\lambda_k > 0$. $\\square$"
          }
        ]
      }
    }
  ]
}
```
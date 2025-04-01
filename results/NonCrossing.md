```json
{
  "document": [
    {
      "title": "RANDOM WORDS IN FREE GROUPS, NON-CROSSING MATCHINGS AND RNA SECONDARY STRUCTURES"
    },
    {
      "abstract": "Consider a random word $X^n = (X_1, ..., X_n)$ in an alphabet consisting of 4 letters, with the letters viewed either as A, U, G and C (i.e., nucleotides in an RNA sequence) or $α, \\bar{α}, β$ and $\\bar{β}$ (i.e., generators of the free group $(α, β)$ and their inverses). We show that the expected fraction $p(n)$ of unpaired bases in an optimal RNA secondary structure (with only Watson-Crick bonds and no pseudo-knots) converges to a constant $λ_2$ with $0 < λ_2 < 1$ as $n → ∞$. Thus, a positive proportion of the bases of a random RNA string do not form hydrogen bonds. We do not know the exact value of $λ_2$, but we derive upper and lower bounds for it. In terms of free groups, $p(n)$ is the ratio of the length of the shortest word representing $X$ in the generating set consisting of conjugates of generators and their inverses to the word length of $X$ with respect to the standard generators and their inverses. Thus for a typical word the word length in the (infinite) generating set consisting of the conjugates of standard generators grows linearly with the word length in the standard generators. In fact, we show that a similar result holds for all non-abelian finitely generated free groups $(α_1,..., α_k), k ≥ 2$."
    },
    {
      "header": "section",
      "name": "1. INTRODUCTION",
      "content": [
        {
          "Block": "Consider a word $X$ in an alphabet consisting of 4 letters, with the letters viewed either as $α, \\bar{α}, β$ and $\\bar{β}$ (i.e., generators of the free group $(α, β)$ and their inverses, where we use the notation $\\bar{g}$ for $g^{-1}$) or A, U, G and C (i.e., nucleotides in an RNA sequence). There is a natural notion of a length $l(X)$ associated to such a word, which can be defined in several equivalent ways (see [1] and [2] for more details). We give three descriptions of $l$, two of which (as we indicate below) generalize to random words in $2k$ letters, for $k ≥ 2$."
        },
        {
          "Block": "(1) If $X$ is viewed as a word in $(α, β)$ then $l$ is the maximal conjugacy-invariant length function on $(α, β)$ which satisfies $l(α) ≤ 1$ and $l(β) ≤ 1$. Equivalently, $l$ is the word length in the generating set given by all conjugates"
        }
      ]
    },
    {
      "Block": "The first author is partially supported by the SERB-EMR grant EMR/2016/006049. The second author is partially supported by the SERB-MATRICS grant MTR2017/000292. Both authors are partially supported by the UGC centre for advanced studies."
    },
    {
      "Block": "1"
    },
    {
      "header": "section",
      "name": "2",
      "content": [
        {
          "Block": "$gag^{-1}, g\\bar{α}g^{-1}, gβg^{-1}$ and $g\\bar{β}g^{-1}$ of the generators of $\\langle α, β\\rangle$ and their inverses (where $\\bar{α} = α^{-1}$ and $\\bar{β} = β^{-1}$). More generally, an arbitrary word in $2k$ letters gives an element of $(α_1, ..., α_k)$, and $l$ can be defined as a maximal conjugacy-invariant length function (or word length in conjugates of generators and their inverses) in this case too."
        },
        {
          "Block": "(2) If $X$ is viewed as a nucleotide sequence, then we can consider so called secondary structures of RNA [3], i.e., bonds between nucleotides of the RNA, with bonds being Watson-Crick pairs, i.e. hydrogen bonds between Adenine and Uracil and between Guanine and Cytosine, and stereo-chemical forces modelled by not allowing so called pseudo-knots (for details we refer to [1]). Then $l(X)$ is the minimum number of non-bonded nucleotides for secondary structures of $X$. This is a biologically reasonable notion of energy."
        },
        {
          "Block": "(3) Again viewing $X = X^{(n)}$ as a word of length $n$ in the alphabet $α, \\bar{α}, β$ and $\\bar{β}$, we consider incomplete non-crossing matchings of the (indices of) letters in $X$ so that letters are matched with their inverses. Here a non-crossing matching is a set $P$ of pairs of indices $(i, j), 1 < i < j ≤ n$, such that"
        },
        {
          "Block": "(a) each $i$ belongs to at most one element of $P$,"
        },
        {
          "Block": "(b) if $i < j < k < l$, then at most one of $(i, k)$ and $(j, l)$ belong to $P$,"
        },
        {
          "Block": "(c) if $(i, j) ∈ P$ then $X_i = \\bar{X}_j$."
        },
        {
          "Block": "The length $l(X)$ is the minimum number of unmatched letters over all non-crossing matchings. More generally we can take a random word in the alphabet with $2k$ letters $α_1, \\bar{α}_1, ..., α_k, \\bar{α}_k$ (where $\\bar{g}$ denotes $g^{-1}$) and consider non-crossing matchings with letters paired with their inverses, and define $l$ as the minimum number of unmatched letters over all non-crossing matchings."
        },
        {
          "Block": "Henceforth, fix $k ≥ 2$ and consider a random string $X = X^{(n)}$ of length $n$ in $2k$ letters as above (i.e., a random word). The case $k = 2$ corresponds to RNA secondary structures, but most of our results and proofs are uniform in $k$. Let $L_k(n) = E [l(X^{(n)})]$ where the expectation is over uniform distribution on strings of length $n$. Let $p_k(n) = L_k(n)/n$ denote the average proportion of unpaired letters."
        },
        {
          "Block": "Our main result is that this fraction converges to a positive constant."
        }
      ]
    },
    {
      "header": "theorem",
      "name": "Theorem 1.",
      "claim": "With the above notations, $p_k(n) → λ_k$ for some constant $0 < λ_k < 1$."
    },
    {
      "content": [
        {
          "Block": "3"
        },
        {
          "Block": "Thus, the average proportion of unpaired bases in an optimal secondary structure for a random RNA string converges to a positive constant as the length of the RNA string approaches infinity. Equivalently, for a word $X$ in the free group $(α, β)$ (or more generally in the free group $(α_1,..., α_k)$ for $k ≥ 2$), the average ratio of the word length of $X$ in the (infinite) generating set consisting of conjugates of generators and their inverses to the word length of $X$ in the standard generators and their inverses converges to a positive constant. We remark that this result is also true, but essentially trivial, for the free group $\\mathbb{Z}$ on 1 generator (for the group $\\mathbb{Z}$, the two generating sets, hence the corresponding word lengths, coincide)."
        },
        {
          "Block": "We also show that $l(X^n)/n$ has exponential concentration in a window of length $1/\\sqrt{n}$ around its expectation $p_k(n)$, and hence around $λ_k$."
        }
      ]
    },
    {
      "header": "theorem",
      "name": "Proposition 2.",
      "claim": "$P { | l(X^{(n)}) – np_k(n) | > t\\sqrt{n}} < 2e^{-\\frac{t^2}{2}}$ for any $t > 0$."
    },
    {
      "content": [
        {
          "Block": "An immediate corollary is that the standard deviation of $l(X^n)$ is $O(\\sqrt{n})$. As for proofs, the existence of the limit $λ_k$ and the exponential concentration are proved using sub-additivity and Hoeffding's inequality respectively, which are standard methods in combinatorial optimization problems. Showing that $λ_k$ is strictly positive, and getting bounds for its value require more involved arguments. It would be interesting to find the exact value of $λ_k$, particularly $λ_2$. We are only able to get bounds."
        },
        {
          "Block": "For $k = 2$, we prove the explicit bounds $0.034 < λ_2 < 0.231$. The proof of Theorem 1 given in Section 3 gives the lower bound of 0.03, which is then refined to get the slightly better lower bound of 0.034. Elementary arguments in Section 4 give an upper bound of 0.289 which is improved to $\\frac{3}{13} = 0.2307...$ in Section 6. This is achieved by analysing a specific algorithm for producing a non-crossing matching described below."
        },
        {
          "Block": "**The one-sided greedy algorithm.** Scan the letters $X_1, X_2, ...$ in that order and when the turn of $X_t$ comes (starting from $t = 1$), match it to $X_s$ with the largest value of $s < t$, if possible (i.e., $X_s = \\bar{X}_t$, and there is no $u ∈ (s,t)$ such that $X_u = \\bar{X}_t$, and the non-crossing condition is maintained)."
        },
        {
          "Block": "For example, if $k = 2$ and the word is $αβ\\bar{α}βα\\bar{α}β\\bar{β}$, then the matching is $3 → 5, 2 → 7$ (here $3, 5, 2, 7$ represent the indices in the word, of course)."
        }
      ]
    },
    {
      "header": "section",
      "name": "RANDOM WORDS AND NON-CROSSING MATCHINGS",
      "content": [
        {
          "header": "theorem",
          "name": "Proposition 3.",
          "claim": "In the one-sided greedy algorithm, the proportion of unmatched letters converges to\n\n$\\bar{λ}_k = 1- \\frac{\\sum_{r=1}^{k} \\binom{k}{r}^2 \\prod_{j=1}^{r} \\frac{j(j+1)}{j(2k-j)-1}}{\\sum_{r=0}^{k} \\binom{k}{r}^2 \\prod_{j=1}^{r} \\frac{j(j+1)}{j(2k-j)-1}}$\n\nTherefore $λ_k ≤ \\bar{λ}_k$."
        },
        {
          "Block": "4"
        },
        {
          "Block": "The numerical values of upper bound for the first few $k$ are"
        },
        {
          "Block": "| k | 2 | 3 | 4 | 5 |\n|---|---|---|---|---|\n| $\\bar{λ}_k$ | $\\frac{3}{13} = 0.231...$ | $\\frac{33}{100} = 0.33$ | $\\frac{297}{755} = 0.393...$ | $\\frac{3126}{7115} = 0.439...$ |"
        },
        {
          "Block": "Proposition 3 is proved by analysing an associated Markov chain on the space of words. This Markov chain is described in Section 6, where we also find its stationary distribution explicitly. It may be of independent interest, as there are not many examples of chains that are neither reversible nor have a doubly stochastic transition matrix for which we can solve for the stationary distribution exactly."
        },
        {
          "Block": "There is some slack in our proofs, so our bounds can be sharpened. However our goal here is to give a simple and transparent proof. In fact certain enumerative algorithms suggest that $λ_2 < 0.11$ but we are unable to analyse these algorithms rigorously."
        },
        {
          "Block": "**Dependence of $λ_k$ on $k$.** One may also ask about the behaviour of $λ_k$ as a function of $k$. We claim that $λ_k ≤ λ_{k+1}$. This is easiest seen by coupling. Consider a random word $X^n$ using symbols $a_i, \\bar{a}_i, 1 ≤ i ≤ k + 1$. Let $X^{(j)}$ denote the word got by deleting all occurrences of $a_j,\\bar{a}_j$ in $X^{(n)}$, and let $N_j$ be the length of $X^{(j)}$. Let $l^{(j)}$ denote the number of unmatched letters when the optimal matching on $X^n$ is restricted to $X^{(j)}$. Then $l^{(1)} + ... + l^{(k+1)} = kl(X^n)$ and hence taking expectations and using symmetry,"
        },
        {
          "Block": "$(k+1)E[L_k(N_1)] ≤ kL_{k+1}(n).$"
        },
        {
          "Block": "The expectation on the left is over the randomness in $N_1$ which has Binomial distribution with parameters $(n, k/(k+1))$. By Chebyshev's inequality, $P{n_- < N_1 ≤ n_+} ≥ 1 – O(n^{-\\frac{1}{2}})$, where $n_{\\pm} = \\frac{kn}{k+1} \\pm n^{\\frac{1}{2}}$. As $n → ∞$, $L_k(n)$ is obviously increasing in $n$,"
        },
        {
          "Block": "$E[L_k(N_1)] ≥ (1 – O(n^{-\\frac{1}{2}}))L_k(n).$"
        },
        {
          "Block": "Combine this with (2), divide by $n$, and let $n → ∞$ to get $λ_k ≤ λ_{k+1}$."
        },
        {
          "Block": "Further, we show in Proposition 15 that $λ_k → 1$ as $k → ∞$."
        }
      ]
    },
    {
      "header": "section",
      "name": "RANDOM WORDS AND NON-CROSSING MATCHINGS",
      "content": [
        {
          "header": "remark",
          "name": "Remark 4.",
          "remark": "As a consequence of the convergence of the fraction unmatched to a positive constant and the concentration result, it follows that there is some scale $N$ so that, for a generic RNA strand, optimal structures on pieces of length $N$ can be concatenated to give a near-optimal structure on the whole strand. As bonds at long distances are less likely to form, it follows that RNA folding can be localized to this scale, which makes foldings easier to analyse."
        },
        {
          "Block": "5"
        },
        {
          "Block": "**Outline of the paper.** In Section 2 we show that the different ways of defining the length $l$ outlined above give the same function. In Section 3 we prove Theorem 1 and the above-stated lower bounds for $λ_2$. In Section 4 we present an elementary argument to obtain the upper bound of 0.289 for $λ_2$. In Section 5, we prove Proposition 2. In Section 6 we introduce the Markov chain associated to the one-sided greedy algorithm, and explicitly analyse it prove Proposition 3. In particular, this leads to the improved upper bound for $λ_2$."
        }
      ]
    },
    {
      "header": "section",
      "name": "2. PRELIMINARIES",
      "content": [
        {
          "Block": "For the convenience of the reader, we define length functions on groups and show that three definitions of the length $l$ on $(α_1,...,α_k)$ given above give the same function. The results in this section are elementary."
        },
        {
          "header": "definition",
          "name": "Definition 5.",
          "definition": "Let $G = (G,.,e, (\\cdot)^{-1})$ be a group (written multiplicatively, with identity element $e$). A length function on $G$ is a map $l : G → [0, +∞)$ that obeys the properties\n\n* $l(e) = 0$,\n* $l(x) > 0$, for all $x ∈ G \\setminus {e}$,\n* $l(x^{-1}) = l(x)$, for all $x, y ∈ G$.\n* $l(xy) ≤ l(x) + l(y)$, for all $x, y ∈ G$."
        },
        {
          "header": "definition",
          "name": "Definition 6.",
          "definition": "We say that a length function $l$ is conjugacy-invariant if $l(xyx^{-1}) = l(y)$ for all $x, y ∈ G$."
        },
        {
          "Block": "We shall see here that three definitions of a length $l : (α_1,..., α_k) → [0,∞)$ coincide. We also give more details of these definitions."
        },
        {
          "header": "subsection",
          "name": "2.1. Maximal length.",
          "content": [
            {
              "Block": "Consider the set $L$ consisting of conjugacy-invariant length functions $l: (α_1,..., α_k) → [0, +∞)$ satisfying $l(α_i) ≤ 1$ for all $1 ≤ i ≤ k$. We have a partial order on length functions on $(α_1, ..., α_k)$ given by $l_1 ≤ l_2$ if and only if"
            }
          ]
        }
      ]
    },
    {
      "Block": "6"
    },
    {
      "content": [
        {
          "Block": "$l_1(g) ≤ l_2(g)$ for all $g ∈ (α_1, ..., α_k)$. For this order, it is well known that there is a (necessarily unique, by properties of posets) maximal element. Namely, define"
        },
        {
          "Block": "$l_{max}(g) = \\sup{l(g) : l ∈ L}$."
        },
        {
          "Block": "Note that the set ${l(g) : l ∈ L}$ is bounded by the word length of $g$, so has a supremum. It is easy to see that $l_{max}$ is a conjugacy-invariant length function, and that $l(α_i) < 1$ for all $1 < i < k$. Thus $l_{max} ∈ L$. Further, by construction, if $l ∈ L$, then $l ≤ l_{max}$. Thus $l_{max}$ is the maximum of the set $L$."
        },
        {
          "header": "subsection",
          "name": "2.2. Word length in conjugates of generators.",
          "content": [
            {
              "Block": "Let $l_{cw}: (α_1,..., α_k) → [0,+∞)$ be the function given by the word length in the generating set consisting of all conjugates of the generators $α_i, 1 ≤ i ≤ k$. Thus, for $g ∈ (α_1,..., α_k), l_{cw}(g)$ is the smallest value $r ≥ 0$ so that $g$ can be expressed as"
            },
            {
              "Block": "$g = \\prod_{j=1}^{r} β_j α_{i_j}^{\\epsilon_j} \\bar{β}_j^{-1}$"
            },
            {
              "Block": "where $β_j ∈ (α_1,..., α_k)$ and $ε_j = ±1$, for $1 ≤ j ≤r$."
            },
            {
              "header": "theorem",
              "name": "Proposition 7.",
              "claim": "We have $l_{cw} = l_{max}$."
            },
            {
              "proof": {
                "claim_name": "Proposition 7.",
                "proof_steps": [
                  {
                    "Block": "Proof. We see that $l_{cw} ∈ L$. This is because the word length in a conjugacy-invariant set is a conjugacy-invariant length function, and $l_{cw}(α_i) = 1$ for $1 < i <k$."
                  },
                  {
                    "Block": "Further, we see that $l_{cw}$ is maximal. Namely, let $l ∈ L, g ∈ G$ and let $r = l_{cw} (g)$. Then we can express $g$ as $g = \\prod_{j=1}^{r} β_j α_{i_j}^{\\epsilon_j} \\bar{β}_j^{-1}$. By the triangle inequality, conjugacy-invariance, symmetry, and using $l(α_i) < 1$ for $i ≤ i ≤k$,"
                  },
                  {
                    "Block": "$l(g) ≤ \\sum_{j=1}^{r} l(β_j α_{i_j}^{\\epsilon_j} \\bar{β}_j^{-1}) = \\sum_{j=1}^{r} l(α_{i_j}^{\\epsilon_j}) ≤ \\sum_{j=1}^{r} 1 = r = l_{cw} (g)$,"
                  },
                  {
                    "Block": "as required"
                  },
                  {
                    "Block": "As $l_{cw} ∈ L$ is maximal, $l_{cw} = l_{max}$. $\\Box$"
                  }
                ]
              }
            }
          ]
        },
        {
          "header": "subsection",
          "name": "2.3. Length from non-crossing matchings.",
          "content": [
            {
              "Block": "Let $X^{(n)} = (X_1, ..., X_n)$ be a word in the alphabet with $2k$ letters $a_1, \\bar{a}_1, ..., A_k, \\bar{a}_k$. Let $NC$ stand for incomplete non-crossing matchings of $[n] = {1,2,..., n}$. Let $NC_k(X)$ be the subset of $M ∈ NC$ such that for each matched pair $(i, j) ∈ M$ we have ${X_i, X_j} = {a_l,\\bar{a}_l}$ for some $l <k$."
            },
            {
              "Block": "let $l_{NC}(X)$ be the minimum number of unmatched pairs in all non-crossing matchings so that letters are paired with their inverses. We sketch the proofs that"
            }
          ]
        }
      ]
    },
    {
      "Block": "7"
    },
    {
      "content": [
        {
          "Block": "this is well-defined on $(a_1, ..., a_k)$, a conjugacy invariant length function and that $l_{NC} = l_{max}$. For more details, see [2] (which however has different terminology, and considers proofs for the case of two generators, though the proofs work just the same for general $k$)."
        },
        {
          "header": "lemma",
          "name": "Lemma 8.",
          "claim": "Suppose $X_1$ and $X_2$ represent the same element in the group $(a_1,..., α_k)$, then $l_{nc}(X_1) = l_{nc}(X_2)$."
        },
        {
          "proof": {
            "claim_name": "Lemma 8.",
            "proof_steps": [
              {
                "Block": "Proof. It suffices to consider the case where $X_1$ and $X_2$ are related by a single cancellation. Without loss of generality, assume that there exist words $W_1$ and $W_2$ and an index $1 ≤ j ≤ k$ such that $X_1 = W_1W_2$ and $X_2 = W_1a_j\\bar{a}_j^{-1}W_2$. Let $μ_p$ be the length of $W_p$ for $p = 1,2$. Note that the cancelling pair corresponds to the pair $(μ_1 + 1, μ_1 + 2)$ of indices."
              },
              {
                "Block": "We show that $l_{NC}(X_1) = l_{nc}(X_2)$. First, fix a non-crossing matching $M_1$ of $X_1$ with $l_{NC}(X_1)$ unmatched letters and with letters paired with their inverses. Let $σ: \\mathbb{N} → \\mathbb{N}$ be defined by"
              },
              {
                "Block": "$σ(m) = \\begin{cases} m & \\text{if } m ≤ μ_1, \\\\ m+2 & \\text{if } m > μ_1 \\end{cases}$"
              },
              {
                "Block": "Then $M_2 := σ(M_1) ∪ {(μ_1 + 1,μ_1 + 2)} ∈ NC_k (X_2)$ and has $l_{NC} (X_1)$ unmatched letters (i.e., the same as $M_1$). Hence $l_{NC}(X_2) ≤ l_{nc}(X_1)$."
              },
              {
                "Block": "Conversely, fix a non-crossing matching $M_2 ∈ NC_k(X_2)$ with $l_{NC}(X_2)$ unmatched letters. Suppose at most one of $μ + 1$ and $μ + 2$ is matched in $M'_2$, and $(i, j) ∈ M$ is the corresponding pair with $j ∈ {μ + 1, μ + 2}$. Then $M_1 := M_2 \\setminus {(i, j)} ∈ NC_k(X_1)$ and $M_1$ has at most $l_{NC} (X_2)$ unmatched letters."
              },
              {
                "Block": "Next, if $(μ + 1, μ + 2) ∈ M_2$, then $M_1 := M_2 \\setminus {(μ + 1, μ + 2)} ∈ NC_k(X_1)$ and $M_1$ has $l_{NC}(X_2)$ unmatched letters."
              },
              {
                "Block": "Finally, if for some indices $i$ and $j$ we have $(i, μ + 1) ∈ M_2$ and $(j, μ + 2) ∈ M_2$ (after possibly flipping some pairs), we can see that"
              },
              {
                "Block": "$M_1 := M_2 ∪ {(μ + 1, μ + 2)} \\setminus {{(i, μ + 1), (j, μ + 2)}} ∈ NC_k(X_1)$"
              },
              {
                "Block": "and $M_1$ has $l_{NC} (X_2)$ unmatched letters."
              },
              {
                "Block": "In all cases, we conclude that $l_{NC}(X_1) ≤ l_{nc}(X_2)$. $\\Box$"
              }
            ]
          }
        }
      ]
    },
    {
      "Block": "8"
    },
    {
      "content": [
        {
          "Block": "It follows that $l_{nc}$ induces a well-defined function on $(a_1,..., α_k)$, which we also denote as $l_{nc}$. It is easy to see that it is a length function. The proof of the following is very similar to that of Lemma 8."
        },
        {
          "header": "lemma",
          "name": "Lemma 9.",
          "claim": "Suppose $g, h ∈ (a_1, ..., a_k)$, then $l_{NC}(hgh^{-1}) = l_{nc}(g)$."
        },
        {
          "Block": "$\\Box$"
        },
        {
          "Block": "It is easy to see that $l_{nc}(a_i) = 1$ for all $1 ≤ i ≤ k$, and that $l_{NC}$ is symmetric. Thus $l_{nc} ∈ L$. Hence, to show that $l_{NC} = l_{max}$ it suffices to prove maximality, which we prove next."
        },
        {
          "header": "lemma",
          "name": "Lemma 10.",
          "claim": "Suppose $l ∈ L$ and $g ∈ (a_1, ..., α_k)$. Then $l(g) ≤ l_{nc}(g)$."
        },
        {
          "proof": {
            "claim_name": "Lemma 10.",
            "proof_steps": [
              {
                "Block": "Proof. Let $X$ be a word representing $g$. We prove the lemma by (strong) induction on the length $n$ of $X$. The case when the length is zero is clear. Consider a non-crossing matching $M∈ NC_k(X)$ with $l_{NC}(X)$ unmatched letters. First, suppose the index 1 is unmatched in $M$, let $\\bar{X}$ be obtained from $X$ by deleting the first letter. Then $M∈ NC_k(\\bar{X})$, so by induction hypothesis, $l(\\bar{X}) ≤ l_{nc}(\\bar{X})$. Further, as $M$ restricted to $\\bar{X}$ has one less unmatched letter than $M$, we conclude that $l_{NC}(X) = l_{nc}(\\bar{X}) + 1$. As the first letter of $X$ is a generator or the inverse of a generator, using the triangle inequality"
              },
              {
                "Block": "$l(X) ≤1+l(\\bar{X}) ≤ 1 + l_{nc}(\\bar{X}) = l_{nc}(X)$."
              },
              {
                "Block": "Next, if the pair $(1,j) ∈ M$ with $j < n$, we split the word $X$ as $X = X_1 * X_2$ with $X_1$ of length $j$. Observe that the non-crossing condition implies that $M$ decomposes as $M_1 ∪ M_2$ with $M_1 ∈ NC_k(X_1)$ and $M_2 ∈ NC_k(X_2)$. Again, we use the induction hypothesis and the triangle inequality to conclude that $l(X) ≤ l_{NC}(X)$."
              },
              {
                "Block": "Finally, if $(1,n) ∈ M$, let $\\bar{X}$ be obtained from $X$ by deleting the first and last letter. By conjugacy invariance of $l$ and $l_{nc}, l(\\bar{X}) = l(X)$ and $l_{nc}(\\bar{X}) = l_{NC}(X)$. Applying the induction hypothesis to $\\bar{X}$ gives the claim. $\\Box$"
              }
            ]
          }
        },
        {
          "Block": "Thus, we can conclude the following."
        },
        {
          "header": "theorem",
          "name": "Proposition 11.",
          "claim": "We have $l_{NC} = l_{max}$."
        },
        {
          "header": "section",
          "name": "3. THE PROPORTION OF UNMATCHED INDICES",
          "content": [
            {
              "Block": "In this section, we prove Theorem 1 and get lower bounds on $λ_2$. At first, $k$ is fixed, hence we drop it in the subscripts of $L(n)$ and $p(n)$."
            }
          ]
        }
      ]
    },
    {
      "Block": "9"
    },
    {
      "content": [
        {
          "Block": "The first observation is that $L(n)$ is sub-additive."
        },
        {
          "header": "lemma",
          "name": "Lemma 12.",
          "claim": "For $m, n > 0, L(m + n) ≤ L(m) + L(n)$."
        },
        {
          "proof": {
            "claim_name": "Lemma 12.",
            "proof_steps": [
              {
                "Block": "Proof. A string $X^{(m+n)}$ of i.i.d. random variables of length $m + n$ is obtained by taking the concatenation $X^{(n)} * X^{(m)}$ of two strings $X^{(n)}$ and $X^{(m)}$ of i.i.d. random variables of lengths $n$ and $m$ respectively. As the union of elements $M_1 = NC_k(X_1)$ and $M_2 = NC_k(X_2)$ gives a matching $M ∈ NC_k(X)$, it is easy to see that $l(X) ≤ l(X_1) + l(X_2)$. By taking expectations the lemma follows. $\\Box$"
              }
            ]
          }
        },
        {
          "Block": "As a well known consequence of sub-additivity (Fekete's lemma), we obtain the following."
        },
        {
          "header": "corollary",
          "name": "Corollary 13.",
          "claim": "The sequence $p(n) = L(n)/n$ converges to $λ_k := \\inf_n p(n)$."
        },
        {
          "content": [
            {
              "Block": "As $0 ≤ p(n) ≤ 1$, we get $0 ≤ λ_k ≤ 1$. It is easy to get some upper bounds for $λ_k$ by computing $p(n)$ for small $n$ (as $λ_k$ is the infimum of $p(n)$). For instance, for $k = 2$ and $n = 4, l(X)$ takes values $0, 2$ and $4$ with probabilities $28/256, 168/256$ and $60/256$, respectively, hence $λ_2 ≤ ρ(4) = 9/16$. The harder thing is to get lower bounds. Our main result is that $λ_k$, which is the asymptotic proportion of unpaired bases, is positive."
            }
          ]
        },
        {
          "header": "lemma",
          "name": "Lemma 14.",
          "claim": "We have $λ_k > 0$."
        },
        {
          "proof": {
            "claim_name": "Lemma 14.",
            "proof_steps": [
              {
                "Block": "Proof. Fix $δ > 0$. Observe that"
              },
              {
                "Block": "$L(n) ≥ nδ \\cdot P(l(X^{(n)}) ≥ nδ)$,"
              },
              {
                "Block": "and hence"
              },
              {
                "Block": "$ρ(η) ≥ δP(l(X^{(n)}) ≥ nδ)$."
              },
              {
                "Block": "Thus, if we have $P(l(X^{(n)}) ≥ nδ) → 1$ as $n → ∞$, then $λ_k > δ$. Thus it suffices to find a $δ > 0$ for which we can show that $P(l(X^{(n)}) > nδ) → 1$, or equivalently show that"
              },
              {
                "Block": "$P(l(X^{(n)}) < nδ) → 0$"
              },
              {
                "Block": "as $n→∞$."
              },
              {
                "Block": "We shall now bound $P(l(X^{(n)}) < nδ)$ for small enough $δ$. Note that if $W (n, δ)$ is the number of words $X$ of length $n$ with $l(X) < nδ$, then"
              },
              {
                "Block": "$P(l(X^{(n)}) <nδ) = \\frac{W(η, δ)}{(2k)^n}$"
              }
            ]
          }
        }
      ]
    },
    {
      "Block": "10"
    },
    {
      "content": [
        {
          "Block": "Let $m = [\\frac{n-nδ}{2}]$ and let $r = n - 2m$. Observe that if $l(X^{(n)}) < nδ$, then $X = X^{(n)}$ has a non-crossing matching with at least $2m$ pairs, and hence a non-crossing matching $M$ with exactly $2m$ pairs (by simply dropping a few pairs). Given such an $M$, we can associate to $X$ a triple $(Y, Z, s)$ where"
        },
        {
          "Block": "* Y is the word (of length $r$) consisting of the letters of $X$ that are unmatched in $M$, in the same order as in $X$,"
        },
        {
          "Block": "* Z is the word (of length $2m$) consisting of the letters of $X$ that are matched in $M$, in the same order as in $X$, and,"
        },
        {
          "Block": "* s is the set of indices $i, 1 ≤ i ≤ n$, that are unmatched."
        },
        {
          "Block": "Note that $M$ gives a complete non-crossing matching on $Z$, and hence $Z$ represents the trivial word in $(a_1, ..., α_k)$. As the triple $(Y, Z, s)$ determines $X$, it follows that the number $W (n, δ)$ of words $X$ of length $n$ with $l(X) < nδ$ is bounded above by the number of triples $(Y, Z, s)$, with"
        },
        {
          "Block": "* Y a word of length $r$,"
        },
        {
          "Block": "* Z a word of length $2m$ that represents the trivial element in the free group, and"
        },
        {
          "Block": "* s a subset of size $r$ of ${1, 2, ..., n}$."
        },
        {
          "Block": "Let $T_p$ denote the set of words of length $p$ that represent the trivial element in the group $(α_1,..., α_k)$. It follows that"
        },
        {
          "Block": "$|W(η, δ)| ≤ \\binom{n}{r} (2k)^r \\cdot |T_{2m}|$"
        },
        {
          "Block": "The main step remaining is to bound $T_{2m}$. Let $τ_p = T_p/(2k)^p$ represent the probability that a random word of length $p$ represents the trivial element in $(a_1, ..., α_k)$. We observe that this is the probability that the standard symmetric random walk on the Cayley graph of the free group (with the canonical generators and their inverses) starting at the identity returns to the identity in $p$ steps. It is clear that $τ_pτ_q ≤ τ_{p+q}$, and hence by the Fekete lemma (applied to $\\log τ_p$), we see that $τ_{\\frac{1}{p}} → θ_k := \\sup_p τ_{\\frac{1}{p}}$. This means that $τ_p^{\\frac{1}{p}} ≤ θ_k$ for each $p ≥ 1$. Of course $τ_p = 0$ for odd $p$."
        },
        {
          "Block": "It is a known fact that $θ_k = \\frac{\\sqrt{2k-1}}{\\sqrt{k}}$ (for example Kesten [4]). To see this, observe that the graph distance of the random walk to the identity element is itself a random walk on $\\mathbb{N} = {0, 1, 2, ...}$ that goes from $i → i + 1$ with probability $(2k-1)/2k$ and $i ↔ i − 1$ with probability $1/2k$, for $i ≥ 1$, and from 0 to 1 with probability 1."
        },
        {
          "Block": "The number of walks of length $p = 2m$ that return to the origin in $\\mathbb{N}$ is the Catalan number $\\frac{1}{m+1} \\binom{2m}{m}$, and each such path (since it has $m$ up-steps and $m$ down-steps)"
        }
      ]
    },
    {
      "Block": "11"
    },
    {
      "content": [
        {
          "header": "section",
          "name": "RANDOM WORDS AND NON-CROSSING MATCHINGS",
          "content": []
        },
        {
          "Block": "has probability $(2k – 1)^m/(2k)^{2m}$. Therefore,"
        },
        {
          "Block": "$τ_{2m} ~ \\frac{(2k-1)^m}{(2k)^{2m}(m + 1)} \\binom{2m}{m} ~ \\frac{1}{\\sqrt{π}m^{\\frac{3}{2}}} \\frac{(2k - 1)^m}{k^{2m}} \\binom{2m}{m}$"
        },
        {
          "Block": "by Stirling's formula, where $a_m ~ b_m$ means that $a_m/b_m$ converges to 1 as $m → ∞$. In particular, we see that $τ_{2m}^{\\frac{1}{2m}} → \\frac{\\sqrt{2k-1}}{k} = θ_k^2$. Hence $θ_k = \\frac{\\sqrt{2k-1}}{\\sqrt{k}}$. In particular, $θ_2 = \\frac{1}{\\sqrt{2}} = \\frac{\\sqrt{3}}{2}$, which we use for explicit estimates on $λ_2$."
        },
        {
          "Block": "It is now straightforward to complete the proof. For simplicity of notation, we ignore the error in rounding off to an integer and assume $r = nδ$. Using the elementary fact that $\\binom{n}{r} ≤ e^{nh(δ)}$ where $h(δ) = −δ \\log(δ) – (1 – δ) \\log(1 – δ)$ in (3), we get"
        },
        {
          "Block": "$P(l(X^{(n)}) < nδ) ≤ \\exp {n (h(δ) + \\logθ_k))}$"
        },
        {
          "Block": "Hence $P(l(X^{(n)}) < nδ) → 0$ as $n → ∞$ provided $h(δ) + \\log θ_k < 0$."
        },
        {
          "Block": "When $k = 2$, as $θ_2 = \\frac{1}{\\sqrt{2}} = \\frac{\\sqrt{3}}{2}$, this happens, for example, for $δ = 0.03$. Thus, we have $λ_2 > 0.03$, i.e. at least 3% of the letters are unmatched for the best non-crossing matching for most words."
        },
        {
          "Block": "Next, suppose $k → ∞$. We see that $λ_k → ∞$."
        },
        {
          "header": "theorem",
          "name": "Proposition 15.",
          "claim": "We have $\\lim_{k→∞} λ_k = 1$."
        },
        {
          "proof": {
            "claim_name": "Proposition 15.",
            "proof_steps": [
              {
                "Block": "Proof. Observe that $θ_k = \\frac{\\sqrt{2k-1}}{\\sqrt{k}} → 0$ as $k → ∞$, hence $\\log(θ_k) → −∞$. It follows that for any fixed $δ∈ (0,1)$, if $k$ is sufficiently large we have $h(δ) + \\log θ_k < 0$, hence $λ_k > δ$. As $λ_k < 1$ for all $k$, $\\lim_{k→∞} λ_k = 1$. $\\Box$"
              }
            ]
          }
        },
        {
          "Block": "Thus, we have shown that the limit $λ_k$ of the sequence $p(n)$ exists and is positive. This completes the proof of Theorem 1, with the effective bound $λ_2 ≥ 0.03$ for $k = 2$ (other effective bounds can be computed similarly). $\\Box$"
        },
        {
          "header": "subsection",
          "name": "3.1. Refinement of the lower bound for $λ_2$ using maximal triples.",
          "content": [
            {
              "Block": "We can refine the bound we obtained by choosing the triple $(Y, Z, s)$ in a canonical way (note that we do not, however, choose a canonical non-crossing matching on $Z$). Namely we try to match letters with as low indices as possible among all minimal non-crossing matchings. We fix $k = 2$ (so $(a_1,..., α_k) = (α, β)$) in this subsection."
            },
            {
              "Block": "First, observe that for fixed $X$, the words $Y$ and $Z$ are determined by $s$. More generally, given $X$, any subset $s ⊂ [n]$ determines words $Y = Y(X, s)$ and $Z = Z(X, s)$, but in general the word $Z(X, s)$ may not represent the trivial element in"
            }
          ]
        }
      ]
    },
    {
      "Block": "12"
    },
    {
      "content": [
        {
          "header": "section",
          "name": "SIDDHARTHA GADGIL AND MANJUNATH KRISHNAPUR",
          "content": []
        },
        {
          "Block": "$(α_1,..., α_k)$. We shall say the triple $(Y(s), Z(s), s)$ determined by $s$ (and $X$) is admissible provided $Z$ represents the trivial element."
        },
        {
          "Block": "The set $s$ can be viewed as a finite sequence by ordering its elements lexicographically, and two such sets can be compared using the lexicographic ordering on finite sequences, which is a total ordering. We order admissible triples $(Y, Z, s)$ by the component $s$ and choose the maximal admissible triple for each fixed $X$."
        },
        {
          "Block": "We can decompose $s$ as $s = s_1 ∪ s_2$, with $s_2$ (the tail) consisting of those elements $i ∈ s$ such that if $j ∈ [n] \\setminus s$, then $j < i$. Conversely, given an element $i ∈ s_1$ there exists $j∈ [n] \\setminus s$ such that $j > i$. For $i ∈ s_1$, let $\\bar{i}$ be the smallest element in $[n] \\setminus s$ such that $\\bar{i} > i$, i.e., $\\bar{i}$ is the first matched index after the unmatched index $i$. Geometrically, the unmatched indices $s$ are in general interspersed with the matched indices, with a (possibly empty) tail $s_2$ of unmatched indices which are larger than all matched indices."
        },
        {
          "Block": "We claim that if $(X, Y, s)$ is maximal and $i ∈ s_1$, then $X_i ≠ \\bar{X}_{\\bar{i}}$. For, if $X_i = \\bar{X}_{\\bar{i}}$, let $s' = s \\setminus {i} ∪ {\\bar{i}}, Y' = Y(X, s')$ and $Z' = Z(X, s')$. Then $Z' = Z$ as words in the free group, as the letter $X_{\\bar{i}}$ in $Z$ has been replaced by $X_i = \\bar{X}_{\\bar{i}}$ in $Z'$, and in the order on indices, $i$ has the same position in $Z'$ as $\\bar{i}$ has in $Z$ (this is because, if $j∈ [n] \\setminus (s ∪ s')$ is an index in both $Z$ and $Z'$, then $j < i$ if and only if $j < \\bar{i}$ by definition of $\\bar{i}$). Hence $Z'$ represents the trivial word. Hence the triple $(Y', Z', s')$ is admissible, and $s$ and $s'$ have the same cardinality. But $s < s'$, contradicting maximality of $s$."
        },
        {
          "Block": "Thus, writing $Y = Y_1 * Y_2$ with $Y_1$ the word with letters $X_j, j ∈ s_i$, and letting $r_i$ be the cardinality of $s_i$, we see that there are only $3^{r_1}4^{r_2}$ possibilities for the word $Y$ (corresponding to a maximal triple). On the other hand, the set $s_2$ is determined by $r_2$ as it consists of the last $r_2$ elements, and $s_1$ is a subset of size $r_1$ of the first $n-r_2=n- r + r_1$ elements."
        },
        {
          "Block": "Hence, using (3) once more and recalling that $θ_2 = \\sqrt{3}/2$, we see that"
        },
        {
          "Block": "$W(η, δ) ≤ \\sum_{r} \\binom{n}{r} \\sum_{r_1=0}^{r} \\binom{r}{r_1} 3^{r_1}4^{r-r_1} (\\frac{\\sqrt{3}}{2})^{n-r} 4^{n-r} = \\sum_{r} \\binom{n}{r} \\binom{r}{r_1} 3^{r_1}4^{r-r_1} (\\frac{\\sqrt{3}}{2})^{n-r} 4^{n-r}$"
        },
        {
          "Block": "We use $\\binom{n-r+r_1}{r_1} ≤ \\binom{n}{r_1}$ and the Chernoff bound for the tail of the binomial distribution to get"
        },
        {
          "Block": "$\\sum_{r_1=0}^{r} \\binom{n}{r_1} 3^{r_1}4^{r-r_1} τ^{n-r} ≤ \\sum_{r=0}^{n} \\binom{n}{r} 3^{r}4^{n-r} τ^{n-r} \\lesssim e^{n \\{-δ \\log(\\frac{δ}{3/7}) + (1-δ) \\log(\\frac{1-δ}{4/7})\\}}$"
        },
        {
          "Block": "$= \\exp{n[h(δ) + δ \\log 3 + (1 − δ) \\log 4]}.$ "
        }
      ]
    },
    {
      "Block": "13"
    },
    {
      "content": [
        {
          "header": "section",
          "name": "RANDOM WORDS AND NON-CROSSING MATCHINGS",
          "content": []
        },
        {
          "Block": "Therefore, we get the improved bound"
        },
        {
          "Block": "$P(l(X^{(n)}) < nδ) ≤ |W(η, δ)|4^{-n}$"
        },
        {
          "Block": "$< \\exp{n[h(δ) + δ \\log(3/4) + (1 − δ) \\log(\\sqrt{3}/2)]}$."
        },
        {
          "Block": "However the improved lower bound only gives a marginal improvement to 0.034, i.e., at least 3.4% of the letters are unmatched on average."
        }
      ]
    },
    {
      "header": "section",
      "name": "4. AN ELEMENTARY UPPER BOUND ON $λ_2$",
      "content": [
        {
          "Block": "We claim that $λ_2 ≤ 0.29$ (we shall use more sophisticated methods to obtain a better bound in Section 6). This is achieved as follows. Let $U_1, V_1, U_2, V_2, ...$ be i.i.d. Geometric(1/2) random variables, i.e., $P[U_1 = j] = 2^{-j}$ for $j ≥ 1$. Then $E[U_1] = 2$, and hence with $m = [n/4]$ we get $N_n := U_1+V_1+...+U_m+V_m = n+O(\\sqrt{n})$ with high probability. We create a string $S∈ {α,\\bar{α}, β,\\bar{β}}^{N_n}$ by setting down a random string of ${α, \\bar{α}}$ of length $U_1$, then a random string of ${β, \\bar{β}}$ of length $V_1$, etc. Thus, $U_i, V_i$ are the length of runs of the two species of symbols. This makes the length of the string random but since it is in a $\\sqrt{n}$ length window of $n$, this should not change anything much (as regards the proportion of unpaired sites). Consider the following matching algorithm."
        },
        {
          "Block": "Fix any maximal noncrossing matching of all the $β,\\bar{β}$ symbols. Then we make the best possible non-crossing matching of each run of $α, \\bar{α}$ within itself. Thus, if the first run happens to be $α, \\bar{α}, α$, then, we could match up the first two sites and leave the third one unpaired."
        },
        {
          "Block": "In this matching scheme, in the first stage there are $O(\\sqrt{n})$ unpaired sites (the difference between the number of $β$ and the number of $\\bar{β}$ symbols in $S$). For the second stage, note that in the $j$th run (the one that has length $U_j$), the number of $α$-symbols is $ξ_j ~ Binomial(U_j, \\frac{1}{2})$, and hence the number of left overs is $|2ξ_j – U_j|$. The total number of left over sites has expectation $mE[|2ξ_1 – U_1|] + O(\\sqrt{n})$ which gives us the bound"
        },
        {
          "Block": "$λ_2 ≤ \\frac{1}{4} E[|2ξ_1 – U_1|]$."
        },
        {
          "Block": "Numerical evaluation of the expectation (expressed as an infinite sum) gives the bound $λ_2 ≤ 0.2886...$."
        }
      ]
    },
    {
      "Block": "14"
    },
    {
      "content": [
        {
          "header": "section",
          "name": "SIDDHARTHA GADGIL AND MANJUNATH KRISHNAPUR",
          "content": []
        },
        {
          "header": "section",
          "name": "5. CONCENTRATION AROUND EXPECTED BEHAVIOUR",
          "content": [
            {
              "Block": "We prove Proposition 2 in this section. The tool is the well-known Hoeffding's inequality for sums of martingale differences (see section 4.1 of Ledoux [5] for a proof and the book of Steele [6] for its use in many combinatorial optimization problems similar to ours). It says that if $d_1, d_2, ..., d_n$ is a martingale difference sequence, that is $E[d_j|d_1, ... d_{j-1}] = 0$ for each $j$ (for $j = 1$ this is to be interpreted as $E[d_1] = 0$) and $|d_j| ≤ B_j$ with probability 1 for some constant $B_j$, then for any $t > 0$, we have"
            },
            {
              "Block": "$P \\Big{ | \\sum_{j=1}^{n} d_j | > t \\Big} < 2e^{-\\frac{t^2}{2(B_1^2+...+B_n^2)}}.$"
            },
            {
              "header": "proof",
              "name": "Proof of Proposition 2.",
              "proof_steps": [
                {
                  "Block": "Proof. Let $X = X^{(n)} = (X_1, ..., X_n)$. Define for $j = 1, ... n$,"
                },
                {
                  "Block": "$d_j = E [L(X_1, ..., X_n) | X_1, ..., X_j] – E [L(X_1, ..., X_n) | X_1, ..., X_{j-1}] $."
                },
                {
                  "Block": "Then $d_j$ is a martingale difference sequence by the tower property"
                },
                {
                  "Block": "$E[E[U | V, W] | W] = E[U | W]$."
                },
                {
                  "Block": "Further, $L(X) – E[L(X)] = d_1 + ... + d_n$. If we show that $|d_j| ≤ 2$, then by applying Hoeffding's inequality (4), we get the statement in the lemma."
                },
                {
                  "Block": "To prove that $|d_j| ≤ 2$, fix $j$ and let $Y = (X_1, ..., X_{j-1}, X'_j, X_{j+1}, ..., X_n)$ where $X'_j$ is an independent copy of $X_j$ that is also independent of all $X_j$s. Then,"
                },
                {
                  "Block": "$E[L(Y) | X_1, ..., X_j] = E[L(Y) | X_1,...,X_{j-1}] = E[L(X) | X_1,..., X_{j-1}],$"
                },
                {
                  "Block": "where the first equality holds because $X'_j$ is independent of $Y$ and the second equality holds because $X_1, ... X_{j-1}$ bear the same relationship to $X$ as to $Y$. Thus, we conclude that"
                },
                {
                  "Block": "$d_j = E [L(X) – L(Y) | X_1, ... X_j] $."
                },
                {
                  "Block": "But $X$ and $Y$ differ only in one co-ordinate. From any non-crossing matching of $X$, by deleting the edge (if any) matching the $j$th co-ordinate, we obtain a non-crossing matching for $Y$ with at most two more unmatched indices. Therefore $L(Y) ≤ L(X) + 2$ and by symmetry between $X$ and $Y$, we get $|L(X) – L(Y)| ≤ 2$. Therefore $|d_j| ≤ E [|L(X) – L(Y)| | X_1, ... X_j] < 2$. $\\Box$"
                }
              ]
            }
          ]
        }
      ]
    },
    {
      "Block": "15"
    },
    {
      "content": [
        {
          "header": "section",
          "name": "RANDOM WORDS AND NON-CROSSING MATCHINGS",
          "content": []
        },
        {
          "header": "section",
          "name": "6. GREEDY ALGORITHMS AND UPPER BOUNDS",
          "content": [
            {
              "Block": "The goal of this section is to prove Proposition 3. First we introduce a Markov chain related to this algorithm. Recall the description of the algorithm from the introduction."
            },
            {
              "header": "subsection",
              "name": "6.1. The associated Markov chain and its stationary distribution.",
              "content": [
                {
                  "Block": "For simplicity of notation, we write the alphabet set as $A = {\\bar{1},1,...,\\bar{k},k}$. Let $w[t]$ be the word formed by all the accessible letters at “time” $t$ – these are the letters among $X_1,..., X_t$ that are still available for matching in future in the above greedy algorithm. Then $w[t]$ is a Markov chain whose state space is $Ω = A^0 ∪ A^1 ∪ A^2 ∪ ..., $ the set of all finite strings in the alphabet $A$ (including the empty string) and whose dynamics are as follows:"
                },
                {
                  "Block": "If $w[t] = (w_1,..., w_p)$ and $X_{t+1} = x$, then $w[t + 1] = (w_1, ..., w_p, x)$ if $\\bar{x}$ does not occur in $w[t]$. Otherwise $w[t+1] = (w_1, ..., w_{j-1})$ where $j$ is the largest index such that $w_j = \\bar{x}$. Two letters get matched each time the length of $w[t]$ reduces. Hence the number left unmatched after $n$ steps is $n − 2 \\sum_{t=2}^{n} \\mathbf{1}_{length(w[t])<length(w[t-1])}.$ "
                },
                {
                  "Block": "The Markov chain is not irreducible. From any state it is possible to go to $Ø$ but from $Ø$ the chain can only go to states in"
                },
                {
                  "Block": "$Ω_0 = {w∈Ω : \\text{at most one of } x, \\bar{x} ∈ w \\text{ for each } x ∈ A}$"
                },
                {
                  "Block": "which makes $Ω_0$ the unique irreducible class. As we shall show next, this Markov chain has a stationary probability distribution $π$. By the general theory of Markov chains, the stationary distribution is unique. To give the formula for $π$, we need some notation."
                },
                {
                  "Block": "For a word $w ∈ Ω_0$, define $a_i (w)$ inductively by declaring $a_1 (w) + ... + a_j (w)$ to be the length of the maximal initial segment in $w$ (reading from the left) containing at most $j$ distinct symbols. Note that if $w$ has only $j$ different symbols from $A$, it follows that $a_i(w) = 0$ for $i ≥ j$. In particular, as $w ∈ Ω_0$, it has at most $k$ distinct symbols. For example, if $k = 3$ and $w = \\bar{1}1\\bar{2}1\\bar{2}2\\bar{1}2\\bar{3}11\\bar{2}3\\bar{2}$, then $(a_1,a_2, a_3) = (2,8,6)$. If $w = \\bar{2}22\\bar{1}2$ then $(a_1, a_2, a_3) = (3,2,0)$. For the empty word, $a_i (w) = 0$ for all $i$."
                },
                {
                  "header": "theorem",
                  "name": "Proposition 16.",
                  "claim": "Fix $k ≥ 2$. Let $τ_j = \\frac{j+1}{j(2k-j)-1}$ for $1 ≤ j ≤ k$. Then the unique stationary probability distribution is given by\n\n$π(w) = \\frac{1}{Z} τ_1^{a_1(w)} τ_2^{a_2(w)} ... τ_k^{a_k(w)}$"
                }
              ]
            }
          ]
        }
      ]
    },
    {
      "Block": "16"
    },
    {
      "content": [
        {
          "header": "section",
          "name": "SIDDHARTHA GADGIL AND MANJUNATH KRISHNAPUR",
          "content": []
        },
        {
          "Block": "where $Z = \\sum_{r=0}^{k} \\binom{k}{r}^2 \\prod_{j=1}^{r} \\frac{jτ_j}{1-jτ_j} = \\sum_{r=0}^{k} \\binom{k}{r}^2 \\prod_{j=1}^{r} \\frac{j(j+1)}{j(2k-j)-1}$."
        },
        {
          "Block": "Assuming this proposition, we prove Proposition 3."
        },
        {
          "header": "subsection",
          "name": "6.2. Proof of Proposition 3.",
          "content": [
            {
              "Block": "From the earlier observation, the expected proportion of matched letters after $n$ steps is"
            },
            {
              "Block": "$\\frac{2}{n} \\sum_{t=2}^{n} P{length(w[t]) < length(w[t – 1])} → 2P_π{length(w[1]) < length(w[0])}$"
            },
            {
              "Block": "where the subscript $π$ is to indicate that $w[0]$ is sampled from $π$ (in the actual chain, we start with $w[0] = (Ø)$ and the convergence follows from the general theory of Markov chains which asserts that the distribution of $(w[t – 1], w[t])$ (from any starting point) converges to the distribution of $(w[0], w[1])$ when $w[0]$ has distribution $π$. As a consequence, we arrive at the upper bound"
            },
            {
              "Block": "$λ_k ≤ 1 − 2P_π{length(w[1]) < length(w[0])}.$ "
            },
            {
              "Block": "If $w$ has $r$ distinct symbols, then $a_r(w) > 0(= a_{r+1}(w))$ and its length gets reduced if and only if the next arriving letter can match up with one of them, i.e., with probability $\\frac{r}{2k}$. Further, for a given choice of strictly positive integers $a_1, ..., a_r$, the number of words $w$ with $a_1(w) = a_i$ is precisely"
            },
            {
              "Block": "$2^r k(k − 1) ... (k − r + 1)2^{a_2-1}3^{a_3-1}...r^{a_r-1}$."
            },
            {
              "Block": "Here $2k - 2i + 2$ is for the choice of $i$th new symbol (the locations are determined by $a_1,..., a_r$) and the $a_j − 1$ letters between the $j$th new symbol and $(j + 1)$st new symbol each have $j$ choices, hence the factor of $j^{a_j−1}$. Thus,"
            },
            {
              "Block": "$P_π{length(w[1]) < length(w[0])} = \\frac{1}{2kZ} \\sum_{r=1}^{k} \\binom{k}{r}^2 \\sum_{a_i≥1:i≤r} \\prod_{j=1}^{r} (jτ_j)^{a_j}$"
            },
            {
              "Block": "$= \\frac{1}{2kZ} \\sum_{r=1}^{k} \\binom{k}{r}^2 (\\frac{rτ_r}{1-rτ_r}) = \\frac{1}{2kZ} \\sum_{r=1}^{k} \\binom{k}{r}^2 \\prod_{j=1}^{r} (\\frac{jτ_j}{1-jτ_j})$"
            },
            {
              "Block": "Substituting the value of $τ_j$ given in the statement of the proposition,"
            },
            {
              "Block": "$\\bar{λ}_k = 1- \\frac{1}{kZ} \\sum_{r=1}^{k} \\binom{k}{r}^2 (\\frac{rτ_r}{1-rτ_r}) = 1- \\frac{\\sum_{r=1}^{k} \\binom{k}{r}^2 \\prod_{j=1}^{r} \\frac{j(j+1)}{j(2k-j)-1}}{\\sum_{r=0}^{k} \\binom{k}{r}^2 \\prod_{j=1}^{r} \\frac{j(j+1)}{j(2k-j)-1}}$"
            },
            {
              "Block": "Plugging in the expression for $Z$ given in Proposition 16 completes the proof of Proposition 3. $\\Box$"
            }
          ]
        }
      ]
    },
    {
      "Block": "17"
    },
    {
      "content": [
        {
          "header": "section",
          "name": "RANDOM WORDS AND NON-CROSSING MATCHINGS",
          "content": []
        },
        {
          "header": "subsection",
          "name": "6.3. Proof of Proposition 16.",
          "content": [
            {
              "Block": "**Case $k = 2$:** This is the case we care most about. We see that $τ_1 = \\frac{1}{2}$ and $τ_2 = \\frac{3}{2}$ and $Z = \\frac{13}{3}$. Hence $π(w) = \\frac{3}{13} (\\frac{1}{2})^{a_1 (w)} (\\frac{3}{2})^{length(w)}$ where $a_1 (w)$ is the length of the first run (i.e., the maximum $j$ such that $w_1 = w_2 = ... = w_j$). Therefore, (7) becomes"
            },
            {
              "Block": "$λ_2 = 1 - \\frac{1}{2 \\times 13} (4 + 16) = \\frac{3}{13} = 0.2307...$"
            },
            {
              "Block": "**6.3. Proof of Proposition 16.** Let $σ(w) = τ_1^{a_1 (w)} ... τ_k^{a_k (w)}$. If $w$ has $r$ distinct symbols, then $a_j ≥ 1$ for $j ≤ r$ and $a_j = 0$ for $j > r$. The number of words $w$ with given $a_1,..., a_r$ is given in (6). Hence the sum of $σ(w)$ over such $w$ is"
            },
            {
              "Block": "$2^r \\binom{k}{r} \\sum_{a_1,...,a_r≥1} \\prod_{j=1}^{r} (jτ_j)^{a_j} = 2^r \\binom{k}{r} \\prod_{j=1}^{r} (\\frac{jτ_j}{1-jτ_j})$"
            },
            {
              "Block": "Sum over $r$ (including $r = 0$) to get the given expression for $Z$."
            },
            {
              "Block": "It suffices to check that $σ$ satisfies the equations for the stationary distribution, since we know the uniqueness (up to scalar multiples) of stationary distribution. The general equations are"
            },
            {
              "Block": "$\\sum_{w' → w} σ(w') = 2kσ(w)$"
            },
            {
              "Block": "where the notation $w' → w$ means that $w'$ can lead to $w$ in one step (in our Markov chain, a given $w'$ can lead to a given $w$ in at most one way, hence the transition probability is exactly 1/2k). If $w = (w_1,..., w_p)$ has exactly $r$ distinct symbols, then $a_r(w) > 0 = a_{r+1}(w)$, and $σ(w) = τ_1^{a_1 (w)} ... τ_r^{a_r (w)}$. The possible $w'$ are:"
            },
            {
              "Block": "(1) $w' = (w_1,..., w_{p-1})$. Then $a_i(w') = a_i(w)$ for $i ≤ r − 1$ and $a_r(w') = a_r (w) – 1$."
            },
            {
              "Block": "(2) $w' = wxy^1t_1y^2 ... t_jy^{j+1}$ where $x ∈ A$ is a symbol that occurs in $w$ and $t_i ∈ A$ are the new symbols that did not occur before and $y^i = (y^i_1, ..., y^i_{m_i})$ with $m_i ≥ 0$. Here $j$ can vary from 0 to $k – r$. Further, $x$ should not occur in $y^1t_1y^2 ... t_jy^{j+1}$ so that $w'$ can lead to $w$ when an $\\bar{x}$ arrives (it is tacit that all our words are in $Ω_0$, so we do not write those conditions again). Then"
            },
            {
              "Block": "$a_i(w') = \\begin{cases} a_i (w) & \\text{if } i ≤ r - 1, \\\\ a_r(w) + m_1+1 & \\text{if } i = r, \\\\ m_{i-r+1}+1 & \\text{if } r + 1 ≤ i ≤ r + j. \\end{cases}$"
            },
            {
              "Block": "For given $j$ and $m_1, ..., m_j$, the number of choices of such $w'$ is"
            },
            {
              "Block": "$2^j (k - r)(k - r − 1) ... (k - r − j + 1) × r(r − 1)^{m_1} r^{m_2} ... (r + j − 1)^{m_{j+1}}.$"
            }
          ]
        }
      ]
    },
    {
      "Block": "18"
    },
    {
      "content": [
        {
          "header": "section",
          "name": "SIDDHARTHA GADGIL AND MANJUNATH KRISHNAPUR",
          "content": []
        },
        {
          "Block": "This is because there are $2k - 2r - 2i + 2$ choices for $t_i$ and $r + i – 2$ choices for each letter in $y^i$."
        },
        {
          "Block": "(3) $w' = wt_1y^1t_2y^2 ... t_jy^j$ where $y^i = (y^i_1, ..., y^i_{m_i})$ with $m_i ≥ 0$ and $t_i ∈ A$ are the new symbols that did not occur before. Here $j$ can vary from 1 to $k - r$. Further, $t_1$ should not occur in $y^1t_2y^2 ... t_jy^j$. Then"
        },
        {
          "Block": "$a_i(w') = \\begin{cases} a_i (w) & \\text{if } i < r, \\\\ m_{i-r}+1 & \\text{if } r + 1 ≤ i ≤ r + j. \\end{cases}$"
        },
        {
          "Block": "For given $j$ and $m_1, ..., m_j$, the number of choices of such $w'$ is"
        },
        {
          "Block": "$2^j (k - r)(k - r − 1) ... (k − r − j + 1) × r^{m_1} (r + 1)^{m_2} ... (r + j – 1)^{m_j} $."
        },
        {
          "Block": "Here $2k - 2r - 2i + 2$ is the number of choices for $t_i$ and $r + i – 1$ is the number of choices for each letter in $y^i$."
        },
        {
          "Block": "Using these and cancelling common factors, the equation for stationary distribution becomes"
        },
        {
          "Block": "$2kτ_r = 1 + \\frac{rτ_r}{1- (r-1) τ_r} + \\sum_{j=0}^{k-r} \\binom{k-r}{j} 2^j (k - r)^{(j)} \\prod_{i=r+1}^{r+j} τ_i$"
        },
        {
          "Block": "$+ τ_r \\sum_{j=1}^{k-r} \\binom{k-r}{j} 2^j (k - r)^{(j)} \\prod_{i=r+1}^{r+j} τ_i$"
        },
        {
          "Block": "$= 1+ \\frac{rτ_r^2}{1- (r-1) τ_r} + (\\frac{rτ_r}{1- (r-1) τ_r} + τ_r) \\sum_{j=1}^{k-r} \\binom{k-r}{j} 2^j (k - r)^{(j)} \\prod_{i=r+1}^{r+j} τ_i$"
        },
        {
          "Block": "which is the same as (empty products are interpreted as 1)"
        },
        {
          "Block": "$(2k+1)τ_r - 1 = \\frac{τ_r(τ_{r+1})}{1- (r-1) τ_r} \\sum_{j=0}^{k-r} \\binom{k-r}{j} 2^j (k - r)^{(j)} \\prod_{i=r+1}^{r+j} τ_i, \\quad 0 ≤ r ≤ k.$"
        },
        {
          "Block": "Notice that the sum on the right is of the form $1 + u_{r+1} + u_{r+1}u_{r+2} + ... = 1 + u_{r+1} (1 + u_{r+2} + u_{r+2}u_{r+3} + ...)$, and the quantity in brackets on the right occurs in exactly that form in the equation for $r + 1$. Therefore, the above equation can be re-written for $r < k$ as"
        },
        {
          "Block": "$((2k + 1)τ_r − 1)(1 – (r − 1)τ_r) \\frac{τ_r(τ_{r+1})}{τ_r(τ_{r+1})} = 1+ \\frac{2(k - r)τ_{r+1}}{1-rτ_{r+1}} \\frac{((2k+1)τ_{r+1} - 1)(1 – τ_{r+1})}{τ_{r+1}(τ_{r+1}+1)}$"
        },
        {
          "Block": "Plugging in the stated values of $τ_r$ and $τ_{r+1}$, a short calculation shows that both sides are equal to $(2k + 2 – r)/r$, hence equality holds."
        },
        {
          "Block": "For $r = k$, the original equation is $(2k + 1)τ_k 1 = \\frac{τ_k(τ_{k+1})}{1-(k-1)τ_k}$ which is easily seen to be satisfied by $τ_k = 1/(2k − 1)$. This completes the proof. $\\Box$"
        }
      ]
    },
    {
      "Block": "19"
    },
    {
      "content": [
        {
          "header": "section",
          "name": "RANDOM WORDS AND NON-CROSSING MATCHINGS",
          "content": []
        },
        {
          "header": "remark",
          "name": "Remark 17.",
          "remark": "Although the proof is more or less straightforward checking with some calculations, it hinged on having the form of the stationary distribution. All features of the stationary distribution, namely the product form with exponents being $a_is$ and the values of $τ_is$ were arrived at by extensive checking on Mathematica software for several values of $k$, along with some guess work. On a computer, one must restrict to finite state space chains, and a natural restriction is to words of length at most $L$ (steps outside this are forbidden). If $π_L$ is the stationary distribution of this Markov chain, then not only does $π_L$ converge to $π$, but curiously $π_L(w) = π(w)$ for all $w$ of length $L – 1$ or less!"
        },
        {
          "header": "section",
          "name": "REFERENCES",
          "content": [
            {
              "Block": "[1] Gadgil, S. Watson-Crick pairing, the Heisenberg group and Milnor invariants, J. Math. Biol. 59, 123 (2009)."
            },
            {
              "Block": "[2] Gadgil, S. Conjugacy invariant pseudo-norms, representability and RNA secondary structures, Indian J Pure Appl Math 42, 225 (2011)."
            },
            {
              "Block": "[3] Gesteland, R. F. and Cech T. R. and Atkins, J. F. The RNA world: the nature of modern RNA suggests a prebiotic RNA world, Cold Spring Harbor Laboratory Press, 1993."
            },
            {
              "Block": "[4] Kesten, H. Symmetric Random Walks on Groups, Transactions of the American Mathematical Society 92, 336-354."
            },
            {
              "Block": "[5] Ledoux, M. The concentration of measure phenomenon, Mathematical Surveys and Monographs, 89, American Mathematical Society, Providence, RI, 2001."
            },
            {
              "Block": "[6] Steele, J. M. Probability theory and combinatorial optimization, CBMS-NSF Regional Conference Series in Applied Mathematics, 69, Society for Industrial and Applied Mathematics (SIAM), Philadelphia, PA, 1997."
            },
            {
              "Block": "Email address: gadgil@iisc.ac.in"
            },
            {
              "Block": "Email address: manju@iisc.ac.in"
            },
            {
              "Block": "DEPARTMENT OF MATHEMATICS, INDIAN INSTITUTE OF SCIENCE, BANGALORE 560012, INDIA"
            }
          ]
        }
      ]
    }
  ]
}
```
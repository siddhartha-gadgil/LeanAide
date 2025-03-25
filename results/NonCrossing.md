```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "Mathematical Document Wrapper",
  "description": "JSON schema for a structured mathematical document.",
  "type": "object",
  "properties": {
    "document": {
      "type": "array",
      "description": "The root of the mathematical document, containing a sequence of environments.",
      "items": {
        "oneOf": [
          {
            "$ref": "#/components/schemas/Title"
          },
          {
            "$ref": "#/components/schemas/Abstract"
          },
          {
            "$ref": "#/components/schemas/Section"
          },
          {
            "$ref": "#/components/schemas/Theorem"
          },
          {
            "$ref": "#/components/schemas/Definition"
          },
          {
            "$ref": "#/components/schemas/Remark"
          },
          {
            "$ref": "#/components/schemas/Block"
          },
          {
            "$ref": "#/components/schemas/Proof"
          },
          {
            "$ref": "#/components/schemas/Case"
          }
        ]
      }
    }
  },
  "required": [
    "document"
  ],
  "components": {
    "schemas": {
      "Title": {
        "type": "object",
        "description": "The title of the document.",
        "properties": {
          "title": {
            "type": "string",
            "description": "The title text."
          }
        },
        "required": [
          "title"
        ],
        "additionalProperties": false
      },
      "Abstract": {
        "type": "object",
        "description": "The abstract of the document.",
        "properties": {
          "abstract": {
            "type": "string",
            "description": "The abstract text."
          }
        },
        "required": [
          "abstract"
        ],
        "additionalProperties": false
      },
      "Section": {
        "type": "object",
        "description": "A section at some level (chapter, section, subsection, etc.).",
        "properties": {
          "name": {
            "type": "string",
            "description": "The identifier of the section following Mathlib conventions (e.g., `group_theory.definitions`). NOT a theorem, definition, proof or other mathematical environment. Use the appropriate schema for those. If the `header` is a `proof`, this is an ERROR and a `Proof` environment should be used instead."
          },
          "header": {
            "type": "string",
            "description": "The header type of the section (e.g., 'chapter', 'section', 'subsection')."
          },
          "content": {
            "type": "array",
            "description": "The content of the section, which can contain other environments (but not direct nested sections in this version).",
            "items": {
              "oneOf": [
                {
                  "$ref": "#/components/schemas/Theorem"
                },
                {
                  "$ref": "#/components/schemas/Definition"
                },
                {
                  "$ref": "#/components/schemas/Remark"
                },
                {
                  "$ref": "#/components/schemas/Block"
                },
                {
                  "$ref": "#/components/schemas/Proof"
                },
                {
                  "$ref": "#/components/schemas/Case"
                }
              ]
            }
          }
        },
        "required": [
          "name",
          "header",
          "content"
        ],
        "additionalProperties": false
      },
      "Theorem": {
        "type": "object",
        "description": "A mathematical theorem, lemma, claim, etc. (corresponding to AMSLaTeX 'plain' style).",
        "properties": {
          "name": {
            "type": "string",
            "description": "The identifier of the theorem following Lean Prover's Mathlib conventions (e.g., `group.abelian`). NOT just a reference number, but a unique identifier for the theorem."
          },
          "header": {
            "type": "string",
            "description": "The header type of the theorem (e.g., 'theorem', 'lemma', 'proposition', 'corollary', 'claim')."
          },
          "claim": {
            "type": "string",
            "description": "The statement of the theorem."
          }
        },
        "required": [
          "name",
          "header",
          "claim"
        ],
        "additionalProperties": false
      },
      "Definition": {
        "type": "object",
        "description": "A mathematical definition (corresponding to AMSLaTeX 'definition' style).",
        "properties": {
          "name": {
            "type": "string",
            "description": "The identifier of the definition following Mathlib conventions (e.g., `group.is_abelian`)."
          },
          "header": {
            "type": "string",
            "description": "The header type of the definition (e.g., 'definition', 'def')."
          },
          "definition": {
            "type": "string",
            "description": "The content of the definition."
          }
        },
        "required": [
          "name",
          "header",
          "content"
        ],
        "additionalProperties": false
      },
      "Remark": {
        "type": "object",
        "description": "A remark, example, note, etc. (corresponding to AMSLaTeX 'remark' style).",
        "properties": {
          "name": {
            "type": "string",
            "description": "The identifier of the remark following Mathlib conventions (e.g., `group.example_cyclic`)."
          },
          "header": {
            "type": "string",
            "description": "The header type of the remark (e.g., 'remark', 'example', 'note')."
          },
          "remark": {
            "type": "string",
            "description": "The content of the remark."
          }
        },
        "required": [
          "name",
          "header",
          "content"
        ],
        "additionalProperties": false
      },
      "Block": {
        "type": "string",
        "description": "A block of text that is not partitioned further, even into subsections.",
        "additionalProperties": false
      },
      "Proof": {
        "type": "object",
        "description": "A proof environment.",
        "properties": {
          "claim_name": {
            "type": "string",
            "description": "The name of the theorem being proved."
          },
          "proof_steps": {
            "type": "array",
            "description": "The content of the proof, which is a document itself.",
            "items": {
              "oneOf": [
                {
                  "$ref": "#/components/schemas/Section"
                },
                {
                  "$ref": "#/components/schemas/Theorem"
                },
                {
                  "$ref": "#/components/schemas/Definition"
                },
                {
                  "$ref": "#/components/schemas/Remark"
                },
                {
                  "$ref": "#/components/schemas/Block"
                },
                {
                  "$ref": "#/components/schemas/Proof"
                },
                {
                  "$ref": "#/components/schemas/Case"
                }
              ]
            }
          }
        },
        "required": [
          "proof_steps",
          "claim_name"
        ],
        "additionalProperties": false
      },
      "Case": {
        "type": "object",
        "description": "A section of a proof that corresponds to a case.",
        "properties": {
          "condition": {
            "type": "string",
            "description": "The condition defining this case."
          },
          "proof": {
            "type": "array",
            "description": "The proof for this case, which is a document.",
            "items": {
              "oneOf": [
                {
                  "$ref": "#/components/schemas/Section"
                },
                {
                  "$ref": "#/components/schemas/Theorem"
                },
                {
                  "$ref": "#/components/schemas/Definition"
                },
                {
                  "$ref": "#/components/schemas/Remark"
                },
                {
                  "$ref": "#/components/schemas/Block"
                },
                {
                  "$ref": "#/components/schemas/Proof"
                },
                {
                  "$ref": "#/components/schemas/Case"
                }
              ]
            }
          }
        },
        "required": [
          "condition",
          "proof"
        ],
        "additionalProperties": false
      }
    }
  }
}
```

```json
{
  "document": [
    {
      "title": "RANDOM WORDS IN FREE GROUPS, NON-CROSSING MATCHINGS\nAND RNA SECONDARY STRUCTURES"
    },
    {
      "abstract": "Consider a random word $X^n = (X_1, ..., X_n)$ in an alphabet consisting of 4 letters, with the letters viewed either as A, U, G and C (i.e., nucleotides in an RNA sequence) or $\\alpha, \\bar{\\alpha}, \\beta$ and $\\bar{\\beta}$ (i.e., generators of the free group $\\langle\\alpha, \\beta\\rangle$ and their inverses). We show that the expected fraction $p(n)$ of unpaired bases in an optimal RNA secondary structure (with only Watson-Crick bonds and no pseudo-knots) converges to a constant $\\lambda_2$ with $0 < \\lambda_2 < 1$ as $n \\rightarrow \\infty$. Thus, a positive proportion of the bases of a random RNA string do not form hydrogen bonds. We do not know the exact value of $\\lambda_2$, but we derive upper and lower bounds for it.\nIn terms of free groups, $p(n)$ is the ratio of the length of the shortest word representing $X$ in the generating set consisting of conjugates of generators and their inverses to the word length of $X$ with respect to the standard generators and their inverses. Thus for a typical word the word length in the (infinite) generating set consisting of the conjugates of standard generators grows linearly with the word length in the standard generators. In fact, we show that a similar result holds for all non-abelian finitely generated free groups $(\\alpha_1,..., \\alpha_k), k \\geq 2$."
    },
    {
      "header": "section",
      "name": "introduction",
      "content": [
        {
          "Block": "Consider a word $X$ in an alphabet consisting of 4 letters, with the letters viewed either as $\\alpha, \\bar{\\alpha}, \\beta$ and $\\bar{\\beta}$ (i.e., generators of the free group $\\langle\\alpha, \\beta\\rangle$ and their inverses, where we use the notation $\\bar{g}$ for $g^{-1}$) or A, U, G and C (i.e., nucleotides in an RNA sequence). There is a natural notion of a length $l(X)$ associated to such a word, which can be defined in several equivalent ways (see [1] and [2] for more details). We give three descriptions of $l$, two of which (as we indicate below) generalize to random words in $2k$ letters, for $k \\geq 2$.\n(1) If $X$ is viewed as a word in $\\langle\\alpha, \\beta\\rangle$ then $l$ is the maximal conjugacy-invariant length function on $\\langle\\alpha, \\beta\\rangle$ which satisfies $l(\\alpha) \\leq 1$ and $l(\\beta) \\leq 1$. Equivalently, $l$ is the word length in the generating set given by all conjugates"
        }
      ]
    },
    {
      "Block": "$\\mathit{gag}^{-1}, \\mathit{g}\\bar{\\alpha}\\mathit{g}^{-1}, \\mathit{g}\\beta\\mathit{g}^{-1}$ and $\\mathit{g}\\bar{\\beta}\\mathit{g}^{-1}$ of the generators of $\\langle\\alpha, \\beta\\rangle$ and their inverses (where $\\bar{\\alpha} = \\alpha^{-1}$ and $\\bar{\\beta} = \\beta^{-1}$). More generally, an arbitrary word in $2k$ letters gives an element of $\\langle\\alpha_1, ..., \\alpha_k\\rangle$, and $l$ can be defined as a maximal conjugacy-invariant length function (or word length in conjugates of generators and their inverses) in this case too.\n(2) If $X$ is viewed as a nucleotide sequence, then we can consider so called secondary structures of RNA [3], i.e., bonds between nucleotides of the RNA, with bonds being Watson-Crick pairs, i.e. hydrogen bonds between Adenine and Uracil and between Guanine and Cytosine, and stereo-chemical forces modelled by not allowing so called pseudo-knots (for details we refer to [1]). Then $l(X)$ is the minimum number of non-bonded nucleotides for secondary structures of $X$. This is a biologically reasonable notion of energy.\n(3) Again viewing $X = X^{(n)}$ as a word of length $n$ in the alphabet $\\alpha, \\bar{\\alpha}, \\beta$ and $\\bar{\\beta}$, we consider incomplete non-crossing matchings of the (indices of) letters in $X$ so that letters are matched with their inverses. Here a non-crossing matching is a set $P$ of pairs of indices $(i, j), 1 < i < j \\leq n$, such that\n(a) each $i$ belongs to at most one element of $P$,\n(b) if $i < j < k < l$, then at most one of $(i, k)$ and $(j, l)$ belong to $P$,\n(c) if $(i, j) \\in P$ then $X_i = \\bar{X}_j$.\nThe length $l(X)$ is the minimum number of unmatched letters over all non-crossing matchings. More generally we can take a random word in the alphabet with $2k$ letters $\\alpha_1, \\bar{\\alpha}_1, ..., \\alpha_k, \\bar{\\alpha}_k$ (where $\\bar{g}$ denotes $g^{-1}$) and consider non-crossing matchings with letters paired with their inverses, and define $l$ as the minimum number of unmatched letters over all non-crossing matchings.\nHenceforth, fix $k \\geq 2$ and consider a random string $X = X^{(n)}$ of length $n$ in 2k letters as above (i.e., a random word). The case $k = 2$ corresponds to RNA secondary structures, but most of our results and proofs are uniform in $k$. Let $L_k(n) = \\mathbb{E} [l(X^{(n)})]$ where the expectation is over uniform distribution on strings of length $n$. Let $p_k(n) = L_k(n)/n$ denote the average proportion of unpaired letters.\nOur main result is that this fraction converges to a positive constant."
    },
    {
      "header": "theorem",
      "name": "theorem_1",
      "claim": "With the above notations, $p_k(n) \\rightarrow \\lambda_k$ for some constant $0 < \\lambda_k < 1$."
    },
    {
      "Block": "Thus, the average proportion of unpaired bases in an optimal secondary structure for a random RNA string converges to a positive constant as the length of the RNA string approaches infinity. Equivalently, for a word $X$ in the free group $\\langle\\alpha, \\beta\\rangle$ (or more generally in the free group $\\langle\\alpha_1,..., \\alpha_k\\rangle$ for $k \\geq 2$), the average ratio of the word length of $X$ in the (infinite) generating set consisting of conjugates of generators and their inverses to the word length of $X$ in the standard generators and their inverses converges to a positive constant. We remark that this result is also true, but essentially trivial, for the free group $\\mathbb{Z}$ on 1 generator (for the group $\\mathbb{Z}$, the two generating sets, hence the corresponding word lengths, coincide).\nWe also show that $l(X^n)/n$ has exponential concentration in a window of length $1/\\sqrt{n}$ around its expectation $p_k(n)$, and hence around $\\lambda_k$."
    },
    {
      "header": "proposition",
      "name": "proposition_2",
      "claim": "$\\mathbb{P} { | l(X^{(n)}) – np_k(n) | > t\\sqrt{n}} < 2e^{-\\frac{t^2}{2}}$ for any $t > 0$."
    },
    {
      "Block": "An immediate corollary is that the standard deviation of $l(X^n)$ is $O(\\sqrt{n})$.\nAs for proofs, the existence of the limit $\\lambda_k$ and the exponential concentration are proved using sub-additivity and Hoeffding's inequality respectively, which are standard methods in combinatorial optimization problems. Showing that $\\lambda_k$ is strictly positive, and getting bounds for its value require more involved arguments. It would be interesting to find the exact value of $\\lambda_k$, particularly $\\lambda_2$. We are only able to get bounds.\nFor $k = 2$, we prove the explicit bounds $0.034 < \\lambda_2 < 0.231$. The proof of Theorem 1 given in Section 3 gives the lower bound of 0.03, which is then refined to get the slightly better lower bound of 0.034. Elementary arguments in Section 4 give an upper bound of 0.289 which is improved to $\\frac{3}{13} = 0.2307...$ in Section 6. This is achieved by analysing a specific algorithm for producing a non-crossing matching described below."
    },
    {
      "Block": "**The one-sided greedy algorithm.** Scan the letters $X_1, X_2, ...$ in that order and when the turn of $X_t$ comes (starting from $t = 1$), match it to $X_s$ with the largest value of $s < t$, if possible (i.e., $X_s = \\bar{X}_t$, and there is no $u \\in (s,t)$ such that $X_u = \\bar{X}_t$, and the non-crossing condition is maintained).\nFor example, if $k = 2$ and the word is $\\alpha\\beta\\bar{\\alpha}\\beta\\alpha\\bar{\\alpha}\\bar{\\beta}\\bar{\\beta}$, then the matching is $3 \\rightarrow 5, 2 \\rightarrow 7$ (here 3, 5, 2, 7 represent the indices in the word, of course)."
    },
    {
      "header": "section",
      "name": "random_words_and_non_crossing_matchings_1",
      "content": [
        {
          "header": "proposition",
          "name": "proposition_3",
          "claim": "In the one-sided greedy algorithm, the proportion of unmatched letters converges to\n\n$\\bar{\\lambda}_k = 1- \\frac{\\sum_{r=1}^k \\frac{r^2}{(k)^2} \\prod_{j=1}^r \\frac{j(j+1)}{j(2k-j)-1}}{\\sum_{r=0}^k \\frac{r^2}{(k)^2} \\prod_{j=1}^r \\frac{j(j+1)}{j(2k-j)-1}}$\n\nTherefore $\\lambda_k \\leq \\bar{\\lambda}_k$."
        },
        {
          "Block": "The numerical values of upper bound for the first few k are\n\n| k   | 2       | 3       | 4       | 5       |\n| --- | ------- | ------- | ------- | ------- |\n| $\\bar{\\lambda}_k$ | $\\frac{3}{13} = 0.231...$ | $\\frac{33}{100} = 0.33$ | $\\frac{297}{455} = 0.393...$ | $\\frac{3126}{7115} = 0.439...$ |\n\nProposition 3 is proved by analysing an associated Markov chain on the space of words. This Markov chain is described in Section 6, where we also find its stationary distribution explicitly. It may be of independent interest, as there are not many examples of chains that are neither reversible nor have a doubly stochastic transition matrix for which we can solve for the stationary distribution exactly.\nThere is some slack in our proofs, so our bounds can be sharpened. However our goal here is to give a simple and transparent proof. In fact certain enumerative algorithms suggest that $\\lambda_2 < 0.11$ but we are unable to analyse these algorithms rigorously."
        },
        {
          "Block": "**Dependence of $\\lambda_k$ on $k$.** One may also ask about the behaviour of $\\lambda_k$ as a function of $k$. We claim that $\\lambda_k \\leq \\lambda_{k+1}$. This is easiest seen by coupling. Consider a random word $X^n$ using symbols $\\alpha_i, \\bar{\\alpha}_i, 1 \\leq i \\leq k + 1$. Let $X^{(j)}$ denote the word got by deleting all occurrences of $\\alpha_j,\\bar{\\alpha}_j$ in $X^{(n)}$, and let $N_j$ be the length of $X^{(j)}$. Let $l^{(j)}$ denote the number of unmatched letters when the optimal matching on $X^n$ is restricted to $X^{(j)}$. Then $l^{(1)} + ... + l^{(k+1)} = kl(X^n)$ and hence taking expectations and using symmetry,\n\n$(k+1)\\mathbb{E}[L_k(N_1)] \\leq kL_{k+1}(n)$.\n\nThe expectation on the left is over the randomness in $N_1$ which has Binomial distribution with parameters $(n, k/(k+1))$. By Chebyshev's inequality, $\\mathbb{P}{n_- < N_1 \\leq n_+} \\geq 1 – O(n^{-\\frac{1}{2}})$, where $n_{\\pm} = \\frac{kn}{k+1} \\pm n^{\\frac{1}{2}}$. As $n \\rightarrow \\infty$ $L_k(n)$ is obviously increasing in $n$,\n\n$\\mathbb{E}[L_k(N_1)] \\geq (1 – O(n^{-\\frac{1}{2}}))L_k(n)$.\n\nCombine this with (2), divide by $n$, and let $n \\rightarrow \\infty$ to get $\\lambda_k \\leq \\lambda_{k+1}$.\nFurther, we show in Proposition 15 that $\\lambda_k \\rightarrow 1$ as $k \\rightarrow \\infty$."
        }
      ]
    },
    {
      "header": "section",
      "name": "random_words_and_non_crossing_matchings_2",
      "content": [
        {
          "remark": {
            "name": "remark_4",
            "header": "remark",
            "remark": "As a consequence of the convergence of the fraction unmatched to a positive constant and the concentration result, it follows that there is some scale $N$ so that, for a generic RNA strand, optimal structures on pieces of length $N$ can be concatenated to give a near-optimal structure on the whole strand. As bonds at long distances are less likely to form, it follows that RNA folding can be localized to this scale, which makes foldings easier to analyse."
          }
        },
        {
          "Block": "**Outline of the paper.** In Section 2 we show that the different ways of defining the length $l$ outlined above give the same function. In Section 3 we prove Theorem 1 and the above-stated lower bounds for $\\lambda_2$. In Section 4 we present an elementary argument to obtain the upper bound of 0.289 for $\\lambda_2$. In Section 5, we prove Proposition 2. In Section 6 we introduce the Markov chain associated to the one-sided greedy algorithm, and explicitly analyse it prove Proposition 3. In particular, this leads to the improved upper bound for $\\lambda_2$."
        }
      ]
    },
    {
      "header": "section",
      "name": "preliminaries",
      "content": [
        {
          "Block": "For the convenience of the reader, we define length functions on groups and show that three definitions of the length $l$ on $\\langle\\alpha_1,...,\\alpha_k\\rangle$ given above give the same function. The results in this section are elementary."
        },
        {
          "header": "definition",
          "name": "definition_5",
          "definition": "Let $G = (G,.,e, (\\cdot)^{-1})$ be a group (written multiplicatively, with identity element $e$). A length function on $G$ is a map $l : G \\rightarrow [0, +\\infty)$ that obeys the properties\n* $l(e) = 0$,\n* $l(x) > 0$, for all $x \\in G \\setminus {e}$,\n* $l(x^{-1}) = l(x)$, for all $x, y \\in G$.\n* $l(xy) \\leq l(x) + l(y)$, for all $x, y \\in G$."
        },
        {
          "header": "definition",
          "name": "definition_6",
          "definition": "We say that a length function $l$ is conjugacy-invariant if $l(xyx^{-1}) = l(y)$ for all $x, y \\in G$.\nWe shall see here that three definitions of a length $l : \\langle\\alpha_1,..., \\alpha_k\\rangle \\rightarrow [0,\\infty)$ coincide. We also give more details of these definitions."
        },
        {
          "header": "section",
          "name": "maximal_length",
          "content": [
            {
              "Block": "**2.1. Maximal length.** Consider the set $\\mathcal{L}$ consisting of conjugacy-invariant length functions $l: \\langle\\alpha_1,..., \\alpha_k\\rangle \\rightarrow [0, +\\infty)$ satisfying $l(\\alpha_i) \\leq 1$ for all $1 \\leq i \\leq k$. We have a partial order on length functions on $\\langle\\alpha_1, ..., \\alpha_k\\rangle$ given by $l_1 \\leq l_2$ if and only if"
            },
            {
              "Block": "$l_1(g) \\leq l_2(g)$ for all $g \\in \\langle\\alpha_1, ..., \\alpha_k\\rangle$. For this order, it is well known that there is a (necessarily unique, by properties of posets) maximal element. Namely, define\n\n$l_{max}(g) = \\sup{l(g) : l \\in \\mathcal{L}}$.\n\nNote that the set ${l(g) : l \\in \\mathcal{L}}$ is bounded by the word length of $g$, so has a supremum. It is easy to see that $l_{max}$ is a conjugacy-invariant length function, and that $l(\\alpha_i) < 1$ for all $1 < i < k$. Thus $l_{max} \\in \\mathcal{L}$. Further, by construction, if $l \\in \\mathcal{L}$, then $l \\leq l_{max}$. Thus $l_{max}$ is the maximum of the set $\\mathcal{L}$."
            }
          ]
        },
        {
          "header": "section",
          "name": "word_length_in_conjugates_of_generators",
          "content": [
            {
              "Block": "**2.2. Word length in conjugates of generators.** Let $l_{cw}: \\langle\\alpha_1,..., \\alpha_k\\rangle \\rightarrow [0,+\\infty)$ be the function given by the word length in the generating set consisting of all conjugates of the generators $\\alpha_i, 1 \\leq i \\leq k$. Thus, for $g \\in \\langle\\alpha_1,..., \\alpha_k\\rangle$, $l_{cw}(g)$ is the smallest value $r \\geq 0$ so that $g$ can be expressed as\n\n$g = \\prod_{j=1}^r \\beta_j \\alpha_{i_j}^{\\epsilon_j} \\beta_j^{-1}$,\n\nwhere $\\beta_j \\in \\langle\\alpha_1,..., \\alpha_k\\rangle$ and $\\epsilon_j = \\pm 1$, for $1 \\leq j \\leq r$."
            },
            {
              "header": "proposition",
              "name": "proposition_7",
              "claim": "We have $l_{cw} = l_{max}$."
            },
            {
              "proof_steps": [
                {
                  "Block": "**Proof.** We see that $l_{cw} \\in \\mathcal{L}$. This is because the word length in a conjugacy-invariant set is a conjugacy-invariant length function, and $l_{cw}(\\alpha_i) = 1$ for $1 < i < k$.\nFurther, we see that $l_{cw}$ is maximal. Namely, let $l \\in \\mathcal{L}, g \\in G$ and let $r = l_{cw} (g)$. Then we can express $g$ as $g = \\prod_{j=1}^r \\beta_j \\alpha_{i_j}^{\\epsilon_j} \\beta_j^{-1}$. By the triangle inequality, conjugacy-invariance, symmetry, and using $l(\\alpha_i) \\leq 1$ for $i \\leq i \\leq k$,\n\n$l(g) \\leq \\sum_{j=1}^r l(\\beta_j \\alpha_{i_j}^{\\epsilon_j} \\beta_j^{-1}) \\leq \\sum_{j=1}^r l(\\alpha_{i_j}^{\\epsilon_j}) \\leq \\sum_{j=1}^r 1 = r = l_{cw} (g)$,\n\nas required\nAs $l_{cw} \\in \\mathcal{L}$ is maximal, $l_{cw} = l_{max}$."
                }
              ],
              "claim_name": "proposition_7"
            }
          ]
        },
        {
          "header": "section",
          "name": "length_from_non_crossing_matchings",
          "content": [
            {
              "Block": "**2.3. Length from non-crossing matchings.** Let $X^{(n)} = (X_1, ..., X_n)$ be a word in the alphabet with $2k$ letters $\\alpha_1, \\bar{\\alpha}_1, ..., \\alpha_k, \\bar{\\alpha}_k$. Let $NC$ stand for incomplete non-crossing matchings of $[n] = {1,2,..., n}$. Let $NC_k(X)$ be the subset of $M \\in NC$ such that for each matched pair $(i, j) \\in M$ we have ${X_i, X_j} = {\\alpha_\\ell,\\bar{\\alpha}_\\ell}$ for some $l <k$.\nlet $l_{NC}(X)$ be the minimum number of unmatched pairs in all non-crossing matchings so that letters are paired with their inverses. We sketch the proofs that"
            },
            {
              "header": "lemma",
              "name": "lemma_8",
              "claim": "Suppose $X_1$ and $X_2$ represent the same element in the group $\\langle\\alpha_1,..., \\alpha_k\\rangle$, then $l_{nc}(X_1) = l_{nc}(X_2)$."
            },
            {
              "proof_steps": [
                {
                  "Block": "**Proof.** It suffices to consider the case where $X_1$ and $X_2$ are related by a single cancellation. Without loss of generality, assume that there exist words $W_1$ and $W_2$ and an index $1 \\leq j \\leq k$ such that $X_1 = W_1W_2$ and $X_2 = W_1\\alpha_j\\bar{\\alpha}_j^{-1}W_2$. Let $\\mu_p$ be the length of $W_p$ for $p = 1,2$. Note that the cancelling pair corresponds to the pair $(\\mu_1 + 1, \\mu_1 + 2)$ of indices.\nWe show that $l_{NC}(X_1) = l_{nc}(X_2)$. First, fix a non-crossing matching $M_1$ of $X_1$ with $l_{NC}(X_1)$ unmatched letters and with letters paired with their inverses. Let $\\sigma: \\mathbb{N} \\rightarrow \\mathbb{N}$ be defined by\n\n$\\sigma(m) = \\begin{cases} m & \\text{if } m \\leq \\mu_1, \\\\ m+2 & \\text{if } m > \\mu_1 \\end{cases}$\n\nThen $M_2 := \\sigma(M_1) \\cup {(\\mu_1 + 1,\\mu_1 + 2)} \\in NC_k (X_2)$ and has $l_{NC} (X_1)$ unmatched letters (i.e., the same as $M_1$). Hence $l_{NC}(X_2) \\leq l_{nc}(X_1)$.\nConversely, fix a non-crossing matching $M_2 \\in NC_k(X_2)$ with $l_{NC}(X_2)$ unmatched letters. Suppose at most one of $\\mu + 1$ and $\\mu + 2$ is matched in $M'$, and $(i, j) \\in M$ is the corresponding pair with $j \\in {\\mu + 1, \\mu + 2}$. Then $M_1 := M_2 \\setminus {(i, j)} \\in NC_k(X_1)$ and $M_1$ has at most $l_{NC} (X_2)$ unmatched letters.\nNext, if $(\\mu + 1, \\mu + 2) \\in M_2$, then $M_1 := M_2 \\setminus {(\\mu + 1, \\mu + 2)} \\in NC_k(X_1)$ and $M_1$ has $l_{NC}(X_2)$ unmatched letters.\nFinally, if for some indices $i$ and $j$ we have $(i, \\mu + 1) \\in M_2$ and $(j, \\mu + 2) \\in M_2$ (after possibly flipping some pairs), we can see that\n\n$M_1 := M_2 \\cup {(\\mu + 1, \\mu + 2)} \\setminus {((i, \\mu + 1), (j, \\mu + 2))} \\in NC_k(X_1)$\n\nand $M_1$ has $l_{NC} (X_2)$ unmatched letters.\nIn all cases, we conclude that $l_{NC}(X_1) \\leq l_{nc}(X_2)$."
                }
              ],
              "claim_name": "lemma_8"
            }
          ]
        },
        {
          "Block": "It follows that $l_{nc}$ induces a well-defined function on $\\langle\\alpha_1,..., \\alpha_k\\rangle$, which we also denote as $l_{nc}$. It is easy to see that it is a length function. The proof of the following is very similar to that of Lemma 8."
        },
        {
          "header": "lemma",
          "name": "lemma_9",
          "claim": "Suppose $g, h \\in \\langle\\alpha_1, ..., \\alpha_k\\rangle$, then $l_{NC}(hgh^{-1}) = l_{nc}(g)$."
        },
        {
          "Block": "It is easy to see that $l_{nc}(\\alpha_i) = 1$ for all $1 \\leq i \\leq k$, and that $l_{NC}$ is symmetric.\nThus $l_{nc} \\in \\mathcal{L}$. Hence, to show that $l_{NC} = l_{max}$ it suffices to prove maximality, which we prove next."
        },
        {
          "header": "lemma",
          "name": "lemma_10",
          "claim": "Suppose $l \\in \\mathcal{L}$ and $g \\in \\langle\\alpha_1, ..., \\alpha_k\\rangle$. Then $l(g) \\leq l_{nc}(g)$."
        },
        {
          "proof_steps": [
            {
              "Block": "**Proof.** Let $X$ be a word representing $g$. We prove the lemma by (strong) induction on the length $n$ of $X$. The case when the length is zero is clear. Consider a non-crossing matching $M\\in NC_k(X)$ with $l_{NC}(X)$ unmatched letters. First, suppose the index 1 is unmatched in $M$, let $\\bar{X}$ be obtained from $X$ by deleting the first letter. Then $M\\in NC_k(\\bar{X})$, so by induction hypothesis, $l(\\bar{X}) \\leq l_{nc}(\\bar{X})$. Further, as $M$ restricted to $\\bar{X}$ has one less unmatched letter than $M$, we conclude that $l_{NC}(X) = l_{nc}(\\bar{X}) + 1$. As the first letter of $X$ is a generator or the inverse of a generator, using the triangle inequality\n\n$l(X) \\leq 1+l(\\bar{X}) \\leq 1 + l_{nc}(\\bar{X}) = l_{nc}(X)$.\n\nNext, if the pair $(1,j) \\in M$ with $j < n$, we split the word $X$ as $X = X_1 * X_2$ with $X_1$ of length $j$. Observe that the non-crossing condition implies that $M$ decomposes as $M_1 \\cup M_2$ with $M_1 \\in NC_k(X_1)$ and $M_2 \\in NC_k(X_2)$. Again, we use the induction hypothesis and the triangle inequality to conclude that $l(X) \\leq l_{NC}(X)$.\nFinally, if $(1,n) \\in M$, let $\\bar{X}$ be obtained from $X$ by deleting the first and last letter. By conjugacy invariance of $l$ and $l_{nc}$, $l(\\bar{X}) = l(X)$ and $l_{nc}(\\bar{X}) = l_{NC}(X)$. Applying the induction hypothesis to $\\bar{X}$ gives the claim."
            }
          ],
          "claim_name": "lemma_10"
        },
        {
          "Block": "Thus, we can conclude the following."
        },
        {
          "header": "proposition",
          "name": "proposition_11",
          "claim": "We have $l_{NC} = l_{max}$."
        }
      ]
    },
    {
      "header": "section",
      "name": "the_proportion_of_unmatched_indices",
      "content": [
        {
          "Block": "**3. THE PROPORTION OF UNMATCHED INDICES**\nIn this section, we prove Theorem 1 and get lower bounds on $\\lambda_2$. At first, $k$ is fixed, hence we drop it in the subscripts of $L(n)$ and $p(n)$."
        },
        {
          "Block": "The first observation is that $L(n)$ is sub-additive."
        },
        {
          "header": "lemma",
          "name": "lemma_12",
          "claim": "For $m, n > 0$, $L(m + n) \\leq L(m) + L(n)$."
        },
        {
          "proof_steps": [
            {
              "Block": "**Proof.** A string $X^{(m+n)}$ of i.i.d. random variables of length $m + n$ is obtained by taking the concatenation $X^{(n)} * X^{(m)}$ of two strings $X^{(n)}$ and $X^{(m)}$ of i.i.d. random variables of lengths $n$ and $m$ respectively. As the union of elements $M_1 = NC_k(X_1)$ and $M_2 = NC_k(X_2)$ gives a matching $M \\in NC_k(X)$, it is easy to see that $l(X) \\leq l(X_1) + l(X_2)$. By taking expectations the lemma follows."
            }
          ],
          "claim_name": "lemma_12"
        },
        {
          "Block": "As a well known consequence of sub-additivity (Fekete's lemma), we obtain the following."
        },
        {
          "header": "corollary",
          "name": "corollary_13",
          "claim": "The sequence $p(n) = L(n)/n$ converges to $\\lambda_k := \\inf_n p(n)$."
        },
        {
          "Block": "As $0 \\leq p(n) \\leq 1$, we get $0 \\leq \\lambda_k \\leq 1$. It is easy to get some upper bounds for $\\lambda_k$ by computing $p(n)$ for small $n$ (as $\\lambda_k$ is the infimum of $p(n)$). For instance, for $k = 2$ and $n = 4$, $l(X)$ takes values 0, 2 and 4 with probabilities 28/256, 168/256 and 60/256, respectively, hence $\\lambda_2 \\leq \\rho(4) = 9/16$. The harder thing is to get lower bounds. Our main result is that $\\lambda_k$, which is the asymptotic proportion of unpaired bases, is positive."
        },
        {
          "header": "lemma",
          "name": "lemma_14",
          "claim": "We have $\\lambda_k > 0$."
        },
        {
          "proof_steps": [
            {
              "Block": "**Proof.** Fix $\\delta > 0$. Observe that\n\n$L(n) \\geq n\\delta \\cdot \\mathbb{P}(l(X^{(n)}) \\geq n\\delta)$,\n\nand hence\n\n$\\rho(n) \\geq \\delta\\mathbb{P}(l(X^{(n)}) \\geq n\\delta)$.\n\nThus, if we have $\\mathbb{P}(l(X^{(n)}) \\geq n\\delta) \\rightarrow 1$ as $n \\rightarrow \\infty$, then $\\lambda_k > \\delta$. Thus it suffices to find a $\\delta > 0$ for which we can show that $\\mathbb{P}(l(X^{(n)}) > n\\delta) \\rightarrow 1$, or equivalently show that\n\n$\\mathbb{P}(l(X^{(n)}) < n\\delta) \\rightarrow 0$\n\nas $n\\rightarrow\\infty$.\nWe shall now bound $\\mathbb{P}(l(X^{(n)}) < n\\delta)$ for small enough $\\delta$. Note that if $W (n, \\delta)$ is the number of words $X$ of length $n$ with $l(X) < n\\delta$, then\n\n$\\mathbb{P}(l(X^{(n)}) <n\\delta) = \\frac{W(n, \\delta)}{(2k)^n}$"
            },
            {
              "Block": "Let $m = [\\frac{n-n\\delta}{2}]$ and let $r = n - 2m$. Observe that if $l(X^{(n)}) < n\\delta$, then $X = X^{(n)}$ has a non-crossing matching with at least $2m$ pairs, and hence a non-crossing matching $M$ with exactly $2m$ pairs (by simply dropping a few pairs). Given such an $M$, we can associate to $X$ a triple $(Y, Z, s)$ where\n* $Y$ is the word (of length $r$) consisting of the letters of $X$ that are unmatched in $M$, in the same order as in $X$,\n* $Z$ is the word (of length $2m$) consisting of the letters of $X$ that are matched in $M$, in the same order as in $X$, and,\n* $s$ is the set of indices $i, 1 \\leq i \\leq n$, that are unmatched.\nNote that $M$ gives a complete non-crossing matching on $Z$, and hence $Z$ represents the trivial word in $\\langle\\alpha_1, ..., \\alpha_k\\rangle$. As the triple $(Y, Z, s)$ determines $X$, it follows that the number $W (n, \\delta)$ of words $X$ of length $n$ with $l(X) < n\\delta$ is bounded above by the number of triples $(Y, Z, s)$, with\n* $Y$ a word of length $r$,\n* $Z$ a word of length $2m$ that represents the trivial element in the free group, and\n* $s$ a subset of size $r$ of ${1, 2, ..., n}$.\nLet $T_p$ denote the set of words of length $p$ that represent the trivial element in the group $\\langle\\alpha_1,..., \\alpha_k\\rangle$. It follows that\n\n$|W(n, \\delta)| \\leq {n \\choose r} (2k)^r |T_{2m}|$\n\nThe main step remaining is to bound $T_{2m}$. Let $\\tau_p = |T_p|/(2k)^p$ represent the probability that a random word of length $p$ represents the trivial element in $\\langle\\alpha_1, ..., \\alpha_k\\rangle$. We observe that this is the probability that the standard symmetric random walk on the Cayley graph of the free group (with the canonical generators and their inverses) starting at the identity returns to the identity in $p$ steps. It is clear that $\\tau_p\\tau_q \\leq \\tau_{p+q}$, and hence by the Fekete lemma (applied to $\\log \\tau_p$), we see that $\\tau_n^{\\frac{1}{n}} \\rightarrow \\theta_k := \\sup_p \\tau_p^{\\frac{1}{p}}$. This means that $\\tau_p \\leq \\theta_k^p$ for each $p \\geq 1$. Of course $T_p = 0$ for odd $p$.\nIt is a known fact that $\\theta_k = \\frac{\\sqrt{2k-1}}{k}$ (for example Kesten [4]). To see this, observe that the graph distance of the random walk to the identity element is itself a random walk on $\\mathbb{N} = {0, 1, 2, ...}$ that goes from $i \\rightarrow i + 1$ with probability $(2k-1)/2k$ and $i \\leftrightarrow i - 1$ with probability $1/2k$, for $i \\geq 1$, and from 0 to 1 with probability 1. The number of walks of length $p = 2m$ that return to the origin in $\\mathbb{N}$ is the Catalan number $\\frac{1}{m+1} {2m \\choose m}$, and each such path (since it has m up-steps and m down-steps)"
            },
            {
              "Block": "has probability $(2k – 1)^m/(2k)^{2m}$. Therefore,\n\n$\\tau_{2m} \\sim \\frac{(2k-1)^m}{(2k)^{2m}(m + 1)} {2m \\choose m} \\sim \\frac{1}{\\sqrt{\\pi}m^{\\frac{3}{2}}} \\frac{(2k - 1)^m}{k^{2m}}$\n\nby Stirling's formula, where $a_m \\sim b_m$ means that $a_m/b_m$ converges to 1 as $m \\rightarrow \\infty$. In particular, we see that $\\tau_{2m}^{\\frac{1}{2m}} \\rightarrow \\frac{\\sqrt{2k-1}}{k}$. Hence $\\theta_k = \\frac{\\sqrt{2k-1}}{k}$. In particular, $\\theta_2 = \\frac{\\sqrt{3}}{2}$, which we use for explicit estimates on $\\lambda_2$.\nIt is now straightforward to complete the proof. For simplicity of notation, we ignore the error in rounding off to an integer and assume $r = n\\delta$. Using the elementary fact that ${n \\choose r} \\leq e^{nh(\\delta)}$ where $h(\\delta) = -\\delta \\log(\\delta) – (1 – \\delta) \\log(1 – \\delta)$ in (3), we get\n\n$\\mathbb{P}(l(X^{(n)}) < n\\delta) \\leq \\exp {n (h(\\delta) + \\log\\theta_k))}$\n\nHence $\\mathbb{P}(l(X^{(n)}) < n\\delta) \\rightarrow 0$ as $n \\rightarrow \\infty$ provided $h(\\delta) + \\log \\theta_k < 0$.\nWhen $k = 2$, as $\\theta_2 = \\sqrt{3}/2$, this happens, for example, for $\\delta = 0.03$. Thus, we have $\\lambda_2 > 0.03$, i.e. at least 3% of the letters are unmatched for the best non-crossing matching for most words.\nNext, suppose $k \\rightarrow \\infty$. We see that $\\lambda_k \\rightarrow \\infty$."
            }
          ],
          "claim_name": "lemma_14"
        },
        {
          "header": "proposition",
          "name": "proposition_15",
          "claim": "We have $\\lim_{k\\rightarrow\\infty} \\lambda_k = 1$."
        },
        {
          "proof_steps": [
            {
              "Block": "**Proof.** Observe that $\\theta_k = \\frac{\\sqrt{2k-1}}{k} \\rightarrow 0$ as $k \\rightarrow \\infty$, hence $\\log(\\theta_k) \\rightarrow -\\infty$. It follows that for any fixed $\\delta \\in (0,1)$, if $k$ is sufficiently large we have $h(\\delta) + \\log \\theta_k < 0$, hence $\\lambda_k > \\delta$. As $\\lambda_k \\leq 1$ for all $k$, $\\lim_{k\\rightarrow\\infty} \\lambda_k = 1$."
            }
          ],
          "claim_name": "proposition_15"
        },
        {
          "Block": "Thus, we have shown that the limit $\\lambda_k$ of the sequence $p(n)$ exists and is positive. This completes the proof of Theorem 1, with the effective bound $\\lambda_2 \\geq 0.03$ for $k = 2$ (other effective bounds can be computed similarly)."
        },
        {
          "header": "section",
          "name": "refinement_of_the_lower_bound_for_lambda2_using_maximal_triples",
          "content": [
            {
              "Block": "**3.1. Refinement of the lower bound for $\\lambda_2$ using maximal triples.** We can refine the bound we obtained by choosing the triple $(Y, Z, s)$ in a canonical way (note that we do not, however, choose a canonical non-crossing matching on $Z$). Namely we try to match letters with as low indices as possible among all minimal non-crossing matchings. We fix $k = 2$ (so $\\langle\\alpha_1,..., \\alpha_k\\rangle = \\langle\\alpha, \\beta\\rangle$) in this subsection.\nFirst, observe that for fixed $X$, the words $Y$ and $Z$ are determined by $s$. More generally, given $X$, any subset $s \\subset [n]$ determines words $Y = Y(X, s)$ and $Z = Z(X, s)$, but in general the word $Z(X, s)$ may not represent the trivial element in"
            },
            {
              "Block": "$\\langle\\alpha_1,..., \\alpha_k\\rangle$. We shall say the triple $(Y(s), Z(s), s)$ determined by $s$ (and $X$) is admissible provided $Z$ represents the trivial element.\nThe set $s$ can be viewed as a finite sequence by ordering its elements lexicographically, and two such sets can be compared using the lexicographic ordering on finite sequences, which is a total ordering. We order admissible triples $(Y, Z, s)$ by the component $s$ and choose the maximal admissible triple for each fixed $X$.\nWe can decompose $s$ as $s = s_1 \\cup s_2$, with $s_2$ (the tail) consisting of those elements $i \\in s$ such that if $j \\in [n] \\setminus s$, then $j < i$. Conversely, given an element $i \\in s_1$ there exists $j \\in [n] \\setminus s$ such that $j > i$. For $i \\in s_1$, let $\\hat{i}$ be the smallest element in $[n] \\setminus s$ such that $\\hat{i} > i$, i.e., $\\hat{i}$ is the first matched index after the unmatched index $i$. Geometrically, the unmatched indices $s$ are in general interspersed with the matched indices, with a (possibly empty) tail $s_2$ of unmatched indices which are larger than all matched indices.\nWe claim that if $(X, Y, s)$ is maximal and $i \\in s_1$, then $X_i \\neq \\bar{X}_{\\hat{i}}$. For, if $X_i = \\bar{X}_{\\hat{i}}$, let $s' = s \\setminus {i} \\cup {\\hat{i}}$, $Y' = Y(X, s')$ and $Z' = Z(X, s')$. Then $Z' = Z$ as words in the free group, as the letter $X_{\\hat{i}}$ in $Z$ has been replaced by $X_i = \\bar{X}_{\\hat{i}}$ in $Z'$, and in the order on indices, $i$ has the same position in $Z'$ as $\\hat{i}$ has in $Z$ (this is because, if $j \\in [n] \\setminus (s \\cup s')$ is an index in both $Z$ and $Z'$, then $j < \\hat{i}$ if and only if $j < i$ by definition of $\\hat{i}$). Hence $Z'$ represents the trivial word. Hence the triple $(Y', Z', s')$ is admissible, and $s$ and $s'$ have the same cardinality. But $s < s'$, contradicting maximality of $s$.\nThus, writing $Y = Y_1 * Y_2$ with $Y_1$ the word with letters $X_j, j \\in s_i$, and letting $r_i$ be the cardinality of $s_i$, we see that there are only $3^{r_1}4^{r_2}$ possibilities for the word $Y$ (corresponding to a maximal triple). On the other hand, the set $s_2$ is determined by $r_2$ as it consists of the last $r_2$ elements, and $s_1$ is a subset of size $r_1$ of the first $n-r_2=n- r + r_1$ elements.\nHence, using (3) once more and recalling that $\\theta_2 = \\sqrt{3}/2$, we see that\n\n$W(n, \\delta) \\leq \\sum_{r=0}^{[n\\delta]} {n-r+r_1 \\choose r_1} 3^{r_1}4^{r-r_1} {r \\choose r_1} (\\frac{\\sqrt{3}}{2})^{n-r} 4^{n-r}$.\n\nWe use ${n-r+r_1 \\choose r_1} \\leq {n \\choose r}$ and the Chernoff bound for the tail of the binomial distribution to get\n\n$\\sum_{r_1=0}^{[n\\delta]} {n \\choose r} 3^{r_1}4^{r-r_1}7^r \\leq {n \\choose r} \\exp {-n \\left( \\delta \\log(\\frac{\\delta}{3/7}) + (1-\\delta) \\log(\\frac{1-\\delta}{4/7}) \\right)}$\n\n$= \\exp{n[h(\\delta) + \\delta \\log 3 + (1 – \\delta) \\log 4]}$."
            },
            {
              "Block": "Therefore, we get the improved bound\n\n$\\mathbb{P}(l(X^{(n)}) < n\\delta) \\leq |W(n, \\delta)|4^{-n}$\n\n$< \\exp{n[h(\\delta) + \\delta \\log(3/4) + (1 – \\delta) \\log(\\sqrt{3}/2)]}$.\n\nHowever the improved lower bound only gives a marginal improvement to 0.034, i.e., at least 3.4% of the letters are unmatched on average."
            }
          ]
        }
      ]
    },
    {
      "header": "section",
      "name": "an_elementary_upper_bound_on_lambda2",
      "content": [
        {
          "Block": "**4. AN ELEMENTARY UPPER BOUND ON $\\lambda_2$**\nWe claim that $\\lambda_2 \\leq 0.29$ (we shall use more sophisticated methods to obtain a better bound in Section 6). This is achieved as follows. Let $U_1, V_1, U_2, V_2, ...$ be i.i.d. Geometric(1/2) random variables, i.e., $\\mathbb{P}[U_1 = j] = 2^{-j}$ for $j \\geq 1$. Then $\\mathbb{E}[U_1] = 2$, and hence with $m = [n/4]$ we get $N_n := U_1+V_1+...+U_m+V_m = n+O(\\sqrt{n})$ with high probability. We create a string $S\\in {\\alpha,\\bar{\\alpha}, \\beta,\\bar{\\beta}}^{N_n}$ by setting down a random string of ${\\alpha, \\bar{\\alpha}}$ of length $U_1$, then a random string of ${\\beta, \\bar{\\beta}}$ of length $V_1$, etc. Thus, $U_i, V_i$ are the length of runs of the two species of symbols. This makes the length of the string random but since it is in a $\\sqrt{n}$ length window of $n$, this should not change anything much (as regards the proportion of unpaired sites). Consider the following matching algorithm."
        },
        {
          "Block": "Fix any maximal noncrossing matching of all the $\\beta,\\bar{\\beta}$ symbols. Then we make the best possible non-crossing matching of each run of $\\alpha, \\bar{\\alpha}$ within itself. Thus, if the first run happens to be $\\alpha, \\bar{\\alpha}, \\alpha$, then, we could match up the first two sites and leave the third one unpaired.\nIn this matching scheme, in the first stage there are $O(\\sqrt{n})$ unpaired sites (the difference between the number of $\\beta$ and the number of $\\bar{\\beta}$ symbols in $S$). For the second stage, note that in the $j$th run (the one that has length $U_j$), the number of $\\alpha$-symbols is $\\xi_j \\sim \\text{Binomial}(U_j, \\frac{1}{2})$, and hence the number of left overs is $|2\\xi_j – U_j|$. The total number of left over sites has expectation $m\\mathbb{E}[|2\\xi_1 – U_1|] + O(\\sqrt{n})$ which gives us the bound\n\n$\\lambda_2 \\leq \\frac{1}{4} \\mathbb{E}[|2\\xi_1 - U_1|]$.\n\nNumerical evaluation of the expectation (expressed as an infinite sum) gives the bound $\\lambda_2 \\leq 0.2886...$."
        }
      ]
    },
    {
      "header": "section",
      "name": "concentration_around_expected_behaviour",
      "content": [
        {
          "Block": "**5. CONCENTRATION AROUND EXPECTED BEHAVIOUR**\nWe prove Proposition 2 in this section. The tool is the well-known Hoeffding's inequality for sums of martingale differences (see section 4.1 of Ledoux [5] for a proof and the book of Steele [6] for its use in many combinatorial optimization problems similar to ours). It says that if $d_1, d_2, ..., d_n$ is a martingale difference sequence, that is $\\mathbb{E}[d_j|d_1, ... d_{j-1}] = 0$ for each $j$ (for $j = 1$ this is to be interpreted as $\\mathbb{E}[d_1] = 0$) and $|d_j| \\leq B_j$ with probability 1 for some constant $B_j$, then for any $t > 0$, we have\n\n$\\mathbb{P} { | \\sum_{j=1}^n d_j | > t} < 2e^{-\\frac{t^2}{2(\\sum_{j=1}^n B_j^2)}}$"
        },
        {
          "proof_steps": [
            {
              "Block": "**Proof of Proposition 2.** Let $X = X^{(n)} = (X_1, ..., X_n)$. Define for $j = 1, ... n$,\n\n$d_j = \\mathbb{E} [L(X_1, ..., X_n) | X_1, ..., X_j] – \\mathbb{E} [L(X_1, ..., X_n) | X_1, ..., X_{j-1}] $.\n\nThen $d_j$ is a martingale difference sequence by the tower property\n\n$\\mathbb{E}[\\mathbb{E}[U | V, W] | W] = \\mathbb{E}[U | W]$.\n\nFurther, $L(X) – \\mathbb{E}[L(X)] = d_1 + ... + d_n $. If we show that $|d_j| \\leq 2$, then by applying Hoeffding's inequality (4), we get the statement in the lemma.\nTo prove that $|d_j| \\leq 2$, fix $j$ and let $Y = (X_1, ..., X_{j-1}, X'_j, X_{j+1}, ..., X_n)$ where $X'_j$ is an independent copy of $X_j$ that is also independent of all $X_j$s. Then,\n\n$\\mathbb{E}[L(Y) | X_1, ..., X_j] = \\mathbb{E}[L(Y) | X_1,...,X_{j-1}] = \\mathbb{E}[L(X) | X_1,..., X_{j-1}]$,\n\nwhere the first equality holds because $X'_j$ is independent of $Y$ and the second equality holds because $X_1, ... X_{j-1}$ bear the same relationship to $X$ as to $Y$. Thus, we conclude that\n\n$d_j = \\mathbb{E} [L(X) – L(Y) | X_1, ... X_j] $.\n\nBut $X$ and $Y$ differ only in one co-ordinate. From any non-crossing matching of $X$, by deleting the edge (if any) matching the $j$th co-ordinate, we obtain a non-crossing matching for $Y$ with at most two more unmatched indices. Therefore $L(Y) \\leq L(X) + 2$ and by symmetry between $X$ and $Y$, we get $|L(X) – L(Y)| \\leq 2$. Therefore $|d_j| \\leq \\mathbb{E} [|L(X) – L(Y)| | X_1, ... X_j] < 2$."
            }
          ],
          "claim_name": "proposition_2"
        }
      ]
    },
    {
      "header": "section",
      "name": "greedy_algorithms_and_upper_bounds",
      "content": [
        {
          "Block": "**6. GREEDY ALGORITHMS AND UPPER BOUNDS**\nThe goal of this section is to prove Proposition 3. First we introduce a Markov chain related to this algorithm. Recall the description of the algorithm from the introduction."
        },
        {
          "header": "section",
          "name": "the_associated_markov_chain_and_its_stationary_distribution",
          "content": [
            {
              "Block": "**6.1. The associated Markov chain and its stationary distribution.** For simplicity of notation, we write the alphabet set as $\\mathcal{A} = {1,\\bar{1},...,k,\\bar{k}}$. Let $w[t]$ be the word formed by all the accessible letters at “time” $t$ – these are the letters among $X_1,..., X_t$ that are still available for matching in future in the above greedy algorithm. Then $w[t]$ is a Markov chain whose state space is $\\Omega = \\mathcal{A}^0 \\cup \\mathcal{A}^1 \\cup \\mathcal{A}^2 \\cup ...$, the set of all finite strings in the alphabet $\\mathcal{A}$ (including the empty string) and whose dynamics are as follows:\nIf $w[t] = (w_1,..., w_p)$ and $X_{t+1} = x$, then $w[t + 1] = (w_1, ..., w_p, x)$ if $\\bar{x}$ does not occur in $w[t]$. Otherwise $w[t+1] = (w_1, ..., w_{j-1})$ where $j$ is the largest index such that $w_j = \\bar{x}$. Two letters get matched each time the length of $w[t]$ reduces. Hence the number left unmatched after $n$ steps is $n – 2 \\sum_{t=2}^n 1_{\\{length(w[t])<length(w[t-1])\\}}$.\nThe Markov chain is not irreducible. From any state it is possible to go to $\\emptyset$ but from $\\emptyset$ the chain can only go to states in\n\n$\\Omega_0 = {w\\in\\Omega : \\text{at most one of } x, \\bar{x} \\in w \\text{ for each } x \\in \\mathcal{A}}$\n\nwhich makes $\\Omega_0$ the unique irreducible class. As we shall show next, this Markov chain has a stationary probability distribution $\\pi$. By the general theory of Markov chains, the stationary distribution is unique. To give the formula for $\\pi$, we need some notation."
            },
            {
              "Block": "For a word $w \\in \\Omega_0$, define $a_i (w)$ inductively by declaring $a_1 (w) + ... + a_j (w)$ to be the length of the maximal initial segment in $w$ (reading from the left) containing at most $j$ distinct symbols. Note that if $w$ has only $j$ different symbols from $\\mathcal{A}$, it follows that $a_i(w) = 0$ for $i \\geq j$. In particular, as $w \\in \\Omega_0$, it has at most $k$ distinct symbols. For example, if $k = 3$ and $w = 11\\bar{2}12\\bar{2}12311\\bar{2}3\\bar{2}$, then $(a_1,a_2, a_3) = (2,8,6)$. If $w = \\bar{2}\\bar{2}\\bar{2}1\\bar{2}$ then $(a_1, a_2, a_3) = (3,2,0)$. For the empty word, $a_i (w) = 0$ for all $i$."
            },
            {
              "header": "proposition",
              "name": "proposition_16",
              "claim": "Fix $k \\geq 2$. Let $\\tau_j = \\frac{j+1}{j(2k+1)-1}$ for $1 \\leq j \\leq k$. Then the unique stationary probability distribution is given by\n\n$\\pi(w) = \\frac{1}{Z} \\tau_1^{a_1(w)} \\tau_2^{a_2(w)} ... \\tau_k^{a_k(w)}$"
            },
            {
              "Block": "where $Z = \\sum_{r=0}^k {k \\choose r}^2 \\prod_{j=1}^r \\frac{j\\tau_j}{1-j\\tau_j} = \\sum_{r=0}^k {k \\choose r}^2 \\prod_{j=1}^r \\frac{j(j+1)}{j(2k-j)-1}$.\nAssuming this proposition, we prove Proposition 3."
            }
          ]
        },
        {
          "header": "section",
          "name": "proof_of_proposition_3",
          "content": [
            {
              "Block": "**6.2. Proof of Proposition 3.** From the earlier observation, the expected proportion of matched letters after $n$ steps is\n\n$\\frac{2}{n} \\sum_{t=2}^n \\mathbb{P}{length(w[t]) < length(w[t – 1])} \\rightarrow 2\\mathbb{P}_{\\pi}{length(w[1]) < length(w[0])}$\n\nwhere the subscript $\\pi$ is to indicate that $w[0]$ is sampled from $\\pi$ (in the actual chain, we start with $w[0] = (\\emptyset)$ and the convergence follows from the general theory of Markov chains which asserts that the distribution of $(w[t – 1], w[t])$ (from any starting point) converges to the distribution of $(w[0], w[1])$ when $w[0]$ has distribution $\\pi$. As a consequence, we arrive at the upper bound\n\n$\\lambda_k \\leq 1 − 2\\mathbb{P}_{\\pi} {length(w[1]) < length(w[0])}$.\n\nIf $w$ has $r$ distinct symbols, then $a_r(w) > 0(= a_{r+1}(w))$ and its length gets reduced if and only if the next arriving letter can match up with one of them, i.e., with probability $\\frac{r}{2k}$. Further, for a given choice of strictly positive integers $a_1, ..., a_r$, the number of words $w$ with $a_i(w) = a_i$ is precisely\n\n$2^rk(k − 1) ... (k − r + 1)2^{a_2-1}3^{a_3-1}...r^{a_r-1}$.\n\nHere $2k - 2i + 2$ is for the choice of $i$th new symbol (the locations are determined by $a_1,..., a_r$) and the $a_j – 1$ letters between the $j$th new symbol and $(j + 1)$st new symbol each have $j$ choices, hence the factor of $j^{a_j-1}$. Thus,\n\n$\\mathbb{P}_{\\pi}{length(w[1]) < length(w[0])} = \\frac{1}{2kZ} \\sum_{r=1}^k 2^r {k \\choose r} \\left( \\sum_{a_i \\geq 1: \\sum a_i = r} \\prod_{j=1}^r (j\\tau_j)^{a_j-1} \\right) \\sum_{a_i \\geq 1: \\sum a_i = r} \\prod_{j=1}^r (j\\tau_j)^{a_j-1} = \\frac{1}{2kZ} \\sum_{r=1}^k r^2 {k \\choose r}^2 \\prod_{j=1}^r \\frac{j\\tau_j}{1-j\\tau_j}$\n\nSubstituting the value of $\\tau_j$ given in the statement of the proposition,\n\n$\\bar{\\lambda}_k = 1- \\frac{1}{kZ} \\sum_{r=1}^k r^2 {k \\choose r}^2 \\prod_{j=1}^r \\frac{j\\tau_j}{1-j\\tau_j} = 1- \\frac{1}{kZ} \\sum_{r=1}^k r^2 {k \\choose r}^2 \\prod_{j=1}^r \\frac{j(j + 1)}{j(2k-j)-1}$.\n\nPlugging in the expression for $Z$ given in Proposition 16 completes the proof of Proposition 3."
            }
          ],
          "claim_name": "proposition_3"
        }
      ]
    },
    {
      "header": "section",
      "name": "proof_of_proposition_16",
      "content": [
        {
          "header": "section",
          "name": "proof_of_proposition_16_case_k=2",
          "content": [
            {
              "case": {
                "condition": "Case $k = 2$",
                "proof": [
                  {
                    "Block": "This is the case we care most about. We see that $\\tau_1 = \\frac{1}{2}$ and $\\tau_2 = \\frac{3}{7}$ and $Z = \\frac{13}{3}$. Hence $\\pi(w) = (\\frac{1}{2})^{a_1(w)} (\\frac{3}{7})^{a_2(w)} (\\frac{3}{13})^{length(w)}$ where $a_1 (w)$ is the length of the first run (i.e., the maximum $j$ such that $w_1 = w_2 = ... = w_j$). Therefore, (7) becomes\n\n$\\bar{\\lambda}_2 = 1 - \\frac{1}{2 \\times 13} (4 + 16) = \\frac{3}{13} = 0.2307...$"
                  }
                ]
              }
            }
          ]
        },
        {
          "Block": "**6.3. Proof of Proposition 16.** Let $\\sigma(w) = \\tau_1^{a_1(w)} ... \\tau_k^{a_k(w)}$. If $w$ has $r$ distinct symbols, then $a_j \\geq 1$ for $j \\leq r$ and $a_j = 0$ for $j > r$. The number of words $w$ with given $a_1,..., a_r$ is given in (6). Hence the sum of $\\sigma(w)$ over such $w$ is\n\n$2^r {k \\choose r} \\left( \\sum_{a_1,...,a_r \\geq 1} \\prod_{j=1}^r (j\\tau_j)^{a_j-1} \\right) = 2^r {k \\choose r} \\prod_{j=1}^r \\frac{j\\tau_j}{1-j\\tau_j}$\n\nSum over $r$ (including $r = 0$) to get the given expression for $Z$.\nIt suffices to check that $\\sigma$ satisfies the equations for the stationary distribution, since we know the uniqueness (up to scalar multiples) of stationary distribution. The general equations are\n\n$\\sum_{w' \\rightarrow w} \\sigma(w') = 2k\\sigma(w)$\n\nwhere the notation $w' \\rightarrow w$ means that $w'$ can lead to $w$ in one step (in our Markov chain, a given $w'$ can lead to a given $w$ in at most one way, hence the transition probability is exactly $1/2k$). If $w = (w_1,..., w_p)$ has exactly $r$ distinct symbols, then $a_r(w) > 0 = a_{r+1}(w)$, and $\\sigma(w) = \\tau_1^{a_1(w)} ... \\tau_r^{a_r(w)}$. The possible $w'$ are:\n(1) $w' = (w_1,..., w_{p-1})$. Then $a_i(w') = a_i(w)$ for $i \\leq r – 1$ and $a_r(w') = a_r (w) – 1$.\n(2) $w' = wxy^1t_1y^2 ... t_jy^{j+1}$ where $x \\in \\mathcal{A}$ is a symbol that occurs in $w$ and $t_i \\in \\mathcal{A}$ are the new symbols that did not occur before and $y^i = (y^i_1, ..., y^i_{m_i})$ with $m_i \\geq 0$. Here $j$ can vary from 0 to $k – r$. Further, $x$ should not occur in $y^1t_1y^2 ... t_jy^{j+1}$ so that $w'$ can lead to $w$ when an $\\bar{x}$ arrives (it is tacit that all our words are in $\\Omega_0$, so we do not write those conditions again). Then\n\n$a_i(w') = \\begin{cases} a_i (w) & \\text{if } i \\leq r - 1, \\\\ a_r(w) + m_1+1 & \\text{if } i = r, \\\\ m_{i-r+1}+1 & \\text{if } r + 1 \\leq i \\leq r + j. \\end{cases}$\n\nFor given $j$ and $m_1, ..., m_j$, the number of choices of such $w'$ is\n\n$2^j (k - r)(k - r − 1) ... (k - r − j + 1) \\times r(r − 1)^{m_1} r^{m_2} . . . (r + j − 1)^{m_{j+1}}$."
            },
            {
              "Block": "This is because there are $2k - 2r - 2i + 2$ choices for $t_i$ and $r + i – 2$ choices for each letter in $y^i$.\n(3) $w' = wt_1y^1t_2y^2 ... t_jy^j$ where $y^i = (y^i_1, ..., y^i_{m_i})$ with $m_i \\geq 0$ and $t_i \\in \\mathcal{A}$ are the new symbols that did not occur before. Here $j$ can vary from 1 to $k – r$. Further, $t_1$ should not occur in $y^1t_2y^2 . . . t_jy^j$. Then\n\n$a_i(w') = \\begin{cases} a_i (w) & \\text{if } i \\leq r, \\\\ m_{i-r} +1 & \\text{if } r + 1 \\leq i \\leq r + j. \\end{cases}$\n\nFor given $j$ and $m_1, ..., m_j$, the number of choices of such $w'$ is\n\n$2^j (k - r)(k - r − 1) . . . (k − r − j + 1) \\times r^{m_1} (r + 1)^{m_2} . . . (r + j – 1)^{m_j}$.\n\nHere $2k – 2r – 2i + 2$ is the number of choices for $t_i$ and $r + i – 1$ is the number of choices for each letter in $y^2$.\nUsing these and cancelling common factors, the equation for stationary distribution becomes\n\n$2k\\tau_r = 1 + \\frac{r\\tau_r}{1- (r-1) \\tau_r} + \\sum_{j=0}^{k-r} 2^j {k - r \\choose j} \\prod_{i=1}^j \\frac{r+i}{1- (r-1) \\tau_r} \\frac{\\tau_{r+i}}{\\tau_r} + \\sum_{j=1}^{k-r} 2^j {k - r \\choose j} \\prod_{i=1}^j \\frac{r+i}{1- (i - 1) \\tau_i} \\frac{\\tau_{r+i}}{\\tau_r}$\n\n$= 1 + \\frac{r\\tau_r}{1- (r-1) \\tau_r} + (\\frac{r\\tau_r}{1- (r-1) \\tau_r} + \\tau_r) \\sum_{j=1}^{k-r} 2^j {k - r \\choose j} \\prod_{i=1}^j \\frac{1}{1- (i - 1) \\tau_i}$\n\nwhich is the same as (empty products are interpreted as 1)\n\n$(2k+1)\\tau_r - 1 = \\frac{\\tau_r(\\tau_{r+1})}{1- (r-1) \\tau_r} \\sum_{j=0}^{k-r} 2^j {k - r \\choose j} \\prod_{i=r+1}^{r+j} \\frac{1}{1- (i - 1) \\tau_i} , 0 \\leq r \\leq k$.\n\nNotice that the sum on the right is of the form $1 + u_{r+1} + u_{r+1}u_{r+2} + ... = 1 + u_{r+1} (1 + u_{r+2} + u_{r+2}u_{r+3} + ...)$, and the quantity in brackets on the right occurs in exactly that form in the equation for $r + 1$. Therefore, the above equation can be re-written for $r < k$ as\n\n$\\frac{((2k + 1)\\tau_r − 1)(1 – (r − 1)\\tau_r)}{\\tau_r(\\tau_{r+1})} = 1+ \\frac{2(k - r)\\tau_{r+1}}{1-r\\tau_{r+1}} \\frac{((2k+1)\\tau_{r+1} - 1)(1 – \\tau_{r+1})}{\\tau_{r+1}(\\tau_{r+1+1})}$\n\nPlugging in the stated values of $\\tau_r$ and $\\tau_{r+1}$, a short calculation shows that both sides are equal to $(2k + 2 – r)/r$, hence equality holds.\nFor $r = k$, the original equation is $(2k + 1)\\tau_k - 1 = \\frac{\\tau_k(\\tau_{k+1})}{1-(k-1)\\tau_k}$ which is easily seen to be satisfied by $\\tau_k = 1/(2k − 1)$. This completes the proof."
            }
          ]
        }
      ]
    },
    {
      "header": "section",
      "name": "random_words_and_non_crossing_matchings_3",
      "content": [
        {
          "remark": {
            "name": "remark_17",
            "header": "remark",
            "remark": "Although the proof is more or less straightforward checking with some calculations, it hinged on having the form of the stationary distribution. All features of the stationary distribution, namely the product form with exponents being $a_is$ and the values of $\\tau_is$ were arrived at by extensive checking on Mathematica software for several values of $k$, along with some guess work. On a computer, one must restrict to finite state space chains, and a natural restriction is to words of length at most $L$ (steps outside this are forbidden). If $\\pi_L$ is the stationary distribution of this Markov chain, then not only does $\\pi_L$ converge to $\\pi$, but curiously $\\pi_L(w) = \\pi(w)$ for all $w$ of length $L – 1$ or less!"
          }
        },
        {
          "header": "section",
          "name": "references",
          "content": [
            {
              "Block": "**REFERENCES**\n1. Gadgil, S. Watson-Crick pairing, the Heisenberg group and Milnor invariants, J. Math. Biol. 59, 123 (2009).\n2. Gadgil, S. Conjugacy invariant pseudo-norms, representability and RNA secondary structures, Indian J Pure Appl Math 42, 225 (2011).\n3. Gesteland, R. F. and Cech T. R. and Atkins, J. F. *The RNA world: the nature of modern RNA suggests a prebiotic RNA world*, Cold Spring Harbor Laboratory Press, 1993.\n4. Kesten, H. Symmetric Random Walks on Groups, Transactions of the American Mathematical Society 92, 336-354.\n5. Ledoux, M. *The concentration of measure phenomenon*, Mathematical Surveys and Monographs, 89, American Mathematical Society, Providence, RI, 2001.\n6. Steele, J. M. *Probability theory and combinatorial optimization*, CBMS-NSF Regional Conference Series in Applied Mathematics, 69, Society for Industrial and Applied Mathematics (SIAM), Philadelphia, PA, 1997."
            },
            {
              "Block": "Email address: gadgil@iisc.ac.in\nEmail address: manju@iisc.ac.in\nDEPARTMENT OF MATHEMATICS, INDIAN INSTITUTE OF SCIENCE, BANGALORE 560012, INDIA"
            }
          ]
        }
      ]
    }
  ]
}
```
### Introduction

Consider the free group $F$ on two generators α and β, with ̅α and ̅β the inverses of α and β respectively. Elements of $F$ are words in α, β, ̅α and ̅β. We shall consider the problem of finding lower bounds on the number of unpaired letters in a word in α, β, ̅α and ̅β, which is a problem arising in the study of RNA secondary structures.

\begin{definition}
For $g=l_1\dots l_n$, we say that the pairs of letter $(l_i,l_j),i<j$ and $(l_k,l_m), k<m$, are *linked* if either $i<k<j<m$ or $k<i<m<j$.
\end{definition}

\begin{definition}\label{deffold}
A *non-crossing matching* of a word $g=l_1l_2\dots l_n$ in α, β, ̅α and ̅β is a collection of
*disjoint* pairs $\F\subset\{(i,j):1\leq i<j\leq n\}$
such that

1. For $(i,j)\in \F$,
$$(l_i,l_j)\in\{(α, ̅α),( ̅α,α), (β, ̅β),( ̅β,β)\}$$
2. Any two pairs $(i_1,j_1)\in \F$ and $(i_2,j_2)\in\F$ are not linked.

\end{definition}

The number of unpaired letters in a non-crossing matching $\F$ as above is $u(g;\F)=n-2\vert \F\vert$. 
We shall denote the minimum number of unpaired letters in a word $g$ in α, β, ̅α and ̅β by $N(g)$, i.e.,
$$N(g)=\min\{u(g;\F) : \text{$\F$ is a non-crossing matching of $g$}\}$$

A central problem in understanding the secondary structures of RNA is to find lower bounds on the number of unpaired letters in a secondary structure -- any technique giving such a bound is also likely to lead to insights on the structure of the *energy landscape* for secondary structures. In this note, we show that the minimum number of unpaired letters can be viewed as the maximal conjugacy invariant pseudo-norm on the free group $F$ subject to bounds on the generators. This gives a general method for obtaining lower bounds.

\begin{remark}
In considering the function $N$ defined in terms of matchings, we have made two major simplifying assumptions -- we have assumed that there are no pseudo-knots and we have ignored the stereochemical restriction that there are no small loops. 

However, the lower bounds continue to hold even if we include the no small loop restriction, as introducing the restriction means that we are minimising $u(g;\F)$ over a subset of matchings (those satisfying the restriction), so the corresponding minimum is at least as large as $N(g)$, and thus satisfies lower bounds satisfied by $N(g)$. We remark that the number of unpaired letters in an optimal non-crossing matching satisfying the no small loops restriction is no longer a well-defined function on $F$.

Further, while pseudo -knots are present in nature, they account for a small fraction of all bonds. Thus our model agrees to a reasonable extent with molecular biology.
\end{remark}

Our first observation is that $N(g)$ gives a well-defined function on the free group $F$. We prove this in Section~\ref{cancel}.

\begin{theorem}\label{welldef}
If $g_1$ and $g_2$ are strings in α, β, ̅α and ̅β representing the same word in the free group $F$, then $N(g_1)=N(g_2)$.
\end{theorem}

Thus, we can regard the number of unpaired letters in an optimal non-crossing matching as a function $N:F\to \R$ on the free group $F$. We show that $N:F\to\R$
is the maximal conjugacy-invariant pseudo-norm on the free group so that the generators and their inverses have pseudo-norm (at most) $1$. 

\begin{definition}\label{cnjinvnrm}
A conjugacy invariant pseudo-norm on the free group $F$ is a function $n:F\to\R$ such that


1. $n(g)\geq 0$ for all $g\in F$.
2. $n(1)=0$.
3. $n(gh)\leq n(g)+n(h)$ for all $g,h\in F$.
4. $n(\overline{h}gh)=n(g)$ for all $g,h\in F$.

\end{definition}

We use here and throughout the notation $\bar{h}$ to denote inverse of $h\in F$.

\begin{remark}
One may also wish to add the symmetry condition $n(g)=n(\bar g)$ as part of the definition of conjugacy invariant pseudo-norms. All the pseudo-norms we consider automatically satisfy this, so such a change in definition would not affect any of our results.
\end{remark}

It is easy to see that $N(α)=N( ̅α)=N(β)=N( ̅β)=1$.

\begin{theorem}\label{maxconj}
The function $N:F\to \R$ is a conjugacy-invariant pseudo-norm on $F$. Furthermore, if $M:F\to \R$ is a conjugacy-invariant pseudo-norm satisfying the bounds $M(α)\leq 1$, $M( ̅α)\leq 1$, $M(β)\leq 1$ and $M( ̅β)\leq 1$, then $N(g)\geq M(g)$ for all $g\in F$.
\end{theorem}

The main technical lemma in the proof is Lemma~\ref{prodconj}, which gives a representation of a word $g$ as a product of conjugates, corresponding to a non-crossing matching of $g$. Applying this to an optimal non-crossing matching gives an effective description of $N(g)$, which is pivotal in this paper.

Theorem~\ref{maxconj} gives us a general method to construct lower bounds -- we construct pseudo-norms $M$ that are conjugacy invariant and normalise to achieve the conditions $M(α)\leq 1$, $M( ̅α)\leq 1$, $M(β)\leq 1$ and $M( ̅β)\leq 1$. We shall consider two methods to construct such pseudo-norms. We show that the first -- isometric actions on metric spaces, gives sharp bounds (Section~\ref{S:metric}). The second -- orthogonal representations, which is more practically implementable, is also sharp in some important cases. Whether this is sharp in general is a purely mathematical question which we formulate (Section~\ref{S:ortho}).

The formulation of RNA non-crossing matching we consider is a special case of an estimate for the c-conjugating norm, as in~\cite{GIP}. This suggests that mathematical work in~\cite{GIP} and related papers may shed light on RNA non-crossing matching.

### Matchings and cancellations
\label{cancel}

In this section we prove Theorem~\ref{welldef}, which says that $N$ is a well-defined function on the free group $F$. As words representing the same element in the free group are related by insertion or deletion of cancelling pairs of letters, Theorem~\ref{welldef} follows from the following lemma and analogous results for other pairs of generators.

\begin{lemma}
For words $g=\lambda_1\dots \lambda_k$ and $h=\mu_1\dots \mu_m$ in α, β, ̅α and ̅β, 
$$N(gh)=N(gα ̅α h)$$
\end{lemma}
#### Proof

First, we see that $N(gh)\geq N(gα ̅α h)$. Namely, let $\F$ be an optimal non-crossing matching of $gh$, i.e., $N(gh)=u(gh;\F)$. Consider the word $gα ̅α h=l_1\dots l_{k+m+2}=\lambda_1\dots \lambda_kα ̅α\mu_1\dots \mu_m$. As the cancelling pair of letters $l_{k+1}=α$ and $l_{k+2}= ̅α$ are adjacent, they are not linked with any other pair. It follows that the union of $\F$ with the cancelling pair $(l_{k+1},l_{k+2})$ is a non-crossing matching $\F'$. Further, $u(gα ̅α h;\F')=u(gh;\F)$. By the optimality of $\F$, the result follows.

Conversely, let $\F'$ be an optimal non-crossing matching for $gα ̅α h$. We shall show that there is a non-crossing matching $\F$ of $gh$ with $\vert \F\vert\geq\vert\F'\vert-1$. This implies that $u(gh;\F)\leq u(g_1α ̅α h;\F')$, giving the claim.

Firstly, if $(l_{k+1},l_{k+2})\in\F'$, then we delete this pair to obtain $\F$. Next, if at most one of the cancelling letters is in a pair of $\F'$, we delete this pair (if there is one such) to obtain $\F$. In both these cases we obtain a non-crossing matching $\F$ with $\vert \F\vert\geq\vert\F'\vert-1$.
Hence we are reduced to the case where the cancelling letters $l_{k+1}$ and $l_{k+2}$ are paired with different letters $l_i$ and $l_j$.

We claim that we can delete both the pairs involving the cancelling letters $l_{k+1}$ and $l_{k+2}$ and introduce the pair $(l_i,l_j)$ (or $(l_j,l_i)$) to obtain a non-crossing matching $\F$ with $\vert \F\vert=\vert\F'\vert-1$. Observe that $\vert\F\vert\geq\vert\F'\vert-1$. To show $\F$ is a non-crossing matching, it suffices to verify that no pair of $\F$ is linked with $(l_i,l_j)$. This can be seen topologically as an arc intersecting $(l_i,l_j)$ transversally in a single point must also intersect either the segment from $l_{k+1}$ to $l_{k+2}$ or arcs joining one of the points $l_i$ and $l_j$ to the vertex in $\{l_{k+1},l_{k+2}\}$ with which it is paired. However we give an elementary argument below.

Suppose to the contrary, i.e., assume that a pair $(l_p,l_q)$ of $\F$ is linked with $(l_i,l_j)$. We assume without loss of generality that $i<p<j<q$, as the proof in the other case is obtained similarly by reversing all inequalities. We shall consider different cases depending on the relation of $k+1$ to $p$ and $q$, and in each case contradict the assumption that $\F'$ is a non-crossing matching.



1. If $k+1<p$, then as $k+1\neq p$, $k+2<p$. Thus, $k+1<k+2<p<j<q$, so both $l_{k+1}-l_j$ and $l_{k+2}-l_j$ are linked with $l_p-l_q$. At least one of $(l_{k+1},l_j)$ and $(l_{k+2},l_j)$ must be in $\F'$, contradicting the hypothesis that $\F'$ is a non-crossing matching as $(l_p,l_q)\in\F'$.
1. If $p<k+1<q$, then $i<p<k+1<k+2<q$, so both $l_i-l_{k+1}$ and $l_i-l_{k+2}$ are linked with $l_p-l_q$. At least one of $(l_i,l_{k+1})$ and $(l_i,l_{k+2})$ must be in $\F'$, contradicting the hypothesis that $\F'$ is a non-crossing matching as $(l_p,l_q)\in\F'$.
1. If $q<k+1$, then $p<j<q<k+1<k+2$, so both $l_j-l_{k+1}$ and $l_j-l_{k+2}$ are linked with $l_p-l_q$. At least one of $(l_j,l_{k+1})$ and $(l_j,l_{k+2})$ must be in $\F'$, contradicting the hypothesis that $\F'$ is a non-crossing matching as $(l_p,l_q)\in\F'$.


Thus, it must be that $\F$ is a non-crossing matching with $\vert \F\vert=\vert\F'\vert-1$, completing the proof.


### Conjugacy invariance


By Theorem~\ref{welldef}, proved in the previous section, we have a well-defined function $N:F\to\R$. In this section, we show that $N:F\to\R$ is a conjugacy invariant pseudo-norm . First, observe that subadditivity follows as matchings $\F_1$ of $g_1$ and $\F_2$ of $g_2$ give a non-crossing matching $\F=\F_1\cup \F_2$ of $g_1g_2$ with $u(g_1g_2;\F)=u(g_1;\F_1)+u(g_2;\F_2)$. Further, by construction $N(1)=0$ and $N(g)\geq 0$ for all $g\in F$. It only remains to prove conjugacy invariance.

\begin{lemma}
For $g,h\in F$, $N(g)=N(\overline{h}gh)$
\end{lemma}
#### Proof

As $N$ is well-defined on $F$ and conjugacy gives an equivalence relation on a group, it suffices to show that $N(g)\geq N(\overline{h}gh)$. Furthermore, given words $g=\lambda_1\dots \lambda_k$ and $h=\mu_1\dots \mu_m$ representing the elements $g$ and $h$, it suffices to consider the word
$$w=l_1\dots l_{k+2m}=\overline{\mu_m}\dots \overline{\mu_1}\lambda_1\dots \lambda_k\mu_1\dots \mu_m$$
representing $\bar{h}gh$ obtained by concatenation.

Let $\F$ be an optimal non-crossing matching for $g$. We may regard $\F$ as a non-crossing matching of $w=\bar{h}gh$ with each pair of the form $(l_i,l_j)$ with $m<i<j\leq k+m$. We can extend $\F$ to a non-crossing matching $\F'$ of $\overline{h}gh$ given by
$$\F'=\F\cup \{(l_i,l_{k+2m-i}):1\leq i\leq m \}$$

By construction, the letters $l_i=\overline{\mu}_{m-i}$ and $l_{k+2m-i}=\mu_{m-i}$ are inverses and no two pairs of $\F'$ are linked, so $\F'$ is a non-crossing matching. The unpaired letters of $g$ for $\F$ are the same as those of $\overline{h}gh$ for $\F'$, hence $u(g;\F)=u(\bar{h}gh;\F')$. By the optimality of $\F$, it follows that $N(g)\geq N(\bar{h}gh)$ as required.


### Products of conjugates and Maximality


We show that matchings of a word $g$ give, in an appropriate sense, representations of $g$ as a product of conjugates. This allows us to deduce maximality of $N:F\to\R$. 

For an element $g\in F$, let $\vert g\vert$ denote its length in the word metric.

\begin{lemma}\label{prodconj}
Let $\F$ be a non-crossing matching of $g$. Then there is a representation of $g$ as 
$$g=\prod_i \overline{\nu_i}\lambda_i\nu_i,$$
with $\nu_i$ and $\lambda_i$ words in α, β, ̅α and ̅β (hence elements of $F$), so that 
$$u(g;\F)=\sum_i \vert \lambda_i\vert$$
\end{lemma}
#### Proof

We proceed by induction on the length of the word $g$. If $\F$ is empty the result is clear. Otherwise, choose a pair $(l_i,l_j)\in\F$ with $i$ minimal. Without loss of generality, we assume $(l_i,l_j)=( ̅α,α)$, so we obtain
$$g=g(1) ̅α g(2)α g(3)$$

As $i$ is minimal and pairs in $\F$ are not linked, and hence no other pair is linked with $(l_i,l_j)$, for each pair $(l_k,l_m)$ both $l_k$ and $l_m$ are in the subword $g(i)$ for $i=2$ or $i=3$. It follows that $\F$ is the disjoint union
$$\F=\F(2)\cup \F(3)\cup \{(l_i,l_j)\}$$
of sets with $F(j)$ a non-crossing matching of $g(j)$ for $j=2,3$. Hence we see that
$$u(g;\F)=\vert g(1)\vert+ u(g(2);\F(2))+u(g(3);\F(3))$$

By induction hypothesis, it follows that we can express
$$g(j)=\prod_i \overline{\nu_i(j)}\lambda_i(j)\nu_i(j)$$ for $j=2,3$
so that
$$u(g(j);\F)=\sum_i \vert \lambda_i(j)\vert$$

It follows that
$$g=g(1)\cdot
\prod_i \overline{( \nu_i(2)α)}\lambda_i(2)(\nu_i(2)α)
\cdot \prod_i \overline{\nu_i(3)}\lambda_i(3)\nu_i(3)$$
and
$$u(g;\F)=\vert g(1)\vert+\sum_i \vert \lambda_i(2)\vert+\sum_i \vert \lambda_i(3)\vert$$
which gives the required representation.


We deduce another characterisation of the function $N$.

\begin{corollary}
For $g\in F$, $N(g)$ is given by 
$$N(g)=\inf\left\{\sum_i \vert \lambda_i\vert: g=\prod_i \overline{\nu_i}\lambda_i\nu_i\right\}$$
\end{corollary}
#### Proof

By Lemma~\ref{prodconj}, it is immediate that
$$N(g)\geq \inf\left\{\sum_i \vert \lambda_i\vert: g=\prod_i \overline{\nu_i}\lambda_i\nu_i\right\}$$
Conversely, it suffices to show that if $g=\prod_i \overline{\nu_i}\lambda_i\nu_i$, then $N(g)\leq \sum_i\vert\lambda_i\vert$. As $N(α)=N( ̅α)=N(β)=N( ̅β)=1$ and $N$ is subadditive, $N(\lambda_i)\leq \vert\lambda_i\vert$. By conjugacy invariance, $N(\overline{\nu_i}\lambda_i\nu_i)=N(\lambda_i)$. Hence, using subadditivy once more, we obtain
$$N(g)=N(\prod_i \overline{\nu_i}\lambda_i\nu_i)\leq \sum_i N(\overline{\nu_i}\lambda_i\nu_i)= \sum_i N(\lambda_i)
\leq\sum_i\vert\lambda_i\vert$$
as required.


We now deduce the maximality of $N$.

\begin{lemma}\label{max}
If $M:F\to \R$ is a conjugacy invariant pseudo-norm such that $M(α)\leq 1$, $M( ̅α)\leq 1$, $M(β)\leq 1$ and $M( ̅β)\leq 1$, then $N(g)\geq M(g)$ for all $g\in F$.
\end{lemma}
#### Proof

Let $M$ be as above and $g\in F$. Let $\F$ be an optimal non-crossing matching for $g$. Then we have a representation
$$g=\prod_i \overline{\nu_i}\lambda_i\nu_i$$
so that
$$N(g)=u(g;\F)=\sum_i \vert \lambda_i\vert$$

As $M$ is a pseudo-norm with $M(α)\leq 1$, $M( ̅α)\leq 1$, $M(β)\leq 1$ and $M( ̅β)\leq 1$, it follows that $M(h)\leq\vert h\vert$ for all $h\in F$. As $M$ is conjugacy invariant and sub-additive, we get
$$M(g)=M(\prod_i \overline{\nu_i}\lambda_i\nu_i)\leq \sum_i M(\overline{\nu_i}\lambda_i\nu_i)= \sum_i M(\lambda_i)
\leq \sum_i\vert\lambda_i\vert=N(g).$$


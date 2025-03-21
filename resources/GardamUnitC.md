# Non-trivial units of complex group rings

Giles Gardam  Mathematisches Institut, Universität Bonn, Endenicher Allee 60,
53115 Bonn, Germany  [gardam@math.uni-bonn.de](mailto:gardam@math.uni-bonn.de)

###### Abstract.

The Kaplansky unit conjecture for group rings is false in characteristic zero.

###### Key words and phrases:

Group rings, unit conjecture

###### 2020 Mathematics Subject Classification:

20C07 (16S34, 16U60)

## Introduction

Let $G$ be a torsion-free group and $K$ be a field. The question of whether
the group ring $K[G]$ can have any units other than the
_trivial units_ , i.e. the non-zero scalar multiples of group elements, dates
back to Higman’s thesis [Hig40, p. 77] and is generally known as the Kaplansky
unit conjecture. An important consequence of a given $K[G]$
satisfying the conjecture is that it has no zero divisors [Pas85, Lemma
13.1.2].

Once a counterexample to the unit conjecture was finally given in
characteristic 2 [Gar21] and then generalized to arbitrary positive
characteristic [Mur21], the obvious question was whether this phenomenon is
simply an accident of positive characteristic that cannot be found in
characteristic 0. The characteristic 0 case is the most interesting: the
topological motivation such as underlies Higman’s thesis is focussed on the
integral group ring $\mathbb{Z}[G]$ and in an analytic
setting such as operator algebras one generally restricts attention to
$K=\mathbb{C}$. For instance, one way to give a counterexample to the
Atiyah conjecture on integrality of $L^2$-Betti numbers would
be to find $G$ such that $\mathbb{C}[G]$ has zero divisors,
but this necessitates $\mathbb{C}[G]$ having non-trivial
units. Moreover, a counterexample in characteristic 0 necessarily gives a
counterexample in characteristic $p$ for all but finitely many $p$.

## The counterexample

Surprisingly, the exact same 21-element subset of the group that supports
the non-trivial unit over $\mathbb{F}_{2}$ given in [Gar21] also
supports a non-trivial unit over $\mathbb{C}$.

######  Theorem A.

Let $P$ be the torsion-free group defined by the presentation
$\langle a,b \mid b^{-1}a^{2}b=a^{-2}, a^{-1}b^{2}a=b^{-2} \rangle$.
Then $\mathbb{C}[P]$ has non-trivial units. For example, set
$x=a^{2}, y=b^{2}, z=(ab)^{2}$, let
$\omega = \zeta_{8}$ be a primitive 8th root of unity and let
$i = \omega^{2}$. Set

| $p$ | $=1-ix+iy+xy-(1+ix-iy+xy)z^{-1}$ |
---|---|---|---
| $q$ | $=x^{-1}y^{-1}-ix+iy^{-1}z-z$ |
| $r$ | $=1+ix-iy^{-1}z-xyz$ |
| $s$ | $=1+i(x-x^{-1}-y+y^{-1})z^{-1}.$ |

Then $\alpha = p + \omega qa + \omega^{-1}rb + sab$ is a non-trivial unit in the group ring
$\mathbb{C}[P]$.

###### Proof.

This is readily verified using computer algebra. The inverse is given by
$p^{\prime} + \omega q^{\prime}a + \omega^{-1}r^{\prime}b + s^{\prime}ab$ where

| $p^{\prime}$ | $=ix^{-1}+1+x^{-1}y^{-1}-iy^{-1}-(-ix^{-1}+1+x^{-1}y^{-1}+iy^{-1})z$ |
---|---|---|---
| $q^{\prime}$ | $=ix^{-2}y^{-1}-1+x^{-1}y^{-1}z-ix^{-1}z$ |
| $r^{\prime}$ | $=-iy^{-1}-xy^{-1}+y^{-2}z+ixz$ |
| $s^{\prime}$ | $=z^{-1}+i(x-x^{-1}+y^{-1}-y).$ |

The group $P$ arises as a group of affine isometries of Euclidean space
$\mathbb{R}^{3}$ and can be conveniently implemented using the
faithful representation
\[
a\mapsto\begin{pmatrix}1&0&0&1\\ 0&-1&0&1\\ 0&0&-1&0\\ 0&0&0&1 \end{pmatrix},\quad b\mapsto\begin{pmatrix}-1&0&0&0\\ 0&1&0&1\\ 0&0&-1&1\\ 0&0&0&1 \end{pmatrix}.
\]
Indeed, as computed from the group presentation in [Gar21], the index-4
subgroup $\langle x,y,z \rangle$ is isomorphic to
$\mathbb{Z}^{3}$ and faithfulness on this subgroup is seen
immediately. $\qed$

Since the unit has coefficients in
$\mathbb{Z}[\zeta_{8}]$, it yields units in
characteristic $p$ for _all_ primes $p$ and not simply all but finitely many
$p$. To be precise:

######  Corollary.

The 21-element set of the theorem supports non-trivial units over
$\mathbb{F}_{p^{2}}$ for any prime $p$, or
$\mathbb{F}_{p}$ if $p=2$ or $p\equiv 1\mod 8$.

######  Remark 1.

There is a homomorphism $\rho\colon P\to\langle\omega\rangle/\{\pm 1\}\cong\mathbb{Z}/4$
defined by mapping $a\mapsto\{\pm\omega\},b\mapsto\{\pm\omega^{-1}\}$. The
unit $\alpha \in \mathbb{C}[P]$ has the property that it is
of the form $\sum \lambda_{g}g$ where the coefficients
$\lambda_{g} \in \rho(g)$. As the abelianization of $P$ is
$\mathbb{Z}/4\mathbb{Z} \oplus \mathbb{Z}/4\mathbb{Z}$,
there is no homomorphism to
$\langle\omega\rangle\cong\mathbb{Z}/8\mathbb{Z}$,
which would otherwise allow us to “untwist” the unit into an element of
$\mathbb{Z}[P]$.

######  Remark 2.

This unit is also _symmetric_ and _twisted unitary_ in the following sense, as
noted by Bartholdi for positive characteristic units [Bar23]. This is most
elegantly expressed if we shift it by multiplying on the right by
$(ab)^{-1}$ and then apply the automorphism
$a\mapsto a, b\mapsto a^{-2}b$. Call the resulting unit $\gamma$, which in the notation of Theorem A
is
$s + \omega^{-1}x^{-1}ra + \omega zqb + x^{-1}z^{-1}pab$. Let $\phi_{0}\colon a\mapsto a^{-1},b\mapsto b^{-1}$ and $\phi_{1}\colon a\mapsto a,b\mapsto b^{-1}$ be automorphisms of $P$ and let $\chi_{0}\colon a\to -i,b\to -i$ and
$\chi_{1}\colon a\to i,b\to -1$ be
homomorphisms $P\to\mathbb{C}^{\times}$. Then the
automorphisms of $\mathbb{C}[P]$ defined by
\[
\theta_{0}\left(\sum_{g}\lambda_{g}g\right)=\sum_{g}\chi_{0}(g)\lambda_{g}\phi_{0}(g)
\]
and
\[
\theta_{1}\left(\sum_{g}\lambda_{g}g\right)=\sum_{g}\chi_{1}(g)\lambda_{g}\phi_{1}(g)
\]
satisfy $\theta_{0}(\gamma)=\gamma$ and
$\theta_{1}(\gamma)^{*}=\gamma^{-1}$,
that is, it is $\theta_{0}$-symmetric and
$\theta_{1}$-unitary. Here we write
${*}\colon\mathbb{C}[P]\to\mathbb{C}[P]$ for the anti-involution
extending $g\mapsto g^{-1}$ linearly. (Due to the
specific structure of the unit described in Remark 1, one could alternatively
formulate these symmetries using complex conjugation.)

## Finding the solution

The problem of finding a non-trivial unit in $\mathbb{C}[P]$
resisted many attempts of the author over the last three years and surely
attracted the attention of many others; this problem of course looks easier in
hindsight.

A very natural idea is to attempt to lift the solution over
$\mathbb{Z}/2\mathbb{Z}$ to
$\mathbb{Z}/2^{n}\mathbb{Z}$ for increasing $n$ so as to
arrive at a solution over the ring of 2-adic integers. The obstacle here is
that $\mathbb{Z}_{2}$ has no square root of $-1$.

Finding a unit such that it and its inverse are supported on the corresponding
21-element sets means solving a large systems of quadratic equations in
42 variables. One should assume the units are normalized (have
coefficients summing to 1); this means in particular that the trivial units
are a 0-dimensional set. After Bartholdi’s coherent reformulation of [Gar21,
Lemma 1] in terms of automorphisms of the group ring [Bar23], one could
attempt to solve the system of quadratic equations over $\mathbb{C}$ by adding
these additional constraints. As $P$ has abelianization $\mathbb{Z}/4 \oplus \mathbb{Z}/4$ we have the freedom to consider
characters taking values other than $\pm 1$. That reduces the
number of variables from 42 to 11 ($\phi_{0}$ has
precisely one fixpoint in $\operatorname{supp}(\gamma)$). It is
more efficient to enumerate over the $4^{4}$ choices of a pair of
characters $\chi_{0}, \chi_{1}$ than to express them
using additional variables. The resulting collection of systems of equations
can be solved in a matter of seconds for example using singular [DGPS22] via
sage [SD21], even when performing the Gröbner basis computation directly over
$\mathbb{Q}$ instead of over $\mathbb{F}_{p}$ for some large prime
$p$.

The automorphisms $\theta_{0}, \theta_{1}$ of
$\mathbb{C}[P]$ are arguably unnatural, as one does not get
the desirable property of pairs of elements $\alpha$,
$\alpha^{\prime}$ satisfying the symmetry as described by [Gar21,
Lemma 1] that $\alpha\alpha^{\prime}$ automatically vanishes
outside an index 2 subgroup of $P$. Nonetheless, such a trick can only work
for virtually abelian groups, whereas one naturally wishes to understand the
units of other torsion-free groups. The author knows one other torsion-free
group supporting non-trivial units over $\mathbb{F}_{2}$, and here
one again has symmetry but in an unexpected way, emphasizing the point that
[Gar21, Lemma 1] is not the end of the story of symmetry for units. This is
presented in the following section.

However, it turns out that one can solve the problem without imposing these
symmetry constraints using the state of the art software msolve [BES21]. The
time needed to compute a Gröbner basis is only on the scale of hours but one
needs a machine with copious memory. This Gröbner basis itself has limited
value, as the computation is performed modulo a large prime $p$, the variety
it defines has dimension 0, and the basis polynomials are complicated (with
coefficients that are seemingly random elements of
$\mathbb{F}_{p}$). As the system has 17 isolated trivial
solutions, this is perhaps not surprising. We can however avoid the issue of
the trivial solutions by localizing a pair of the variables (enumerating over
different cases so as to be exhaustive). After doing this, the computed
Gröbner basis being non-trivial already tells us that there is a non-trivial
solution (at least modulo $p$) but even better: the coefficients are
$\pm 1 \in \mathbb{F}_{p}$ so that it is clear how
to construct a Gröbner basis over $\mathbb{Q}$ and thus extract solutions over
$\mathbb{C}$.

## Beyond virtually abelian groups

Let
\[
S = \langle x,y \mid (xy)^{2}(xy^{-1})^{2},(yx)^{2}(yx^{-1})^{2} \rangle
\]
be the virtually nilpotent non-unique product group identified in [Soe18, p.
23] (see also [NS]), where it is presented as
$\langle a,b \mid a^{-1}b^{2}ab^{2},a^{-2}ba^{-2}b^{3} \rangle$;
this is isomorphic to $S$ via $x\mapsto a, y\mapsto ab^{-1}$. It has a faithful representation
\[
x\mapsto\begin{pmatrix}-1&1&0\\ 0&-1&0\\ 0&0&1\end{pmatrix},\quad y\mapsto\begin{pmatrix}1&1&0\\ 0&-1&1\\ 0&0&-1\end{pmatrix},
\]
as one can verify by checking (for example with GAP [GAP22]) that
$\langle x^{2},y^{2} \rangle$ is a subgroup of
index 16 isomorphic to the integral Heisenberg group, on which the
representation is easily seen to be faithful. We note that $S$ is torsion-
free, which can be proved by writing it as the free product with amalgamation
of two Klein bottle subgroups:
\begin{align*}
\langle x,y \mid (xy)^{2}(xy^{-1})^{2},(yx)^{2}(yx^{-1})^{2} \rangle &\cong \langle x,y \mid (xy)^{2}(xy^{-1})^{2},(xy)^{2}(yx)^{2} \rangle \\
&\cong \langle a,b,w,x,y \mid a^{2}b^{2}, xw^{2}x, a=xy, b=x^{-1}y, w=yxy \rangle \\
&\cong \langle a,b,w,x,y \mid a^{2}b^{2}, w^{2}x^{2}, a=xy, ba^{-1}=x^{-2}, wa^{-1}=y \rangle \\
&\cong \langle a,b,w,x \mid a^{2}b^{2}, w^{2}x^{2}, a^{2}=xw, ba^{-1}=x^{-2} \rangle \\
&\cong \langle a,b \mid a^{2}b^{2} \rangle *_{\mathbb{Z}^{2}} \langle w,x \mid w^{2}x^{2} \rangle
\end{align*}
This means the representation is faithful on all of the group $S$. From the
presentation we conclude that $\phi\colon S\to S\colon x\mapsto y,y\mapsto x^{-1}$ is a homomorphism and thus an order 4 automorphism. It is
a straightforward computer verification to prove:

######  Theorem B.

The element
\begin{align*}
\nu &= x+x^{-1}+y+y^{-1}+xy+x^{-1}y^{-1}+yx^{-1}+y^{2}+y^{-1}x+y^{-2} \\
&+x^{2}y+xy^{-1}x+xy^{-2}+x^{-2}y^{-1}+x^{-1}yx^{-1}+x^{-1}y^{2}+yxy+y^{-1}x^{-1}y^{-1} \\
&+x^{2}y^{-1}x+xyx^{2}+x^{-2}yx^{-1}+x^{-1}y^{-1}x^{-2}+yx^{-2}y^{-1}+y^{-1}x^{2}y \\
&+x^{2}yx^{2}+xy^{-1}x^{2}y+x^{-2}y^{-1}x^{-2}+x^{-1}yx^{-2}y^{-1}+x^{2}y^{-1}x^{2}y
\end{align*}
of $\mathbb{F}_{2}[S]$ is a $\phi$-unitary
unit, that is, $\nu^{-1}=\phi(\nu)^{*}$.

Thus $\phi^{2}$ is a non-trivial automorphism that fixes
the unit; the symmetry exhibited by $\nu$ and its inverse is order 4 but
isomorphic to $\mathbb{Z}/4$ rather than
$\mathbb{Z}/2\times\mathbb{Z}/2$ as was the case for $P$.

### Acknowledgements

This work was funded by the European Union (ERC, SATURN, 101076148) and the
Deutsche Forschungsgemeinschaft (DFG, German Research Foundation) under
Project-ID 506523109 (Emmy Noether) and under Germany’s Excellence Strategy
EXC 2044–390685587 and EXC-2047/1 – 390685813.

The Max Planck Institute for Mathematics in the Sciences hosted a stimulating
workshop in Leipzig in April 2023 on _Solving hard polynomial systems_. I
thank the organizers and the other participants, especially Georgy Scholten,
for helpful discussions. I also thank Franziska Jahnke and Daniel Windisch for
many interesting discussions on model theoretic approaches to constructing
units in characteristic zero.

## References

  * [Bar23] Laurent Bartholdi.  On Gardam’s and Murray’s units in group rings.  Algebra Discrete Math., 35(1):22–29, 2023.
  * [BES21] Jérémy Berthomieu, Christian Eder, and Mohab Safey El Din.  msolve: A Library for Solving Polynomial Systems.  In 2021 International Symposium on Symbolic and Algebraic Computation, 46th International Symposium on Symbolic and Algebraic Computation, pages 51–58, Saint Petersburg, Russia, July 2021. ACM.
  * [DGPS22] Wolfram Decker, Gert-Martin Greuel, Gerhard Pfister, and Hans Schönemann.  Singular 4-3-0 — A computer algebra system for polynomial computations.  <http://www.singular.uni-kl.de>, 2022.
  * [GAP22] The GAP Group.  GAP – Groups, Algorithms, and Programming, Version 4.12.2, 2022\.
  * [Gar21] Giles Gardam.  A counterexample to the unit conjecture for group rings.  Ann. of Math. (2), 194(3):967–979, 2021.
  * [Hig40] Graham Higman.  Units in group rings.  D.Phil. thesis, University of Oxford, 1940.
  * [Mur21] Alan G. Murray.  More counterexamples to the unit conjecture for group rings.  2021\.  arXiv preprint arXiv:2106.02147.
  * [NS] Pace Nielsen and Lindsay Soelberg.  Small sets without unique products in torsion-free groups.  J. Algebra Appl. To appear, published online.
  * [Pas85] Donald S. Passman.  The algebraic structure of group rings.  Robert E. Krieger Publishing Co., Inc., Melbourne, FL, 1985.  Reprint of the 1977 original.
  * [SD21] The Sage Developers.  SageMath, the Sage Mathematics Software System (Version 9.4), 2021.  https://www.sagemath.org.
  * [Soe18] Lindsay Jennae Soelberg.  Finding torsion-free groups which do not have the unique product property.  Master’s thesis, Brigham Young University, 2018.  https://scholarsarchive.byu.edu/etd/6932.
```
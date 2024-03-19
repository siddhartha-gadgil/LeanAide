### Length functions on groups  

*  A *pseudo-length function* on a group $G$ is a function $l: G \to [0, \infty)$ such that
   *  $l(e) = 0$, where $e\in G$ is the identity,
   *  $l(g^{-1}) = l(g)$ for all $g \in G$ (**symmetry**),
   *  $l(gh) \leq l(g) + l(h)$ for all $g,h\in G$ (the **triangle inequality**).

* A pseudo-length function $l$ on a group $G$ is said to be a \alert{length function} if $l(g) > 0$ for all $g\in G \setminus \{ e \}$.
* Norms on vector spaces, such as $l(x, y) = \sqrt{x^2 + y^2}$ on $\R^2$, are length functions. 
*  A pseudo-length function $l$ on a group $G$ is said to be *homogeneous* if $l(g^n) = nl(g)$ for all $g\in G$, $n \in\Z$.
*  A pseudo-length function $l$ on a group $G$ is said to be *conjugacy invariant* if $l(ghg^{-1}) = l(h)$ for all $g, h\in G$ \pause -- if
$G$ is \alert{abelian} every pseudo-length function is conjugacy-invariant.


### Question[Apoorva Khare via Terence Tao]

#### Question
  Is there a function $l: \langle \alpha, \beta\rangle \to [0, \infty)$ on the free group on two generators such that 
    
*  $l(g) = 0$ if and \alert{only if} $g = e$ (\alert{positivity}).
*  $l(g^{-1}) = l(g)$ for all $g\in \langle \alpha, \beta\rangle$.
*  $l(gh) \leq l(g)+ l(h)$ for all $g, h\in \langle \alpha, \beta\rangle$.
*  $l(ghg^{-1}) = l(h)$ for all $g, h\in \langle \alpha, \beta\rangle$.
*  $l(g^n) = nl(g)$ for all $g\in \langle \alpha, \beta\rangle$, $n\in\mathbb{Z}$.

###  The Theorem and Proof

####  Theorem:
    For any group $G$, every homogeneous pseudo-length $l: G \to \R$ is the pullback of a homogeneous pseudo-length on the abelianization $G/ [G, G]$. 

#### Corollary
    If $G$ is not abelian (e.g. $G = \mathbb{F}_2$) there is no homogeneous length function on $G$.

### Internal Repetition trick
#### Lemma    
If $x = s(wy)s^{-1} = t(zw^{-1})t^{-1}$, we have $l(x)\leq \frac{l(y)+ l(z)}{2}$.
#### Proof:      
* $\begin{aligned}
l(x^nx^n) &= l(s(wy)^ns^{-1}t(zw^{-1})^nt^{-1}) \\\\
&\leq n(l(y) +l(z)) + 2(l(s) + l(t))
\end{aligned}$
*  Use $l(x) = \frac{l(x^nx^n)}{2n}$ and take limits.

### The key inequality
  
*  The above lemma says that if $x \sim wy$ and $x \sim zw^{-1}$, then $l(x)\leq \frac{l(y)+ l(z)}{2}$.
*  We can now deduce $f(m,k)\leq \frac{f(m-1,k)+f(m+1,k-1)}{2}$.
*  Namely, observe that $x^m[x, y]^k$ is conjugate to both $x(x^{m-1}[x, y]^k)$ and $(y^{-1}x^m[x, y]^{k-1}xy)x^{-1}$.
*  Hence $l(x^m[x, y]^k) \leq\frac{l(x^{m-1}[x, y]^k) + l(y^{-1}x^m[x, y]^{k-1}xy)}{2}$.
*  Since $y^{-1}x^m[x, y]^{k-1}xy$ is conjugate to $x^{m+1}[x, y]^{k-1}$, the claim follows.
   
  
### Tao's probability theory argument
  
*  The inequality $f(m,k)\leq \frac{f(m-1,k)+f(m+1,k-1)}{2}$ can be interpreted as the average of $f$ being non-decreasing along the random walk on $\Z^2$ where we move by $(-1, 0)$ or $(1, -1)$ with equal probability.
*  The average displacement of a step is $(0, -1/2)$.
*  Hence taking $2n$ steps starting at $(0, n)$ gives an upper bound for $f(0, 2n)=l((\alpha\beta\alpha^{-1}\beta^{-1})^n)$ by the average length for a distribution centered at the origin.
*  This was bounded using the Chebyshev inequality.


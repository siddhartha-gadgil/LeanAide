You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. The translated code is preceded by `import Mathlib._`, so do not include import statements. Suppress proofs for brevity. Follow EXACTLY the examples given.

The following are some examples of statements and their translations (proofs are suppressed for brevity):

## Natural language statement

Let `f : X x Y → Z`. If as `y` tends to `l`, `f(x, y) = O(g(y))` uniformly on `s : Set X`
of finite measure, then f is eventually (as `y` tends to `l`) integrable along `s`. 

## Lean Code

∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] {g : α → F} {l : Filter α} {ι : Type u_4}
  [inst_1 : MeasurableSpace ι] {f : ι × α → E} {s : Set ι} {μ : MeasureTheory.Measure ι} [inst_2 : Norm F],
  f =O[Filter.principal s ×ˢ l] (g ∘ Prod.snd) →
    (∀ᶠ (x : α) in l, MeasureTheory.AEStronglyMeasurable (fun (i : ι) ↦ f (i, x)) (μ.restrict s)) →
      MeasurableSet s → μ s < ⊤ → ∀ᶠ (x : α) in l, MeasureTheory.IntegrableOn (fun (i : ι) ↦ f (i, x)) s μ

## Natural language statement

If `v` and `w` are two non-trivial and inequivalent absolute values then we can find an `a : R`
such that `1 < v a` while `w a < 1`.


## Lean Code

∀ {R : Type u_1} {S : Type u_2} [inst : Field R] [inst_1 : Semifield S] [inst_2 : LinearOrder S] [IsStrictOrderedRing S]
  [Archimedean S] [ExistsAddOfLE S] {v w : AbsoluteValue R S},
  v.IsNontrivial → w.IsNontrivial → ¬v.IsEquiv w → ∃ (a : R), 1 < v a ∧ w a < 1

## Natural language statement

Consider two actions `f₁ f₂ : G → α → α` of a group on a conditionally complete lattice by order
isomorphisms. Suppose that each set $s(x)=\\{f_1(g)^{-1} (f_2(g)(x)) | g \\in G\\}$ is bounded above.
Then the map `x ↦ sSup s(x)` semiconjugates each `f₁ g'` to `f₂ g'`.

This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homéomorphismes du cercle et
cohomologie bornée][ghys87:groupes]. 

## Lean Code

∀ {α : Type u_1} {G : Type u_4} [inst : ConditionallyCompleteLattice α] [inst_1 : Group G] (f₁ f₂ : G →* α ≃o α),
  (∀ (x : α), BddAbove (Set.range fun (g : G) ↦ (f₁ g)⁻¹ ((f₂ g) x))) →
    ∀ (g : G), Function.Semiconj (fun (x : α) ↦ ⨆ (g' : G), (f₁ g')⁻¹ ((f₂ g') x)) ⇑(f₂ g) ⇑(f₁ g)

## Natural language statement

If `1 < |z|`, then `|S • z| < 1`. 

## Lean Code

∀ {z : UpperHalfPlane}, 1 < Complex.normSq ↑z → Complex.normSq ↑(ModularGroup.S • z) < 1

## Natural language statement

 For any set `s`, functions `w` and `z` from `s` to nonnegative real numbers with sum `1`, and natural number `n`, the `n`-th power of the weighted sum of `w(i) * z(i)` is less than or equal to the weighted sum of `w(i) * z(i)` raised to the `n`-th power.

## Lean Code

∀ {ι : Type u} (s : Finset ι) (w z : ι → NNReal),
  ∑ i ∈ s, w i = 1 → ∀ (n : ℕ), (∑ i ∈ s, w i * z i) ^ n ≤ ∑ i ∈ s, w i * z i ^ n

## Natural language statement

`∑ z ∈ L, ‖z‖⁻ʳ ≤ A⁻ʳ * ∑ k : ℕ, kᵈ⁻ʳ⁻¹` for some `A > 0` depending only on `L`. 

## Lean Code

∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [inst_3 : DiscreteTopology ↥L],
  ∀ r < -↑(Module.finrank ℤ ↥L),
    ∑' (z : ↥L), ‖z‖ ^ r ≤ ZLattice.tsumNormRPowBound L ^ r * ∑' (k : ℕ), ↑k ^ (↑(Module.finrank ℤ ↥L) - 1 + r)

## Natural language statement

This theorem states that for any types `R`, `V`, `P` where `R` is an ordered ring, `V` is an additive commutative group, `P` is an affine space over `V` with `R` as its scalar field, and `x`, `y`, `z` are points in this affine space, if `y` is strictly between `x` and `z` (according to the definition `Sbtw`), then `y` is also weakly between `x` and `z` (according to the definition `Wbtw`). In other words, the condition of a point being strictly between two other points implies the condition of the point being weakly between the same two points.

## Lean Code

∀ {R : Type u_1} {V : Type u_2} {P : Type u_4} [inst : Ring R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup V]
  [inst_3 : Module R V] [inst_4 : AddTorsor V P] {x y z : P}, Sbtw R x y z → Wbtw R x y z

## Natural language statement

 For all extended real numbers x, y, z, and t, if x < y and z < t then x + z < y + t.

## Lean Code

∀ {x y z t : EReal}, x < y → z < t → x + z < y + t

## Natural language statement

If `v` and `w` are inequivalent absolute values and `v` is non-trivial, then we can find an `a : R`
such that `v a < 1` while `1 ≤ w a`.


## Lean Code

∀ {R : Type u_1} {S : Type u_2} [inst : Field R] [inst_1 : Semifield S] [inst_2 : LinearOrder S] [IsStrictOrderedRing S]
  [Archimedean S] [ExistsAddOfLE S] {v w : AbsoluteValue R S},
  v.IsNontrivial → ¬v.IsEquiv w → ∃ (a : R), v a < 1 ∧ 1 ≤ w a

## Natural language statement

This theorem states that, given a linear ordered field `𝕜` and three elements `x`, `y`, and `z` from that field with `x < y`, a point `z` is in the left-open right-open interval between `x` and `y` if and only if there exist two positive numbers `a` and `b` such that `a` and `b` sum up to 1 and `z` can be expressed as a strict convex combination of `x` and `y`, in other words, `z` equals to `a * x + b * y`.

## Lean Code

∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {x y z : 𝕜},
  x < y → (z ∈ Set.Ioo x y ↔ ∃ (a : 𝕜) (b : 𝕜), 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z)

## Natural language statement

 For any nonnegative real numbers $w\\_1, w\\_2, z\\_1,$ and $z\\_2$ with $w\\_1 + w\\_2 = 1,$ and for any real number $p \\ge 1,$ we have $w\\_1 * z\\_1^p + w\\_2 * z\\_2^p \\le (w\\_1 * z\\_1 + w\\_2 * z\\_2) ^ p.$

## Lean Code

∀ (w₁ w₂ z₁ z₂ : NNReal), w₁ + w₂ = 1 → ∀ {p : ℝ}, 1 ≤ p → (w₁ * z₁ + w₂ * z₂) ^ p ≤ w₁ * z₁ ^ p + w₂ * z₂ ^ p

## Natural language statement

Given `z : ℍ` and a bottom row `(c,d)`, among the `g : SL(2,ℤ)` with this bottom row, minimize
`|(g•z).re|`. 

## Lean Code

∀ (z : UpperHalfPlane) {cd : Fin 2 → ℤ},
  IsCoprime (cd 0) (cd 1) →
    ∃ (g : Matrix.SpecialLinearGroup (Fin 2) ℤ),
      ↑g 1 = cd ∧ ∀ (g' : Matrix.SpecialLinearGroup (Fin 2) ℤ), ↑g 1 = ↑g' 1 → |(g • z).re| ≤ |(g' • z).re|

## Natural language statement

 Given an Archimedean additive group G, a transitive and covariant relation R on an additive group H, a monotonic function f from a set F to H with constants a and b, if for all x, y in the closed interval [l, l+a] in G with x < y, R holds between f(x) and f(y), then R holds between f(x) and f(y) for all x, y in F with x < y.

## Lean Code

∀ {F : Type u_1} {G : Type u_2} {H : Type u_3} [inst : FunLike F G H] {a : G} {b : H} [inst_1 : AddCommGroup G]
  [inst_2 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] [inst_5 : AddGroup H] [AddConstMapClass F G H a b]
  {f : F} {R : H → H → Prop} [IsTrans H R] [hR : CovariantClass H H (fun (x y : H) ↦ y + x) R],
  0 < a →
    ∀ {l : G},
      (∀ x ∈ Set.Icc l (l + a), ∀ y ∈ Set.Icc l (l + a), x < y → R (f x) (f y)) →
        Relator.LiftFun (fun (x1 x2 : G) ↦ x1 < x2) R ⇑f ⇑f

## Natural language statement

Let `f : X x Y → Z`. If as `y` tends to `l`, `f(x, y) = O(g(y))` uniformly on `s : Set X`
of finite measure, then the integral of `f` along `s` is `O(g(y))`. 

## Lean Code

∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] {g : α → F} {l : Filter α} {ι : Type u_4}
  [inst_1 : MeasurableSpace ι] {f : ι × α → E} {s : Set ι} {μ : MeasureTheory.Measure ι} [inst_2 : NormedSpace ℝ E]
  [inst_3 : NormedAddCommGroup F],
  f =O[Filter.principal s ×ˢ l] (g ∘ Prod.snd) →
    MeasurableSet s → μ s < ⊤ → (fun (x : α) ↦ ∫ (i : ι) in s, f (i, x) ∂μ) =O[l] g

---

Translate the following statement into Lean 4:
## Theorem: Let G be a group and let l : G -> R be a homogeneous pseudo-length function. Let a,w,y,z,s,t in G. Assume a=s(wy)s^{-1} and a=t(zw^{-1})t^{-1}. Then l(a) <= (l(y)+l(z))/2.

Give ONLY the Lean code

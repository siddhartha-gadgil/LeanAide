/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.MeasureTheory.Measure.AeMeasurable

/-!
# Typeclasses for measurability of operations

In this file we define classes `has_measurable_mul` etc and prove dot-style lemmas
(`measurable.mul`, `ae_measurable.mul` etc). For binary operations we define two typeclasses:

- `has_measurable_mul` says that both left and right multiplication are measurable;
- `has_measurable_mul₂` says that `λ p : α × α, p.1 * p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `has_measurable_mul₂`
etc require `α` to have a second countable topology.

We define separate classes for `has_measurable_div`/`has_measurable_sub`
because on some types (e.g., `ℕ`, `ℝ≥0∞`) division and/or subtraction are not defined as `a * b⁻¹` /
`a + (-b)`.

For instances relating, e.g., `has_continuous_mul` to `has_measurable_mul` see file
`measure_theory.borel_space`.

## Implementation notes

For the heuristics of `@[to_additive]` it is important that the type with a multiplication
(or another multiplicative operations) is the first (implicit) argument of all declarations.

## Tags

measurable function, arithmetic operator

## Todo

* Uniformize the treatment of `pow` and `smul`.
* Use `@[to_additive]` to send `has_measurable_pow` to `has_measurable_smul₂`.
* This might require changing the definition (swapping the arguments in the function that is
  in the conclusion of `measurable_smul`.)
-/


universe u v

open BigOperators Pointwise MeasureTheory

open MeasureTheory

/-!
### Binary operations: `(+)`, `(*)`, `(-)`, `(/)`
-/


/-- We say that a type `has_measurable_add` if `((+) c)` and `(+ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (+)` see `has_measurable_add₂`. -/
class HasMeasurableAdd (M : Type _) [MeasurableSpace M] [Add M] : Prop where
  measurable_const_add : ∀ c : M, Measurable ((· + ·) c)
  measurable_add_const : ∀ c : M, Measurable (· + c)

export HasMeasurableAdd (measurable_const_add measurable_add_const)

/-- We say that a type `has_measurable_add` if `uncurry (+)` is a measurable functions.
For a typeclass assuming measurability of `((+) c)` and `(+ c)` see `has_measurable_add`. -/
class HasMeasurableAdd₂ (M : Type _) [MeasurableSpace M] [Add M] : Prop where
  measurable_add : Measurable fun p : M × M => p.1 + p.2

export HasMeasurableAdd₂ (measurable_add)

export HasMeasurableAdd (measurable_const_add measurable_add_const)

/-- We say that a type `has_measurable_mul` if `((*) c)` and `(* c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (*)` see `has_measurable_mul₂`. -/
@[to_additive]
class HasMeasurableMul (M : Type _) [MeasurableSpace M] [Mul M] : Prop where
  measurable_const_mul : ∀ c : M, Measurable ((· * ·) c)
  measurable_mul_const : ∀ c : M, Measurable (· * c)

export HasMeasurableMul (measurable_const_mul measurable_mul_const)

/-- We say that a type `has_measurable_mul` if `uncurry (*)` is a measurable functions.
For a typeclass assuming measurability of `((*) c)` and `(* c)` see `has_measurable_mul`. -/
@[to_additive HasMeasurableAdd₂]
class HasMeasurableMul₂ (M : Type _) [MeasurableSpace M] [Mul M] : Prop where
  measurable_mul : Measurable fun p : M × M => p.1 * p.2

export HasMeasurableMul₂ (measurable_mul)

section Mul

variable {M α : Type _} [MeasurableSpace M] [Mul M] {m : MeasurableSpace α} {f g : α → M} {μ : Measureₓ α}

include m

@[measurability, to_additive]
theorem Measurable.const_mul [HasMeasurableMul M] (hf : Measurable f) (c : M) : Measurable fun x => c * f x :=
  (measurable_const_mul c).comp hf

@[measurability, to_additive]
theorem AeMeasurable.const_mul [HasMeasurableMul M] (hf : AeMeasurable f μ) (c : M) :
    AeMeasurable (fun x => c * f x) μ :=
  (HasMeasurableMul.measurable_const_mul c).comp_ae_measurable hf

@[measurability, to_additive]
theorem Measurable.mul_const [HasMeasurableMul M] (hf : Measurable f) (c : M) : Measurable fun x => f x * c :=
  (measurable_mul_const c).comp hf

@[measurability, to_additive]
theorem AeMeasurable.mul_const [HasMeasurableMul M] (hf : AeMeasurable f μ) (c : M) :
    AeMeasurable (fun x => f x * c) μ :=
  (measurable_mul_const c).comp_ae_measurable hf

@[measurability, to_additive]
theorem Measurable.mul' [HasMeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) : Measurable (f * g) :=
  measurable_mul.comp (hf.prod_mk hg)

@[measurability, to_additive]
theorem Measurable.mul [HasMeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a * g a :=
  measurable_mul.comp (hf.prod_mk hg)

@[measurability, to_additive]
theorem AeMeasurable.mul' [HasMeasurableMul₂ M] (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (f * g) μ :=
  measurable_mul.comp_ae_measurable (hf.prod_mk hg)

@[measurability, to_additive]
theorem AeMeasurable.mul [HasMeasurableMul₂ M] (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (fun a => f a * g a) μ :=
  measurable_mul.comp_ae_measurable (hf.prod_mk hg)

omit m

@[to_additive]
instance (priority := 100) HasMeasurableMul₂.to_has_measurable_mul [HasMeasurableMul₂ M] : HasMeasurableMul M :=
  ⟨fun c => measurable_const.mul measurable_id, fun c => measurable_id.mul measurable_const⟩

@[to_additive]
instance Pi.has_measurable_mul {ι : Type _} {α : ι → Type _} [∀ i, Mul (α i)] [∀ i, MeasurableSpace (α i)]
    [∀ i, HasMeasurableMul (α i)] : HasMeasurableMul (∀ i, α i) :=
  ⟨fun g => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_mul _, fun g =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).mul_const _⟩

@[to_additive Pi.has_measurable_add₂]
instance Pi.has_measurable_mul₂ {ι : Type _} {α : ι → Type _} [∀ i, Mul (α i)] [∀ i, MeasurableSpace (α i)]
    [∀ i, HasMeasurableMul₂ (α i)] : HasMeasurableMul₂ (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => measurable_fst.eval.mul measurable_snd.eval⟩

attribute [measurability]
  Measurable.add' Measurable.add AeMeasurable.add AeMeasurable.add' Measurable.const_add AeMeasurable.const_add Measurable.add_const AeMeasurable.add_const

end Mul

/-- A version of `measurable_div_const` that assumes `has_measurable_mul` instead of
  `has_measurable_div`. This can be nice to avoid unnecessary type-class assumptions. -/
@[to_additive
      " A version of `measurable_sub_const` that assumes `has_measurable_add` instead of\n  `has_measurable_sub`. This can be nice to avoid unnecessary type-class assumptions. "]
theorem measurable_div_const' {G : Type _} [DivInvMonoidₓ G] [MeasurableSpace G] [HasMeasurableMul G] (g : G) :
    Measurable fun h => h / g := by
  simp_rw [div_eq_mul_inv, measurable_mul_const]

/-- This class assumes that the map `β × γ → β` given by `(x, y) ↦ x ^ y` is measurable. -/
class HasMeasurablePow (β γ : Type _) [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] where
  measurable_pow : Measurable fun p : β × γ => p.1 ^ p.2

export HasMeasurablePow (measurable_pow)

/-- `monoid.has_pow` is measurable. -/
instance Monoidₓ.hasMeasurablePow (M : Type _) [Monoidₓ M] [MeasurableSpace M] [HasMeasurableMul₂ M] :
    HasMeasurablePow M ℕ :=
  ⟨measurable_from_prod_encodable fun n => by
      induction' n with n ih
      · simp only [← pow_zeroₓ, Pi.one_def, ← measurable_one]
        
      · simp only [← pow_succₓ]
        exact measurable_id.mul ih
        ⟩

section Pow

variable {β γ α : Type _} [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] [HasMeasurablePow β γ]
  {m : MeasurableSpace α} {μ : Measureₓ α} {f : α → β} {g : α → γ}

include m

@[measurability]
theorem Measurable.pow (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x ^ g x :=
  measurable_pow.comp (hf.prod_mk hg)

@[measurability]
theorem AeMeasurable.pow (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) : AeMeasurable (fun x => f x ^ g x) μ :=
  measurable_pow.comp_ae_measurable (hf.prod_mk hg)

@[measurability]
theorem Measurable.pow_const (hf : Measurable f) (c : γ) : Measurable fun x => f x ^ c :=
  hf.pow measurable_const

@[measurability]
theorem AeMeasurable.pow_const (hf : AeMeasurable f μ) (c : γ) : AeMeasurable (fun x => f x ^ c) μ :=
  hf.pow ae_measurable_const

@[measurability]
theorem Measurable.const_pow (hg : Measurable g) (c : β) : Measurable fun x => c ^ g x :=
  measurable_const.pow hg

@[measurability]
theorem AeMeasurable.const_pow (hg : AeMeasurable g μ) (c : β) : AeMeasurable (fun x => c ^ g x) μ :=
  ae_measurable_const.pow hg

omit m

end Pow

/-- We say that a type `has_measurable_sub` if `(λ x, c - x)` and `(λ x, x - c)` are measurable
functions. For a typeclass assuming measurability of `uncurry (-)` see `has_measurable_sub₂`. -/
class HasMeasurableSub (G : Type _) [MeasurableSpace G] [Sub G] : Prop where
  measurable_const_sub : ∀ c : G, Measurable fun x => c - x
  measurable_sub_const : ∀ c : G, Measurable fun x => x - c

export HasMeasurableSub (measurable_const_sub measurable_sub_const)

/-- We say that a type `has_measurable_sub` if `uncurry (-)` is a measurable functions.
For a typeclass assuming measurability of `((-) c)` and `(- c)` see `has_measurable_sub`. -/
class HasMeasurableSub₂ (G : Type _) [MeasurableSpace G] [Sub G] : Prop where
  measurable_sub : Measurable fun p : G × G => p.1 - p.2

export HasMeasurableSub₂ (measurable_sub)

/-- We say that a type `has_measurable_div` if `((/) c)` and `(/ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (/)` see `has_measurable_div₂`. -/
@[to_additive]
class HasMeasurableDiv (G₀ : Type _) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_const_div : ∀ c : G₀, Measurable ((· / ·) c)
  measurable_div_const : ∀ c : G₀, Measurable (· / c)

export HasMeasurableDiv (measurable_const_div measurable_div_const)

/-- We say that a type `has_measurable_div` if `uncurry (/)` is a measurable functions.
For a typeclass assuming measurability of `((/) c)` and `(/ c)` see `has_measurable_div`. -/
@[to_additive HasMeasurableSub₂]
class HasMeasurableDiv₂ (G₀ : Type _) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_div : Measurable fun p : G₀ × G₀ => p.1 / p.2

export HasMeasurableDiv₂ (measurable_div)

section Div

variable {G α : Type _} [MeasurableSpace G] [Div G] {m : MeasurableSpace α} {f g : α → G} {μ : Measureₓ α}

include m

@[measurability, to_additive]
theorem Measurable.const_div [HasMeasurableDiv G] (hf : Measurable f) (c : G) : Measurable fun x => c / f x :=
  (HasMeasurableDiv.measurable_const_div c).comp hf

@[measurability, to_additive]
theorem AeMeasurable.const_div [HasMeasurableDiv G] (hf : AeMeasurable f μ) (c : G) :
    AeMeasurable (fun x => c / f x) μ :=
  (HasMeasurableDiv.measurable_const_div c).comp_ae_measurable hf

@[measurability, to_additive]
theorem Measurable.div_const [HasMeasurableDiv G] (hf : Measurable f) (c : G) : Measurable fun x => f x / c :=
  (HasMeasurableDiv.measurable_div_const c).comp hf

@[measurability, to_additive]
theorem AeMeasurable.div_const [HasMeasurableDiv G] (hf : AeMeasurable f μ) (c : G) :
    AeMeasurable (fun x => f x / c) μ :=
  (HasMeasurableDiv.measurable_div_const c).comp_ae_measurable hf

@[measurability, to_additive]
theorem Measurable.div' [HasMeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) : Measurable (f / g) :=
  measurable_div.comp (hf.prod_mk hg)

@[measurability, to_additive]
theorem Measurable.div [HasMeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a / g a :=
  measurable_div.comp (hf.prod_mk hg)

@[measurability, to_additive]
theorem AeMeasurable.div' [HasMeasurableDiv₂ G] (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (f / g) μ :=
  measurable_div.comp_ae_measurable (hf.prod_mk hg)

@[measurability, to_additive]
theorem AeMeasurable.div [HasMeasurableDiv₂ G] (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (fun a => f a / g a) μ :=
  measurable_div.comp_ae_measurable (hf.prod_mk hg)

attribute [measurability]
  Measurable.sub Measurable.sub' AeMeasurable.sub AeMeasurable.sub' Measurable.const_sub AeMeasurable.const_sub Measurable.sub_const AeMeasurable.sub_const

omit m

@[to_additive]
instance (priority := 100) HasMeasurableDiv₂.to_has_measurable_div [HasMeasurableDiv₂ G] : HasMeasurableDiv G :=
  ⟨fun c => measurable_const.div measurable_id, fun c => measurable_id.div measurable_const⟩

@[to_additive]
instance Pi.has_measurable_div {ι : Type _} {α : ι → Type _} [∀ i, Div (α i)] [∀ i, MeasurableSpace (α i)]
    [∀ i, HasMeasurableDiv (α i)] : HasMeasurableDiv (∀ i, α i) :=
  ⟨fun g => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_div _, fun g =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).div_const _⟩

@[to_additive Pi.has_measurable_sub₂]
instance Pi.has_measurable_div₂ {ι : Type _} {α : ι → Type _} [∀ i, Div (α i)] [∀ i, MeasurableSpace (α i)]
    [∀ i, HasMeasurableDiv₂ (α i)] : HasMeasurableDiv₂ (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => measurable_fst.eval.div measurable_snd.eval⟩

@[measurability]
theorem measurable_set_eq_fun {m : MeasurableSpace α} {E} [MeasurableSpace E] [AddGroupₓ E] [MeasurableSingletonClass E]
    [HasMeasurableSub₂ E] {f g : α → E} (hf : Measurable f) (hg : Measurable g) : MeasurableSet { x | f x = g x } := by
  suffices h_set_eq : { x : α | f x = g x } = { x | (f - g) x = (0 : E) }
  · rw [h_set_eq]
    exact (hf.sub hg) measurable_set_eq
    
  ext
  simp_rw [Set.mem_set_of_eq, Pi.sub_apply, sub_eq_zero]

theorem measurable_set_eq_fun_of_encodable {m : MeasurableSpace α} {E} [MeasurableSpace E] [MeasurableSingletonClass E]
    [Encodable E] {f g : α → E} (hf : Measurable f) (hg : Measurable g) : MeasurableSet { x | f x = g x } := by
  have : { x | f x = g x } = ⋃ j, { x | f x = j } ∩ { x | g x = j } := by
    ext1 x
    simp only [← Set.mem_set_of_eq, ← Set.mem_Union, ← Set.mem_inter_eq, ← exists_eq_right']
  rw [this]
  refine' MeasurableSet.Union fun j => MeasurableSet.inter _ _
  · exact hf (measurable_set_singleton j)
    
  · exact hg (measurable_set_singleton j)
    

theorem ae_eq_trim_of_measurable {α E} {m m0 : MeasurableSpace α} {μ : Measureₓ α} [MeasurableSpace E] [AddGroupₓ E]
    [MeasurableSingletonClass E] [HasMeasurableSub₂ E] (hm : m ≤ m0) {f g : α → E} (hf : measurable[m] f)
    (hg : measurable[m] g) (hfg : f =ᵐ[μ] g) : f =ᶠ[@Measure.ae α m (μ.trim hm)] g := by
  rwa [Filter.EventuallyEq, ae_iff, trim_measurable_set_eq hm _]
  exact @MeasurableSet.compl α _ m (@measurable_set_eq_fun α m E _ _ _ _ _ _ hf hg)

end Div

/-- We say that a type `has_measurable_neg` if `x ↦ -x` is a measurable function. -/
class HasMeasurableNeg (G : Type _) [Neg G] [MeasurableSpace G] : Prop where
  measurable_neg : Measurable (Neg.neg : G → G)

/-- We say that a type `has_measurable_inv` if `x ↦ x⁻¹` is a measurable function. -/
@[to_additive]
class HasMeasurableInv (G : Type _) [Inv G] [MeasurableSpace G] : Prop where
  measurable_inv : Measurable (Inv.inv : G → G)

export HasMeasurableInv (measurable_inv)

export HasMeasurableNeg (measurable_neg)

@[to_additive]
instance (priority := 100) has_measurable_div_of_mul_inv (G : Type _) [MeasurableSpace G] [DivInvMonoidₓ G]
    [HasMeasurableMul G] [HasMeasurableInv G] : HasMeasurableDiv G where
  measurable_const_div := fun c => by
    convert measurable_inv.const_mul c
    ext1
    apply div_eq_mul_inv
  measurable_div_const := fun c => by
    convert measurable_id.mul_const c⁻¹
    ext1
    apply div_eq_mul_inv

section Inv

variable {G α : Type _} [Inv G] [MeasurableSpace G] [HasMeasurableInv G] {m : MeasurableSpace α} {f : α → G}
  {μ : Measureₓ α}

include m

@[measurability, to_additive]
theorem Measurable.inv (hf : Measurable f) : Measurable fun x => (f x)⁻¹ :=
  measurable_inv.comp hf

@[measurability, to_additive]
theorem AeMeasurable.inv (hf : AeMeasurable f μ) : AeMeasurable (fun x => (f x)⁻¹) μ :=
  measurable_inv.comp_ae_measurable hf

attribute [measurability] Measurable.neg AeMeasurable.neg

@[simp, to_additive]
theorem measurable_inv_iff {G : Type _} [Groupₓ G] [MeasurableSpace G] [HasMeasurableInv G] {f : α → G} :
    (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by
    simpa only [← inv_invₓ] using h.inv, fun h => h.inv⟩

@[simp, to_additive]
theorem ae_measurable_inv_iff {G : Type _} [Groupₓ G] [MeasurableSpace G] [HasMeasurableInv G] {f : α → G} :
    AeMeasurable (fun x => (f x)⁻¹) μ ↔ AeMeasurable f μ :=
  ⟨fun h => by
    simpa only [← inv_invₓ] using h.inv, fun h => h.inv⟩

@[simp]
theorem measurable_inv_iff₀ {G₀ : Type _} [GroupWithZeroₓ G₀] [MeasurableSpace G₀] [HasMeasurableInv G₀] {f : α → G₀} :
    (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by
    simpa only [← inv_invₓ] using h.inv, fun h => h.inv⟩

@[simp]
theorem ae_measurable_inv_iff₀ {G₀ : Type _} [GroupWithZeroₓ G₀] [MeasurableSpace G₀] [HasMeasurableInv G₀]
    {f : α → G₀} : AeMeasurable (fun x => (f x)⁻¹) μ ↔ AeMeasurable f μ :=
  ⟨fun h => by
    simpa only [← inv_invₓ] using h.inv, fun h => h.inv⟩

omit m

@[to_additive]
instance Pi.has_measurable_inv {ι : Type _} {α : ι → Type _} [∀ i, Inv (α i)] [∀ i, MeasurableSpace (α i)]
    [∀ i, HasMeasurableInv (α i)] : HasMeasurableInv (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => (measurable_pi_apply i).inv⟩

@[to_additive]
theorem MeasurableSet.inv {s : Set G} (hs : MeasurableSet s) : MeasurableSet s⁻¹ :=
  measurable_inv hs

end Inv

/-- `div_inv_monoid.has_pow` is measurable. -/
instance DivInvMonoidₓ.hasMeasurableZpow (G : Type u) [DivInvMonoidₓ G] [MeasurableSpace G] [HasMeasurableMul₂ G]
    [HasMeasurableInv G] : HasMeasurablePow G ℤ :=
  ⟨measurable_from_prod_encodable fun n => by
      cases' n with n n
      · simp_rw [zpow_of_nat]
        exact measurable_id.pow_const _
        
      · simp_rw [zpow_neg_succ_of_nat]
        exact (measurable_id.pow_const (n + 1)).inv
        ⟩

@[to_additive]
instance (priority := 100) has_measurable_div₂_of_mul_inv (G : Type _) [MeasurableSpace G] [DivInvMonoidₓ G]
    [HasMeasurableMul₂ G] [HasMeasurableInv G] : HasMeasurableDiv₂ G :=
  ⟨by
    simp only [← div_eq_mul_inv]
    exact measurable_fst.mul measurable_snd.inv⟩

/-- We say that the action of `M` on `α` `has_measurable_vadd` if for each `c` the map `x ↦ c +ᵥ x`
is a measurable function and for each `x` the map `c ↦ c +ᵥ x` is a measurable function. -/
class HasMeasurableVadd (M α : Type _) [HasVadd M α] [MeasurableSpace M] [MeasurableSpace α] : Prop where
  measurable_const_vadd : ∀ c : M, Measurable ((· +ᵥ ·) c : α → α)
  measurable_vadd_const : ∀ x : α, Measurable fun c : M => c +ᵥ x

/-- We say that the action of `M` on `α` `has_measurable_smul` if for each `c` the map `x ↦ c • x`
is a measurable function and for each `x` the map `c ↦ c • x` is a measurable function. -/
@[to_additive]
class HasMeasurableSmul (M α : Type _) [HasSmul M α] [MeasurableSpace M] [MeasurableSpace α] : Prop where
  measurable_const_smul : ∀ c : M, Measurable ((· • ·) c : α → α)
  measurable_smul_const : ∀ x : α, Measurable fun c : M => c • x

/-- We say that the action of `M` on `α` `has_measurable_vadd₂` if the map
`(c, x) ↦ c +ᵥ x` is a measurable function. -/
class HasMeasurableVadd₂ (M α : Type _) [HasVadd M α] [MeasurableSpace M] [MeasurableSpace α] : Prop where
  measurable_vadd : Measurable (Function.uncurry (· +ᵥ ·) : M × α → α)

/-- We say that the action of `M` on `α` `has_measurable_smul₂` if the map
`(c, x) ↦ c • x` is a measurable function. -/
@[to_additive HasMeasurableVadd₂]
class HasMeasurableSmul₂ (M α : Type _) [HasSmul M α] [MeasurableSpace M] [MeasurableSpace α] : Prop where
  measurable_smul : Measurable (Function.uncurry (· • ·) : M × α → α)

export HasMeasurableSmul (measurable_const_smul measurable_smul_const)

export HasMeasurableSmul₂ (measurable_smul)

export HasMeasurableVadd (measurable_const_vadd measurable_vadd_const)

export HasMeasurableVadd₂ (measurable_vadd)

@[to_additive]
instance has_measurable_smul_of_mul (M : Type _) [Mul M] [MeasurableSpace M] [HasMeasurableMul M] :
    HasMeasurableSmul M M :=
  ⟨measurable_id.const_mul, measurable_id.mul_const⟩

@[to_additive]
instance has_measurable_smul₂_of_mul (M : Type _) [Mul M] [MeasurableSpace M] [HasMeasurableMul₂ M] :
    HasMeasurableSmul₂ M M :=
  ⟨measurable_mul⟩

@[to_additive]
instance Submonoid.has_measurable_smul {M α} [MeasurableSpace M] [MeasurableSpace α] [Monoidₓ M] [MulAction M α]
    [HasMeasurableSmul M α] (s : Submonoid M) : HasMeasurableSmul s α :=
  ⟨fun c => by
    simpa only using measurable_const_smul (c : M), fun x =>
    (measurable_smul_const x : Measurable fun c : M => c • x).comp measurable_subtype_coe⟩

@[to_additive]
instance Subgroup.has_measurable_smul {G α} [MeasurableSpace G] [MeasurableSpace α] [Groupₓ G] [MulAction G α]
    [HasMeasurableSmul G α] (s : Subgroup G) : HasMeasurableSmul s α :=
  s.toSubmonoid.HasMeasurableSmul

section Smul

variable {M β α : Type _} [MeasurableSpace M] [MeasurableSpace β] [HasSmul M β] {m : MeasurableSpace α} {f : α → M}
  {g : α → β}

include m

@[measurability, to_additive]
theorem Measurable.smul [HasMeasurableSmul₂ M β] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x • g x :=
  measurable_smul.comp (hf.prod_mk hg)

@[measurability, to_additive]
theorem AeMeasurable.smul [HasMeasurableSmul₂ M β] {μ : Measureₓ α} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (fun x => f x • g x) μ :=
  HasMeasurableSmul₂.measurable_smul.comp_ae_measurable (hf.prod_mk hg)

omit m

@[to_additive]
instance (priority := 100) HasMeasurableSmul₂.to_has_measurable_smul [HasMeasurableSmul₂ M β] : HasMeasurableSmul M β :=
  ⟨fun c => measurable_const.smul measurable_id, fun y => measurable_id.smul measurable_const⟩

include m

variable [HasMeasurableSmul M β] {μ : Measureₓ α}

@[measurability, to_additive]
theorem Measurable.smul_const (hf : Measurable f) (y : β) : Measurable fun x => f x • y :=
  (HasMeasurableSmul.measurable_smul_const y).comp hf

@[measurability, to_additive]
theorem AeMeasurable.smul_const (hf : AeMeasurable f μ) (y : β) : AeMeasurable (fun x => f x • y) μ :=
  (HasMeasurableSmul.measurable_smul_const y).comp_ae_measurable hf

@[measurability, to_additive]
theorem Measurable.const_smul' (hg : Measurable g) (c : M) : Measurable fun x => c • g x :=
  (HasMeasurableSmul.measurable_const_smul c).comp hg

@[measurability, to_additive]
theorem Measurable.const_smul (hg : Measurable g) (c : M) : Measurable (c • g) :=
  hg.const_smul' c

@[measurability, to_additive]
theorem AeMeasurable.const_smul' (hg : AeMeasurable g μ) (c : M) : AeMeasurable (fun x => c • g x) μ :=
  (HasMeasurableSmul.measurable_const_smul c).comp_ae_measurable hg

@[measurability, to_additive]
theorem AeMeasurable.const_smul (hf : AeMeasurable g μ) (c : M) : AeMeasurable (c • g) μ :=
  hf.const_smul' c

omit m

@[to_additive]
instance Pi.has_measurable_smul {ι : Type _} {α : ι → Type _} [∀ i, HasSmul M (α i)] [∀ i, MeasurableSpace (α i)]
    [∀ i, HasMeasurableSmul M (α i)] : HasMeasurableSmul M (∀ i, α i) :=
  ⟨fun g => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_smul _, fun g =>
    measurable_pi_iff.mpr fun i => measurable_smul_const _⟩

/-- `add_monoid.has_smul_nat` is measurable. -/
instance AddMonoidₓ.has_measurable_smul_nat₂ (M : Type _) [AddMonoidₓ M] [MeasurableSpace M] [HasMeasurableAdd₂ M] :
    HasMeasurableSmul₂ ℕ M :=
  ⟨by
    suffices Measurable fun p : M × ℕ => p.2 • p.1 by
      apply this.comp measurable_swap
    refine' measurable_from_prod_encodable fun n => _
    induction' n with n ih
    · simp only [← zero_smul, Pi.zero_def, ← measurable_zero]
      
    · simp only [← succ_nsmul]
      exact measurable_id.add ih
      ⟩

/-- `sub_neg_monoid.has_smul_int` is measurable. -/
instance SubNegMonoidₓ.has_measurable_smul_int₂ (M : Type _) [SubNegMonoidₓ M] [MeasurableSpace M] [HasMeasurableAdd₂ M]
    [HasMeasurableNeg M] : HasMeasurableSmul₂ ℤ M :=
  ⟨by
    suffices Measurable fun p : M × ℤ => p.2 • p.1 by
      apply this.comp measurable_swap
    refine' measurable_from_prod_encodable fun n => _
    induction' n with n n ih
    · simp only [← of_nat_zsmul]
      exact measurable_const_smul _
      
    · simp only [← zsmul_neg_succ_of_nat]
      exact (measurable_const_smul _).neg
      ⟩

end Smul

section MulAction

variable {M β α : Type _} [MeasurableSpace M] [MeasurableSpace β] [Monoidₓ M] [MulAction M β] [HasMeasurableSmul M β]
  [MeasurableSpace α] {f : α → β} {μ : Measureₓ α}

variable {G : Type _} [Groupₓ G] [MeasurableSpace G] [MulAction G β] [HasMeasurableSmul G β]

@[to_additive]
theorem measurable_const_smul_iff (c : G) : (Measurable fun x => c • f x) ↔ Measurable f :=
  ⟨fun h => by
    simpa only [← inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩

@[to_additive]
theorem ae_measurable_const_smul_iff (c : G) : AeMeasurable (fun x => c • f x) μ ↔ AeMeasurable f μ :=
  ⟨fun h => by
    simpa only [← inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩

@[to_additive]
instance : MeasurableSpace Mˣ :=
  MeasurableSpace.comap (coe : Mˣ → M) ‹_›

@[to_additive]
instance Units.has_measurable_smul : HasMeasurableSmul Mˣ β where
  measurable_const_smul := fun c => (measurable_const_smul (c : M) : _)
  measurable_smul_const := fun x =>
    (measurable_smul_const x : Measurable fun c : M => c • x).comp MeasurableSpace.le_map_comap

@[to_additive]
theorem IsUnit.measurable_const_smul_iff {c : M} (hc : IsUnit c) : (Measurable fun x => c • f x) ↔ Measurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ measurable_const_smul_iff u

@[to_additive]
theorem IsUnit.ae_measurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AeMeasurable (fun x => c • f x) μ ↔ AeMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ ae_measurable_const_smul_iff u

variable {G₀ : Type _} [GroupWithZeroₓ G₀] [MeasurableSpace G₀] [MulAction G₀ β] [HasMeasurableSmul G₀ β]

theorem measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) : (Measurable fun x => c • f x) ↔ Measurable f :=
  (IsUnit.mk0 c hc).measurable_const_smul_iff

theorem ae_measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) : AeMeasurable (fun x => c • f x) μ ↔ AeMeasurable f μ :=
  (IsUnit.mk0 c hc).ae_measurable_const_smul_iff

end MulAction

/-!
### Opposite monoid
-/


section Opposite

open MulOpposite

@[to_additive]
instance {α : Type _} [h : MeasurableSpace α] : MeasurableSpace αᵐᵒᵖ :=
  MeasurableSpace.map op h

@[to_additive]
theorem measurable_mul_op {α : Type _} [MeasurableSpace α] : Measurable (op : α → αᵐᵒᵖ) := fun s => id

@[to_additive]
theorem measurable_mul_unop {α : Type _} [MeasurableSpace α] : Measurable (unop : αᵐᵒᵖ → α) := fun s => id

@[to_additive]
instance {M : Type _} [Mul M] [MeasurableSpace M] [HasMeasurableMul M] : HasMeasurableMul Mᵐᵒᵖ :=
  ⟨fun c => measurable_mul_op.comp (measurable_mul_unop.mul_const _), fun c =>
    measurable_mul_op.comp (measurable_mul_unop.const_mul _)⟩

@[to_additive]
instance {M : Type _} [Mul M] [MeasurableSpace M] [HasMeasurableMul₂ M] : HasMeasurableMul₂ Mᵐᵒᵖ :=
  ⟨measurable_mul_op.comp ((measurable_mul_unop.comp measurable_snd).mul (measurable_mul_unop.comp measurable_fst))⟩

/-- If a scalar is central, then its right action is measurable when its left action is. -/
instance HasMeasurableSmul.op {M α} [MeasurableSpace M] [MeasurableSpace α] [HasSmul M α] [HasSmul Mᵐᵒᵖ α]
    [IsCentralScalar M α] [HasMeasurableSmul M α] : HasMeasurableSmul Mᵐᵒᵖ α :=
  ⟨MulOpposite.rec fun c =>
      show Measurable fun x => op c • x by
        simpa only [← op_smul_eq_smul] using measurable_const_smul c,
    fun x =>
    show Measurable fun c => op (unop c) • x by
      simpa only [← op_smul_eq_smul] using (measurable_smul_const x).comp measurable_mul_unop⟩

/-- If a scalar is central, then its right action is measurable when its left action is. -/
instance HasMeasurableSmul₂.op {M α} [MeasurableSpace M] [MeasurableSpace α] [HasSmul M α] [HasSmul Mᵐᵒᵖ α]
    [IsCentralScalar M α] [HasMeasurableSmul₂ M α] : HasMeasurableSmul₂ Mᵐᵒᵖ α :=
  ⟨show Measurable fun x : Mᵐᵒᵖ × α => op (unop x.1) • x.2 by
      simp_rw [op_smul_eq_smul]
      refine' (measurable_mul_unop.comp measurable_fst).smul measurable_snd⟩

@[to_additive]
instance has_measurable_smul_opposite_of_mul {M : Type _} [Mul M] [MeasurableSpace M] [HasMeasurableMul M] :
    HasMeasurableSmul Mᵐᵒᵖ M :=
  ⟨fun c => measurable_mul_const (unop c), fun x => measurable_mul_unop.const_mul x⟩

@[to_additive]
instance has_measurable_smul₂_opposite_of_mul {M : Type _} [Mul M] [MeasurableSpace M] [HasMeasurableMul₂ M] :
    HasMeasurableSmul₂ Mᵐᵒᵖ M :=
  ⟨measurable_snd.mul (measurable_mul_unop.comp measurable_fst)⟩

end Opposite

/-!
### Big operators: `∏` and `∑`
-/


section Monoidₓ

variable {M α : Type _} [Monoidₓ M] [MeasurableSpace M] [HasMeasurableMul₂ M] {m : MeasurableSpace α} {μ : Measureₓ α}

include m

@[measurability, to_additive]
theorem List.measurable_prod' (l : List (α → M)) (hl : ∀, ∀ f ∈ l, ∀, Measurable f) : Measurable l.Prod := by
  induction' l with f l ihl
  · exact measurable_one
    
  rw [List.forall_mem_consₓ] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)

@[measurability, to_additive]
theorem List.ae_measurable_prod' (l : List (α → M)) (hl : ∀, ∀ f ∈ l, ∀, AeMeasurable f μ) : AeMeasurable l.Prod μ := by
  induction' l with f l ihl
  · exact ae_measurable_one
    
  rw [List.forall_mem_consₓ] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)

@[measurability, to_additive]
theorem List.measurable_prod (l : List (α → M)) (hl : ∀, ∀ f ∈ l, ∀, Measurable f) :
    Measurable fun x => (l.map fun f : α → M => f x).Prod := by
  simpa only [Pi.list_prod_apply] using l.measurable_prod' hl

@[measurability, to_additive]
theorem List.ae_measurable_prod (l : List (α → M)) (hl : ∀, ∀ f ∈ l, ∀, AeMeasurable f μ) :
    AeMeasurable (fun x => (l.map fun f : α → M => f x).Prod) μ := by
  simpa only [Pi.list_prod_apply] using l.ae_measurable_prod' hl

omit m

end Monoidₓ

section CommMonoidₓ

variable {M ι α : Type _} [CommMonoidₓ M] [MeasurableSpace M] [HasMeasurableMul₂ M] {m : MeasurableSpace α}
  {μ : Measureₓ α} {f : ι → α → M}

include m

@[measurability, to_additive]
theorem Multiset.measurable_prod' (l : Multiset (α → M)) (hl : ∀, ∀ f ∈ l, ∀, Measurable f) : Measurable l.Prod := by
  rcases l with ⟨l⟩
  simpa using
    l.measurable_prod'
      (by
        simpa using hl)

@[measurability, to_additive]
theorem Multiset.ae_measurable_prod' (l : Multiset (α → M)) (hl : ∀, ∀ f ∈ l, ∀, AeMeasurable f μ) :
    AeMeasurable l.Prod μ := by
  rcases l with ⟨l⟩
  simpa using
    l.ae_measurable_prod'
      (by
        simpa using hl)

@[measurability, to_additive]
theorem Multiset.measurable_prod (s : Multiset (α → M)) (hs : ∀, ∀ f ∈ s, ∀, Measurable f) :
    Measurable fun x => (s.map fun f : α → M => f x).Prod := by
  simpa only [Pi.multiset_prod_apply] using s.measurable_prod' hs

@[measurability, to_additive]
theorem Multiset.ae_measurable_prod (s : Multiset (α → M)) (hs : ∀, ∀ f ∈ s, ∀, AeMeasurable f μ) :
    AeMeasurable (fun x => (s.map fun f : α → M => f x).Prod) μ := by
  simpa only [Pi.multiset_prod_apply] using s.ae_measurable_prod' hs

@[measurability, to_additive]
theorem Finset.measurable_prod' (s : Finset ι) (hf : ∀, ∀ i ∈ s, ∀, Measurable (f i)) : Measurable (∏ i in s, f i) :=
  Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf

@[measurability, to_additive]
theorem Finset.measurable_prod (s : Finset ι) (hf : ∀, ∀ i ∈ s, ∀, Measurable (f i)) :
    Measurable fun a => ∏ i in s, f i a := by
  simpa only [Finset.prod_apply] using s.measurable_prod' hf

@[measurability, to_additive]
theorem Finset.ae_measurable_prod' (s : Finset ι) (hf : ∀, ∀ i ∈ s, ∀, AeMeasurable (f i) μ) :
    AeMeasurable (∏ i in s, f i) μ :=
  (Multiset.ae_measurable_prod' _) fun g hg =>
    let ⟨i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi

@[measurability, to_additive]
theorem Finset.ae_measurable_prod (s : Finset ι) (hf : ∀, ∀ i ∈ s, ∀, AeMeasurable (f i) μ) :
    AeMeasurable (fun a => ∏ i in s, f i a) μ := by
  simpa only [Finset.prod_apply] using s.ae_measurable_prod' hf

omit m

end CommMonoidₓ


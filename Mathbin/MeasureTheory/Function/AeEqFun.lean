/-
Copyright (c) 2019 Johannes Hölzl, Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Zhouhang Zhou
-/
import Mathbin.MeasureTheory.Integral.Lebesgue
import Mathbin.Order.Filter.Germ
import Mathbin.Topology.ContinuousFunction.Algebra
import Mathbin.MeasureTheory.Function.StronglyMeasurable

/-!

# Almost everywhere equal functions

We build a space of equivalence classes of functions, where two functions are treated as identical
if they are almost everywhere equal. We form the set of equivalence classes under the relation of
being almost everywhere equal, which is sometimes known as the `L⁰` space.
To use this space as a basis for the `L^p` spaces and for the Bochner integral, we consider
equivalence classes of strongly measurable functions (or, equivalently, of almost everywhere
strongly measurable functions.)

See `l1_space.lean` for `L¹` space.

## Notation

* `α →ₘ[μ] β` is the type of `L⁰` space, where `α` is a measurable space, `β` is a topological
  space, and `μ` is a measure on `α`. `f : α →ₘ β` is a "function" in `L⁰`.
  In comments, `[f]` is also used to denote an `L⁰` function.

  `ₘ` can be typed as `\_m`. Sometimes it is shown as a box if font is missing.

## Main statements

* The linear structure of `L⁰` :
    Addition and scalar multiplication are defined on `L⁰` in the natural way, i.e.,
    `[f] + [g] := [f + g]`, `c • [f] := [c • f]`. So defined, `α →ₘ β` inherits the linear structure
    of `β`. For example, if `β` is a module, then `α →ₘ β` is a module over the same ring.

    See `mk_add_mk`,  `neg_mk`,     `mk_sub_mk`,  `smul_mk`,
        `add_to_fun`, `neg_to_fun`, `sub_to_fun`, `smul_to_fun`

* The order structure of `L⁰` :
    `≤` can be defined in a similar way: `[f] ≤ [g]` if `f a ≤ g a` for almost all `a` in domain.
    And `α →ₘ β` inherits the preorder and partial order of `β`.

    TODO: Define `sup` and `inf` on `L⁰` so that it forms a lattice. It seems that `β` must be a
    linear order, since otherwise `f ⊔ g` may not be a measurable function.

## Implementation notes

* `f.to_fun`     : To find a representative of `f : α →ₘ β`, use the coercion `(f : α → β)`, which
                 is implemented as `f.to_fun`.
                 For each operation `op` in `L⁰`, there is a lemma called `coe_fn_op`,
                 characterizing, say, `(f op g : α → β)`.
* `ae_eq_fun.mk` : To constructs an `L⁰` function `α →ₘ β` from an almost everywhere strongly
                 measurable function `f : α → β`, use `ae_eq_fun.mk`
* `comp`         : Use `comp g f` to get `[g ∘ f]` from `g : β → γ` and `[f] : α →ₘ γ` when `g` is
                 continuous. Use `comp_measurable` if `g` is only measurable (this requires the
                 target space to be second countable).
* `comp₂`        : Use `comp₂ g f₁ f₂ to get `[λ a, g (f₁ a) (f₂ a)]`.
                 For example, `[f + g]` is `comp₂ (+)`


## Tags

function space, almost everywhere equal, `L⁰`, ae_eq_fun

-/


noncomputable section

open Classical Ennreal TopologicalSpace

open Set Filter TopologicalSpace Ennreal Emetric MeasureTheory Function

variable {α β γ δ : Type _} [MeasurableSpace α] {μ ν : Measureₓ α}

namespace MeasureTheory

section MeasurableSpace

variable [TopologicalSpace β]

variable (β)

/-- The equivalence relation of being almost everywhere equal for almost everywhere strongly
measurable functions. -/
def Measure.aeEqSetoid (μ : Measure α) : Setoidₓ { f : α → β // AeStronglyMeasurable f μ } :=
  ⟨fun f g => (f : α → β) =ᵐ[μ] g, fun f => ae_eq_refl f, fun f g => ae_eq_symm, fun f g h => ae_eq_trans⟩

variable (α)

/-- The space of equivalence classes of almost everywhere strongly measurable functions, where two
    strongly measurable functions are equivalent if they agree almost everywhere, i.e.,
    they differ on a set of measure `0`.  -/
def AeEqFun (μ : Measure α) : Type _ :=
  Quotientₓ (μ.aeEqSetoid β)

variable {α β}

-- mathport name: «expr →ₘ[ ] »
notation:25 α " →ₘ[" μ "] " β => AeEqFun α β μ

end MeasurableSpace

namespace AeEqFun

variable [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

/-- Construct the equivalence class `[f]` of an almost everywhere measurable function `f`, based
    on the equivalence relation of being almost everywhere equal. -/
def mk {β : Type _} [TopologicalSpace β] (f : α → β) (hf : AeStronglyMeasurable f μ) : α →ₘ[μ] β :=
  Quotientₓ.mk' ⟨f, hf⟩

/-- A measurable representative of an `ae_eq_fun` [f] -/
instance : CoeFun (α →ₘ[μ] β) fun _ => α → β :=
  ⟨fun f => AeStronglyMeasurable.mk _ (Quotientₓ.out' f : { f : α → β // AeStronglyMeasurable f μ }).2⟩

protected theorem strongly_measurable (f : α →ₘ[μ] β) : StronglyMeasurable f :=
  AeStronglyMeasurable.strongly_measurable_mk _

protected theorem ae_strongly_measurable (f : α →ₘ[μ] β) : AeStronglyMeasurable f μ :=
  f.StronglyMeasurable.AeStronglyMeasurable

protected theorem measurable [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] (f : α →ₘ[μ] β) :
    Measurable f :=
  AeStronglyMeasurable.measurable_mk _

protected theorem ae_measurable [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] (f : α →ₘ[μ] β) :
    AeMeasurable f μ :=
  f.Measurable.AeMeasurable

@[simp]
theorem quot_mk_eq_mk (f : α → β) (hf) : (Quot.mk (@Setoidₓ.R _ <| μ.aeEqSetoid β) ⟨f, hf⟩ : α →ₘ[μ] β) = mk f hf :=
  rfl

@[simp]
theorem mk_eq_mk {f g : α → β} {hf hg} : (mk f hf : α →ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g :=
  Quotientₓ.eq'

@[simp]
theorem mk_coe_fn (f : α →ₘ[μ] β) : mk f f.AeStronglyMeasurable = f := by
  conv_rhs => rw [← Quotientₓ.out_eq' f]
  set g : { f : α → β // ae_strongly_measurable f μ } := Quotientₓ.out' f with hg
  have : g = ⟨g.1, g.2⟩ := Subtype.eq rfl
  rw [this, ← mk, mk_eq_mk]
  exact (ae_strongly_measurable.ae_eq_mk _).symm

@[ext]
theorem ext {f g : α →ₘ[μ] β} (h : f =ᵐ[μ] g) : f = g := by
  rwa [← f.mk_coe_fn, ← g.mk_coe_fn, mk_eq_mk]

theorem ext_iff {f g : α →ₘ[μ] β} : f = g ↔ f =ᵐ[μ] g :=
  ⟨fun h => by
    rw [h], fun h => ext h⟩

theorem coe_fn_mk (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β) =ᵐ[μ] f := by
  apply (ae_strongly_measurable.ae_eq_mk _).symm.trans
  exact @Quotientₓ.mk_out' _ (μ.ae_eq_setoid β) (⟨f, hf⟩ : { f // ae_strongly_measurable f μ })

@[elab_as_eliminator]
theorem induction_on (f : α →ₘ[μ] β) {p : (α →ₘ[μ] β) → Prop} (H : ∀ f hf, p (mk f hf)) : p f :=
  Quotientₓ.induction_on' f <| Subtype.forall.2 H

@[elab_as_eliminator]
theorem induction_on₂ {α' β' : Type _} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'} (f : α →ₘ[μ] β)
    (f' : α' →ₘ[μ'] β') {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → Prop} (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) :
    p f f' :=
  (induction_on f) fun f hf => induction_on f' <| H f hf

@[elab_as_eliminator]
theorem induction_on₃ {α' β' : Type _} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'} {α'' β'' : Type _}
    [MeasurableSpace α''] [TopologicalSpace β''] {μ'' : Measure α''} (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β')
    (f'' : α'' →ₘ[μ''] β'') {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → (α'' →ₘ[μ''] β'') → Prop}
    (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) : p f f' f'' :=
  (induction_on f) fun f hf => induction_on₂ f' f'' <| H f hf

/-- Given a continuous function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
    return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
    `[g ∘ f] : α →ₘ γ`. -/
def comp (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
  (Quotientₓ.liftOn' f fun f => mk (g ∘ (f : α → β)) (hg.comp_ae_strongly_measurable f.2)) fun f f' H =>
    mk_eq_mk.2 <| H.fun_comp g

@[simp]
theorem comp_mk (g : β → γ) (hg : Continuous g) (f : α → β) (hf) :
    comp g hg (mk f hf : α →ₘ[μ] β) = mk (g ∘ f) (hg.comp_ae_strongly_measurable hf) :=
  rfl

theorem comp_eq_mk (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) :
    comp g hg f = mk (g ∘ f) (hg.comp_ae_strongly_measurable f.AeStronglyMeasurable) := by
  rw [← comp_mk g hg f f.ae_strongly_measurable, mk_coe_fn]

theorem coe_fn_comp (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f := by
  rw [comp_eq_mk]
  apply coe_fn_mk

section CompMeasurable

variable [MeasurableSpace β] [PseudoMetrizableSpace β] [BorelSpace β] [MeasurableSpace γ] [PseudoMetrizableSpace γ]
  [OpensMeasurableSpace γ] [SecondCountableTopology γ]

/-- Given a measurable function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
    return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
    `[g ∘ f] : α →ₘ γ`. This requires that `γ` has a second countable topology. -/
def compMeasurable (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
  (Quotientₓ.liftOn' f fun f' => mk (g ∘ (f' : α → β)) (hg.comp_ae_measurable f'.2.AeMeasurable).AeStronglyMeasurable)
    fun f f' H => mk_eq_mk.2 <| H.fun_comp g

@[simp]
theorem comp_measurable_mk (g : β → γ) (hg : Measurable g) (f : α → β) (hf : AeStronglyMeasurable f μ) :
    compMeasurable g hg (mk f hf : α →ₘ[μ] β) =
      mk (g ∘ f) (hg.comp_ae_measurable hf.AeMeasurable).AeStronglyMeasurable :=
  rfl

theorem comp_measurable_eq_mk (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    compMeasurable g hg f = mk (g ∘ f) (hg.comp_ae_measurable f.AeMeasurable).AeStronglyMeasurable := by
  rw [← comp_measurable_mk g hg f f.ae_strongly_measurable, mk_coe_fn]

theorem coe_fn_comp_measurable (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) : compMeasurable g hg f =ᵐ[μ] g ∘ f := by
  rw [comp_measurable_eq_mk]
  apply coe_fn_mk

end CompMeasurable

/-- The class of `x ↦ (f x, g x)`. -/
def pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : α →ₘ[μ] β × γ :=
  (Quotientₓ.liftOn₂' f g fun f g => mk (fun x => (f.1 x, g.1 x)) (f.2.prod_mk g.2)) fun f g f' g' Hf Hg =>
    mk_eq_mk.2 <| Hf.prod_mk Hg

@[simp]
theorem pair_mk_mk (f : α → β) (hf) (g : α → γ) (hg) :
    (mk f hf : α →ₘ[μ] β).pair (mk g hg) = mk (fun x => (f x, g x)) (hf.prod_mk hg) :=
  rfl

theorem pair_eq_mk (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) :
    f.pair g = mk (fun x => (f x, g x)) (f.AeStronglyMeasurable.prod_mk g.AeStronglyMeasurable) := by
  simp only [pair_mk_mk, ← mk_coe_fn]

theorem coe_fn_pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : f.pair g =ᵐ[μ] fun x => (f x, g x) := by
  rw [pair_eq_mk]
  apply coe_fn_mk

/-- Given a continuous function `g : β → γ → δ`, and almost everywhere equal functions
    `[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
    `λ a, g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
    `[λ a, g (f₁ a) (f₂ a)] : α →ₘ γ` -/
def comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) : α →ₘ[μ] δ :=
  comp _ hg (f₁.pair f₂)

@[simp]
theorem comp₂_mk_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α → β) (f₂ : α → γ) (hf₁ hf₂) :
    comp₂ g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a)) (hg.comp_ae_strongly_measurable (hf₁.prod_mk hf₂)) :=
  rfl

theorem comp₂_eq_pair (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    comp₂ g hg f₁ f₂ = comp _ hg (f₁.pair f₂) :=
  rfl

theorem comp₂_eq_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    comp₂ g hg f₁ f₂ =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_ae_strongly_measurable (f₁.AeStronglyMeasurable.prod_mk f₂.AeStronglyMeasurable)) :=
  by
  rw [comp₂_eq_pair, pair_eq_mk, comp_mk] <;> rfl

theorem coe_fn_comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    comp₂ g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) := by
  rw [comp₂_eq_mk]
  apply coe_fn_mk

section

variable [MeasurableSpace β] [PseudoMetrizableSpace β] [BorelSpace β] [SecondCountableTopology β] [MeasurableSpace γ]
  [PseudoMetrizableSpace γ] [BorelSpace γ] [SecondCountableTopology γ] [MeasurableSpace δ] [PseudoMetrizableSpace δ]
  [OpensMeasurableSpace δ] [SecondCountableTopology δ]

/-- Given a measurable function `g : β → γ → δ`, and almost everywhere equal functions
    `[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
    `λ a, g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
    `[λ a, g (f₁ a) (f₂ a)] : α →ₘ γ`. This requires `δ` to have second-countable topology. -/
def comp₂Measurable (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) : α →ₘ[μ] δ :=
  compMeasurable _ hg (f₁.pair f₂)

@[simp]
theorem comp₂_measurable_mk_mk (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α → β) (f₂ : α → γ) (hf₁ hf₂) :
    comp₂Measurable g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_ae_measurable (hf₁.AeMeasurable.prod_mk hf₂.AeMeasurable)).AeStronglyMeasurable :=
  rfl

theorem comp₂_measurable_eq_pair (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    comp₂Measurable g hg f₁ f₂ = compMeasurable _ hg (f₁.pair f₂) :=
  rfl

theorem comp₂_measurable_eq_mk (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    comp₂Measurable g hg f₁ f₂ =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_ae_measurable (f₁.AeMeasurable.prod_mk f₂.AeMeasurable)).AeStronglyMeasurable :=
  by
  rw [comp₂_measurable_eq_pair, pair_eq_mk, comp_measurable_mk] <;> rfl

theorem coe_fn_comp₂_measurable (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    comp₂Measurable g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) := by
  rw [comp₂_measurable_eq_mk]
  apply coe_fn_mk

end

/-- Interpret `f : α →ₘ[μ] β` as a germ at `μ.ae` forgetting that `f` is almost everywhere
    strongly measurable. -/
def toGerm (f : α →ₘ[μ] β) : Germ μ.ae β :=
  (Quotientₓ.liftOn' f fun f => ((f : α → β) : Germ μ.ae β)) fun f g H => Germ.coe_eq.2 H

@[simp]
theorem mk_to_germ (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β).toGerm = f :=
  rfl

theorem to_germ_eq (f : α →ₘ[μ] β) : f.toGerm = (f : α → β) := by
  rw [← mk_to_germ, mk_coe_fn]

theorem to_germ_injective : Injective (toGerm : (α →ₘ[μ] β) → Germ μ.ae β) := fun f g H =>
  ext <|
    Germ.coe_eq.1 <| by
      rwa [← to_germ_eq, ← to_germ_eq]

theorem comp_to_germ (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : (comp g hg f).toGerm = f.toGerm.map g :=
  (induction_on f) fun f hf => by
    simp

theorem comp_measurable_to_germ [MeasurableSpace β] [BorelSpace β] [PseudoMetrizableSpace β] [PseudoMetrizableSpace γ]
    [SecondCountableTopology γ] [MeasurableSpace γ] [OpensMeasurableSpace γ] (g : β → γ) (hg : Measurable g)
    (f : α →ₘ[μ] β) : (compMeasurable g hg f).toGerm = f.toGerm.map g :=
  (induction_on f) fun f hf => by
    simp

theorem comp₂_to_germ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    (comp₂ g hg f₁ f₂).toGerm = f₁.toGerm.map₂ g f₂.toGerm :=
  (induction_on₂ f₁ f₂) fun f₁ hf₁ f₂ hf₂ => by
    simp

theorem comp₂_measurable_to_germ [PseudoMetrizableSpace β] [SecondCountableTopology β] [MeasurableSpace β]
    [BorelSpace β] [PseudoMetrizableSpace γ] [SecondCountableTopology γ] [MeasurableSpace γ] [BorelSpace γ]
    [PseudoMetrizableSpace δ] [SecondCountableTopology δ] [MeasurableSpace δ] [OpensMeasurableSpace δ] (g : β → γ → δ)
    (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    (comp₂Measurable g hg f₁ f₂).toGerm = f₁.toGerm.map₂ g f₂.toGerm :=
  (induction_on₂ f₁ f₂) fun f₁ hf₁ f₂ hf₂ => by
    simp

/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
    for almost all `a` -/
def LiftPred (p : β → Prop) (f : α →ₘ[μ] β) : Prop :=
  f.toGerm.lift_pred p

/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
    `(f a, g a)` for almost all `a` -/
def LiftRel (r : β → γ → Prop) (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : Prop :=
  f.toGerm.LiftRel r g.toGerm

theorem lift_rel_mk_mk {r : β → γ → Prop} {f : α → β} {g : α → γ} {hf hg} :
    LiftRel r (mk f hf : α →ₘ[μ] β) (mk g hg) ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
  Iff.rfl

theorem lift_rel_iff_coe_fn {r : β → γ → Prop} {f : α →ₘ[μ] β} {g : α →ₘ[μ] γ} :
    LiftRel r f g ↔ ∀ᵐ a ∂μ, r (f a) (g a) := by
  rw [← lift_rel_mk_mk, mk_coe_fn, mk_coe_fn]

section Order

instance [Preorderₓ β] : Preorderₓ (α →ₘ[μ] β) :=
  Preorderₓ.lift toGerm

@[simp]
theorem mk_le_mk [Preorderₓ β] {f g : α → β} (hf hg) : (mk f hf : α →ₘ[μ] β) ≤ mk g hg ↔ f ≤ᵐ[μ] g :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_fn_le [Preorderₓ β] {f g : α →ₘ[μ] β} : (f : α → β) ≤ᵐ[μ] g ↔ f ≤ g :=
  lift_rel_iff_coe_fn.symm

instance [PartialOrderₓ β] : PartialOrderₓ (α →ₘ[μ] β) :=
  PartialOrderₓ.lift toGerm to_germ_injective

section Lattice

section Sup

variable [SemilatticeSup β] [HasContinuousSup β]

instance : HasSup (α →ₘ[μ] β) where sup := fun f g => AeEqFun.comp₂ (·⊔·) continuous_sup f g

theorem coe_fn_sup (f g : α →ₘ[μ] β) : ⇑(f⊔g) =ᵐ[μ] fun x => f x⊔g x :=
  coe_fn_comp₂ _ _ _ _

protected theorem le_sup_left (f g : α →ₘ[μ] β) : f ≤ f⊔g := by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_sup f g] with _ ha
  rw [ha]
  exact le_sup_left

protected theorem le_sup_right (f g : α →ₘ[μ] β) : g ≤ f⊔g := by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_sup f g] with _ ha
  rw [ha]
  exact le_sup_right

protected theorem sup_le (f g f' : α →ₘ[μ] β) (hf : f ≤ f') (hg : g ≤ f') : f⊔g ≤ f' := by
  rw [← coe_fn_le] at hf hg⊢
  filter_upwards [hf, hg, coe_fn_sup f g] with _ haf hag ha_sup
  rw [ha_sup]
  exact sup_le haf hag

end Sup

section Inf

variable [SemilatticeInf β] [HasContinuousInf β]

instance : HasInf (α →ₘ[μ] β) where inf := fun f g => AeEqFun.comp₂ (·⊓·) continuous_inf f g

theorem coe_fn_inf (f g : α →ₘ[μ] β) : ⇑(f⊓g) =ᵐ[μ] fun x => f x⊓g x :=
  coe_fn_comp₂ _ _ _ _

protected theorem inf_le_left (f g : α →ₘ[μ] β) : f⊓g ≤ f := by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_inf f g] with _ ha
  rw [ha]
  exact inf_le_left

protected theorem inf_le_right (f g : α →ₘ[μ] β) : f⊓g ≤ g := by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_inf f g] with _ ha
  rw [ha]
  exact inf_le_right

protected theorem le_inf (f' f g : α →ₘ[μ] β) (hf : f' ≤ f) (hg : f' ≤ g) : f' ≤ f⊓g := by
  rw [← coe_fn_le] at hf hg⊢
  filter_upwards [hf, hg, coe_fn_inf f g] with _ haf hag ha_inf
  rw [ha_inf]
  exact le_inf haf hag

end Inf

instance [Lattice β] [TopologicalLattice β] : Lattice (α →ₘ[μ] β) :=
  { AeEqFun.partialOrder with sup := HasSup.sup, le_sup_left := AeEqFun.le_sup_left,
    le_sup_right := AeEqFun.le_sup_right, sup_le := AeEqFun.sup_le, inf := HasInf.inf,
    inf_le_left := AeEqFun.inf_le_left, inf_le_right := AeEqFun.inf_le_right, le_inf := AeEqFun.le_inf }

end Lattice

end Order

variable (α)

/-- The equivalence class of a constant function: `[λ a:α, b]`, based on the equivalence relation of
    being almost everywhere equal -/
def const (b : β) : α →ₘ[μ] β :=
  mk (fun a : α => b) ae_strongly_measurable_const

theorem coe_fn_const (b : β) : (const α b : α →ₘ[μ] β) =ᵐ[μ] Function.const α b :=
  coe_fn_mk _ _

variable {α}

instance [Inhabited β] : Inhabited (α →ₘ[μ] β) :=
  ⟨const α default⟩

@[to_additive]
instance [One β] : One (α →ₘ[μ] β) :=
  ⟨const α 1⟩

@[to_additive]
theorem one_def [One β] : (1 : α →ₘ[μ] β) = mk (fun a : α => 1) ae_strongly_measurable_const :=
  rfl

@[to_additive]
theorem coe_fn_one [One β] : ⇑(1 : α →ₘ[μ] β) =ᵐ[μ] 1 :=
  coe_fn_const _ _

@[simp, to_additive]
theorem one_to_germ [One β] : (1 : α →ₘ[μ] β).toGerm = 1 :=
  rfl

-- Note we set up the scalar actions before the `monoid` structures in case we want to
-- try to override the `nsmul` or `zsmul` fields in future.
section HasSmul

variable {𝕜 𝕜' : Type _}

variable [HasSmul 𝕜 γ] [HasContinuousConstSmul 𝕜 γ]

variable [HasSmul 𝕜' γ] [HasContinuousConstSmul 𝕜' γ]

instance : HasSmul 𝕜 (α →ₘ[μ] γ) :=
  ⟨fun c f => comp ((· • ·) c) (continuous_id.const_smul c) f⟩

@[simp]
theorem smul_mk (c : 𝕜) (f : α → γ) (hf : AeStronglyMeasurable f μ) :
    c • (mk f hf : α →ₘ[μ] γ) = mk (c • f) (hf.const_smul _) :=
  rfl

theorem coe_fn_smul (c : 𝕜) (f : α →ₘ[μ] γ) : ⇑(c • f) =ᵐ[μ] c • f :=
  coe_fn_comp _ _ _

theorem smul_to_germ (c : 𝕜) (f : α →ₘ[μ] γ) : (c • f).toGerm = c • f.toGerm :=
  comp_to_germ _ _ _

instance [SmulCommClass 𝕜 𝕜' γ] : SmulCommClass 𝕜 𝕜' (α →ₘ[μ] γ) :=
  ⟨fun a b f =>
    (induction_on f) fun f hf => by
      simp_rw [smul_mk, smul_comm]⟩

instance [HasSmul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' γ] : IsScalarTower 𝕜 𝕜' (α →ₘ[μ] γ) :=
  ⟨fun a b f =>
    (induction_on f) fun f hf => by
      simp_rw [smul_mk, smul_assoc]⟩

instance [HasSmul 𝕜ᵐᵒᵖ γ] [IsCentralScalar 𝕜 γ] : IsCentralScalar 𝕜 (α →ₘ[μ] γ) :=
  ⟨fun a f =>
    (induction_on f) fun f hf => by
      simp_rw [smul_mk, op_smul_eq_smul]⟩

end HasSmul

section Mul

variable [Mul γ] [HasContinuousMul γ]

@[to_additive]
instance : Mul (α →ₘ[μ] γ) :=
  ⟨comp₂ (· * ·) continuous_mul⟩

@[simp, to_additive]
theorem mk_mul_mk (f g : α → γ) (hf : AeStronglyMeasurable f μ) (hg : AeStronglyMeasurable g μ) :
    (mk f hf : α →ₘ[μ] γ) * mk g hg = mk (f * g) (hf.mul hg) :=
  rfl

@[to_additive]
theorem coe_fn_mul (f g : α →ₘ[μ] γ) : ⇑(f * g) =ᵐ[μ] f * g :=
  coe_fn_comp₂ _ _ _ _

@[simp, to_additive]
theorem mul_to_germ (f g : α →ₘ[μ] γ) : (f * g).toGerm = f.toGerm * g.toGerm :=
  comp₂_to_germ _ _ _ _

end Mul

instance [AddMonoidₓ γ] [HasContinuousAdd γ] : AddMonoidₓ (α →ₘ[μ] γ) :=
  to_germ_injective.AddMonoid toGerm zero_to_germ add_to_germ fun _ _ => smul_to_germ _ _

instance [AddCommMonoidₓ γ] [HasContinuousAdd γ] : AddCommMonoidₓ (α →ₘ[μ] γ) :=
  to_germ_injective.AddCommMonoid toGerm zero_to_germ add_to_germ fun _ _ => smul_to_germ _ _

section Monoidₓ

variable [Monoidₓ γ] [HasContinuousMul γ]

instance : Pow (α →ₘ[μ] γ) ℕ :=
  ⟨fun f n => comp _ (continuous_pow n) f⟩

@[simp]
theorem mk_pow (f : α → γ) (hf) (n : ℕ) :
    (mk f hf : α →ₘ[μ] γ) ^ n = mk (f ^ n) ((continuous_pow n).comp_ae_strongly_measurable hf) :=
  rfl

theorem coe_fn_pow (f : α →ₘ[μ] γ) (n : ℕ) : ⇑(f ^ n) =ᵐ[μ] f ^ n :=
  coe_fn_comp _ _ _

@[simp]
theorem pow_to_germ (f : α →ₘ[μ] γ) (n : ℕ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_to_germ _ _ _

@[to_additive]
instance : Monoidₓ (α →ₘ[μ] γ) :=
  to_germ_injective.Monoid toGerm one_to_germ mul_to_germ pow_to_germ

/-- `ae_eq_fun.to_germ` as a `monoid_hom`. -/
@[to_additive "`ae_eq_fun.to_germ` as an `add_monoid_hom`.", simps]
def toGermMonoidHom : (α →ₘ[μ] γ) →* μ.ae.Germ γ where
  toFun := toGerm
  map_one' := one_to_germ
  map_mul' := mul_to_germ

end Monoidₓ

@[to_additive]
instance [CommMonoidₓ γ] [HasContinuousMul γ] : CommMonoidₓ (α →ₘ[μ] γ) :=
  to_germ_injective.CommMonoid toGerm one_to_germ mul_to_germ pow_to_germ

section Groupₓ

variable [Groupₓ γ] [TopologicalGroup γ]

section Inv

@[to_additive]
instance : Inv (α →ₘ[μ] γ) :=
  ⟨comp Inv.inv continuous_inv⟩

@[simp, to_additive]
theorem inv_mk (f : α → γ) (hf) : (mk f hf : α →ₘ[μ] γ)⁻¹ = mk f⁻¹ hf.inv :=
  rfl

@[to_additive]
theorem coe_fn_inv (f : α →ₘ[μ] γ) : ⇑f⁻¹ =ᵐ[μ] f⁻¹ :=
  coe_fn_comp _ _ _

@[to_additive]
theorem inv_to_germ (f : α →ₘ[μ] γ) : f⁻¹.toGerm = f.toGerm⁻¹ :=
  comp_to_germ _ _ _

end Inv

section Div

@[to_additive]
instance : Div (α →ₘ[μ] γ) :=
  ⟨comp₂ Div.div continuous_div'⟩

@[simp, to_additive]
theorem mk_div (f g : α → γ) (hf : AeStronglyMeasurable f μ) (hg : AeStronglyMeasurable g μ) :
    mk (f / g) (hf.div hg) = (mk f hf : α →ₘ[μ] γ) / mk g hg :=
  rfl

@[to_additive]
theorem coe_fn_div (f g : α →ₘ[μ] γ) : ⇑(f / g) =ᵐ[μ] f / g :=
  coe_fn_comp₂ _ _ _ _

@[to_additive]
theorem div_to_germ (f g : α →ₘ[μ] γ) : (f / g).toGerm = f.toGerm / g.toGerm :=
  comp₂_to_germ _ _ _ _

end Div

section Zpow

instance hasIntPow : Pow (α →ₘ[μ] γ) ℤ :=
  ⟨fun f n => comp _ (continuous_zpow n) f⟩

@[simp]
theorem mk_zpow (f : α → γ) (hf) (n : ℤ) :
    (mk f hf : α →ₘ[μ] γ) ^ n = mk (f ^ n) ((continuous_zpow n).comp_ae_strongly_measurable hf) :=
  rfl

theorem coe_fn_zpow (f : α →ₘ[μ] γ) (n : ℤ) : ⇑(f ^ n) =ᵐ[μ] f ^ n :=
  coe_fn_comp _ _ _

@[simp]
theorem zpow_to_germ (f : α →ₘ[μ] γ) (n : ℤ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_to_germ _ _ _

end Zpow

end Groupₓ

instance [AddGroupₓ γ] [TopologicalAddGroup γ] : AddGroupₓ (α →ₘ[μ] γ) :=
  to_germ_injective.AddGroup toGerm zero_to_germ add_to_germ neg_to_germ sub_to_germ (fun _ _ => smul_to_germ _ _)
    fun _ _ => smul_to_germ _ _

instance [AddCommGroupₓ γ] [TopologicalAddGroup γ] : AddCommGroupₓ (α →ₘ[μ] γ) :=
  to_germ_injective.AddCommGroup toGerm zero_to_germ add_to_germ neg_to_germ sub_to_germ (fun _ _ => smul_to_germ _ _)
    fun _ _ => smul_to_germ _ _

@[to_additive]
instance [Groupₓ γ] [TopologicalGroup γ] : Groupₓ (α →ₘ[μ] γ) :=
  to_germ_injective.Group _ one_to_germ mul_to_germ inv_to_germ div_to_germ pow_to_germ zpow_to_germ

@[to_additive]
instance [CommGroupₓ γ] [TopologicalGroup γ] : CommGroupₓ (α →ₘ[μ] γ) :=
  to_germ_injective.CommGroup _ one_to_germ mul_to_germ inv_to_germ div_to_germ pow_to_germ zpow_to_germ

section Module

variable {𝕜 : Type _}

instance [Monoidₓ 𝕜] [MulAction 𝕜 γ] [HasContinuousConstSmul 𝕜 γ] : MulAction 𝕜 (α →ₘ[μ] γ) :=
  to_germ_injective.MulAction toGerm smul_to_germ

instance [Monoidₓ 𝕜] [AddMonoidₓ γ] [HasContinuousAdd γ] [DistribMulAction 𝕜 γ] [HasContinuousConstSmul 𝕜 γ] :
    DistribMulAction 𝕜 (α →ₘ[μ] γ) :=
  to_germ_injective.DistribMulAction (toGermAddMonoidHom : (α →ₘ[μ] γ) →+ _) fun c : 𝕜 => smul_to_germ c

instance [Semiringₓ 𝕜] [AddCommMonoidₓ γ] [HasContinuousAdd γ] [Module 𝕜 γ] [HasContinuousConstSmul 𝕜 γ] :
    Module 𝕜 (α →ₘ[μ] γ) :=
  to_germ_injective.Module 𝕜 (toGermAddMonoidHom : (α →ₘ[μ] γ) →+ _) smul_to_germ

end Module

open Ennreal

/-- For `f : α → ℝ≥0∞`, define `∫ [f]` to be `∫ f` -/
def lintegral (f : α →ₘ[μ] ℝ≥0∞) : ℝ≥0∞ :=
  Quotientₓ.liftOn' f (fun f => ∫⁻ a, (f : α → ℝ≥0∞) a ∂μ) fun f g => lintegral_congr_ae

@[simp]
theorem lintegral_mk (f : α → ℝ≥0∞) (hf) : (mk f hf : α →ₘ[μ] ℝ≥0∞).lintegral = ∫⁻ a, f a ∂μ :=
  rfl

theorem lintegral_coe_fn (f : α →ₘ[μ] ℝ≥0∞) : (∫⁻ a, f a ∂μ) = f.lintegral := by
  rw [← lintegral_mk, mk_coe_fn]

@[simp]
theorem lintegral_zero : lintegral (0 : α →ₘ[μ] ℝ≥0∞) = 0 :=
  lintegral_zero

@[simp]
theorem lintegral_eq_zero_iff {f : α →ₘ[μ] ℝ≥0∞} : lintegral f = 0 ↔ f = 0 :=
  (induction_on f) fun f hf => (lintegral_eq_zero_iff' hf.AeMeasurable).trans mk_eq_mk.symm

theorem lintegral_add (f g : α →ₘ[μ] ℝ≥0∞) : lintegral (f + g) = lintegral f + lintegral g :=
  (induction_on₂ f g) fun f hf g hg => by
    simp [← lintegral_add_left' hf.ae_measurable]

theorem lintegral_mono {f g : α →ₘ[μ] ℝ≥0∞} : f ≤ g → lintegral f ≤ lintegral g :=
  (induction_on₂ f g) fun f hf g hg hfg => lintegral_mono_ae hfg

section Abs

theorem coe_fn_abs {β} [TopologicalSpace β] [Lattice β] [TopologicalLattice β] [AddGroupₓ β] [TopologicalAddGroup β]
    (f : α →ₘ[μ] β) : ⇑(abs f) =ᵐ[μ] fun x => abs (f x) := by
  simp_rw [abs_eq_sup_neg]
  filter_upwards [ae_eq_fun.coe_fn_sup f (-f), ae_eq_fun.coe_fn_neg f] with x hx_sup hx_neg
  rw [hx_sup, hx_neg, Pi.neg_apply]

end Abs

section PosPart

variable [LinearOrderₓ γ] [OrderClosedTopology γ] [Zero γ]

/-- Positive part of an `ae_eq_fun`. -/
def posPart (f : α →ₘ[μ] γ) : α →ₘ[μ] γ :=
  comp (fun x => max x 0) (continuous_id.max continuous_const) f

@[simp]
theorem pos_part_mk (f : α → γ) (hf) :
    posPart (mk f hf : α →ₘ[μ] γ) =
      mk (fun x => max (f x) 0) ((continuous_id.max continuous_const).comp_ae_strongly_measurable hf) :=
  rfl

theorem coe_fn_pos_part (f : α →ₘ[μ] γ) : ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0 :=
  coe_fn_comp _ _ _

end PosPart

end AeEqFun

end MeasureTheory

namespace ContinuousMap

open MeasureTheory

variable [TopologicalSpace α] [BorelSpace α] (μ)

variable [TopologicalSpace β] [SecondCountableTopologyEither α β] [PseudoMetrizableSpace β]

/-- The equivalence class of `μ`-almost-everywhere measurable functions associated to a continuous
map. -/
def toAeEqFun (f : C(α, β)) : α →ₘ[μ] β :=
  AeEqFun.mk f f.Continuous.AeStronglyMeasurable

theorem coe_fn_to_ae_eq_fun (f : C(α, β)) : f.toAeEqFun μ =ᵐ[μ] f :=
  AeEqFun.coe_fn_mk f _

variable [Groupₓ β] [TopologicalGroup β]

/-- The `mul_hom` from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
@[to_additive
      "The `add_hom` from the group of continuous maps from `α` to `β` to the group of\nequivalence classes of `μ`-almost-everywhere measurable functions."]
def toAeEqFunMulHom : C(α, β) →* α →ₘ[μ] β where
  toFun := ContinuousMap.toAeEqFun μ
  map_one' := rfl
  map_mul' := fun f g => AeEqFun.mk_mul_mk _ _ f.Continuous.AeStronglyMeasurable g.Continuous.AeStronglyMeasurable

variable {𝕜 : Type _} [Semiringₓ 𝕜]

variable [TopologicalSpace γ] [PseudoMetrizableSpace γ] [AddCommGroupₓ γ] [Module 𝕜 γ] [TopologicalAddGroup γ]
  [HasContinuousConstSmul 𝕜 γ] [SecondCountableTopologyEither α γ]

/-- The linear map from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
def toAeEqFunLinearMap : C(α, γ) →ₗ[𝕜] α →ₘ[μ] γ :=
  { toAeEqFunAddHom μ with map_smul' := fun c f => AeEqFun.smul_mk c f f.Continuous.AeStronglyMeasurable }

end ContinuousMap


/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.MeasureTheory.Measure.AeMeasurable

/-!
# Typeclasses for measurability of lattice operations

In this file we define classes `has_measurable_sup` and `has_measurable_inf` and prove dot-style
lemmas (`measurable.sup`, `ae_measurable.sup` etc). For binary operations we define two typeclasses:

- `has_measurable_sup` says that both left and right sup are measurable;
- `has_measurable_sup₂` says that `λ p : α × α, p.1 ⊔ p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `has_measurable_sup₂`
etc require `α` to have a second countable topology.

For instances relating, e.g., `has_continuous_sup` to `has_measurable_sup` see file
`measure_theory.borel_space`.

## Tags

measurable function, lattice operation

-/


open MeasureTheory

/-- We say that a type `has_measurable_sup` if `((⊔) c)` and `(⊔ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (⊔)` see `has_measurable_sup₂`. -/
class HasMeasurableSup (M : Type _) [MeasurableSpace M] [HasSup M] : Prop where
  measurable_const_sup : ∀ c : M, Measurable ((·⊔·) c)
  measurable_sup_const : ∀ c : M, Measurable (·⊔c)

/-- We say that a type `has_measurable_sup₂` if `uncurry (⊔)` is a measurable functions.
For a typeclass assuming measurability of `((⊔) c)` and `(⊔ c)` see `has_measurable_sup`. -/
class HasMeasurableSup₂ (M : Type _) [MeasurableSpace M] [HasSup M] : Prop where
  measurable_sup : Measurable fun p : M × M => p.1⊔p.2

export HasMeasurableSup₂ (measurable_sup)

export HasMeasurableSup (measurable_const_sup measurable_sup_const)

/-- We say that a type `has_measurable_inf` if `((⊓) c)` and `(⊓ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (⊓)` see `has_measurable_inf₂`. -/
class HasMeasurableInf (M : Type _) [MeasurableSpace M] [HasInf M] : Prop where
  measurable_const_inf : ∀ c : M, Measurable ((·⊓·) c)
  measurable_inf_const : ∀ c : M, Measurable (·⊓c)

/-- We say that a type `has_measurable_inf₂` if `uncurry (⊔)` is a measurable functions.
For a typeclass assuming measurability of `((⊔) c)` and `(⊔ c)` see `has_measurable_inf`. -/
class HasMeasurableInf₂ (M : Type _) [MeasurableSpace M] [HasInf M] : Prop where
  measurable_inf : Measurable fun p : M × M => p.1⊓p.2

export HasMeasurableInf₂ (measurable_inf)

export HasMeasurableInf (measurable_const_inf measurable_inf_const)

variable {M : Type _} [MeasurableSpace M]

section OrderDual

instance (priority := 100) [HasInf M] [HasMeasurableInf M] : HasMeasurableSup Mᵒᵈ :=
  ⟨@measurable_const_inf M _ _ _, @measurable_inf_const M _ _ _⟩

instance (priority := 100) [HasSup M] [HasMeasurableSup M] : HasMeasurableInf Mᵒᵈ :=
  ⟨@measurable_const_sup M _ _ _, @measurable_sup_const M _ _ _⟩

instance (priority := 100) [HasInf M] [HasMeasurableInf₂ M] : HasMeasurableSup₂ Mᵒᵈ :=
  ⟨@measurable_inf M _ _ _⟩

instance (priority := 100) [HasSup M] [HasMeasurableSup₂ M] : HasMeasurableInf₂ Mᵒᵈ :=
  ⟨@measurable_sup M _ _ _⟩

end OrderDual

variable {α : Type _} {m : MeasurableSpace α} {μ : Measureₓ α} {f g : α → M}

include m

section Sup

variable [HasSup M]

section MeasurableSup

variable [HasMeasurableSup M]

@[measurability]
theorem Measurable.const_sup (hf : Measurable f) (c : M) : Measurable fun x => c⊔f x :=
  (measurable_const_sup c).comp hf

@[measurability]
theorem AeMeasurable.const_sup (hf : AeMeasurable f μ) (c : M) : AeMeasurable (fun x => c⊔f x) μ :=
  (HasMeasurableSup.measurable_const_sup c).comp_ae_measurable hf

@[measurability]
theorem Measurable.sup_const (hf : Measurable f) (c : M) : Measurable fun x => f x⊔c :=
  (measurable_sup_const c).comp hf

@[measurability]
theorem AeMeasurable.sup_const (hf : AeMeasurable f μ) (c : M) : AeMeasurable (fun x => f x⊔c) μ :=
  (measurable_sup_const c).comp_ae_measurable hf

end MeasurableSup

section MeasurableSup₂

variable [HasMeasurableSup₂ M]

@[measurability]
theorem Measurable.sup' (hf : Measurable f) (hg : Measurable g) : Measurable (f⊔g) :=
  measurable_sup.comp (hf.prod_mk hg)

@[measurability]
theorem Measurable.sup (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a⊔g a :=
  measurable_sup.comp (hf.prod_mk hg)

@[measurability]
theorem AeMeasurable.sup' (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) : AeMeasurable (f⊔g) μ :=
  measurable_sup.comp_ae_measurable (hf.prod_mk hg)

@[measurability]
theorem AeMeasurable.sup (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) : AeMeasurable (fun a => f a⊔g a) μ :=
  measurable_sup.comp_ae_measurable (hf.prod_mk hg)

omit m

instance (priority := 100) HasMeasurableSup₂.to_has_measurable_sup : HasMeasurableSup M :=
  ⟨fun c => measurable_const.sup measurable_id, fun c => measurable_id.sup measurable_const⟩

include m

end MeasurableSup₂

end Sup

section Inf

variable [HasInf M]

section MeasurableInf

variable [HasMeasurableInf M]

@[measurability]
theorem Measurable.const_inf (hf : Measurable f) (c : M) : Measurable fun x => c⊓f x :=
  (measurable_const_inf c).comp hf

@[measurability]
theorem AeMeasurable.const_inf (hf : AeMeasurable f μ) (c : M) : AeMeasurable (fun x => c⊓f x) μ :=
  (HasMeasurableInf.measurable_const_inf c).comp_ae_measurable hf

@[measurability]
theorem Measurable.inf_const (hf : Measurable f) (c : M) : Measurable fun x => f x⊓c :=
  (measurable_inf_const c).comp hf

@[measurability]
theorem AeMeasurable.inf_const (hf : AeMeasurable f μ) (c : M) : AeMeasurable (fun x => f x⊓c) μ :=
  (measurable_inf_const c).comp_ae_measurable hf

end MeasurableInf

section MeasurableInf₂

variable [HasMeasurableInf₂ M]

@[measurability]
theorem Measurable.inf' (hf : Measurable f) (hg : Measurable g) : Measurable (f⊓g) :=
  measurable_inf.comp (hf.prod_mk hg)

@[measurability]
theorem Measurable.inf (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a⊓g a :=
  measurable_inf.comp (hf.prod_mk hg)

@[measurability]
theorem AeMeasurable.inf' (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) : AeMeasurable (f⊓g) μ :=
  measurable_inf.comp_ae_measurable (hf.prod_mk hg)

@[measurability]
theorem AeMeasurable.inf (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) : AeMeasurable (fun a => f a⊓g a) μ :=
  measurable_inf.comp_ae_measurable (hf.prod_mk hg)

omit m

instance (priority := 100) HasMeasurableInf₂.to_has_measurable_inf : HasMeasurableInf M :=
  ⟨fun c => measurable_const.inf measurable_id, fun c => measurable_id.inf measurable_const⟩

include m

end MeasurableInf₂

end Inf

section SemilatticeSup

open Finset

variable {δ : Type _} [MeasurableSpace δ] [SemilatticeSup α] [HasMeasurableSup₂ α]

@[measurability]
theorem Finset.measurable_sup' {ι : Type _} {s : Finset ι} (hs : s.Nonempty) {f : ι → δ → α}
    (hf : ∀, ∀ n ∈ s, ∀, Measurable (f n)) : Measurable (s.sup' hs f) :=
  Finset.sup'_induction hs _ (fun f hf g hg => hf.sup hg) fun n hn => hf n hn

@[measurability]
theorem Finset.measurable_range_sup' {f : ℕ → δ → α} {n : ℕ} (hf : ∀, ∀ k ≤ n, ∀, Measurable (f k)) :
    Measurable ((range (n + 1)).sup' nonempty_range_succ f) := by
  simp_rw [← Nat.lt_succ_iffₓ] at hf
  refine' Finset.measurable_sup' _ _
  simpa [← Finset.mem_range]

@[measurability]
theorem Finset.measurable_range_sup'' {f : ℕ → δ → α} {n : ℕ} (hf : ∀, ∀ k ≤ n, ∀, Measurable (f k)) :
    Measurable fun x => (range (n + 1)).sup' nonempty_range_succ fun k => f k x := by
  convert Finset.measurable_range_sup' hf
  ext x
  simp

end SemilatticeSup


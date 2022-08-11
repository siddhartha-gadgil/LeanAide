/-
Copyright © 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Shing Tak Lam
-/
import Mathbin.Topology.Algebra.Order.ProjIcc
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Bundled continuous maps into orders, with order-compatible topology

-/


variable {α : Type _} {β : Type _} {γ : Type _}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace ContinuousMap

section

variable [LinearOrderedAddCommGroup β] [OrderTopology β]

/-- The pointwise absolute value of a continuous function as a continuous function. -/
def abs (f : C(α, β)) : C(α, β) where toFun := fun x => abs (f x)

-- see Note [lower instance priority]
instance (priority := 100) : HasAbs C(α, β) :=
  ⟨fun f => abs f⟩

@[simp]
theorem abs_apply (f : C(α, β)) (x : α) : (abs f) x = abs (f x) :=
  rfl

end

/-!
We now set up the partial order and lattice structure (given by pointwise min and max)
on continuous functions.
-/


section Lattice

instance partialOrder [PartialOrderₓ β] : PartialOrderₓ C(α, β) :=
  PartialOrderₓ.lift (fun f => f.toFun)
    (by
      tidy)

theorem le_def [PartialOrderₓ β] {f g : C(α, β)} : f ≤ g ↔ ∀ a, f a ≤ g a :=
  Pi.le_def

theorem lt_def [PartialOrderₓ β] {f g : C(α, β)} : f < g ↔ (∀ a, f a ≤ g a) ∧ ∃ a, f a < g a :=
  Pi.lt_def

instance hasSup [LinearOrderₓ β] [OrderClosedTopology β] :
    HasSup C(α, β) where sup := fun f g => { toFun := fun a => max (f a) (g a) }

@[simp, norm_cast]
theorem sup_coe [LinearOrderₓ β] [OrderClosedTopology β] (f g : C(α, β)) : ((f⊔g : C(α, β)) : α → β) = (f⊔g : α → β) :=
  rfl

@[simp]
theorem sup_apply [LinearOrderₓ β] [OrderClosedTopology β] (f g : C(α, β)) (a : α) : (f⊔g) a = max (f a) (g a) :=
  rfl

instance [LinearOrderₓ β] [OrderClosedTopology β] : SemilatticeSup C(α, β) :=
  { ContinuousMap.partialOrder, ContinuousMap.hasSup with
    le_sup_left := fun f g =>
      le_def.mpr
        (by
          simp [← le_reflₓ]),
    le_sup_right := fun f g =>
      le_def.mpr
        (by
          simp [← le_reflₓ]),
    sup_le := fun f₁ f₂ g w₁ w₂ =>
      le_def.mpr fun a => by
        simp [← le_def.mp w₁ a, ← le_def.mp w₂ a] }

instance hasInf [LinearOrderₓ β] [OrderClosedTopology β] :
    HasInf C(α, β) where inf := fun f g => { toFun := fun a => min (f a) (g a) }

@[simp, norm_cast]
theorem inf_coe [LinearOrderₓ β] [OrderClosedTopology β] (f g : C(α, β)) : ((f⊓g : C(α, β)) : α → β) = (f⊓g : α → β) :=
  rfl

@[simp]
theorem inf_apply [LinearOrderₓ β] [OrderClosedTopology β] (f g : C(α, β)) (a : α) : (f⊓g) a = min (f a) (g a) :=
  rfl

instance [LinearOrderₓ β] [OrderClosedTopology β] : SemilatticeInf C(α, β) :=
  { ContinuousMap.partialOrder, ContinuousMap.hasInf with
    inf_le_left := fun f g =>
      le_def.mpr
        (by
          simp [← le_reflₓ]),
    inf_le_right := fun f g =>
      le_def.mpr
        (by
          simp [← le_reflₓ]),
    le_inf := fun f₁ f₂ g w₁ w₂ =>
      le_def.mpr fun a => by
        simp [← le_def.mp w₁ a, ← le_def.mp w₂ a] }

instance [LinearOrderₓ β] [OrderClosedTopology β] : Lattice C(α, β) :=
  { ContinuousMap.semilatticeInf, ContinuousMap.semilatticeSup with }

-- TODO transfer this lattice structure to `bounded_continuous_function`
section Sup'

variable [LinearOrderₓ γ] [OrderClosedTopology γ]

theorem sup'_apply {ι : Type _} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) (b : β) :
    s.sup' H f b = s.sup' H fun a => f a b :=
  Finset.comp_sup'_eq_sup'_comp H (fun f : C(β, γ) => f b) fun i j => rfl

@[simp, norm_cast]
theorem sup'_coe {ι : Type _} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) :
    ((s.sup' H f : C(β, γ)) : ι → β) = s.sup' H fun a => (f a : β → γ) := by
  ext
  simp [← sup'_apply]

end Sup'

section Inf'

variable [LinearOrderₓ γ] [OrderClosedTopology γ]

theorem inf'_apply {ι : Type _} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) (b : β) :
    s.inf' H f b = s.inf' H fun a => f a b :=
  @sup'_apply _ γᵒᵈ _ _ _ _ _ _ H f b

@[simp, norm_cast]
theorem inf'_coe {ι : Type _} {s : Finset ι} (H : s.Nonempty) (f : ι → C(β, γ)) :
    ((s.inf' H f : C(β, γ)) : ι → β) = s.inf' H fun a => (f a : β → γ) :=
  @sup'_coe _ γᵒᵈ _ _ _ _ _ _ H f

end Inf'

end Lattice

section Extend

variable [LinearOrderₓ α] [OrderTopology α] {a b : α} (h : a ≤ b)

/-- Extend a continuous function `f : C(set.Icc a b, β)` to a function `f : C(α, β)`.
-/
def iccExtend (f : C(Set.Icc a b, β)) : C(α, β) :=
  ⟨Set.iccExtend h f⟩

@[simp]
theorem coe_Icc_extend (f : C(Set.Icc a b, β)) : ((iccExtend h f : C(α, β)) : α → β) = Set.iccExtend h f :=
  rfl

end Extend

end ContinuousMap


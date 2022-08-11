/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathbin.Topology.Homotopy.Basic
import Mathbin.Topology.PathConnected
import Mathbin.Analysis.Convex.Basic

/-!
# Homotopy between paths

In this file, we define a `homotopy` between two `path`s. In addition, we define a relation
`homotopic` on `path`s, and prove that it is an equivalence relation.

## Definitions

* `path.homotopy p₀ p₁` is the type of homotopies between paths `p₀` and `p₁`
* `path.homotopy.refl p` is the constant homotopy between `p` and itself
* `path.homotopy.symm F` is the `path.homotopy p₁ p₀` defined by reversing the homotopy
* `path.homotopy.trans F G`, where `F : path.homotopy p₀ p₁`, `G : path.homotopy p₁ p₂` is the
  `path.homotopy p₀ p₂` defined by putting the first homotopy on `[0, 1/2]` and the second on
  `[1/2, 1]`
* `path.homotopy.hcomp F G`, where `F : path.homotopy p₀ q₀` and `G : path.homotopy p₁ q₁` is
  a `path.homotopy (p₀.trans p₁) (q₀.trans q₁)`
* `path.homotopic p₀ p₁` is the relation saying that there is a homotopy between `p₀` and `p₁`
* `path.homotopic.setoid x₀ x₁` is the setoid on `path`s from `path.homotopic`
* `path.homotopic.quotient x₀ x₁` is the quotient type from `path x₀ x₀` by `path.homotopic.setoid`

-/


universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

variable {x₀ x₁ x₂ x₃ : X}

noncomputable section

open UnitInterval

namespace Path

/-- The type of homotopies between two paths.
-/
abbrev Homotopy (p₀ p₁ : Path x₀ x₁) :=
  ContinuousMap.HomotopyRel p₀.toContinuousMap p₁.toContinuousMap {0, 1}

namespace Homotopy

section

variable {p₀ p₁ : Path x₀ x₁}

instance : CoeFun (Homotopy p₀ p₁) fun _ => I × I → X :=
  ⟨fun F => F.toFun⟩

theorem coe_fn_injective : @Function.Injective (Homotopy p₀ p₁) (I × I → X) coeFn :=
  ContinuousMap.HomotopyWith.coe_fn_injective

@[simp]
theorem source (F : Homotopy p₀ p₁) (t : I) : F (t, 0) = x₀ := by
  simp_rw [← p₀.source]
  apply ContinuousMap.HomotopyRel.eq_fst
  simp

@[simp]
theorem target (F : Homotopy p₀ p₁) (t : I) : F (t, 1) = x₁ := by
  simp_rw [← p₁.target]
  apply ContinuousMap.HomotopyRel.eq_snd
  simp

/-- Evaluating a path homotopy at an intermediate point, giving us a `path`.
-/
def eval (F : Homotopy p₀ p₁) (t : I) : Path x₀ x₁ where
  toFun := F.toHomotopy.curry t
  source' := by
    simp
  target' := by
    simp

@[simp]
theorem eval_zero (F : Homotopy p₀ p₁) : F.eval 0 = p₀ := by
  ext t
  simp [← eval]

@[simp]
theorem eval_one (F : Homotopy p₀ p₁) : F.eval 1 = p₁ := by
  ext t
  simp [← eval]

end

section

variable {p₀ p₁ p₂ : Path x₀ x₁}

/-- Given a path `p`, we can define a `homotopy p p` by `F (t, x) = p x`
-/
@[simps]
def refl (p : Path x₀ x₁) : Homotopy p p :=
  ContinuousMap.HomotopyRel.refl p.toContinuousMap {0, 1}

/-- Given a `homotopy p₀ p₁`, we can define a `homotopy p₁ p₀` by reversing the homotopy.
-/
@[simps]
def symm (F : Homotopy p₀ p₁) : Homotopy p₁ p₀ :=
  ContinuousMap.HomotopyRel.symm F

@[simp]
theorem symm_symm (F : Homotopy p₀ p₁) : F.symm.symm = F :=
  ContinuousMap.HomotopyRel.symm_symm F

/-- Given `homotopy p₀ p₁` and `homotopy p₁ p₂`, we can define a `homotopy p₀ p₂` by putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) : Homotopy p₀ p₂ :=
  ContinuousMap.HomotopyRel.trans F G

theorem trans_apply (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) (x : I × I) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then F (⟨2 * x.1, (UnitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else G (⟨2 * x.1 - 1, UnitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_leₓ.1 h).le, x.1.2.2⟩⟩, x.2) :=
  ContinuousMap.HomotopyRel.trans_apply _ _ _

theorem symm_trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) : (F.trans G).symm = G.symm.trans F.symm :=
  ContinuousMap.HomotopyRel.symm_trans _ _

/-- Casting a `homotopy p₀ p₁` to a `homotopy q₀ q₁` where `p₀ = q₀` and `p₁ = q₁`.
-/
@[simps]
def cast {p₀ p₁ q₀ q₁ : Path x₀ x₁} (F : Homotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : p₁ = q₁) : Homotopy q₀ q₁ :=
  ContinuousMap.HomotopyRel.cast F (congr_arg _ h₀) (congr_arg _ h₁)

end

section

variable {p₀ q₀ : Path x₀ x₁} {p₁ q₁ : Path x₁ x₂}

/-- Suppose `p₀` and `q₀` are paths from `x₀` to `x₁`, `p₁` and `q₁` are paths from `x₁` to `x₂`.
Furthermore, suppose `F : homotopy p₀ q₀` and `G : homotopy p₁ q₁`. Then we can define a homotopy
from `p₀.trans p₁` to `q₀.trans q₁`.
-/
def hcomp (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) : Homotopy (p₀.trans p₁) (q₀.trans q₁) where
  toFun := fun x => if (x.2 : ℝ) ≤ 1 / 2 then (F.eval x.1).extend (2 * x.2) else (G.eval x.1).extend (2 * x.2 - 1)
  continuous_to_fun := by
    refine'
      continuous_if_le (continuous_induced_dom.comp continuous_snd) continuous_const
        (F.to_homotopy.continuous.comp
            (by
              continuity)).ContinuousOn
        (G.to_homotopy.continuous.comp
            (by
              continuity)).ContinuousOn
        _
    intro x hx
    norm_num [← hx]
  map_zero_left' := fun x => by
    norm_num [← Path.trans]
  map_one_left' := fun x => by
    norm_num [← Path.trans]
  prop' := by
    rintro x t ht
    cases ht
    · rw [ht]
      simp
      
    · rw [Set.mem_singleton_iff] at ht
      rw [ht]
      norm_num
      

theorem hcomp_apply (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (x : I × I) :
    F.hcomp G x =
      if h : (x.2 : ℝ) ≤ 1 / 2 then F.eval x.1 ⟨2 * x.2, (UnitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.2.2.1, h⟩⟩
      else G.eval x.1 ⟨2 * x.2 - 1, UnitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_leₓ.1 h).le, x.2.2.2⟩⟩ :=
  show ite _ _ _ = _ by
    split_ifs <;> exact Path.extend_extends _ _

theorem hcomp_half (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (t : I) :
    F.hcomp G
        (t,
          ⟨1 / 2, by
            norm_num, by
            norm_num⟩) =
      x₁ :=
  show ite _ _ _ = _ by
    norm_num

end

/-- Suppose `p` is a path, then we have a homotopy from `p` to `p.reparam f` by the convexity of `I`.
-/
def reparam (p : Path x₀ x₁) (f : I → I) (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Homotopy p (p.reparam f hf hf₀ hf₁) where
  toFun := fun x =>
    p
      ⟨σ x.1 * x.2 + x.1 * f x.2,
        show (σ x.1 : ℝ) • (x.2 : ℝ) + (x.1 : ℝ) • (f x.2 : ℝ) ∈ I from
          convex_Icc _ _ x.2.2 (f x.2).2
            (by
              unit_interval)
            (by
              unit_interval)
            (by
              simp )⟩
  map_zero_left' := fun x => by
    norm_num
  map_one_left' := fun x => by
    norm_num
  prop' := fun t x hx => by
    cases hx
    · rw [hx]
      norm_num [← hf₀]
      
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      norm_num [← hf₁]
      

/-- Suppose `F : homotopy p q`. Then we have a `homotopy p.symm q.symm` by reversing the second
argument.
-/
@[simps]
def symm₂ {p q : Path x₀ x₁} (F : p.Homotopy q) : p.symm.Homotopy q.symm where
  toFun := fun x => F ⟨x.1, σ x.2⟩
  map_zero_left' := by
    simp [← Path.symm]
  map_one_left' := by
    simp [← Path.symm]
  prop' := fun t x hx => by
    cases hx
    · rw [hx]
      simp
      
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp
      

/-- Given `F : homotopy p q`, and `f : C(X, Y)`, we can define a homotopy from `p.map f.continuous` to
`q.map f.continuous`.
-/
@[simps]
def map {p q : Path x₀ x₁} (F : p.Homotopy q) (f : C(X, Y)) : Homotopy (p.map f.Continuous) (q.map f.Continuous) where
  toFun := f ∘ F
  map_zero_left' := by
    simp
  map_one_left' := by
    simp
  prop' := fun t x hx => by
    cases hx
    · simp [← hx]
      
    · rw [Set.mem_singleton_iff] at hx
      simp [← hx]
      

end Homotopy

/-- Two paths `p₀` and `p₁` are `path.homotopic` if there exists a `homotopy` between them.
-/
def Homotopic (p₀ p₁ : Path x₀ x₁) : Prop :=
  Nonempty (p₀.Homotopy p₁)

namespace Homotopic

@[refl]
theorem refl (p : Path x₀ x₁) : p.Homotopic p :=
  ⟨Homotopy.refl p⟩

@[symm]
theorem symm ⦃p₀ p₁ : Path x₀ x₁⦄ (h : p₀.Homotopic p₁) : p₁.Homotopic p₀ :=
  h.map Homotopy.symm

@[trans]
theorem trans ⦃p₀ p₁ p₂ : Path x₀ x₁⦄ (h₀ : p₀.Homotopic p₁) (h₁ : p₁.Homotopic p₂) : p₀.Homotopic p₂ :=
  h₀.map2 Homotopy.trans h₁

theorem equivalence : Equivalenceₓ (@Homotopic X _ x₀ x₁) :=
  ⟨refl, symm, trans⟩

theorem map {p q : Path x₀ x₁} (h : p.Homotopic q) (f : C(X, Y)) :
    Homotopic (p.map f.Continuous) (q.map f.Continuous) :=
  h.map fun F => F.map f

theorem hcomp {p₀ p₁ : Path x₀ x₁} {q₀ q₁ : Path x₁ x₂} (hp : p₀.Homotopic p₁) (hq : q₀.Homotopic q₁) :
    (p₀.trans q₀).Homotopic (p₁.trans q₁) :=
  hp.map2 Homotopy.hcomp hq

/-- The setoid on `path`s defined by the equivalence relation `path.homotopic`. That is, two paths are
equivalent if there is a `homotopy` between them.
-/
protected def setoid (x₀ x₁ : X) : Setoidₓ (Path x₀ x₁) :=
  ⟨Homotopic, equivalence⟩

/-- The quotient on `path x₀ x₁` by the equivalence relation `path.homotopic`.
-/
protected def Quotient (x₀ x₁ : X) :=
  Quotientₓ (Homotopic.setoid x₀ x₁)

attribute [local instance] homotopic.setoid

instance : Inhabited (Homotopic.Quotient () ()) :=
  ⟨Quotientₓ.mk <| Path.refl ()⟩

/-- The composition of path homotopy classes. This is `path.trans` descended to the quotient. -/
def Quotient.comp (P₀ : Path.Homotopic.Quotient x₀ x₁) (P₁ : Path.Homotopic.Quotient x₁ x₂) :
    Path.Homotopic.Quotient x₀ x₂ :=
  Quotientₓ.map₂ Path.trans (fun (p₀ : Path x₀ x₁) p₁ hp (q₀ : Path x₁ x₂) q₁ hq => hcomp hp hq) P₀ P₁

theorem comp_lift (P₀ : Path x₀ x₁) (P₁ : Path x₁ x₂) : ⟦P₀.trans P₁⟧ = Quotient.comp ⟦P₀⟧ ⟦P₁⟧ :=
  rfl

/-- The image of a path homotopy class `P₀` under a map `f`.
    This is `path.map` descended to the quotient -/
def Quotient.mapFn (P₀ : Path.Homotopic.Quotient x₀ x₁) (f : C(X, Y)) : Path.Homotopic.Quotient (f x₀) (f x₁) :=
  Quotientₓ.map (fun q : Path x₀ x₁ => q.map f.Continuous) (fun p₀ p₁ h => Path.Homotopic.map h f) P₀

theorem map_lift (P₀ : Path x₀ x₁) (f : C(X, Y)) : ⟦P₀.map f.Continuous⟧ = Quotient.mapFn ⟦P₀⟧ f :=
  rfl

theorem hpath_hext {p₁ : Path x₀ x₁} {p₂ : Path x₂ x₃} (hp : ∀ t, p₁ t = p₂ t) : HEq ⟦p₁⟧ ⟦p₂⟧ := by
  obtain rfl : x₀ = x₂ := by
    convert hp 0 <;> simp
  obtain rfl : x₁ = x₃ := by
    convert hp 1 <;> simp
  rw [heq_iff_eq]
  congr
  ext t
  exact hp t

end Homotopic

end Path

namespace ContinuousMap.Homotopy

/-- Given a homotopy H: f ∼ g, get the path traced by the point `x` as it moves from
`f x` to `g x`
-/
def evalAt {X : Type _} {Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (H : ContinuousMap.Homotopy f g) (x : X) : Path (f x) (g x) where
  toFun := fun t => H (t, x)
  source' := H.apply_zero x
  target' := H.apply_one x

end ContinuousMap.Homotopy


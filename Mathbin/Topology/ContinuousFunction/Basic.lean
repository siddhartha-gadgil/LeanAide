/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathbin.Data.Set.UnionLift
import Mathbin.Topology.Homeomorph

/-!
# Continuous bundled maps

In this file we define the type `continuous_map` of continuous bundled maps.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.
-/


open Function

/-- The type of continuous maps from `α` to `β`.

When possible, instead of parametrizing results over `(f : C(α, β))`,
you should parametrize over `{F : Type*} [continuous_map_class F α β] (f : F)`.

When you extend this structure, make sure to extend `continuous_map_class`. -/
@[protect_proj]
structure ContinuousMap (α β : Type _) [TopologicalSpace α] [TopologicalSpace β] where
  toFun : α → β
  continuous_to_fun : Continuous to_fun := by
    run_tac
      tactic.interactive.continuity'

-- mathport name: «exprC( , )»
notation "C(" α ", " β ")" => ContinuousMap α β

/-- `continuous_map_class F α β` states that `F` is a type of continuous maps.

You should extend this class when you extend `continuous_map`. -/
class ContinuousMapClass (F : Type _) (α β : outParam <| Type _) [TopologicalSpace α] [TopologicalSpace β] extends
  FunLike F α fun _ => β where
  map_continuous (f : F) : Continuous f

export ContinuousMapClass (map_continuous)

attribute [continuity] map_continuous

section ContinuousMapClass

variable {F α β : Type _} [TopologicalSpace α] [TopologicalSpace β] [ContinuousMapClass F α β]

include β

theorem map_continuous_at (f : F) (a : α) : ContinuousAt f a :=
  (map_continuous f).ContinuousAt

theorem map_continuous_within_at (f : F) (s : Set α) (a : α) : ContinuousWithinAt f s a :=
  (map_continuous f).ContinuousWithinAt

instance : CoeTₓ F C(α, β) :=
  ⟨fun f => { toFun := f, continuous_to_fun := map_continuous f }⟩

end ContinuousMapClass

/-! ### Continuous maps-/


namespace ContinuousMap

variable {α β γ δ : Type _} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

instance : ContinuousMapClass C(α, β) α β where
  coe := ContinuousMap.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_continuous := ContinuousMap.continuous_to_fun

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun C(α, β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : C(α, β)} : f.toFun = (f : α → β) :=
  rfl

-- this must come after the coe_to_fun definition
initialize_simps_projections ContinuousMap (toFun → apply)

@[ext]
theorem ext {f g : C(α, β)} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext _ _ h

/-- Copy of a `continuous_map` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : C(α, β)) (f' : α → β) (h : f' = f) : C(α, β) where
  toFun := f'
  continuous_to_fun := h.symm ▸ f.continuous_to_fun

variable {α β} {f g : C(α, β)}

/-- Deprecated. Use `map_continuous` instead. -/
protected theorem continuous (f : C(α, β)) : Continuous f :=
  f.continuous_to_fun

@[continuity]
theorem continuous_set_coe (s : Set C(α, β)) (f : s) : Continuous f :=
  f.1.Continuous

/-- Deprecated. Use `map_continuous_at` instead. -/
protected theorem continuous_at (f : C(α, β)) (x : α) : ContinuousAt f x :=
  f.Continuous.ContinuousAt

/-- Deprecated. Use `fun_like.congr_fun` instead. -/
protected theorem congr_fun {f g : C(α, β)} (H : f = g) (x : α) : f x = g x :=
  H ▸ rfl

/-- Deprecated. Use `fun_like.congr_arg` instead. -/
protected theorem congr_arg (f : C(α, β)) {x y : α} (h : x = y) : f x = f y :=
  h ▸ rfl

theorem coe_injective : @Function.Injective C(α, β) (α → β) coeFn := fun f g h => by
  cases f <;> cases g <;> congr

@[simp]
theorem coe_mk (f : α → β) (h : Continuous f) : ⇑(⟨f, h⟩ : C(α, β)) = f :=
  rfl

theorem map_specializes (f : C(α, β)) {x y : α} (h : x ⤳ y) : f x ⤳ f y :=
  h.map f.2

section

variable (α β)

/-- The continuous functions from `α` to `β` are the same as the plain functions when `α` is discrete.
-/
@[simps]
def equivFnOfDiscrete [DiscreteTopology α] : C(α, β) ≃ (α → β) :=
  ⟨fun f => f, fun f => ⟨f, continuous_of_discrete_topology⟩, fun f => by
    ext
    rfl, fun f => by
    ext
    rfl⟩

end

variable (α)

/-- The identity as a continuous map. -/
protected def id : C(α, α) :=
  ⟨id⟩

@[simp]
theorem coe_id : ⇑(ContinuousMap.id α) = id :=
  rfl

/-- The constant map as a continuous map. -/
def const (b : β) : C(α, β) :=
  ⟨const α b⟩

@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

instance [Inhabited β] : Inhabited C(α, β) :=
  ⟨const α default⟩

variable {α}

@[simp]
theorem id_apply (a : α) : ContinuousMap.id α a = a :=
  rfl

@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl

/-- The composition of continuous maps, as a continuous map. -/
def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) :=
  ⟨f ∘ g⟩

@[simp]
theorem coe_comp (f : C(β, γ)) (g : C(α, β)) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α) : comp f g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : C(γ, δ)) (g : C(β, γ)) (h : C(α, β)) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem id_comp (f : C(α, β)) : (ContinuousMap.id _).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : C(α, β)) : f.comp (ContinuousMap.id _) = f :=
  ext fun _ => rfl

@[simp]
theorem const_comp (c : γ) (f : C(α, β)) : (const β c).comp f = const α c :=
  ext fun _ => rfl

@[simp]
theorem comp_const (f : C(β, γ)) (b : β) : f.comp (const α b) = const α (f b) :=
  ext fun _ => rfl

theorem cancel_right {f₁ f₂ : C(β, γ)} {g : C(α, β)} (hg : Surjective g) : f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {f : C(β, γ)} {g₁ g₂ : C(α, β)} (hf : Injective f) : f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h =>
    ext fun a =>
      hf <| by
        rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

instance [Nonempty α] [Nontrivial β] : Nontrivial C(α, β) :=
  ⟨let ⟨b₁, b₂, hb⟩ := exists_pair_ne β
    ⟨const _ b₁, const _ b₂, fun h => hb <| FunLike.congr_fun h <| Classical.arbitrary α⟩⟩

section Prod

variable {α₁ α₂ β₁ β₂ : Type _} [TopologicalSpace α₁] [TopologicalSpace α₂] [TopologicalSpace β₁] [TopologicalSpace β₂]

/-- Given two continuous maps `f` and `g`, this is the continuous map `x ↦ (f x, g x)`. -/
def prodMk (f : C(α, β₁)) (g : C(α, β₂)) : C(α, β₁ × β₂) where
  toFun := fun x => (f x, g x)
  continuous_to_fun := Continuous.prod_mk f.Continuous g.Continuous

/-- Given two continuous maps `f` and `g`, this is the continuous map `(x, y) ↦ (f x, g y)`. -/
@[simps]
def prodMap (f : C(α₁, α₂)) (g : C(β₁, β₂)) : C(α₁ × β₁, α₂ × β₂) where
  toFun := Prod.map f g
  continuous_to_fun := Continuous.prod_map f.Continuous g.Continuous

@[simp]
theorem prod_eval (f : C(α, β₁)) (g : C(α, β₂)) (a : α) : (prodMk f g) a = (f a, g a) :=
  rfl

end Prod

section Pi

variable {I A : Type _} {X : I → Type _} [TopologicalSpace A] [∀ i, TopologicalSpace (X i)]

/-- Abbreviation for product of continuous maps, which is continuous -/
def pi (f : ∀ i, C(A, X i)) : C(A, ∀ i, X i) where toFun := fun (a : A) (i : I) => f i a

@[simp]
theorem pi_eval (f : ∀ i, C(A, X i)) (a : A) : (pi f) a = fun i : I => (f i) a :=
  rfl

end Pi

section Restrict

variable (s : Set α)

/-- The restriction of a continuous function `α → β` to a subset `s` of `α`. -/
def restrict (f : C(α, β)) : C(s, β) :=
  ⟨f ∘ coe⟩

@[simp]
theorem coe_restrict (f : C(α, β)) : ⇑(f.restrict s) = f ∘ coe :=
  rfl

end Restrict

section Gluing

variable {ι : Type _} (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
  (hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩) (hS : ∀ x : α, ∃ i, S i ∈ nhds x)

include hφ hS

/-- A family `φ i` of continuous maps `C(S i, β)`, where the domains `S i` contain a neighbourhood
of each point in `α` and the functions `φ i` agree pairwise on intersections, can be glued to
construct a continuous map in `C(α, β)`. -/
noncomputable def liftCover : C(α, β) := by
  have H : (⋃ i, S i) = Set.Univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_Union]
    obtain ⟨i, hi⟩ := hS x
    exact ⟨i, mem_of_mem_nhds hi⟩
  refine' ⟨Set.liftCover S (fun i => φ i) hφ H, continuous_subtype_nhds_cover hS _⟩
  intro i
  convert (φ i).Continuous
  ext x
  exact Set.lift_cover_coe x

variable {S φ hφ hS}

@[simp]
theorem lift_cover_coe {i : ι} (x : S i) : liftCover S φ hφ hS x = φ i x :=
  Set.lift_cover_coe _

@[simp]
theorem lift_cover_restrict {i : ι} : (liftCover S φ hφ hS).restrict (S i) = φ i :=
  ext <| lift_cover_coe

omit hφ hS

variable (A : Set (Set α)) (F : ∀ (s : Set α) (hi : s ∈ A), C(s, β))
  (hF : ∀ (s) (hs : s ∈ A) (t) (ht : t ∈ A) (x : α) (hxi : x ∈ s) (hxj : x ∈ t), F s hs ⟨x, hxi⟩ = F t ht ⟨x, hxj⟩)
  (hA : ∀ x : α, ∃ i ∈ A, i ∈ nhds x)

include hF hA

/-- A family `F s` of continuous maps `C(s, β)`, where (1) the domains `s` are taken from a set `A`
of sets in `α` which contain a neighbourhood of each point in `α` and (2) the functions `F s` agree
pairwise on intersections, can be glued to construct a continuous map in `C(α, β)`. -/
noncomputable def liftCover' : C(α, β) := by
  let S : A → Set α := coe
  let F : ∀ i : A, C(i, β) := fun i => F i i.Prop
  refine' lift_cover S F (fun i j => hF i i.Prop j j.Prop) _
  intro x
  obtain ⟨s, hs, hsx⟩ := hA x
  exact ⟨⟨s, hs⟩, hsx⟩

variable {A F hF hA}

@[simp]
theorem lift_cover_coe' {s : Set α} {hs : s ∈ A} (x : s) : liftCover' A F hF hA x = F s hs x :=
  let x' : (coe : A → Set α) ⟨s, hs⟩ := x
  lift_cover_coe x'

@[simp]
theorem lift_cover_restrict' {s : Set α} {hs : s ∈ A} : (liftCover' A F hF hA).restrict s = F s hs :=
  ext <| lift_cover_coe'

end Gluing

end ContinuousMap

/-- The forward direction of a homeomorphism, as a bundled continuous map.
-/
@[simps]
def Homeomorph.toContinuousMap {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β) : C(α, β) :=
  ⟨e⟩


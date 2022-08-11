/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Algebra.BigOperators.Finprod
import Mathbin.Data.Set.Pointwise
import Mathbin.Topology.Algebra.MulAction

/-!
# Theory of topological monoids

In this file we define mixin classes `has_continuous_mul` and `has_continuous_add`. While in many
applications the underlying type is a monoid (multiplicative or additive), we do not require this in
the definitions.
-/


universe u v

open Classical Set Filter TopologicalSpace

open Classical TopologicalSpace BigOperators Pointwise

variable {ι α X M N : Type _} [TopologicalSpace X]

@[to_additive]
theorem continuous_one [TopologicalSpace M] [One M] : Continuous (1 : X → M) :=
  @continuous_const _ _ _ _ 1

/-- Basic hypothesis to talk about a topological additive monoid or a topological additive
semigroup. A topological additive monoid over `M`, for example, is obtained by requiring both the
instances `add_monoid M` and `has_continuous_add M`. -/
class HasContinuousAdd (M : Type u) [TopologicalSpace M] [Add M] : Prop where
  continuous_add : Continuous fun p : M × M => p.1 + p.2

/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `M`, for example, is obtained by requiring both the instances `monoid M`
and `has_continuous_mul M`. -/
@[to_additive]
class HasContinuousMul (M : Type u) [TopologicalSpace M] [Mul M] : Prop where
  continuous_mul : Continuous fun p : M × M => p.1 * p.2

section HasContinuousMul

variable [TopologicalSpace M] [Mul M] [HasContinuousMul M]

@[to_additive]
theorem continuous_mul : Continuous fun p : M × M => p.1 * p.2 :=
  HasContinuousMul.continuous_mul

@[to_additive]
instance HasContinuousMul.has_continuous_smul : HasContinuousSmul M M :=
  ⟨continuous_mul⟩

@[continuity, to_additive]
theorem Continuous.mul {f g : X → M} (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x * g x :=
  continuous_mul.comp (hf.prod_mk hg : _)

@[to_additive]
theorem continuous_mul_left (a : M) : Continuous fun b : M => a * b :=
  continuous_const.mul continuous_id

@[to_additive]
theorem continuous_mul_right (a : M) : Continuous fun b : M => b * a :=
  continuous_id.mul continuous_const

@[to_additive]
theorem ContinuousOn.mul {f g : X → M} {s : Set X} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x * g x) s :=
  (continuous_mul.comp_continuous_on (hf.Prod hg) : _)

@[to_additive]
theorem tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b)) :=
  continuous_iff_continuous_at.mp HasContinuousMul.continuous_mul (a, b)

@[to_additive]
theorem Filter.Tendsto.mul {f g : α → M} {x : Filter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) :
    Tendsto (fun x => f x * g x) x (𝓝 (a * b)) :=
  tendsto_mul.comp (hf.prod_mk_nhds hg)

@[to_additive]
theorem Filter.Tendsto.const_mul (b : M) {c : M} {f : α → M} {l : Filter α} (h : Tendsto (fun k : α => f k) l (𝓝 c)) :
    Tendsto (fun k : α => b * f k) l (𝓝 (b * c)) :=
  tendsto_const_nhds.mul h

@[to_additive]
theorem Filter.Tendsto.mul_const (b : M) {c : M} {f : α → M} {l : Filter α} (h : Tendsto (fun k : α => f k) l (𝓝 c)) :
    Tendsto (fun k : α => f k * b) l (𝓝 (c * b)) :=
  h.mul tendsto_const_nhds

/-- Construct a unit from limits of units and their inverses. -/
@[to_additive Filter.Tendsto.addUnits "Construct an additive unit from limits of additive units\nand their negatives.",
  simps]
def Filter.Tendsto.units [TopologicalSpace N] [Monoidₓ N] [HasContinuousMul N] [T2Space N] {f : ι → Nˣ} {r₁ r₂ : N}
    {l : Filter ι} [l.ne_bot] (h₁ : Tendsto (fun x => ↑(f x)) l (𝓝 r₁)) (h₂ : Tendsto (fun x => ↑(f x)⁻¹) l (𝓝 r₂)) :
    Nˣ where
  val := r₁
  inv := r₂
  val_inv :=
    tendsto_nhds_unique
      (by
        simpa using h₁.mul h₂)
      tendsto_const_nhds
  inv_val :=
    tendsto_nhds_unique
      (by
        simpa using h₂.mul h₁)
      tendsto_const_nhds

@[to_additive]
theorem ContinuousAt.mul {f g : X → M} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => f x * g x) x :=
  hf.mul hg

@[to_additive]
theorem ContinuousWithinAt.mul {f g : X → M} {s : Set X} {x : X} (hf : ContinuousWithinAt f s x)
    (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (fun x => f x * g x) s x :=
  hf.mul hg

@[to_additive]
instance [TopologicalSpace N] [Mul N] [HasContinuousMul N] : HasContinuousMul (M × N) :=
  ⟨((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prod_mk
      ((continuous_snd.comp continuous_fst).mul (continuous_snd.comp continuous_snd))⟩

@[to_additive]
instance Pi.has_continuous_mul {C : ι → Type _} [∀ i, TopologicalSpace (C i)] [∀ i, Mul (C i)]
    [∀ i, HasContinuousMul (C i)] :
    HasContinuousMul
      (∀ i,
        C
          i) where continuous_mul :=
    continuous_pi fun i =>
      Continuous.mul ((continuous_apply i).comp continuous_fst) ((continuous_apply i).comp continuous_snd)

/-- A version of `pi.has_continuous_mul` for non-dependent functions. It is needed because sometimes
Lean fails to use `pi.has_continuous_mul` for non-dependent functions. -/
@[to_additive
      "A version of `pi.has_continuous_add` for non-dependent functions. It is needed\nbecause sometimes Lean fails to use `pi.has_continuous_add` for non-dependent functions."]
instance Pi.has_continuous_mul' : HasContinuousMul (ι → M) :=
  Pi.has_continuous_mul

@[to_additive]
instance (priority := 100) has_continuous_mul_of_discrete_topology [TopologicalSpace N] [Mul N] [DiscreteTopology N] :
    HasContinuousMul N :=
  ⟨continuous_of_discrete_topology⟩

open Filter

open Function

@[to_additive]
theorem HasContinuousMul.of_nhds_one {M : Type u} [Monoidₓ M] [TopologicalSpace M]
    (hmul : Tendsto (uncurry ((· * ·) : M → M → M)) (𝓝 1 ×ᶠ 𝓝 1) <| 𝓝 1)
    (hleft : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)) (hright : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)) :
    HasContinuousMul M :=
  ⟨by
    rw [continuous_iff_continuous_at]
    rintro ⟨x₀, y₀⟩
    have key : (fun p : M × M => x₀ * p.1 * (p.2 * y₀)) = ((fun x => x₀ * x) ∘ fun x => x * y₀) ∘ uncurry (· * ·) := by
      ext p
      simp [← uncurry, ← mul_assoc]
    have key₂ : ((fun x => x₀ * x) ∘ fun x => y₀ * x) = fun x => x₀ * y₀ * x := by
      ext x
      simp
    calc map (uncurry (· * ·)) (𝓝 (x₀, y₀)) = map (uncurry (· * ·)) (𝓝 x₀ ×ᶠ 𝓝 y₀) := by
        rw [nhds_prod_eq]_ = map (fun p : M × M => x₀ * p.1 * (p.2 * y₀)) (𝓝 1 ×ᶠ 𝓝 1) := by
        rw [uncurry, hleft x₀, hright y₀, prod_map_map_eq,
          Filter.map_map]_ = map ((fun x => x₀ * x) ∘ fun x => x * y₀) (map (uncurry (· * ·)) (𝓝 1 ×ᶠ 𝓝 1)) :=
        by
        rw [key, ← Filter.map_map]_ ≤ map ((fun x : M => x₀ * x) ∘ fun x => x * y₀) (𝓝 1) :=
        map_mono hmul _ = 𝓝 (x₀ * y₀) := by
        rw [← Filter.map_map, ← hright, hleft y₀, Filter.map_map, key₂, ← hleft]⟩

@[to_additive]
theorem has_continuous_mul_of_comm_of_nhds_one (M : Type u) [CommMonoidₓ M] [TopologicalSpace M]
    (hmul : Tendsto (uncurry ((· * ·) : M → M → M)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)) : HasContinuousMul M := by
  apply HasContinuousMul.of_nhds_one hmul hleft
  intro x₀
  simp_rw [mul_comm, hleft x₀]

end HasContinuousMul

section PointwiseLimits

variable (M₁ M₂ : Type _) [TopologicalSpace M₂] [T2Space M₂]

@[to_additive]
theorem is_closed_set_of_map_one [One M₁] [One M₂] : IsClosed { f : M₁ → M₂ | f 1 = 1 } :=
  is_closed_eq (continuous_apply 1) continuous_const

@[to_additive]
theorem is_closed_set_of_map_mul [Mul M₁] [Mul M₂] [HasContinuousMul M₂] :
    IsClosed { f : M₁ → M₂ | ∀ x y, f (x * y) = f x * f y } := by
  simp only [← set_of_forall]
  exact
    is_closed_Inter fun x =>
      is_closed_Inter fun y => is_closed_eq (continuous_apply _) ((continuous_apply _).mul (continuous_apply _))

variable {M₁ M₂} [MulOneClassₓ M₁] [MulOneClassₓ M₂] [HasContinuousMul M₂] {F : Type _} [MonoidHomClass F M₁ M₂]
  {l : Filter α}

/-- Construct a bundled monoid homomorphism `M₁ →* M₂` from a function `f` and a proof that it
belongs to the closure of the range of the coercion from `M₁ →* M₂` (or another type of bundled
homomorphisms that has a `monoid_hom_class` instance) to `M₁ → M₂`. -/
@[to_additive
      "Construct a bundled additive monoid homomorphism `M₁ →+ M₂` from a function `f`\nand a proof that it belongs to the closure of the range of the coercion from `M₁ →+ M₂` (or another\ntype of bundled homomorphisms that has a `add_monoid_hom_class` instance) to `M₁ → M₂`.",
  simps (config := { fullyApplied := false })]
def monoidHomOfMemClosureRangeCoe (f : M₁ → M₂) (hf : f ∈ Closure (Range fun (f : F) (x : M₁) => f x)) : M₁ →* M₂ where
  toFun := f
  map_one' := (is_closed_set_of_map_one M₁ M₂).closure_subset_iff.2 (range_subset_iff.2 map_one) hf
  map_mul' := (is_closed_set_of_map_mul M₁ M₂).closure_subset_iff.2 (range_subset_iff.2 map_mul) hf

/-- Construct a bundled monoid homomorphism from a pointwise limit of monoid homomorphisms. -/
@[to_additive
      "Construct a bundled additive monoid homomorphism from a pointwise limit of additive\nmonoid homomorphisms",
  simps (config := { fullyApplied := false })]
def monoidHomOfTendsto (f : M₁ → M₂) (g : α → F) [l.ne_bot] (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ →* M₂ :=
  monoidHomOfMemClosureRangeCoe f <| mem_closure_of_tendsto h <| eventually_of_forall fun a => mem_range_self _

variable (M₁ M₂)

@[to_additive]
theorem MonoidHom.is_closed_range_coe : IsClosed (Range (coeFn : (M₁ →* M₂) → M₁ → M₂)) :=
  is_closed_of_closure_subset fun f hf => ⟨monoidHomOfMemClosureRangeCoe f hf, rfl⟩

end PointwiseLimits

namespace Submonoid

@[to_additive]
instance [TopologicalSpace α] [Monoidₓ α] [HasContinuousMul α] (S : Submonoid α) :
    HasContinuousMul S where continuous_mul := by
    rw [embedding_subtype_coe.to_inducing.continuous_iff]
    exact (continuous_subtype_coe.comp continuous_fst).mul (continuous_subtype_coe.comp continuous_snd)

end Submonoid

section HasContinuousMul

variable [TopologicalSpace M] [Monoidₓ M] [HasContinuousMul M]

@[to_additive]
theorem Submonoid.top_closure_mul_self_subset (s : Submonoid M) :
    Closure (s : Set M) * Closure (s : Set M) ⊆ Closure (s : Set M) :=
  calc
    Closure (s : Set M) * Closure (s : Set M) = (fun p : M × M => p.1 * p.2) '' Closure ((s : Set M) ×ˢ (s : Set M)) :=
      by
      simp [← closure_prod_eq]
    _ ⊆ Closure ((fun p : M × M => p.1 * p.2) '' (s : Set M) ×ˢ (s : Set M)) :=
      image_closure_subset_closure_image continuous_mul
    _ = Closure s := by
      simp [← s.coe_mul_self_eq]
    

@[to_additive]
theorem Submonoid.top_closure_mul_self_eq (s : Submonoid M) :
    Closure (s : Set M) * Closure (s : Set M) = Closure (s : Set M) :=
  Subset.antisymm s.top_closure_mul_self_subset fun x hx => ⟨x, 1, hx, subset_closure s.one_mem, mul_oneₓ _⟩

/-- The (topological-space) closure of a submonoid of a space `M` with `has_continuous_mul` is
itself a submonoid. -/
@[to_additive
      "The (topological-space) closure of an additive submonoid of a space `M` with\n`has_continuous_add` is itself an additive submonoid."]
def Submonoid.topologicalClosure (s : Submonoid M) : Submonoid M where
  Carrier := Closure (s : Set M)
  one_mem' := subset_closure s.one_mem
  mul_mem' := fun a b ha hb => s.top_closure_mul_self_subset ⟨a, b, ha, hb, rfl⟩

@[to_additive]
instance Submonoid.topological_closure_has_continuous_mul (s : Submonoid M) :
    HasContinuousMul s.topologicalClosure where continuous_mul := by
    apply continuous_induced_rng
    change Continuous fun p : s.topological_closure × s.topological_closure => (p.1 : M) * (p.2 : M)
    continuity

@[to_additive]
theorem Submonoid.submonoid_topological_closure (s : Submonoid M) : s ≤ s.topologicalClosure :=
  subset_closure

@[to_additive]
theorem Submonoid.is_closed_topological_closure (s : Submonoid M) : IsClosed (s.topologicalClosure : Set M) := by
  convert is_closed_closure

@[to_additive]
theorem Submonoid.topological_closure_minimal (s : Submonoid M) {t : Submonoid M} (h : s ≤ t)
    (ht : IsClosed (t : Set M)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

/-- If a submonoid of a topological monoid is commutative, then so is its topological closure. -/
@[to_additive "If a submonoid of an additive topological monoid is commutative, then so is its\ntopological closure."]
def Submonoid.commMonoidTopologicalClosure [T2Space M] (s : Submonoid M) (hs : ∀ x y : s, x * y = y * x) :
    CommMonoidₓ s.topologicalClosure :=
  { s.topologicalClosure.toMonoid with
    mul_comm := by
      intro a b
      have h₁ : (s.topological_closure : Set M) = Closure s := rfl
      let f₁ := fun x : M × M => x.1 * x.2
      let f₂ := fun x : M × M => x.2 * x.1
      let S : Set (M × M) := (s : Set M) ×ˢ (s : Set M)
      have h₃ : Set.EqOn f₁ f₂ (Closure S) := by
        refine'
          Set.EqOn.closure _ continuous_mul
            (by
              continuity)
        intro x hx
        rw [Set.mem_prod] at hx
        rcases hx with ⟨hx₁, hx₂⟩
        change ((⟨x.1, hx₁⟩ : s) : M) * (⟨x.2, hx₂⟩ : s) = (⟨x.2, hx₂⟩ : s) * (⟨x.1, hx₁⟩ : s)
        exact_mod_cast hs _ _
      ext
      change f₁ ⟨a, b⟩ = f₂ ⟨a, b⟩
      refine' h₃ _
      rw [closure_prod_eq, Set.mem_prod]
      exact
        ⟨by
          simp [h₁], by
          simp [h₁]⟩ }

@[to_additive exists_open_nhds_zero_half]
theorem exists_open_nhds_one_split {s : Set M} (hs : s ∈ 𝓝 (1 : M)) :
    ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧ ∀, ∀ v ∈ V, ∀, ∀ w ∈ V, ∀, v * w ∈ s := by
  have : (fun a : M × M => a.1 * a.2) ⁻¹' s ∈ 𝓝 ((1, 1) : M × M) :=
    tendsto_mul
      (by
        simpa only [← one_mulₓ] using hs)
  simpa only [← prod_subset_iff] using exists_nhds_square this

@[to_additive exists_nhds_zero_half]
theorem exists_nhds_one_split {s : Set M} (hs : s ∈ 𝓝 (1 : M)) :
    ∃ V ∈ 𝓝 (1 : M), ∀, ∀ v ∈ V, ∀, ∀ w ∈ V, ∀, v * w ∈ s :=
  let ⟨V, Vo, V1, hV⟩ := exists_open_nhds_one_split hs
  ⟨V, IsOpen.mem_nhds Vo V1, hV⟩

@[to_additive exists_nhds_zero_quarter]
theorem exists_nhds_one_split4 {u : Set M} (hu : u ∈ 𝓝 (1 : M)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v * w * s * t ∈ u := by
  rcases exists_nhds_one_split hu with ⟨W, W1, h⟩
  rcases exists_nhds_one_split W1 with ⟨V, V1, h'⟩
  use V, V1
  intro v w s t v_in w_in s_in t_in
  simpa only [← mul_assoc] using h _ (h' v v_in w w_in) _ (h' s s_in t t_in)

/-- Given a neighborhood `U` of `1` there is an open neighborhood `V` of `1`
such that `VV ⊆ U`. -/
@[to_additive "Given a open neighborhood `U` of `0` there is a open neighborhood `V` of `0`\n  such that `V + V ⊆ U`."]
theorem exists_open_nhds_one_mul_subset {U : Set M} (hU : U ∈ 𝓝 (1 : M)) :
    ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧ V * V ⊆ U := by
  rcases exists_open_nhds_one_split hU with ⟨V, Vo, V1, hV⟩
  use V, Vo, V1
  rintro _ ⟨x, y, hx, hy, rfl⟩
  exact hV _ hx _ hy

@[to_additive]
theorem IsCompact.mul {s t : Set M} (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s * t) := by
  rw [← image_mul_prod]
  exact (hs.prod ht).Image continuous_mul

@[to_additive]
theorem tendsto_list_prod {f : ι → α → M} {x : Filter α} {a : ι → M} :
    ∀ l : List ι,
      (∀, ∀ i ∈ l, ∀, Tendsto (f i) x (𝓝 (a i))) → Tendsto (fun b => (l.map fun c => f c b).Prod) x (𝓝 (l.map a).Prod)
  | [], _ => by
    simp [← tendsto_const_nhds]
  | f :: l, h => by
    simp only [← List.map_cons, ← List.prod_cons]
    exact (h f (List.mem_cons_selfₓ _ _)).mul (tendsto_list_prod l fun c hc => h c (List.mem_cons_of_memₓ _ hc))

@[to_additive]
theorem continuous_list_prod {f : ι → X → M} (l : List ι) (h : ∀, ∀ i ∈ l, ∀, Continuous (f i)) :
    Continuous fun a => (l.map fun i => f i a).Prod :=
  continuous_iff_continuous_at.2 fun x => (tendsto_list_prod l) fun c hc => continuous_iff_continuous_at.1 (h c hc) x

@[continuity, to_additive]
theorem continuous_pow : ∀ n : ℕ, Continuous fun a : M => a ^ n
  | 0 => by
    simpa using continuous_const
  | k + 1 => by
    simp only [← pow_succₓ]
    exact continuous_id.mul (continuous_pow _)

instance AddMonoidₓ.has_continuous_const_smul_nat {A} [AddMonoidₓ A] [TopologicalSpace A] [HasContinuousAdd A] :
    HasContinuousConstSmul ℕ A :=
  ⟨continuous_nsmul⟩

instance AddMonoidₓ.has_continuous_smul_nat {A} [AddMonoidₓ A] [TopologicalSpace A] [HasContinuousAdd A] :
    HasContinuousSmul ℕ A :=
  ⟨continuous_uncurry_of_discrete_topology continuous_nsmul⟩

@[continuity, to_additive Continuous.nsmul]
theorem Continuous.pow {f : X → M} (h : Continuous f) (n : ℕ) : Continuous fun b => f b ^ n :=
  (continuous_pow n).comp h

@[to_additive]
theorem continuous_on_pow {s : Set M} (n : ℕ) : ContinuousOn (fun x => x ^ n) s :=
  (continuous_pow n).ContinuousOn

@[to_additive]
theorem continuous_at_pow (x : M) (n : ℕ) : ContinuousAt (fun x => x ^ n) x :=
  (continuous_pow n).ContinuousAt

@[to_additive Filter.Tendsto.nsmul]
theorem Filter.Tendsto.pow {l : Filter α} {f : α → M} {x : M} (hf : Tendsto f l (𝓝 x)) (n : ℕ) :
    Tendsto (fun x => f x ^ n) l (𝓝 (x ^ n)) :=
  (continuous_at_pow _ _).Tendsto.comp hf

@[to_additive ContinuousWithinAt.nsmul]
theorem ContinuousWithinAt.pow {f : X → M} {x : X} {s : Set X} (hf : ContinuousWithinAt f s x) (n : ℕ) :
    ContinuousWithinAt (fun x => f x ^ n) s x :=
  hf.pow n

@[to_additive ContinuousAt.nsmul]
theorem ContinuousAt.pow {f : X → M} {x : X} (hf : ContinuousAt f x) (n : ℕ) : ContinuousAt (fun x => f x ^ n) x :=
  hf.pow n

@[to_additive ContinuousOn.nsmul]
theorem ContinuousOn.pow {f : X → M} {s : Set X} (hf : ContinuousOn f s) (n : ℕ) : ContinuousOn (fun x => f x ^ n) s :=
  fun x hx => (hf x hx).pow n

/-- If `R` acts on `A` via `A`, then continuous multiplication implies continuous scalar
multiplication by constants.

Notably, this instances applies when `R = A`, or when `[algebra R A]` is available. -/
instance (priority := 100) IsScalarTower.has_continuous_const_smul {R A : Type _} [Monoidₓ A] [HasSmul R A]
    [IsScalarTower R A A] [TopologicalSpace A] [HasContinuousMul A] :
    HasContinuousConstSmul R A where continuous_const_smul := fun q => by
    simp (config := { singlePass := true })only [smul_one_mul q (_ : A)]
    exact continuous_const.mul continuous_id

/-- If the action of `R` on `A` commutes with left-multiplication, then continuous multiplication
implies continuous scalar multiplication by constants.

Notably, this instances applies when `R = Aᵐᵒᵖ` -/
instance (priority := 100) SmulCommClass.has_continuous_const_smul {R A : Type _} [Monoidₓ A] [HasSmul R A]
    [SmulCommClass R A A] [TopologicalSpace A] [HasContinuousMul A] :
    HasContinuousConstSmul R A where continuous_const_smul := fun q => by
    simp (config := { singlePass := true })only [mul_smul_one q (_ : A)]
    exact continuous_id.mul continuous_const

end HasContinuousMul

namespace MulOpposite

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive "If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`."]
instance [TopologicalSpace α] [Mul α] [HasContinuousMul α] : HasContinuousMul αᵐᵒᵖ :=
  ⟨let h₁ := @continuous_mul α _ _ _
    let h₂ : Continuous fun p : α × α => _ := continuous_snd.prod_mk continuous_fst
    continuous_induced_rng <| (h₁.comp h₂).comp (continuous_unop.prod_map continuous_unop)⟩

end MulOpposite

namespace Units

open MulOpposite

variable [TopologicalSpace α] [Monoidₓ α] [HasContinuousMul α]

/-- If multiplication on a monoid is continuous, then multiplication on the units of the monoid,
with respect to the induced topology, is continuous.

Inversion is also continuous, but we register this in a later file, `topology.algebra.group`,
because the predicate `has_continuous_inv` has not yet been defined. -/
@[to_additive
      "If addition on an additive monoid is continuous, then addition on the additive units\nof the monoid, with respect to the induced topology, is continuous.\n\nNegation is also continuous, but we register this in a later file, `topology.algebra.group`, because\nthe predicate `has_continuous_neg` has not yet been defined."]
instance : HasContinuousMul αˣ :=
  ⟨let h := @continuous_mul (α × αᵐᵒᵖ) _ _ _
    continuous_induced_rng <| h.comp <| continuous_embed_product.prod_map continuous_embed_product⟩

end Units

section

variable [TopologicalSpace M] [CommMonoidₓ M]

@[to_additive]
theorem Submonoid.mem_nhds_one (S : Submonoid M) (oS : IsOpen (S : Set M)) : (S : Set M) ∈ 𝓝 (1 : M) :=
  IsOpen.mem_nhds oS S.one_mem

variable [HasContinuousMul M]

@[to_additive]
theorem tendsto_multiset_prod {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Multiset ι) :
    (∀, ∀ i ∈ s, ∀, Tendsto (f i) x (𝓝 (a i))) → Tendsto (fun b => (s.map fun c => f c b).Prod) x (𝓝 (s.map a).Prod) :=
  by
  rcases s with ⟨l⟩
  simpa using tendsto_list_prod l

@[to_additive]
theorem tendsto_finset_prod {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Finset ι) :
    (∀, ∀ i ∈ s, ∀, Tendsto (f i) x (𝓝 (a i))) → Tendsto (fun b => ∏ c in s, f c b) x (𝓝 (∏ c in s, a c)) :=
  tendsto_multiset_prod _

@[continuity, to_additive]
theorem continuous_multiset_prod {f : ι → X → M} (s : Multiset ι) :
    (∀, ∀ i ∈ s, ∀, Continuous (f i)) → Continuous fun a => (s.map fun i => f i a).Prod := by
  rcases s with ⟨l⟩
  simpa using continuous_list_prod l

@[continuity, to_additive]
theorem continuous_finset_prod {f : ι → X → M} (s : Finset ι) :
    (∀, ∀ i ∈ s, ∀, Continuous (f i)) → Continuous fun a => ∏ i in s, f i a :=
  continuous_multiset_prod _

open Function

@[to_additive]
theorem LocallyFinite.exists_finset_mul_support {M : Type _} [CommMonoidₓ M] {f : ι → X → M}
    (hf : LocallyFinite fun i => mul_support <| f i) (x₀ : X) :
    ∃ I : Finset ι, ∀ᶠ x in 𝓝 x₀, (MulSupport fun i => f i x) ⊆ I := by
  rcases hf x₀ with ⟨U, hxU, hUf⟩
  refine' ⟨hUf.to_finset, (mem_of_superset hxU) fun y hy i hi => _⟩
  rw [hUf.coe_to_finset]
  exact ⟨y, hi, hy⟩

@[to_additive]
theorem finprod_eventually_eq_prod {M : Type _} [CommMonoidₓ M] {f : ι → X → M}
    (hf : LocallyFinite fun i => MulSupport (f i)) (x : X) :
    ∃ s : Finset ι, ∀ᶠ y in 𝓝 x, (∏ᶠ i, f i y) = ∏ i in s, f i y :=
  let ⟨I, hI⟩ := hf.exists_finset_mul_support x
  ⟨I, hI.mono fun y hy => (finprod_eq_prod_of_mul_support_subset _) fun i hi => hy hi⟩

@[to_additive]
theorem continuous_finprod {f : ι → X → M} (hc : ∀ i, Continuous (f i)) (hf : LocallyFinite fun i => MulSupport (f i)) :
    Continuous fun x => ∏ᶠ i, f i x := by
  refine' continuous_iff_continuous_at.2 fun x => _
  rcases finprod_eventually_eq_prod hf x with ⟨s, hs⟩
  refine' ContinuousAt.congr _ (eventually_eq.symm hs)
  exact tendsto_finset_prod _ fun i hi => (hc i).ContinuousAt

@[to_additive]
theorem continuous_finprod_cond {f : ι → X → M} {p : ι → Prop} (hc : ∀ i, p i → Continuous (f i))
    (hf : LocallyFinite fun i => MulSupport (f i)) : Continuous fun x => ∏ᶠ (i) (hi : p i), f i x := by
  simp only [finprod_subtype_eq_finprod_cond]
  exact continuous_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)

end

instance Additive.has_continuous_add {M} [h : TopologicalSpace M] [Mul M] [HasContinuousMul M] :
    @HasContinuousAdd (Additive M) h _ where continuous_add := @continuous_mul M _ _ _

instance Multiplicative.has_continuous_mul {M} [h : TopologicalSpace M] [Add M] [HasContinuousAdd M] :
    @HasContinuousMul (Multiplicative M) h _ where continuous_mul := @continuous_add M _ _ _

section LatticeOps

variable {ι' : Sort _} [Mul M] [Mul N] {ts : Set (TopologicalSpace M)} (h : ∀, ∀ t ∈ ts, ∀, @HasContinuousMul M t _)
  {ts' : ι' → TopologicalSpace M} (h' : ∀ i, @HasContinuousMul M (ts' i) _) {t₁ t₂ : TopologicalSpace M}
  (h₁ : @HasContinuousMul M t₁ _) (h₂ : @HasContinuousMul M t₂ _) {t : TopologicalSpace N} [HasContinuousMul N]
  {F : Type _} [MulHomClass F M N] (f : F)

@[to_additive]
theorem has_continuous_mul_Inf : @HasContinuousMul M (inf ts) _ :=
  { continuous_mul :=
      continuous_Inf_rng fun t ht => continuous_Inf_dom₂ ht ht (@HasContinuousMul.continuous_mul M t _ (h t ht)) }

include h'

@[to_additive]
theorem has_continuous_mul_infi : @HasContinuousMul M (⨅ i, ts' i) _ := by
  rw [← Inf_range]
  exact has_continuous_mul_Inf (set.forall_range_iff.mpr h')

omit h'

include h₁ h₂

@[to_additive]
theorem has_continuous_mul_inf : @HasContinuousMul M (t₁⊓t₂) _ := by
  rw [inf_eq_infi]
  refine' has_continuous_mul_infi fun b => _
  cases b <;> assumption

omit h₁ h₂

@[to_additive]
theorem has_continuous_mul_induced : @HasContinuousMul M (t.induced f) _ :=
  { continuous_mul := by
      let this : TopologicalSpace M := t.induced f
      refine' continuous_induced_rng _
      simp_rw [Function.comp, map_mul]
      change Continuous ((fun p : N × N => p.1 * p.2) ∘ Prod.map f f)
      exact continuous_mul.comp (continuous_induced_dom.prod_map continuous_induced_dom) }

end LatticeOps


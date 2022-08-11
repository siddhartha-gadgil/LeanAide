/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.LinearAlgebra.Basic
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Data.Fin.Tuple.Default
import Mathbin.Data.Fintype.Card
import Mathbin.Data.Fintype.Sort

/-!
# Multilinear maps

We define multilinear maps as maps from `Π(i : ι), M₁ i` to `M₂` which are linear in each
coordinate. Here, `M₁ i` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type
(although some statements will require it to be a fintype). This space, denoted by
`multilinear_map R M₁ M₂`, inherits a module structure by pointwise addition and multiplication.

## Main definitions

* `multilinear_map R M₁ M₂` is the space of multilinear maps from `Π(i : ι), M₁ i` to `M₂`.
* `f.map_smul` is the multiplicativity of the multilinear map `f` along each coordinate.
* `f.map_add` is the additivity of the multilinear map `f` along each coordinate.
* `f.map_smul_univ` expresses the multiplicativity of `f` over all coordinates at the same time,
  writing `f (λi, c i • m i)` as `(∏ i, c i) • f m`.
* `f.map_add_univ` expresses the additivity of `f` over all coordinates at the same time, writing
  `f (m + m')` as the sum over all subsets `s` of `ι` of `f (s.piecewise m m')`.
* `f.map_sum` expresses `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` as the sum of
  `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all possible functions.

We also register isomorphisms corresponding to currying or uncurrying variables, transforming a
multilinear function `f` on `n+1` variables into a linear function taking values in multilinear
functions in `n` variables, and into a multilinear function in `n` variables taking values in linear
functions. These operations are called `f.curry_left` and `f.curry_right` respectively
(with inverses `f.uncurry_left` and `f.uncurry_right`). These operations induce linear equivalences
between spaces of multilinear functions in `n+1` variables and spaces of linear functions into
multilinear functions in `n` variables (resp. multilinear functions in `n` variables taking values
in linear functions), called respectively `multilinear_curry_left_equiv` and
`multilinear_curry_right_equiv`.

## Implementation notes

Expressing that a map is linear along the `i`-th coordinate when all other coordinates are fixed
can be done in two (equivalent) different ways:
* fixing a vector `m : Π(j : ι - i), M₁ j.val`, and then choosing separately the `i`-th coordinate
* fixing a vector `m : Πj, M₁ j`, and then modifying its `i`-th coordinate
The second way is more artificial as the value of `m` at `i` is not relevant, but it has the
advantage of avoiding subtype inclusion issues. This is the definition we use, based on
`function.update` that allows to change the value of `m` at `i`.
-/


open Function Finₓ Set

open BigOperators

universe u v v' v₁ v₂ v₃ w u'

variable {R : Type u} {ι : Type u'} {n : ℕ} {M : Finₓ n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  {M' : Type v'} [DecidableEq ι]

/-- Multilinear maps over the ring `R`, from `Πi, M₁ i` to `M₂` where `M₁ i` and `M₂` are modules
over `R`. -/
structure MultilinearMap (R : Type u) {ι : Type u'} (M₁ : ι → Type v) (M₂ : Type w) [DecidableEq ι] [Semiringₓ R]
  [∀ i, AddCommMonoidₓ (M₁ i)] [AddCommMonoidₓ M₂] [∀ i, Module R (M₁ i)] [Module R M₂] where
  toFun : (∀ i, M₁ i) → M₂
  map_add' :
    ∀ (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i), to_fun (update m i (x + y)) = to_fun (update m i x) + to_fun (update m i y)
  map_smul' : ∀ (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i), to_fun (update m i (c • x)) = c • to_fun (update m i x)

namespace MultilinearMap

section Semiringₓ

variable [Semiringₓ R] [∀ i, AddCommMonoidₓ (M i)] [∀ i, AddCommMonoidₓ (M₁ i)] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]
  [AddCommMonoidₓ M'] [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂] [Module R M₃] [Module R M']
  (f f' : MultilinearMap R M₁ M₂)

instance : CoeFun (MultilinearMap R M₁ M₂) fun f => (∀ i, M₁ i) → M₂ :=
  ⟨toFun⟩

initialize_simps_projections MultilinearMap (toFun → apply)

@[simp]
theorem to_fun_eq_coe : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk (f : (∀ i, M₁ i) → M₂) (h₁ h₂) : ⇑(⟨f, h₁, h₂⟩ : MultilinearMap R M₁ M₂) = f :=
  rfl

theorem congr_fun {f g : MultilinearMap R M₁ M₂} (h : f = g) (x : ∀ i, M₁ i) : f x = g x :=
  congr_arg (fun h : MultilinearMap R M₁ M₂ => h x) h

theorem congr_arg (f : MultilinearMap R M₁ M₂) {x y : ∀ i, M₁ i} (h : x = y) : f x = f y :=
  congr_arg (fun x : ∀ i, M₁ i => f x) h

theorem coe_injective : Injective (coeFn : MultilinearMap R M₁ M₂ → (∀ i, M₁ i) → M₂) := by
  intro f g h
  cases f
  cases g
  cases h
  rfl

@[simp, norm_cast]
theorem coe_inj {f g : MultilinearMap R M₁ M₂} : (f : (∀ i, M₁ i) → M₂) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
theorem ext {f f' : MultilinearMap R M₁ M₂} (H : ∀ x, f x = f' x) : f = f' :=
  coe_injective (funext H)

theorem ext_iff {f g : MultilinearMap R M₁ M₂} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩

@[simp]
theorem mk_coe (f : MultilinearMap R M₁ M₂) (h₁ h₂) : (⟨f, h₁, h₂⟩ : MultilinearMap R M₁ M₂) = f := by
  ext
  rfl

@[simp]
protected theorem map_add (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_add' m i x y

@[simp]
protected theorem map_smul (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i) : f (update m i (c • x)) = c • f (update m i x) :=
  f.map_smul' m i c x

theorem map_coord_zero {m : ∀ i, M₁ i} (i : ι) (h : m i = 0) : f m = 0 := by
  have : (0 : R) • (0 : M₁ i) = 0 := by
    simp
  rw [← update_eq_self i m, h, ← this, f.map_smul, zero_smul]

@[simp]
theorem map_update_zero (m : ∀ i, M₁ i) (i : ι) : f (update m i 0) = 0 :=
  f.map_coord_zero i (update_same i 0 m)

@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 := by
  obtain ⟨i, _⟩ : ∃ i : ι, i ∈ Set.Univ := Set.exists_mem_of_nonempty ι
  exact map_coord_zero f i rfl

instance : Add (MultilinearMap R M₁ M₂) :=
  ⟨fun f f' =>
    ⟨fun x => f x + f' x, fun m i x y => by
      simp [← add_left_commₓ, ← add_assocₓ], fun m i c x => by
      simp [← smul_add]⟩⟩

@[simp]
theorem add_apply (m : ∀ i, M₁ i) : (f + f') m = f m + f' m :=
  rfl

instance : Zero (MultilinearMap R M₁ M₂) :=
  ⟨⟨fun _ => 0, fun m i x y => by
      simp , fun m i c x => by
      simp ⟩⟩

instance : Inhabited (MultilinearMap R M₁ M₂) :=
  ⟨0⟩

@[simp]
theorem zero_apply (m : ∀ i, M₁ i) : (0 : MultilinearMap R M₁ M₂) m = 0 :=
  rfl

section HasSmul

variable {R' A : Type _} [Monoidₓ R'] [Semiringₓ A] [∀ i, Module A (M₁ i)] [DistribMulAction R' M₂] [Module A M₂]
  [SmulCommClass A R' M₂]

instance : HasSmul R' (MultilinearMap A M₁ M₂) :=
  ⟨fun c f =>
    ⟨fun m => c • f m, fun m i x y => by
      simp [← smul_add], fun l i x d => by
      simp [smul_comm x c]⟩⟩

@[simp]
theorem smul_apply (f : MultilinearMap A M₁ M₂) (c : R') (m : ∀ i, M₁ i) : (c • f) m = c • f m :=
  rfl

theorem coe_smul (c : R') (f : MultilinearMap A M₁ M₂) : ⇑(c • f) = c • f :=
  rfl

end HasSmul

instance : AddCommMonoidₓ (MultilinearMap R M₁ M₂) :=
  coe_injective.AddCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[simp]
theorem sum_apply {α : Type _} (f : α → MultilinearMap R M₁ M₂) (m : ∀ i, M₁ i) :
    ∀ {s : Finset α}, (∑ a in s, f a) m = ∑ a in s, f a m := by
  classical
  apply Finset.induction
  · rw [Finset.sum_empty]
    simp
    
  · intro a s has H
    rw [Finset.sum_insert has]
    simp [← H, ← has]
    

/-- If `f` is a multilinear map, then `f.to_linear_map m i` is the linear map obtained by fixing all
coordinates but `i` equal to those of `m`, and varying the `i`-th coordinate. -/
@[simps]
def toLinearMap (m : ∀ i, M₁ i) (i : ι) : M₁ i →ₗ[R] M₂ where
  toFun := fun x => f (update m i x)
  map_add' := fun x y => by
    simp
  map_smul' := fun c x => by
    simp

/-- The cartesian product of two multilinear maps, as a multilinear map. -/
def prod (f : MultilinearMap R M₁ M₂) (g : MultilinearMap R M₁ M₃) : MultilinearMap R M₁ (M₂ × M₃) where
  toFun := fun m => (f m, g m)
  map_add' := fun m i x y => by
    simp
  map_smul' := fun m i c x => by
    simp

/-- Combine a family of multilinear maps with the same domain and codomains `M' i` into a
multilinear map taking values in the space of functions `Π i, M' i`. -/
@[simps]
def pi {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoidₓ (M' i)] [∀ i, Module R (M' i)]
    (f : ∀ i, MultilinearMap R M₁ (M' i)) : MultilinearMap R M₁ (∀ i, M' i) where
  toFun := fun m i => f i m
  map_add' := fun m i x y => funext fun j => (f j).map_add _ _ _ _
  map_smul' := fun m i c x => funext fun j => (f j).map_smul _ _ _ _

section

variable (R M₂)

/-- The evaluation map from `ι → M₂` to `M₂` is multilinear at a given `i` when `ι` is subsingleton.
-/
@[simps]
def ofSubsingleton [Subsingleton ι] (i' : ι) : MultilinearMap R (fun _ : ι => M₂) M₂ where
  toFun := Function.eval i'
  map_add' := fun m i x y => by
    rw [Subsingleton.elimₓ i i']
    simp only [← Function.eval, ← Function.update_same]
  map_smul' := fun m i r x => by
    rw [Subsingleton.elimₓ i i']
    simp only [← Function.eval, ← Function.update_same]

variable {M₂}

/-- The constant map is multilinear when `ι` is empty. -/
@[simps (config := { fullyApplied := false })]
def constOfIsEmpty [IsEmpty ι] (m : M₂) : MultilinearMap R M₁ M₂ where
  toFun := Function.const _ m
  map_add' := fun m => isEmptyElim
  map_smul' := fun m => isEmptyElim

end

/-- Given a multilinear map `f` on `n` variables (parameterized by `fin n`) and a subset `s` of `k`
of these variables, one gets a new multilinear map on `fin k` by varying these variables, and fixing
the other ones equal to a given value `z`. It is denoted by `f.restr s hk z`, where `hk` is a
proof that the cardinality of `s` is `k`. The implicit identification between `fin k` and `s` that
we use is the canonical (increasing) bijection. -/
def restr {k n : ℕ} (f : MultilinearMap R (fun i : Finₓ n => M') M₂) (s : Finset (Finₓ n)) (hk : s.card = k) (z : M') :
    MultilinearMap R (fun i : Finₓ k => M') M₂ where
  toFun := fun v => f fun j => if h : j ∈ s then v ((s.orderIsoOfFin hk).symm ⟨j, h⟩) else z
  map_add' := fun v i x y => by
    erw [dite_comp_equiv_update, dite_comp_equiv_update, dite_comp_equiv_update]
    simp
  map_smul' := fun v i c x => by
    erw [dite_comp_equiv_update, dite_comp_equiv_update]
    simp

variable {R}

/-- In the specific case of multilinear maps on spaces indexed by `fin (n+1)`, where one can build
an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the additivity of a
multilinear map along the first variable. -/
theorem cons_add (f : MultilinearMap R M M₂) (m : ∀ i : Finₓ n, M i.succ) (x y : M 0) :
    f (cons (x + y) m) = f (cons x m) + f (cons y m) := by
  rw [← update_cons_zero x m (x + y), f.map_add, update_cons_zero, update_cons_zero]

/-- In the specific case of multilinear maps on spaces indexed by `fin (n+1)`, where one can build
an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the multiplicativity
of a multilinear map along the first variable. -/
theorem cons_smul (f : MultilinearMap R M M₂) (m : ∀ i : Finₓ n, M i.succ) (c : R) (x : M 0) :
    f (cons (c • x) m) = c • f (cons x m) := by
  rw [← update_cons_zero x m (c • x), f.map_smul, update_cons_zero]

/-- In the specific case of multilinear maps on spaces indexed by `fin (n+1)`, where one can build
an element of `Π(i : fin (n+1)), M i` using `snoc`, one can express directly the additivity of a
multilinear map along the first variable. -/
theorem snoc_add (f : MultilinearMap R M M₂) (m : ∀ i : Finₓ n, M i.cast_succ) (x y : M (last n)) :
    f (snoc m (x + y)) = f (snoc m x) + f (snoc m y) := by
  rw [← update_snoc_last x m (x + y), f.map_add, update_snoc_last, update_snoc_last]

/-- In the specific case of multilinear maps on spaces indexed by `fin (n+1)`, where one can build
an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the multiplicativity
of a multilinear map along the first variable. -/
theorem snoc_smul (f : MultilinearMap R M M₂) (m : ∀ i : Finₓ n, M i.cast_succ) (c : R) (x : M (last n)) :
    f (snoc m (c • x)) = c • f (snoc m x) := by
  rw [← update_snoc_last x m (c • x), f.map_smul, update_snoc_last]

section

variable {M₁' : ι → Type _} [∀ i, AddCommMonoidₓ (M₁' i)] [∀ i, Module R (M₁' i)]

variable {M₁'' : ι → Type _} [∀ i, AddCommMonoidₓ (M₁'' i)] [∀ i, Module R (M₁'' i)]

/-- If `g` is a multilinear map and `f` is a collection of linear maps,
then `g (f₁ m₁, ..., fₙ mₙ)` is again a multilinear map, that we call
`g.comp_linear_map f`. -/
def compLinearMap (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i →ₗ[R] M₁' i) : MultilinearMap R M₁ M₂ where
  toFun := fun m => g fun i => f i (m i)
  map_add' := fun m i x y => by
    have : ∀ j z, f j (update m i z j) = update (fun k => f k (m k)) i (f i z) j := fun j z =>
      Function.apply_update (fun k => f k) _ _ _ _
    simp [← this]
  map_smul' := fun m i c x => by
    have : ∀ j z, f j (update m i z j) = update (fun k => f k (m k)) i (f i z) j := fun j z =>
      Function.apply_update (fun k => f k) _ _ _ _
    simp [← this]

@[simp]
theorem comp_linear_map_apply (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i →ₗ[R] M₁' i) (m : ∀ i, M₁ i) :
    g.compLinearMap f m = g fun i => f i (m i) :=
  rfl

/-- Composing a multilinear map twice with a linear map in each argument is
the same as composing with their composition. -/
theorem comp_linear_map_assoc (g : MultilinearMap R M₁'' M₂) (f₁ : ∀ i, M₁' i →ₗ[R] M₁'' i)
    (f₂ : ∀ i, M₁ i →ₗ[R] M₁' i) : (g.compLinearMap f₁).compLinearMap f₂ = g.compLinearMap fun i => f₁ i ∘ₗ f₂ i :=
  rfl

/-- Composing the zero multilinear map with a linear map in each argument. -/
@[simp]
theorem zero_comp_linear_map (f : ∀ i, M₁ i →ₗ[R] M₁' i) : (0 : MultilinearMap R M₁' M₂).compLinearMap f = 0 :=
  ext fun _ => rfl

/-- Composing a multilinear map with the identity linear map in each argument. -/
@[simp]
theorem comp_linear_map_id (g : MultilinearMap R M₁' M₂) : (g.compLinearMap fun i => LinearMap.id) = g :=
  ext fun _ => rfl

/-- Composing with a family of surjective linear maps is injective. -/
theorem comp_linear_map_injective (f : ∀ i, M₁ i →ₗ[R] M₁' i) (hf : ∀ i, Surjective (f i)) :
    Injective fun g : MultilinearMap R M₁' M₂ => g.compLinearMap f := fun g₁ g₂ h =>
  ext fun x => by
    simpa [← fun i => surj_inv_eq (hf i)] using ext_iff.mp h fun i => surj_inv (hf i) (x i)

theorem comp_linear_map_inj (f : ∀ i, M₁ i →ₗ[R] M₁' i) (hf : ∀ i, Surjective (f i)) (g₁ g₂ : MultilinearMap R M₁' M₂) :
    g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂ :=
  (comp_linear_map_injective _ hf).eq_iff

/-- Composing a multilinear map with a linear equiv on each argument gives the zero map
if and only if the multilinear map is the zero map. -/
@[simp]
theorem comp_linear_equiv_eq_zero_iff (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i ≃ₗ[R] M₁' i) :
    (g.compLinearMap fun i => (f i : M₁ i →ₗ[R] M₁' i)) = 0 ↔ g = 0 := by
  set f' := fun i => (f i : M₁ i →ₗ[R] M₁' i)
  rw [← zero_comp_linear_map f', comp_linear_map_inj f' fun i => (f i).Surjective]

end

/-- If one adds to a vector `m'` another vector `m`, but only for coordinates in a finset `t`, then
the image under a multilinear map `f` is the sum of `f (s.piecewise m m')` along all subsets `s` of
`t`. This is mainly an auxiliary statement to prove the result when `t = univ`, given in
`map_add_univ`, although it can be useful in its own right as it does not require the index set `ι`
to be finite.-/
theorem map_piecewise_add (m m' : ∀ i, M₁ i) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s in t.Powerset, f (s.piecewise m m') := by
  revert m'
  refine'
    Finset.induction_on t
      (by
        simp )
      _
  intro i t hit Hrec m'
  have A : (insert i t).piecewise (m + m') m' = update (t.piecewise (m + m') m') i (m i + m' i) :=
    t.piecewise_insert _ _ _
  have B : update (t.piecewise (m + m') m') i (m' i) = t.piecewise (m + m') m' := by
    ext j
    by_cases' h : j = i
    · rw [h]
      simp [← hit]
      
    · simp [← h]
      
  let m'' := update m' i (m i)
  have C : update (t.piecewise (m + m') m') i (m i) = t.piecewise (m + m'') m'' := by
    ext j
    by_cases' h : j = i
    · rw [h]
      simp [← m'', ← hit]
      
    · by_cases' h' : j ∈ t <;> simp [← h, ← hit, ← m'', ← h']
      
  rw [A, f.map_add, B, C, Finset.sum_powerset_insert hit, Hrec, Hrec, add_commₓ]
  congr 1
  apply Finset.sum_congr rfl fun s hs => _
  have : (insert i s).piecewise m m' = s.piecewise m m'' := by
    ext j
    by_cases' h : j = i
    · rw [h]
      simp [← m'', ← Finset.not_mem_of_mem_powerset_of_not_mem hs hit]
      
    · by_cases' h' : j ∈ s <;> simp [← h, ← m'', ← h']
      
  rw [this]

/-- Additivity of a multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum  of `f (s.piecewise m m')` over all sets `s`. -/
theorem map_add_univ [Fintype ι] (m m' : ∀ i, M₁ i) : f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') := by
  simpa using f.map_piecewise_add m m' Finset.univ

section ApplySum

variable {α : ι → Type _} (g : ∀ i, α i → M₁ i) (A : ∀ i, Finset (α i))

open Classical

open Fintype Finset

/-- If `f` is multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. Here, we give an auxiliary statement tailored for an inductive proof. Use instead
`map_sum_finset`. -/
theorem map_sum_finset_aux [Fintype ι] {n : ℕ} (h : (∑ i, (A i).card) = n) :
    (f fun i => ∑ j in A i, g i j) = ∑ r in piFinset A, f fun i => g i (r i) := by
  induction' n using Nat.strong_induction_onₓ with n IH generalizing A
  -- If one of the sets is empty, then all the sums are zero
  by_cases' Ai_empty : ∃ i, A i = ∅
  · rcases Ai_empty with ⟨i, hi⟩
    have : (∑ j in A i, g i j) = 0 := by
      rw [hi, Finset.sum_empty]
    rw [f.map_coord_zero i this]
    have : pi_finset A = ∅ := by
      apply Finset.eq_empty_of_forall_not_mem fun r hr => _
      have : r i ∈ A i := mem_pi_finset.mp hr i
      rwa [hi] at this
    rw [this, Finset.sum_empty]
    
  push_neg  at Ai_empty
  -- Otherwise, if all sets are at most singletons, then they are exactly singletons and the result
  -- is again straightforward
  by_cases' Ai_singleton : ∀ i, (A i).card ≤ 1
  · have Ai_card : ∀ i, (A i).card = 1 := by
      intro i
      have pos : Finset.card (A i) ≠ 0 := by
        simp [← Finset.card_eq_zero, ← Ai_empty i]
      have : Finset.card (A i) ≤ 1 := Ai_singleton i
      exact le_antisymmₓ this (Nat.succ_le_of_ltₓ (_root_.pos_iff_ne_zero.mpr Pos))
    have : ∀ r : ∀ i, α i, r ∈ pi_finset A → (f fun i => g i (r i)) = f fun i => ∑ j in A i, g i j := by
      intro r hr
      unfold_coes
      congr with i
      have : ∀, ∀ j ∈ A i, ∀, g i j = g i (r i) := by
        intro j hj
        congr
        apply Finset.card_le_one_iff.1 (Ai_singleton i) hj
        exact mem_pi_finset.mp hr i
      simp only [← Finset.sum_congr rfl this, ← Finset.mem_univ, ← Finset.sum_const, ← Ai_card i, ← one_nsmul]
    simp only [← sum_congr rfl this, ← Ai_card, ← card_pi_finset, ← prod_const_one, ← one_nsmul, ← Finset.sum_const]
    
  -- Remains the interesting case where one of the `A i`, say `A i₀`, has cardinality at least 2.
  -- We will split into two parts `B i₀` and `C i₀` of smaller cardinality, let `B i = C i = A i`
  -- for `i ≠ i₀`, apply the inductive assumption to `B` and `C`, and add up the corresponding
  -- parts to get the sum for `A`.
  push_neg  at Ai_singleton
  obtain ⟨i₀, hi₀⟩ : ∃ i, 1 < (A i).card := Ai_singleton
  obtain ⟨j₁, j₂, hj₁, hj₂, j₁_ne_j₂⟩ : ∃ j₁ j₂, j₁ ∈ A i₀ ∧ j₂ ∈ A i₀ ∧ j₁ ≠ j₂ := Finset.one_lt_card_iff.1 hi₀
  let B := Function.update A i₀ (A i₀ \ {j₂})
  let C := Function.update A i₀ {j₂}
  have B_subset_A : ∀ i, B i ⊆ A i := by
    intro i
    by_cases' hi : i = i₀
    · rw [hi]
      simp only [← B, ← sdiff_subset, ← update_same]
      
    · simp only [← hi, ← B, ← update_noteq, ← Ne.def, ← not_false_iff, ← Finset.Subset.refl]
      
  have C_subset_A : ∀ i, C i ⊆ A i := by
    intro i
    by_cases' hi : i = i₀
    · rw [hi]
      simp only [← C, ← hj₂, ← Finset.singleton_subset_iff, ← update_same]
      
    · simp only [← hi, ← C, ← update_noteq, ← Ne.def, ← not_false_iff, ← Finset.Subset.refl]
      
  -- split the sum at `i₀` as the sum over `B i₀` plus the sum over `C i₀`, to use additivity.
  have A_eq_BC :
    (fun i => ∑ j in A i, g i j) =
      Function.update (fun i => ∑ j in A i, g i j) i₀ ((∑ j in B i₀, g i₀ j) + ∑ j in C i₀, g i₀ j) :=
    by
    ext i
    by_cases' hi : i = i₀
    · rw [hi]
      simp only [← Function.update_same]
      have : A i₀ = B i₀ ∪ C i₀ := by
        simp only [← B, ← C, ← Function.update_same, ← Finset.sdiff_union_self_eq_union]
        symm
        simp only [← hj₂, ← Finset.singleton_subset_iff, ← Finset.union_eq_left_iff_subset]
      rw [this]
      apply Finset.sum_union
      apply Finset.disjoint_right.2 fun j hj => _
      have : j = j₂ := by
        dsimp' [← C]  at hj
        simpa using hj
      rw [this]
      dsimp' [← B]
      simp only [← mem_sdiff, ← eq_self_iff_true, ← not_true, ← not_false_iff, ← Finset.mem_singleton, ← update_same, ←
        and_falseₓ]
      
    · simp [← hi]
      
  have Beq : Function.update (fun i => ∑ j in A i, g i j) i₀ (∑ j in B i₀, g i₀ j) = fun i => ∑ j in B i, g i j := by
    ext i
    by_cases' hi : i = i₀
    · rw [hi]
      simp only [← update_same]
      
    · simp only [← hi, ← B, ← update_noteq, ← Ne.def, ← not_false_iff]
      
  have Ceq : Function.update (fun i => ∑ j in A i, g i j) i₀ (∑ j in C i₀, g i₀ j) = fun i => ∑ j in C i, g i j := by
    ext i
    by_cases' hi : i = i₀
    · rw [hi]
      simp only [← update_same]
      
    · simp only [← hi, ← C, ← update_noteq, ← Ne.def, ← not_false_iff]
      
  -- Express the inductive assumption for `B`
  have Brec : (f fun i => ∑ j in B i, g i j) = ∑ r in pi_finset B, f fun i => g i (r i) := by
    have : (∑ i, Finset.card (B i)) < ∑ i, Finset.card (A i) := by
      refine' Finset.sum_lt_sum (fun i hi => Finset.card_le_of_subset (B_subset_A i)) ⟨i₀, Finset.mem_univ _, _⟩
      have : {j₂} ⊆ A i₀ := by
        simp [← hj₂]
      simp only [← B, ← Finset.card_sdiff this, ← Function.update_same, ← Finset.card_singleton]
      exact Nat.pred_ltₓ (ne_of_gtₓ (lt_transₓ Nat.zero_lt_oneₓ hi₀))
    rw [h] at this
    exact IH _ this B rfl
  -- Express the inductive assumption for `C`
  have Crec : (f fun i => ∑ j in C i, g i j) = ∑ r in pi_finset C, f fun i => g i (r i) := by
    have : (∑ i, Finset.card (C i)) < ∑ i, Finset.card (A i) :=
      Finset.sum_lt_sum (fun i hi => Finset.card_le_of_subset (C_subset_A i))
        ⟨i₀, Finset.mem_univ _, by
          simp [← C, ← hi₀]⟩
    rw [h] at this
    exact IH _ this C rfl
  have D : Disjoint (pi_finset B) (pi_finset C) := by
    have : Disjoint (B i₀) (C i₀) := by
      simp [← B, ← C]
    exact pi_finset_disjoint_of_disjoint B C this
  have pi_BC : pi_finset A = pi_finset B ∪ pi_finset C := by
    apply Finset.Subset.antisymm
    · intro r hr
      by_cases' hri₀ : r i₀ = j₂
      · apply Finset.mem_union_right
        apply mem_pi_finset.2 fun i => _
        by_cases' hi : i = i₀
        · have : r i₀ ∈ C i₀ := by
            simp [← C, ← hri₀]
          convert this
          
        · simp [← C, ← hi, ← mem_pi_finset.1 hr i]
          
        
      · apply Finset.mem_union_left
        apply mem_pi_finset.2 fun i => _
        by_cases' hi : i = i₀
        · have : r i₀ ∈ B i₀ := by
            simp [← B, ← hri₀, ← mem_pi_finset.1 hr i₀]
          convert this
          
        · simp [← B, ← hi, ← mem_pi_finset.1 hr i]
          
        
      
    · exact
        Finset.union_subset (pi_finset_subset _ _ fun i => B_subset_A i) (pi_finset_subset _ _ fun i => C_subset_A i)
      
  rw [A_eq_BC]
  simp only [← MultilinearMap.map_add, ← Beq, ← Ceq, ← Brec, ← Crec, ← pi_BC]
  rw [← Finset.sum_union D]

/-- If `f` is multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
theorem map_sum_finset [Fintype ι] : (f fun i => ∑ j in A i, g i j) = ∑ r in piFinset A, f fun i => g i (r i) :=
  f.map_sum_finset_aux _ _ rfl

/-- If `f` is multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
theorem map_sum [Fintype ι] [∀ i, Fintype (α i)] : (f fun i => ∑ j, g i j) = ∑ r : ∀ i, α i, f fun i => g i (r i) :=
  f.map_sum_finset g fun i => Finset.univ

theorem map_update_sum {α : Type _} (t : Finset α) (i : ι) (g : α → M₁ i) (m : ∀ i, M₁ i) :
    f (update m i (∑ a in t, g a)) = ∑ a in t, f (update m i (g a)) := by
  induction' t using Finset.induction with a t has ih h
  · simp
    
  · simp [← Finset.sum_insert has, ← ih]
    

end ApplySum

/-- Restrict the codomain of a multilinear map to a submodule.

This is the multilinear version of `linear_map.cod_restrict`. -/
@[simps]
def codRestrict (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂) (h : ∀ v, f v ∈ p) : MultilinearMap R M₁ p where
  toFun := fun v => ⟨f v, h v⟩
  map_add' := fun v i x y => Subtype.ext <| MultilinearMap.map_add _ _ _ _ _
  map_smul' := fun v i c x => Subtype.ext <| MultilinearMap.map_smul _ _ _ _ _

section RestrictScalar

variable (R) {A : Type _} [Semiringₓ A] [HasSmul R A] [∀ i : ι, Module A (M₁ i)] [Module A M₂]
  [∀ i, IsScalarTower R A (M₁ i)] [IsScalarTower R A M₂]

/-- Reinterpret an `A`-multilinear map as an `R`-multilinear map, if `A` is an algebra over `R`
and their actions on all involved modules agree with the action of `R` on `A`. -/
def restrictScalars (f : MultilinearMap A M₁ M₂) : MultilinearMap R M₁ M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' := fun m i => (f.toLinearMap m i).map_smul_of_tower

@[simp]
theorem coe_restrict_scalars (f : MultilinearMap A M₁ M₂) : ⇑(f.restrictScalars R) = f :=
  rfl

end RestrictScalar

section

variable {ι₁ ι₂ ι₃ : Type _} [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃]

/-- Transfer the arguments to a map along an equivalence between argument indices.

The naming is derived from `finsupp.dom_congr`, noting that here the permutation applies to the
domain of the domain. -/
@[simps apply]
def domDomCongr (σ : ι₁ ≃ ι₂) (m : MultilinearMap R (fun i : ι₁ => M₂) M₃) :
    MultilinearMap R (fun i : ι₂ => M₂) M₃ where
  toFun := fun v => m fun i => v (σ i)
  map_add' := fun v i a b => by
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_add]
  map_smul' := fun v i a b => by
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_smul]

theorem dom_dom_congr_trans (σ₁ : ι₁ ≃ ι₂) (σ₂ : ι₂ ≃ ι₃) (m : MultilinearMap R (fun i : ι₁ => M₂) M₃) :
    m.domDomCongr (σ₁.trans σ₂) = (m.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl

theorem dom_dom_congr_mul (σ₁ : Equivₓ.Perm ι₁) (σ₂ : Equivₓ.Perm ι₁) (m : MultilinearMap R (fun i : ι₁ => M₂) M₃) :
    m.domDomCongr (σ₂ * σ₁) = (m.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl

/-- `multilinear_map.dom_dom_congr` as an equivalence.

This is declared separately because it does not work with dot notation. -/
@[simps apply symmApply]
def domDomCongrEquiv (σ : ι₁ ≃ ι₂) :
    MultilinearMap R (fun i : ι₁ => M₂) M₃ ≃+ MultilinearMap R (fun i : ι₂ => M₂) M₃ where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv := fun m => by
    ext
    simp
  right_inv := fun m => by
    ext
    simp
  map_add' := fun a b => by
    ext
    simp

/-- The results of applying `dom_dom_congr` to two maps are equal if
and only if those maps are. -/
@[simp]
theorem dom_dom_congr_eq_iff (σ : ι₁ ≃ ι₂) (f g : MultilinearMap R (fun i : ι₁ => M₂) M₃) :
    f.domDomCongr σ = g.domDomCongr σ ↔ f = g :=
  (domDomCongrEquiv σ : _ ≃+ MultilinearMap R (fun i => M₂) M₃).apply_eq_iff_eq

end

end Semiringₓ

end MultilinearMap

namespace LinearMap

variable [Semiringₓ R] [∀ i, AddCommMonoidₓ (M₁ i)] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃] [AddCommMonoidₓ M']
  [∀ i, Module R (M₁ i)] [Module R M₂] [Module R M₃] [Module R M']

/-- Composing a multilinear map with a linear map gives again a multilinear map. -/
def compMultilinearMap (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) : MultilinearMap R M₁ M₃ where
  toFun := g ∘ f
  map_add' := fun m i x y => by
    simp
  map_smul' := fun m i c x => by
    simp

@[simp]
theorem coe_comp_multilinear_map (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) : ⇑(g.compMultilinearMap f) = g ∘ f :=
  rfl

@[simp]
theorem comp_multilinear_map_apply (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) (m : ∀ i, M₁ i) :
    g.compMultilinearMap f m = g (f m) :=
  rfl

/-- The multilinear version of `linear_map.subtype_comp_cod_restrict` -/
@[simp]
theorem subtype_comp_multilinear_map_cod_restrict (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂) (h) :
    p.Subtype.compMultilinearMap (f.codRestrict p h) = f :=
  MultilinearMap.ext fun v => rfl

/-- The multilinear version of `linear_map.comp_cod_restrict` -/
@[simp]
theorem comp_multilinear_map_cod_restrict (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) (p : Submodule R M₃) (h) :
    (g.codRestrict p h).compMultilinearMap f = (g.compMultilinearMap f).codRestrict p fun v => h (f v) :=
  MultilinearMap.ext fun v => rfl

variable {ι₁ ι₂ : Type _} [DecidableEq ι₁] [DecidableEq ι₂]

@[simp]
theorem comp_multilinear_map_dom_dom_congr (σ : ι₁ ≃ ι₂) (g : M₂ →ₗ[R] M₃)
    (f : MultilinearMap R (fun i : ι₁ => M') M₂) :
    (g.compMultilinearMap f).domDomCongr σ = g.compMultilinearMap (f.domDomCongr σ) := by
  ext
  simp

end LinearMap

namespace MultilinearMap

section CommSemiringₓ

variable [CommSemiringₓ R] [∀ i, AddCommMonoidₓ (M₁ i)] [∀ i, AddCommMonoidₓ (M i)] [AddCommMonoidₓ M₂]
  [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂] (f f' : MultilinearMap R M₁ M₂)

/-- If one multiplies by `c i` the coordinates in a finset `s`, then the image under a multilinear
map is multiplied by `∏ i in s, c i`. This is mainly an auxiliary statement to prove the result when
`s = univ`, given in `map_smul_univ`, although it can be useful in its own right as it does not
require the index set `ι` to be finite. -/
theorem map_piecewise_smul (c : ι → R) (m : ∀ i, M₁ i) (s : Finset ι) :
    f (s.piecewise (fun i => c i • m i) m) = (∏ i in s, c i) • f m := by
  refine'
    s.induction_on
      (by
        simp )
      _
  intro j s j_not_mem_s Hrec
  have A : Function.update (s.piecewise (fun i => c i • m i) m) j (m j) = s.piecewise (fun i => c i • m i) m := by
    ext i
    by_cases' h : i = j
    · rw [h]
      simp [← j_not_mem_s]
      
    · simp [← h]
      
  rw [s.piecewise_insert, f.map_smul, A, Hrec]
  simp [← j_not_mem_s, ← mul_smul]

/-- Multiplicativity of a multilinear map along all coordinates at the same time,
writing `f (λi, c i • m i)` as `(∏ i, c i) • f m`. -/
theorem map_smul_univ [Fintype ι] (c : ι → R) (m : ∀ i, M₁ i) : (f fun i => c i • m i) = (∏ i, c i) • f m := by
  simpa using map_piecewise_smul f c m Finset.univ

@[simp]
theorem map_update_smul [Fintype ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i) :
    f (update (c • m) i x) = c ^ (Fintype.card ι - 1) • f (update m i x) := by
  have :
    f ((finset.univ.erase i).piecewise (c • update m i x) (update m i x)) =
      (∏ i in finset.univ.erase i, c) • f (update m i x) :=
    map_piecewise_smul f _ _ _
  simpa [Function.update_smul c m] using this

section DistribMulAction

variable {R' A : Type _} [Monoidₓ R'] [Semiringₓ A] [∀ i, Module A (M₁ i)] [DistribMulAction R' M₂] [Module A M₂]
  [SmulCommClass A R' M₂]

instance : DistribMulAction R' (MultilinearMap A M₁ M₂) where
  one_smul := fun f => ext fun x => one_smul _ _
  mul_smul := fun c₁ c₂ f => ext fun x => mul_smul _ _ _
  smul_zero := fun r => ext fun x => smul_zero _
  smul_add := fun r f₁ f₂ => ext fun x => smul_add _ _ _

end DistribMulAction

section Module

variable {R' A : Type _} [Semiringₓ R'] [Semiringₓ A] [∀ i, Module A (M₁ i)] [Module A M₂] [AddCommMonoidₓ M₃]
  [Module R' M₃] [Module A M₃] [SmulCommClass A R' M₃]

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
instance [Module R' M₂] [SmulCommClass A R' M₂] : Module R' (MultilinearMap A M₁ M₂) where
  add_smul := fun r₁ r₂ f => ext fun x => add_smul _ _ _
  zero_smul := fun f => ext fun x => zero_smul _ _

instance [NoZeroSmulDivisors R' M₃] : NoZeroSmulDivisors R' (MultilinearMap A M₁ M₃) :=
  coe_injective.NoZeroSmulDivisors _ rfl coe_smul

variable (M₂ M₃ R' A)

/-- `multilinear_map.dom_dom_congr` as a `linear_equiv`. -/
@[simps apply symmApply]
def domDomCongrLinearEquiv {ι₁ ι₂} [DecidableEq ι₁] [DecidableEq ι₂] (σ : ι₁ ≃ ι₂) :
    MultilinearMap A (fun i : ι₁ => M₂) M₃ ≃ₗ[R'] MultilinearMap A (fun i : ι₂ => M₂) M₃ :=
  { (domDomCongrEquiv σ : MultilinearMap A (fun i : ι₁ => M₂) M₃ ≃+ MultilinearMap A (fun i : ι₂ => M₂) M₃) with
    map_smul' := fun c f => by
      ext
      simp }

variable (R M₁)

/-- The dependent version of `multilinear_map.dom_dom_congr_linear_equiv`. -/
@[simps apply symmApply]
def domDomCongrLinearEquiv' {ι' : Type _} [DecidableEq ι'] (σ : ι ≃ ι') :
    MultilinearMap R M₁ M₂ ≃ₗ[R] MultilinearMap R (fun i => M₁ (σ.symm i)) M₂ where
  toFun := fun f =>
    { toFun := f ∘ (σ.piCongrLeft' M₁).symm,
      map_add' := fun m i => by
        rw [← σ.apply_symm_apply i]
        intro x y
        simp only [← comp_app, ← Pi_congr_left'_symm_update, ← f.map_add],
      map_smul' := fun m i c => by
        rw [← σ.apply_symm_apply i]
        intro x
        simp only [← comp_app, ← Pi_congr_left'_symm_update, ← f.map_smul] }
  invFun := fun f =>
    { toFun := f ∘ σ.piCongrLeft' M₁,
      map_add' := fun m i => by
        rw [← σ.symm_apply_apply i]
        intro x y
        simp only [← comp_app, ← Pi_congr_left'_update, ← f.map_add],
      map_smul' := fun m i c => by
        rw [← σ.symm_apply_apply i]
        intro x
        simp only [← comp_app, ← Pi_congr_left'_update, ← f.map_smul] }
  map_add' := fun f₁ f₂ => by
    ext
    simp only [← comp_app, ← coe_mk, ← add_apply]
  map_smul' := fun c f => by
    ext
    simp only [← comp_app, ← coe_mk, ← smul_apply, ← RingHom.id_apply]
  left_inv := fun f => by
    ext
    simp only [← comp_app, ← coe_mk, ← Equivₓ.symm_apply_apply]
  right_inv := fun f => by
    ext
    simp only [← comp_app, ← coe_mk, ← Equivₓ.apply_symm_apply]

/-- The space of constant maps is equivalent to the space of maps that are multilinear with respect
to an empty family. -/
@[simps]
def constLinearEquivOfIsEmpty [IsEmpty ι] : M₂ ≃ₗ[R] MultilinearMap R M₁ M₂ where
  toFun := MultilinearMap.constOfIsEmpty R
  map_add' := fun x y => rfl
  map_smul' := fun t x => rfl
  invFun := fun f => f 0
  left_inv := fun _ => rfl
  right_inv := fun f => ext fun x => MultilinearMap.congr_arg f <| Subsingleton.elimₓ _ _

end Module

section

variable (R ι) (A : Type _) [CommSemiringₓ A] [Algebra R A] [Fintype ι]

/-- Given an `R`-algebra `A`, `mk_pi_algebra` is the multilinear map on `A^ι` associating
to `m` the product of all the `m i`.

See also `multilinear_map.mk_pi_algebra_fin` for a version that works with a non-commutative
algebra `A` but requires `ι = fin n`. -/
protected def mkPiAlgebra : MultilinearMap R (fun i : ι => A) A where
  toFun := fun m => ∏ i, m i
  map_add' := fun m i x y => by
    simp [← Finset.prod_update_of_mem, ← add_mulₓ]
  map_smul' := fun m i c x => by
    simp [← Finset.prod_update_of_mem]

variable {R A ι}

@[simp]
theorem mk_pi_algebra_apply (m : ι → A) : MultilinearMap.mkPiAlgebra R ι A m = ∏ i, m i :=
  rfl

end

section

variable (R n) (A : Type _) [Semiringₓ A] [Algebra R A]

/-- Given an `R`-algebra `A`, `mk_pi_algebra_fin` is the multilinear map on `A^n` associating
to `m` the product of all the `m i`.

See also `multilinear_map.mk_pi_algebra` for a version that assumes `[comm_semiring A]` but works
for `A^ι` with any finite type `ι`. -/
protected def mkPiAlgebraFin : MultilinearMap R (fun i : Finₓ n => A) A where
  toFun := fun m => (List.ofFnₓ m).Prod
  map_add' := by
    intro m i x y
    have : (List.finRange n).indexOf i < n := by
      simpa using List.index_of_lt_length.2 (List.mem_fin_range i)
    simp [← List.of_fn_eq_map, ← (List.nodup_fin_range n).map_update, ← List.prod_update_nth, ← add_mulₓ, ← this, ←
      mul_addₓ, ← add_mulₓ]
  map_smul' := by
    intro m i c x
    have : (List.finRange n).indexOf i < n := by
      simpa using List.index_of_lt_length.2 (List.mem_fin_range i)
    simp [← List.of_fn_eq_map, ← (List.nodup_fin_range n).map_update, ← List.prod_update_nth, ← this]

variable {R A n}

@[simp]
theorem mk_pi_algebra_fin_apply (m : Finₓ n → A) : MultilinearMap.mkPiAlgebraFin R n A m = (List.ofFnₓ m).Prod :=
  rfl

theorem mk_pi_algebra_fin_apply_const (a : A) : (MultilinearMap.mkPiAlgebraFin R n A fun _ => a) = a ^ n := by
  simp

end

/-- Given an `R`-multilinear map `f` taking values in `R`, `f.smul_right z` is the map
sending `m` to `f m • z`. -/
def smulRight (f : MultilinearMap R M₁ R) (z : M₂) : MultilinearMap R M₁ M₂ :=
  (LinearMap.smulRight LinearMap.id z).compMultilinearMap f

@[simp]
theorem smul_right_apply (f : MultilinearMap R M₁ R) (z : M₂) (m : ∀ i, M₁ i) : f.smul_right z m = f m • z :=
  rfl

variable (R ι)

/-- The canonical multilinear map on `R^ι` when `ι` is finite, associating to `m` the product of
all the `m i` (multiplied by a fixed reference element `z` in the target module). See also
`mk_pi_algebra` for a more general version. -/
protected def mkPiRing [Fintype ι] (z : M₂) : MultilinearMap R (fun i : ι => R) M₂ :=
  (MultilinearMap.mkPiAlgebra R ι R).smul_right z

variable {R ι}

@[simp]
theorem mk_pi_ring_apply [Fintype ι] (z : M₂) (m : ι → R) :
    (MultilinearMap.mkPiRing R ι z : (ι → R) → M₂) m = (∏ i, m i) • z :=
  rfl

theorem mk_pi_ring_apply_one_eq_self [Fintype ι] (f : MultilinearMap R (fun i : ι => R) M₂) :
    MultilinearMap.mkPiRing R ι (f fun i => 1) = f := by
  ext m
  have : m = fun i => m i • 1 := by
    ext j
    simp
  conv_rhs => rw [this, f.map_smul_univ]
  rfl

end CommSemiringₓ

section RangeAddCommGroup

variable [Semiringₓ R] [∀ i, AddCommMonoidₓ (M₁ i)] [AddCommGroupₓ M₂] [∀ i, Module R (M₁ i)] [Module R M₂]
  (f g : MultilinearMap R M₁ M₂)

instance : Neg (MultilinearMap R M₁ M₂) :=
  ⟨fun f =>
    ⟨fun m => -f m, fun m i x y => by
      simp [← add_commₓ], fun m i c x => by
      simp ⟩⟩

@[simp]
theorem neg_apply (m : ∀ i, M₁ i) : (-f) m = -f m :=
  rfl

instance : Sub (MultilinearMap R M₁ M₂) :=
  ⟨fun f g =>
    ⟨fun m => f m - g m, fun m i x y => by
      simp only [← MultilinearMap.map_add, ← sub_eq_add_neg, ← neg_add]
      cc, fun m i c x => by
      simp only [← MultilinearMap.map_smul, ← smul_sub]⟩⟩

@[simp]
theorem sub_apply (m : ∀ i, M₁ i) : (f - g) m = f m - g m :=
  rfl

instance : AddCommGroupₓ (MultilinearMap R M₁ M₂) := by
  refine'
      { MultilinearMap.addCommMonoid with zero := (0 : MultilinearMap R M₁ M₂), add := (· + ·), neg := Neg.neg,
        sub := Sub.sub, sub_eq_add_neg := _,
        nsmul := fun n f =>
          ⟨fun m => n • f m, fun m i x y => by
            simp [← smul_add], fun l i x d => by
            simp [smul_comm x n]⟩,
        zsmul := fun n f =>
          ⟨fun m => n • f m, fun m i x y => by
            simp [← smul_add], fun l i x d => by
            simp [smul_comm x n]⟩,
        zsmul_zero' := _, zsmul_succ' := _, zsmul_neg' := _.. } <;>
    intros <;> ext <;> simp [← add_commₓ, ← add_left_commₓ, ← sub_eq_add_neg, ← add_smul, ← Nat.succ_eq_add_one]

end RangeAddCommGroup

section AddCommGroupₓ

variable [Semiringₓ R] [∀ i, AddCommGroupₓ (M₁ i)] [AddCommGroupₓ M₂] [∀ i, Module R (M₁ i)] [Module R M₂]
  (f : MultilinearMap R M₁ M₂)

@[simp]
theorem map_neg (m : ∀ i, M₁ i) (i : ι) (x : M₁ i) : f (update m i (-x)) = -f (update m i x) :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← MultilinearMap.map_add, add_left_negₓ, f.map_coord_zero i (update_same i 0 m)]

@[simp]
theorem map_sub (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) : f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
  by
  rw [sub_eq_add_neg, sub_eq_add_neg, MultilinearMap.map_add, map_neg]

end AddCommGroupₓ

section CommSemiringₓ

variable [CommSemiringₓ R] [∀ i, AddCommMonoidₓ (M₁ i)] [AddCommMonoidₓ M₂] [∀ i, Module R (M₁ i)] [Module R M₂]

/-- When `ι` is finite, multilinear maps on `R^ι` with values in `M₂` are in bijection with `M₂`,
as such a multilinear map is completely determined by its value on the constant vector made of ones.
We register this bijection as a linear equivalence in `multilinear_map.pi_ring_equiv`. -/
protected def piRingEquiv [Fintype ι] : M₂ ≃ₗ[R] MultilinearMap R (fun i : ι => R) M₂ where
  toFun := fun z => MultilinearMap.mkPiRing R ι z
  invFun := fun f => f fun i => 1
  map_add' := fun z z' => by
    ext m
    simp [← smul_add]
  map_smul' := fun c z => by
    ext m
    simp [← smul_smul, ← mul_comm]
  left_inv := fun z => by
    simp
  right_inv := fun f => f.mk_pi_ring_apply_one_eq_self

end CommSemiringₓ

end MultilinearMap

section Currying

/-!
### Currying

We associate to a multilinear map in `n+1` variables (i.e., based on `fin n.succ`) two
curried functions, named `f.curry_left` (which is a linear map on `E 0` taking values
in multilinear maps in `n` variables) and `f.curry_right` (wich is a multilinear map in `n`
variables taking values in linear maps on `E 0`). In both constructions, the variable that is
singled out is `0`, to take advantage of the operations `cons` and `tail` on `fin n`.
The inverse operations are called `uncurry_left` and `uncurry_right`.

We also register linear equiv versions of these correspondences, in
`multilinear_curry_left_equiv` and `multilinear_curry_right_equiv`.
-/


open MultilinearMap

variable {R M M₂} [CommSemiringₓ R] [∀ i, AddCommMonoidₓ (M i)] [AddCommMonoidₓ M'] [AddCommMonoidₓ M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

/-! #### Left currying -/


/-- Given a linear map `f` from `M 0` to multilinear maps on `n` variables,
construct the corresponding multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (m 0) (tail m)`-/
def LinearMap.uncurryLeft (f : M 0 →ₗ[R] MultilinearMap R (fun i : Finₓ n => M i.succ) M₂) : MultilinearMap R M M₂ where
  toFun := fun m => f (m 0) (tail m)
  map_add' := fun m i x y => by
    by_cases' h : i = 0
    · subst i
      rw [update_same, update_same, update_same, f.map_add, add_apply, tail_update_zero, tail_update_zero,
        tail_update_zero]
      
    · rw [update_noteq (Ne.symm h), update_noteq (Ne.symm h), update_noteq (Ne.symm h)]
      revert x y
      rw [← succ_pred i h]
      intro x y
      rw [tail_update_succ, MultilinearMap.map_add, tail_update_succ, tail_update_succ]
      
  map_smul' := fun m i c x => by
    by_cases' h : i = 0
    · subst i
      rw [update_same, update_same, tail_update_zero, tail_update_zero, ← smul_apply, f.map_smul]
      
    · rw [update_noteq (Ne.symm h), update_noteq (Ne.symm h)]
      revert x
      rw [← succ_pred i h]
      intro x
      rw [tail_update_succ, tail_update_succ, MultilinearMap.map_smul]
      

@[simp]
theorem LinearMap.uncurry_left_apply (f : M 0 →ₗ[R] MultilinearMap R (fun i : Finₓ n => M i.succ) M₂) (m : ∀ i, M i) :
    f.uncurryLeft m = f (m 0) (tail m) :=
  rfl

/-- Given a multilinear map `f` in `n+1` variables, split the first variable to obtain
a linear map into multilinear maps in `n` variables, given by `x ↦ (m ↦ f (cons x m))`. -/
def MultilinearMap.curryLeft (f : MultilinearMap R M M₂) :
    M 0 →ₗ[R] MultilinearMap R (fun i : Finₓ n => M i.succ) M₂ where
  toFun := fun x =>
    { toFun := fun m => f (cons x m),
      map_add' := fun m i y y' => by
        simp ,
      map_smul' := fun m i y c => by
        simp }
  map_add' := fun x y => by
    ext m
    exact cons_add f m x y
  map_smul' := fun c x => by
    ext m
    exact cons_smul f m c x

@[simp]
theorem MultilinearMap.curry_left_apply (f : MultilinearMap R M M₂) (x : M 0) (m : ∀ i : Finₓ n, M i.succ) :
    f.curryLeft x m = f (cons x m) :=
  rfl

@[simp]
theorem LinearMap.curry_uncurry_left (f : M 0 →ₗ[R] MultilinearMap R (fun i : Finₓ n => M i.succ) M₂) :
    f.uncurryLeft.curryLeft = f := by
  ext m x
  simp only [← tail_cons, ← LinearMap.uncurry_left_apply, ← MultilinearMap.curry_left_apply]
  rw [cons_zero]

@[simp]
theorem MultilinearMap.uncurry_curry_left (f : MultilinearMap R M M₂) : f.curryLeft.uncurryLeft = f := by
  ext m
  simp

variable (R M M₂)

/-- The space of multilinear maps on `Π(i : fin (n+1)), M i` is canonically isomorphic to
the space of linear maps from `M 0` to the space of multilinear maps on
`Π(i : fin n), M i.succ `, by separating the first variable. We register this isomorphism as a
linear isomorphism in `multilinear_curry_left_equiv R M M₂`.

The direct and inverse maps are given by `f.uncurry_left` and `f.curry_left`. Use these
unless you need the full framework of linear equivs. -/
def multilinearCurryLeftEquiv :
    (M 0 →ₗ[R] MultilinearMap R (fun i : Finₓ n => M i.succ) M₂) ≃ₗ[R] MultilinearMap R M M₂ where
  toFun := LinearMap.uncurryLeft
  map_add' := fun f₁ f₂ => by
    ext m
    rfl
  map_smul' := fun c f => by
    ext m
    rfl
  invFun := MultilinearMap.curryLeft
  left_inv := LinearMap.curry_uncurry_left
  right_inv := MultilinearMap.uncurry_curry_left

variable {R M M₂}

/-! #### Right currying -/


/-- Given a multilinear map `f` in `n` variables to the space of linear maps from `M (last n)` to
`M₂`, construct the corresponding multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (init m) (m (last n))`-/
def MultilinearMap.uncurryRight (f : MultilinearMap R (fun i : Finₓ n => M i.cast_succ) (M (last n) →ₗ[R] M₂)) :
    MultilinearMap R M M₂ where
  toFun := fun m => f (init m) (m (last n))
  map_add' := fun m i x y => by
    by_cases' h : i.val < n
    · have : last n ≠ i := Ne.symm (ne_of_ltₓ h)
      rw [update_noteq this, update_noteq this, update_noteq this]
      revert x y
      rw [(cast_succ_cast_lt i h).symm]
      intro x y
      rw [init_update_cast_succ, MultilinearMap.map_add, init_update_cast_succ, init_update_cast_succ,
        LinearMap.add_apply]
      
    · revert x y
      rw [eq_last_of_not_lt h]
      intro x y
      rw [init_update_last, init_update_last, init_update_last, update_same, update_same, update_same,
        LinearMap.map_add]
      
  map_smul' := fun m i c x => by
    by_cases' h : i.val < n
    · have : last n ≠ i := Ne.symm (ne_of_ltₓ h)
      rw [update_noteq this, update_noteq this]
      revert x
      rw [(cast_succ_cast_lt i h).symm]
      intro x
      rw [init_update_cast_succ, init_update_cast_succ, MultilinearMap.map_smul, LinearMap.smul_apply]
      
    · revert x
      rw [eq_last_of_not_lt h]
      intro x
      rw [update_same, update_same, init_update_last, init_update_last, map_smul]
      

@[simp]
theorem MultilinearMap.uncurry_right_apply
    (f : MultilinearMap R (fun i : Finₓ n => M i.cast_succ) (M (last n) →ₗ[R] M₂)) (m : ∀ i, M i) :
    f.uncurryRight m = f (init m) (m (last n)) :=
  rfl

/-- Given a multilinear map `f` in `n+1` variables, split the last variable to obtain
a multilinear map in `n` variables taking values in linear maps from `M (last n)` to `M₂`, given by
`m ↦ (x ↦ f (snoc m x))`. -/
def MultilinearMap.curryRight (f : MultilinearMap R M M₂) :
    MultilinearMap R (fun i : Finₓ n => M (Finₓ.castSucc i)) (M (last n) →ₗ[R] M₂) where
  toFun := fun m =>
    { toFun := fun x => f (snoc m x),
      map_add' := fun x y => by
        rw [f.snoc_add],
      map_smul' := fun c x => by
        simp only [← f.snoc_smul, ← RingHom.id_apply] }
  map_add' := fun m i x y => by
    ext z
    change f (snoc (update m i (x + y)) z) = f (snoc (update m i x) z) + f (snoc (update m i y) z)
    rw [snoc_update, snoc_update, snoc_update, f.map_add]
  map_smul' := fun m i c x => by
    ext z
    change f (snoc (update m i (c • x)) z) = c • f (snoc (update m i x) z)
    rw [snoc_update, snoc_update, f.map_smul]

@[simp]
theorem MultilinearMap.curry_right_apply (f : MultilinearMap R M M₂) (m : ∀ i : Finₓ n, M i.cast_succ)
    (x : M (last n)) : f.curryRight m x = f (snoc m x) :=
  rfl

@[simp]
theorem MultilinearMap.curry_uncurry_right
    (f : MultilinearMap R (fun i : Finₓ n => M i.cast_succ) (M (last n) →ₗ[R] M₂)) : f.uncurryRight.curryRight = f := by
  ext m x
  simp only [← snoc_last, ← MultilinearMap.curry_right_apply, ← MultilinearMap.uncurry_right_apply]
  rw [init_snoc]

@[simp]
theorem MultilinearMap.uncurry_curry_right (f : MultilinearMap R M M₂) : f.curryRight.uncurryRight = f := by
  ext m
  simp

variable (R M M₂)

/-- The space of multilinear maps on `Π(i : fin (n+1)), M i` is canonically isomorphic to
the space of linear maps from the space of multilinear maps on `Π(i : fin n), M i.cast_succ` to the
space of linear maps on `M (last n)`, by separating the last variable. We register this isomorphism
as a linear isomorphism in `multilinear_curry_right_equiv R M M₂`.

The direct and inverse maps are given by `f.uncurry_right` and `f.curry_right`. Use these
unless you need the full framework of linear equivs. -/
def multilinearCurryRightEquiv :
    MultilinearMap R (fun i : Finₓ n => M i.cast_succ) (M (last n) →ₗ[R] M₂) ≃ₗ[R] MultilinearMap R M M₂ where
  toFun := MultilinearMap.uncurryRight
  map_add' := fun f₁ f₂ => by
    ext m
    rfl
  map_smul' := fun c f => by
    ext m
    rw [smul_apply]
    rfl
  invFun := MultilinearMap.curryRight
  left_inv := MultilinearMap.curry_uncurry_right
  right_inv := MultilinearMap.uncurry_curry_right

namespace MultilinearMap

variable {ι' : Type _} [DecidableEq ι'] [DecidableEq (Sum ι ι')] {R M₂}

/-- A multilinear map on `Π i : ι ⊕ ι', M'` defines a multilinear map on `Π i : ι, M'`
taking values in the space of multilinear maps on `Π i : ι', M'`. -/
def currySum (f : MultilinearMap R (fun x : Sum ι ι' => M') M₂) :
    MultilinearMap R (fun x : ι => M') (MultilinearMap R (fun x : ι' => M') M₂) where
  toFun := fun u =>
    { toFun := fun v => f (Sum.elim u v),
      map_add' := fun v i x y => by
        simp only [Sum.update_elim_inr, ← f.map_add],
      map_smul' := fun v i c x => by
        simp only [Sum.update_elim_inr, ← f.map_smul] }
  map_add' := fun u i x y =>
    ext fun v => by
      simp only [← MultilinearMap.coe_mk, ← add_apply, Sum.update_elim_inl, ← f.map_add]
  map_smul' := fun u i c x =>
    ext fun v => by
      simp only [← MultilinearMap.coe_mk, ← smul_apply, Sum.update_elim_inl, ← f.map_smul]

@[simp]
theorem curry_sum_apply (f : MultilinearMap R (fun x : Sum ι ι' => M') M₂) (u : ι → M') (v : ι' → M') :
    f.currySum u v = f (Sum.elim u v) :=
  rfl

/-- A multilinear map on `Π i : ι, M'` taking values in the space of multilinear maps
on `Π i : ι', M'` defines a multilinear map on `Π i : ι ⊕ ι', M'`. -/
def uncurrySum (f : MultilinearMap R (fun x : ι => M') (MultilinearMap R (fun x : ι' => M') M₂)) :
    MultilinearMap R (fun x : Sum ι ι' => M') M₂ where
  toFun := fun u => f (u ∘ Sum.inl) (u ∘ Sum.inr)
  map_add' := fun u i x y => by
    cases i <;>
      simp only [← MultilinearMap.map_add, ← add_apply, ← Sum.update_inl_comp_inl, ← Sum.update_inl_comp_inr, ←
        Sum.update_inr_comp_inl, ← Sum.update_inr_comp_inr]
  map_smul' := fun u i c x => by
    cases i <;>
      simp only [← MultilinearMap.map_smul, ← smul_apply, ← Sum.update_inl_comp_inl, ← Sum.update_inl_comp_inr, ←
        Sum.update_inr_comp_inl, ← Sum.update_inr_comp_inr]

@[simp]
theorem uncurry_sum_aux_apply (f : MultilinearMap R (fun x : ι => M') (MultilinearMap R (fun x : ι' => M') M₂))
    (u : Sum ι ι' → M') : f.uncurrySum u = f (u ∘ Sum.inl) (u ∘ Sum.inr) :=
  rfl

variable (ι ι' R M₂ M')

/-- Linear equivalence between the space of multilinear maps on `Π i : ι ⊕ ι', M'` and the space
of multilinear maps on `Π i : ι, M'` taking values in the space of multilinear maps
on `Π i : ι', M'`. -/
def currySumEquiv :
    MultilinearMap R (fun x : Sum ι ι' => M') M₂ ≃ₗ[R]
      MultilinearMap R (fun x : ι => M') (MultilinearMap R (fun x : ι' => M') M₂) where
  toFun := currySum
  invFun := uncurrySum
  left_inv := fun f =>
    ext fun u => by
      simp
  right_inv := fun f => by
    ext
    simp
  map_add' := fun f g => by
    ext
    rfl
  map_smul' := fun c f => by
    ext
    rfl

variable {ι ι' R M₂ M'}

@[simp]
theorem coe_curry_sum_equiv : ⇑(currySumEquiv R ι M₂ M' ι') = curry_sum :=
  rfl

@[simp]
theorem coe_curr_sum_equiv_symm : ⇑(currySumEquiv R ι M₂ M' ι').symm = uncurry_sum :=
  rfl

variable (R M₂ M')

/-- If `s : finset (fin n)` is a finite set of cardinality `k` and its complement has cardinality
`l`, then the space of multilinear maps on `λ i : fin n, M'` is isomorphic to the space of
multilinear maps on `λ i : fin k, M'` taking values in the space of multilinear maps
on `λ i : fin l, M'`. -/
def curryFinFinset {k l n : ℕ} {s : Finset (Finₓ n)} (hk : s.card = k) (hl : sᶜ.card = l) :
    MultilinearMap R (fun x : Finₓ n => M') M₂ ≃ₗ[R]
      MultilinearMap R (fun x : Finₓ k => M') (MultilinearMap R (fun x : Finₓ l => M') M₂) :=
  (domDomCongrLinearEquiv M' M₂ R R (finSumEquivOfFinset hk hl).symm).trans (currySumEquiv R (Finₓ k) M₂ M' (Finₓ l))

variable {R M₂ M'}

@[simp]
theorem curry_fin_finset_apply {k l n : ℕ} {s : Finset (Finₓ n)} (hk : s.card = k) (hl : sᶜ.card = l)
    (f : MultilinearMap R (fun x : Finₓ n => M') M₂) (mk : Finₓ k → M') (ml : Finₓ l → M') :
    curryFinFinset R M₂ M' hk hl f mk ml = f fun i => Sum.elim mk ml ((finSumEquivOfFinset hk hl).symm i) :=
  rfl

@[simp]
theorem curry_fin_finset_symm_apply {k l n : ℕ} {s : Finset (Finₓ n)} (hk : s.card = k) (hl : sᶜ.card = l)
    (f : MultilinearMap R (fun x : Finₓ k => M') (MultilinearMap R (fun x : Finₓ l => M') M₂)) (m : Finₓ n → M') :
    (curryFinFinset R M₂ M' hk hl).symm f m =
      f (fun i => m <| finSumEquivOfFinset hk hl (Sum.inl i)) fun i => m <| finSumEquivOfFinset hk hl (Sum.inr i) :=
  rfl

@[simp]
theorem curry_fin_finset_symm_apply_piecewise_const {k l n : ℕ} {s : Finset (Finₓ n)} (hk : s.card = k)
    (hl : sᶜ.card = l) (f : MultilinearMap R (fun x : Finₓ k => M') (MultilinearMap R (fun x : Finₓ l => M') M₂))
    (x y : M') :
    (curryFinFinset R M₂ M' hk hl).symm f (s.piecewise (fun _ => x) fun _ => y) = f (fun _ => x) fun _ => y := by
  rw [curry_fin_finset_symm_apply]
  congr
  · ext i
    rw [fin_sum_equiv_of_finset_inl, Finset.piecewise_eq_of_mem]
    apply Finset.order_emb_of_fin_mem
    
  · ext i
    rw [fin_sum_equiv_of_finset_inr, Finset.piecewise_eq_of_not_mem]
    exact Finset.mem_compl.1 (Finset.order_emb_of_fin_mem _ _ _)
    

@[simp]
theorem curry_fin_finset_symm_apply_const {k l n : ℕ} {s : Finset (Finₓ n)} (hk : s.card = k) (hl : sᶜ.card = l)
    (f : MultilinearMap R (fun x : Finₓ k => M') (MultilinearMap R (fun x : Finₓ l => M') M₂)) (x : M') :
    ((curryFinFinset R M₂ M' hk hl).symm f fun _ => x) = f (fun _ => x) fun _ => x :=
  rfl

@[simp]
theorem curry_fin_finset_apply_const {k l n : ℕ} {s : Finset (Finₓ n)} (hk : s.card = k) (hl : sᶜ.card = l)
    (f : MultilinearMap R (fun x : Finₓ n => M') M₂) (x y : M') :
    (curryFinFinset R M₂ M' hk hl f (fun _ => x) fun _ => y) = f (s.piecewise (fun _ => x) fun _ => y) := by
  refine' (curry_fin_finset_symm_apply_piecewise_const hk hl _ _ _).symm.trans _
  -- `rw` fails
  rw [LinearEquiv.symm_apply_apply]

end MultilinearMap

end Currying

namespace MultilinearMap

section Submodule

variable {R M M₂} [Ringₓ R] [∀ i, AddCommMonoidₓ (M₁ i)] [AddCommMonoidₓ M'] [AddCommMonoidₓ M₂] [∀ i, Module R (M₁ i)]
  [Module R M'] [Module R M₂]

/-- The pushforward of an indexed collection of submodule `p i ⊆ M₁ i` by `f : M₁ → M₂`.

Note that this is not a submodule - it is not closed under addition. -/
def map [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : ∀ i, Submodule R (M₁ i)) : SubMulAction R M₂ where
  Carrier := f '' { v | ∀ i, v i ∈ p i }
  smul_mem' := fun c _ ⟨x, hx, hf⟩ => by
    let ⟨i⟩ := ‹Nonempty ι›
    refine' ⟨update x i (c • x i), fun j => if hij : j = i then _ else _, hf ▸ _⟩
    · rw [hij, update_same]
      exact (p i).smul_mem _ (hx i)
      
    · rw [update_noteq hij]
      exact hx j
      
    · rw [f.map_smul, update_eq_self]
      

/-- The map is always nonempty. This lemma is needed to apply `sub_mul_action.zero_mem`. -/
theorem map_nonempty [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : ∀ i, Submodule R (M₁ i)) :
    (map f p : Set M₂).Nonempty :=
  ⟨f 0, 0, fun i => (p i).zero_mem, rfl⟩

/-- The range of a multilinear map, closed under scalar multiplication. -/
def range [Nonempty ι] (f : MultilinearMap R M₁ M₂) : SubMulAction R M₂ :=
  f.map fun i => ⊤

end Submodule

end MultilinearMap


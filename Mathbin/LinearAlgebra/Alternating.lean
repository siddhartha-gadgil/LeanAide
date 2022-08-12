/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Zhangir Azerbayev
-/
import Mathbin.GroupTheory.GroupAction.Quotient
import Mathbin.GroupTheory.Perm.Sign
import Mathbin.GroupTheory.Perm.Subgroup
import Mathbin.LinearAlgebra.LinearIndependent
import Mathbin.LinearAlgebra.Multilinear.Basis
import Mathbin.LinearAlgebra.Multilinear.TensorProduct
import Mathbin.Logic.Equiv.Fin

/-!
# Alternating Maps

We construct the bundled function `alternating_map`, which extends `multilinear_map` with all the
arguments of the same type.

## Main definitions
* `alternating_map R M N ι` is the space of `R`-linear alternating maps from `ι → M` to `N`.
* `f.map_eq_zero_of_eq` expresses that `f` is zero when two inputs are equal.
* `f.map_swap` expresses that `f` is negated when two inputs are swapped.
* `f.map_perm` expresses how `f` varies by a sign change under a permutation of its inputs.
* An `add_comm_monoid`, `add_comm_group`, and `module` structure over `alternating_map`s that
  matches the definitions over `multilinear_map`s.
* `multilinear_map.dom_dom_congr`, for permutating the elements within a family.
* `multilinear_map.alternatization`, which makes an alternating map out of a non-alternating one.
* `alternating_map.dom_coprod`, which behaves as a product between two alternating maps.
* `alternating_map.curry_left`, for binding the leftmost argument of an alternating map indexed
  by `fin n.succ`.

## Implementation notes
`alternating_map` is defined in terms of `map_eq_zero_of_eq`, as this is easier to work with than
using `map_swap` as a definition, and does not require `has_neg N`.

`alternating_map`s are provided with a coercion to `multilinear_map`, along with a set of
`norm_cast` lemmas that act on the algebraic structure:

* `alternating_map.coe_add`
* `alternating_map.coe_zero`
* `alternating_map.coe_sub`
* `alternating_map.coe_neg`
* `alternating_map.coe_smul`
-/


-- semiring / add_comm_monoid
variable {R : Type _} [Semiringₓ R]

variable {M : Type _} [AddCommMonoidₓ M] [Module R M]

variable {N : Type _} [AddCommMonoidₓ N] [Module R N]

-- semiring / add_comm_group
variable {M' : Type _} [AddCommGroupₓ M'] [Module R M']

variable {N' : Type _} [AddCommGroupₓ N'] [Module R N']

variable {ι ι' ι'' : Type _} [DecidableEq ι] [DecidableEq ι'] [DecidableEq ι'']

section

variable (R M N ι)

/-- An alternating map is a multilinear map that vanishes when two of its arguments are equal.
-/
structure AlternatingMap extends MultilinearMap R (fun i : ι => M) N where
  map_eq_zero_of_eq' : ∀ (v : ι → M) (i j : ι) (h : v i = v j) (hij : i ≠ j), to_fun v = 0

end

/-- The multilinear map associated to an alternating map -/
add_decl_doc AlternatingMap.toMultilinearMap

namespace AlternatingMap

variable (f f' : AlternatingMap R M N ι)

variable (g g₂ : AlternatingMap R M N' ι)

variable (g' : AlternatingMap R M' N' ι)

variable (v : ι → M) (v' : ι → M')

open Function

/-! Basic coercion simp lemmas, largely copied from `ring_hom` and `multilinear_map` -/


section Coercions

instance : CoeFun (AlternatingMap R M N ι) fun _ => (ι → M) → N :=
  ⟨fun x => x.toFun⟩

initialize_simps_projections AlternatingMap (toFun → apply)

@[simp]
theorem to_fun_eq_coe : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk (f : (ι → M) → N) (h₁ h₂ h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ : AlternatingMap R M N ι) = f :=
  rfl

theorem congr_fun {f g : AlternatingMap R M N ι} (h : f = g) (x : ι → M) : f x = g x :=
  congr_arg (fun h : AlternatingMap R M N ι => h x) h

theorem congr_arg (f : AlternatingMap R M N ι) {x y : ι → M} (h : x = y) : f x = f y :=
  congr_arg (fun x : ι → M => f x) h

theorem coe_injective : Injective (coeFn : AlternatingMap R M N ι → (ι → M) → N) := fun f g h => by
  cases f
  cases g
  cases h
  rfl

@[simp, norm_cast]
theorem coe_inj {f g : AlternatingMap R M N ι} : (f : (ι → M) → N) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
theorem ext {f f' : AlternatingMap R M N ι} (H : ∀ x, f x = f' x) : f = f' :=
  coe_injective (funext H)

theorem ext_iff {f g : AlternatingMap R M N ι} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩

instance : Coe (AlternatingMap R M N ι) (MultilinearMap R (fun i : ι => M) N) :=
  ⟨fun x => x.toMultilinearMap⟩

@[simp, norm_cast]
theorem coe_multilinear_map : ⇑(f : MultilinearMap R (fun i : ι => M) N) = f :=
  rfl

theorem coe_multilinear_map_injective :
    Function.Injective (coe : AlternatingMap R M N ι → MultilinearMap R (fun i : ι => M) N) := fun x y h =>
  ext <| MultilinearMap.congr_fun h

@[simp]
theorem to_multilinear_map_eq_coe : f.toMultilinearMap = f :=
  rfl

@[simp]
theorem coe_multilinear_map_mk (f : (ι → M) → N) (h₁ h₂ h₃) :
    ((⟨f, h₁, h₂, h₃⟩ : AlternatingMap R M N ι) : MultilinearMap R (fun i : ι => M) N) = ⟨f, h₁, h₂⟩ :=
  rfl

end Coercions

/-!
### Simp-normal forms of the structure fields

These are expressed in terms of `⇑f` instead of `f.to_fun`.
-/


@[simp]
theorem map_add (i : ι) (x y : M) : f (update v i (x + y)) = f (update v i x) + f (update v i y) :=
  f.toMultilinearMap.map_add' v i x y

@[simp]
theorem map_sub (i : ι) (x y : M') : g' (update v' i (x - y)) = g' (update v' i x) - g' (update v' i y) :=
  g'.toMultilinearMap.map_sub v' i x y

@[simp]
theorem map_neg (i : ι) (x : M') : g' (update v' i (-x)) = -g' (update v' i x) :=
  g'.toMultilinearMap.map_neg v' i x

@[simp]
theorem map_smul (i : ι) (r : R) (x : M) : f (update v i (r • x)) = r • f (update v i x) :=
  f.toMultilinearMap.map_smul' v i r x

@[simp]
theorem map_eq_zero_of_eq (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) : f v = 0 :=
  f.map_eq_zero_of_eq' v i j h hij

theorem map_coord_zero {m : ι → M} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h

@[simp]
theorem map_update_zero (m : ι → M) (i : ι) : f (update m i 0) = 0 :=
  f.toMultilinearMap.map_update_zero m i

@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero

theorem map_eq_zero_of_not_injective (v : ι → M) (hv : ¬Function.Injective v) : f v = 0 := by
  rw [Function.Injective] at hv
  push_neg  at hv
  rcases hv with ⟨i₁, i₂, heq, hne⟩
  exact f.map_eq_zero_of_eq v HEq hne

/-!
### Algebraic structure inherited from `multilinear_map`

`alternating_map` carries the same `add_comm_monoid`, `add_comm_group`, and `module` structure
as `multilinear_map`
-/


section HasSmul

variable {S : Type _} [Monoidₓ S] [DistribMulAction S N] [SmulCommClass R S N]

instance : HasSmul S (AlternatingMap R M N ι) :=
  ⟨fun c f =>
    { (c • f : MultilinearMap R (fun i : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [← f.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem smul_apply (c : S) (m : ι → M) : (c • f) m = c • f m :=
  rfl

@[norm_cast]
theorem coe_smul (c : S) : ((c • f : AlternatingMap R M N ι) : MultilinearMap R (fun i : ι => M) N) = c • f :=
  rfl

theorem coe_fn_smul (c : S) (f : AlternatingMap R M N ι) : ⇑(c • f) = c • f :=
  rfl

instance [DistribMulAction Sᵐᵒᵖ N] [IsCentralScalar S N] : IsCentralScalar S (AlternatingMap R M N ι) :=
  ⟨fun c f => ext fun x => op_smul_eq_smul _ _⟩

end HasSmul

instance : Add (AlternatingMap R M N ι) :=
  ⟨fun a b =>
    { (a + b : MultilinearMap R (fun i : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [← a.map_eq_zero_of_eq v h hij, ← b.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem add_apply : (f + f') v = f v + f' v :=
  rfl

@[norm_cast]
theorem coe_add : (↑(f + f') : MultilinearMap R (fun i : ι => M) N) = f + f' :=
  rfl

instance : Zero (AlternatingMap R M N ι) :=
  ⟨{ (0 : MultilinearMap R (fun i : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp }⟩

@[simp]
theorem zero_apply : (0 : AlternatingMap R M N ι) v = 0 :=
  rfl

@[norm_cast]
theorem coe_zero : ((0 : AlternatingMap R M N ι) : MultilinearMap R (fun i : ι => M) N) = 0 :=
  rfl

instance : Inhabited (AlternatingMap R M N ι) :=
  ⟨0⟩

instance : AddCommMonoidₓ (AlternatingMap R M N ι) :=
  coe_injective.AddCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => coe_fn_smul _ _

instance : Neg (AlternatingMap R M N' ι) :=
  ⟨fun f =>
    { -(f : MultilinearMap R (fun i : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [← f.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem neg_apply (m : ι → M) : (-g) m = -g m :=
  rfl

@[norm_cast]
theorem coe_neg : ((-g : AlternatingMap R M N' ι) : MultilinearMap R (fun i : ι => M) N') = -g :=
  rfl

instance : Sub (AlternatingMap R M N' ι) :=
  ⟨fun f g =>
    { (f - g : MultilinearMap R (fun i : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [← f.map_eq_zero_of_eq v h hij, ← g.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem sub_apply (m : ι → M) : (g - g₂) m = g m - g₂ m :=
  rfl

@[norm_cast]
theorem coe_sub : (↑(g - g₂) : MultilinearMap R (fun i : ι => M) N') = g - g₂ :=
  rfl

instance : AddCommGroupₓ (AlternatingMap R M N' ι) :=
  coe_injective.AddCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => coe_fn_smul _ _)
    fun _ _ => coe_fn_smul _ _

section DistribMulAction

variable {S : Type _} [Monoidₓ S] [DistribMulAction S N] [SmulCommClass R S N]

instance : DistribMulAction S (AlternatingMap R M N ι) where
  one_smul := fun f => ext fun x => one_smul _ _
  mul_smul := fun c₁ c₂ f => ext fun x => mul_smul _ _ _
  smul_zero := fun r => ext fun x => smul_zero _
  smul_add := fun r f₁ f₂ => ext fun x => smul_add _ _ _

end DistribMulAction

section Module

variable {S : Type _} [Semiringₓ S] [Module S N] [SmulCommClass R S N]

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
instance : Module S (AlternatingMap R M N ι) where
  add_smul := fun r₁ r₂ f => ext fun x => add_smul _ _ _
  zero_smul := fun f => ext fun x => zero_smul _ _

instance [NoZeroSmulDivisors S N] : NoZeroSmulDivisors S (AlternatingMap R M N ι) :=
  coe_injective.NoZeroSmulDivisors _ rfl coe_fn_smul

end Module

section

variable (R M)

/-- The evaluation map from `ι → M` to `M` at a given `i` is alternating when `ι` is subsingleton.
-/
@[simps]
def ofSubsingleton [Subsingleton ι] (i : ι) : AlternatingMap R M M ι :=
  { MultilinearMap.ofSubsingleton R M i with toFun := Function.eval i,
    map_eq_zero_of_eq' := fun v i j hv hij => (hij <| Subsingleton.elimₓ _ _).elim }

/-- The constant map is alternating when `ι` is empty. -/
@[simps (config := { fullyApplied := false })]
def constOfIsEmpty [IsEmpty ι] (m : N) : AlternatingMap R M N ι :=
  { MultilinearMap.constOfIsEmpty R m with toFun := Function.const _ m, map_eq_zero_of_eq' := fun v => isEmptyElim }

end

/-- Restrict the codomain of an alternating map to a submodule. -/
@[simps]
def codRestrict (f : AlternatingMap R M N ι) (p : Submodule R N) (h : ∀ v, f v ∈ p) : AlternatingMap R M p ι :=
  { f.toMultilinearMap.codRestrict p h with toFun := fun v => ⟨f v, h v⟩,
    map_eq_zero_of_eq' := fun v i j hv hij => Subtype.ext <| map_eq_zero_of_eq _ _ hv hij }

end AlternatingMap

/-!
### Composition with linear maps
-/


namespace LinearMap

variable {N₂ : Type _} [AddCommMonoidₓ N₂] [Module R N₂]

/-- Composing a alternating map with a linear map on the left gives again an alternating map. -/
def compAlternatingMap (g : N →ₗ[R] N₂) : AlternatingMap R M N ι →+ AlternatingMap R M N₂ ι where
  toFun := fun f =>
    { g.compMultilinearMap (f : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [← f.map_eq_zero_of_eq v h hij] }
  map_zero' := by
    ext
    simp
  map_add' := fun a b => by
    ext
    simp

@[simp]
theorem coe_comp_alternating_map (g : N →ₗ[R] N₂) (f : AlternatingMap R M N ι) : ⇑(g.compAlternatingMap f) = g ∘ f :=
  rfl

@[simp]
theorem comp_alternating_map_apply (g : N →ₗ[R] N₂) (f : AlternatingMap R M N ι) (m : ι → M) :
    g.compAlternatingMap f m = g (f m) :=
  rfl

@[simp]
theorem subtype_comp_alternating_map_cod_restrict (f : AlternatingMap R M N ι) (p : Submodule R N) (h) :
    p.Subtype.compAlternatingMap (f.codRestrict p h) = f :=
  AlternatingMap.ext fun v => rfl

@[simp]
theorem comp_alternating_map_cod_restrict (g : N →ₗ[R] N₂) (f : AlternatingMap R M N ι) (p : Submodule R N₂) (h) :
    (g.codRestrict p h).compAlternatingMap f = (g.compAlternatingMap f).codRestrict p fun v => h (f v) :=
  AlternatingMap.ext fun v => rfl

end LinearMap

namespace AlternatingMap

variable {M₂ : Type _} [AddCommMonoidₓ M₂] [Module R M₂]

variable {M₃ : Type _} [AddCommMonoidₓ M₃] [Module R M₃]

/-- Composing a alternating map with the same linear map on each argument gives again an
alternating map. -/
def compLinearMap (f : AlternatingMap R M N ι) (g : M₂ →ₗ[R] M) : AlternatingMap R M₂ N ι :=
  { (f : MultilinearMap R (fun _ : ι => M) N).compLinearMap fun _ => g with
    map_eq_zero_of_eq' := fun v i j h hij => f.map_eq_zero_of_eq _ (LinearMap.congr_arg h) hij }

theorem coe_comp_linear_map (f : AlternatingMap R M N ι) (g : M₂ →ₗ[R] M) : ⇑(f.compLinearMap g) = f ∘ (· ∘ ·) g :=
  rfl

@[simp]
theorem comp_linear_map_apply (f : AlternatingMap R M N ι) (g : M₂ →ₗ[R] M) (v : ι → M₂) :
    f.compLinearMap g v = f fun i => g (v i) :=
  rfl

/-- Composing an alternating map twice with the same linear map in each argument is
the same as composing with their composition. -/
theorem comp_linear_map_assoc (f : AlternatingMap R M N ι) (g₁ : M₂ →ₗ[R] M) (g₂ : M₃ →ₗ[R] M₂) :
    (f.compLinearMap g₁).compLinearMap g₂ = f.compLinearMap (g₁ ∘ₗ g₂) :=
  rfl

@[simp]
theorem zero_comp_linear_map (g : M₂ →ₗ[R] M) : (0 : AlternatingMap R M N ι).compLinearMap g = 0 := by
  ext
  simp only [← comp_linear_map_apply, ← zero_apply]

@[simp]
theorem add_comp_linear_map (f₁ f₂ : AlternatingMap R M N ι) (g : M₂ →ₗ[R] M) :
    (f₁ + f₂).compLinearMap g = f₁.compLinearMap g + f₂.compLinearMap g := by
  ext
  simp only [← comp_linear_map_apply, ← add_apply]

@[simp]
theorem comp_linear_map_zero [Nonempty ι] (f : AlternatingMap R M N ι) : f.compLinearMap (0 : M₂ →ₗ[R] M) = 0 := by
  ext
  simp_rw [comp_linear_map_apply, LinearMap.zero_apply, ← Pi.zero_def, map_zero, zero_apply]

/-- Composing an alternating map with the identity linear map in each argument. -/
@[simp]
theorem comp_linear_map_id (f : AlternatingMap R M N ι) : f.compLinearMap LinearMap.id = f :=
  ext fun _ => rfl

/-- Composing with a surjective linear map is injective. -/
theorem comp_linear_map_injective (f : M₂ →ₗ[R] M) (hf : Function.Surjective f) :
    Function.Injective fun g : AlternatingMap R M N ι => g.compLinearMap f := fun g₁ g₂ h =>
  ext fun x => by
    simpa [← Function.surj_inv_eq hf] using ext_iff.mp h (Function.surjInv hf ∘ x)

theorem comp_linear_map_inj (f : M₂ →ₗ[R] M) (hf : Function.Surjective f) (g₁ g₂ : AlternatingMap R M N ι) :
    g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂ :=
  (comp_linear_map_injective _ hf).eq_iff

section DomLcongr

variable (ι R N) (S : Type _) [Semiringₓ S] [Module S N] [SmulCommClass R S N]

/-- Construct a linear equivalence between maps from a linear equivalence between domains. -/
@[simps apply]
def domLcongr (e : M ≃ₗ[R] M₂) : AlternatingMap R M N ι ≃ₗ[S] AlternatingMap R M₂ N ι where
  toFun := fun f => f.compLinearMap e.symm
  invFun := fun g => g.compLinearMap e
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  left_inv := fun f => AlternatingMap.ext fun v => f.congr_arg <| funext fun i => e.symm_apply_apply _
  right_inv := fun f => AlternatingMap.ext fun v => f.congr_arg <| funext fun i => e.apply_symm_apply _

@[simp]
theorem dom_lcongr_refl : domLcongr R N ι S (LinearEquiv.refl R M) = LinearEquiv.refl S _ :=
  LinearEquiv.ext fun _ => AlternatingMap.ext fun v => rfl

@[simp]
theorem dom_lcongr_symm (e : M ≃ₗ[R] M₂) : (domLcongr R N ι S e).symm = domLcongr R N ι S e.symm :=
  rfl

theorem dom_lcongr_trans (e : M ≃ₗ[R] M₂) (f : M₂ ≃ₗ[R] M₃) :
    (domLcongr R N ι S e).trans (domLcongr R N ι S f) = domLcongr R N ι S (e.trans f) :=
  rfl

end DomLcongr

/-- Composing an alternating map with the same linear equiv on each argument gives the zero map
if and only if the alternating map is the zero map. -/
@[simp]
theorem comp_linear_equiv_eq_zero_iff (f : AlternatingMap R M N ι) (g : M₂ ≃ₗ[R] M) :
    f.compLinearMap (g : M₂ →ₗ[R] M) = 0 ↔ f = 0 :=
  (domLcongr R N ι ℕ g.symm).map_eq_zero_iff

variable (f f' : AlternatingMap R M N ι)

variable (g g₂ : AlternatingMap R M N' ι)

variable (g' : AlternatingMap R M' N' ι)

variable (v : ι → M) (v' : ι → M')

open Function

/-!
### Other lemmas from `multilinear_map`
-/


section

open BigOperators

theorem map_update_sum {α : Type _} (t : Finset α) (i : ι) (g : α → M) (m : ι → M) :
    f (update m i (∑ a in t, g a)) = ∑ a in t, f (update m i (g a)) :=
  f.toMultilinearMap.map_update_sum t i g m

end

/-!
### Theorems specific to alternating maps

Various properties of reordered and repeated inputs which follow from
`alternating_map.map_eq_zero_of_eq`.
-/


theorem map_update_self {i j : ι} (hij : i ≠ j) : f (Function.update v i (v j)) = 0 :=
  f.map_eq_zero_of_eq _
    (by
      rw [Function.update_same, Function.update_noteq hij.symm])
    hij

theorem map_update_update {i j : ι} (hij : i ≠ j) (m : M) : f (Function.update (Function.update v i m) j m) = 0 :=
  f.map_eq_zero_of_eq _
    (by
      rw [Function.update_same, Function.update_noteq hij, Function.update_same])
    hij

theorem map_swap_add {i j : ι} (hij : i ≠ j) : f (v ∘ Equivₓ.swap i j) + f v = 0 := by
  rw [Equivₓ.comp_swap_eq_update]
  convert f.map_update_update v hij (v i + v j)
  simp [← f.map_update_self _ hij, ← f.map_update_self _ hij.symm, ← Function.update_comm hij (v i + v j) (v _) v, ←
    Function.update_comm hij.symm (v i) (v i) v]

theorem map_add_swap {i j : ι} (hij : i ≠ j) : f v + f (v ∘ Equivₓ.swap i j) = 0 := by
  rw [add_commₓ]
  exact f.map_swap_add v hij

theorem map_swap {i j : ι} (hij : i ≠ j) : g (v ∘ Equivₓ.swap i j) = -g v :=
  eq_neg_of_add_eq_zero_left <| g.map_swap_add v hij

theorem map_perm [Fintype ι] (v : ι → M) (σ : Equivₓ.Perm ι) : g (v ∘ σ) = σ.sign • g v := by
  apply Equivₓ.Perm.swap_induction_on' σ
  · simp
    
  · intro s x y hxy hI
    simpa [← g.map_swap (v ∘ s) hxy, ← Equivₓ.Perm.sign_swap hxy] using hI
    

theorem map_congr_perm [Fintype ι] (σ : Equivₓ.Perm ι) : g v = σ.sign • g (v ∘ σ) := by
  rw [g.map_perm, smul_smul]
  simp

section DomDomCongr

/-- Transfer the arguments to a map along an equivalence between argument indices.

This is the alternating version of `multilinear_map.dom_dom_congr`. -/
@[simps]
def domDomCongr (σ : ι ≃ ι') (f : AlternatingMap R M N ι) : AlternatingMap R M N ι' :=
  { f.toMultilinearMap.domDomCongr σ with toFun := fun v => f (v ∘ σ),
    map_eq_zero_of_eq' := fun v i j hv hij =>
      f.map_eq_zero_of_eq (v ∘ σ)
        (by
          simpa using hv)
        (σ.symm.Injective.Ne hij) }

@[simp]
theorem dom_dom_congr_refl (f : AlternatingMap R M N ι) : f.domDomCongr (Equivₓ.refl ι) = f :=
  ext fun v => rfl

theorem dom_dom_congr_trans (σ₁ : ι ≃ ι') (σ₂ : ι' ≃ ι'') (f : AlternatingMap R M N ι) :
    f.domDomCongr (σ₁.trans σ₂) = (f.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl

@[simp]
theorem dom_dom_congr_zero (σ : ι ≃ ι') : (0 : AlternatingMap R M N ι).domDomCongr σ = 0 :=
  rfl

@[simp]
theorem dom_dom_congr_add (σ : ι ≃ ι') (f g : AlternatingMap R M N ι) :
    (f + g).domDomCongr σ = f.domDomCongr σ + g.domDomCongr σ :=
  rfl

/-- `alternating_map.dom_dom_congr` as an equivalence.

This is declared separately because it does not work with dot notation. -/
@[simps apply symmApply]
def domDomCongrEquiv (σ : ι ≃ ι') : AlternatingMap R M N ι ≃+ AlternatingMap R M N ι' where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv := fun f => by
    ext
    simp [← Function.comp]
  right_inv := fun m => by
    ext
    simp [← Function.comp]
  map_add' := dom_dom_congr_add σ

/-- The results of applying `dom_dom_congr` to two maps are equal if and only if those maps are. -/
@[simp]
theorem dom_dom_congr_eq_iff (σ : ι ≃ ι') (f g : AlternatingMap R M N ι) : f.domDomCongr σ = g.domDomCongr σ ↔ f = g :=
  (domDomCongrEquiv σ : _ ≃+ AlternatingMap R M N ι').apply_eq_iff_eq

@[simp]
theorem dom_dom_congr_eq_zero_iff (σ : ι ≃ ι') (f : AlternatingMap R M N ι) : f.domDomCongr σ = 0 ↔ f = 0 :=
  (domDomCongrEquiv σ : AlternatingMap R M N ι ≃+ AlternatingMap R M N ι').map_eq_zero_iff

theorem dom_dom_congr_perm [Fintype ι] (σ : Equivₓ.Perm ι) : g.domDomCongr σ = σ.sign • g :=
  AlternatingMap.ext fun v => g.map_perm v σ

@[norm_cast]
theorem coe_dom_dom_congr (σ : ι ≃ ι') : ↑(f.domDomCongr σ) = (f : MultilinearMap R (fun _ : ι => M) N).domDomCongr σ :=
  MultilinearMap.ext fun v => rfl

end DomDomCongr

/-- If the arguments are linearly dependent then the result is `0`. -/
theorem map_linear_dependent {K : Type _} [Ringₓ K] {M : Type _} [AddCommGroupₓ M] [Module K M] {N : Type _}
    [AddCommGroupₓ N] [Module K N] [NoZeroSmulDivisors K N] (f : AlternatingMap K M N ι) (v : ι → M)
    (h : ¬LinearIndependent K v) : f v = 0 := by
  obtain ⟨s, g, h, i, hi, hz⟩ := not_linear_independent_iff.mp h
  suffices f (update v i (g i • v i)) = 0 by
    rw [f.map_smul, Function.update_eq_self, smul_eq_zero] at this
    exact Or.resolve_left this hz
  conv at h in g _ • v _ => rw [← if_t_t (i = x) (g _ • v _)]
  rw [Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, if_pos hi, Finset.sum_singleton, add_eq_zero_iff_eq_neg] at h
  rw [h, f.map_neg, f.map_update_sum, neg_eq_zero, Finset.sum_eq_zero]
  intro j hj
  obtain ⟨hij, _⟩ := finset.mem_erase.mp hj
  rw [f.map_smul, f.map_update_self _ hij.symm, smul_zero]

section Finₓ

open Finₓ

/-- A version of `multilinear_map.cons_add` for `alternating_map`. -/
theorem map_vec_cons_add {n : ℕ} (f : AlternatingMap R M N (Finₓ n.succ)) (m : Finₓ n → M) (x y : M) :
    f (Matrix.vecCons (x + y) m) = f (Matrix.vecCons x m) + f (Matrix.vecCons y m) :=
  f.toMultilinearMap.cons_add _ _ _

/-- A version of `multilinear_map.cons_smul` for `alternating_map`. -/
theorem map_vec_cons_smul {n : ℕ} (f : AlternatingMap R M N (Finₓ n.succ)) (m : Finₓ n → M) (c : R) (x : M) :
    f (Matrix.vecCons (c • x) m) = c • f (Matrix.vecCons x m) :=
  f.toMultilinearMap.cons_smul _ _ _

end Finₓ

end AlternatingMap

open BigOperators

namespace MultilinearMap

open Equivₓ

variable [Fintype ι]

private theorem alternization_map_eq_zero_of_eq_aux (m : MultilinearMap R (fun i : ι => M) N') (v : ι → M) (i j : ι)
    (i_ne_j : i ≠ j) (hv : v i = v j) : (∑ σ : Perm ι, σ.sign • m.domDomCongr σ) v = 0 := by
  rw [sum_apply]
  exact
    Finset.sum_involution (fun σ _ => swap i j * σ)
      (fun σ _ => by
        simp [← perm.sign_swap i_ne_j, ← apply_swap_eq_self hv])
      (fun σ _ _ => (not_congr swap_mul_eq_iff).mpr i_ne_j) (fun σ _ => Finset.mem_univ _) fun σ _ =>
      swap_mul_involutive i j σ

/-- Produce an `alternating_map` out of a `multilinear_map`, by summing over all argument
permutations. -/
def alternatization : MultilinearMap R (fun i : ι => M) N' →+ AlternatingMap R M N' ι where
  toFun := fun m =>
    { ∑ σ : Perm ι, σ.sign • m.domDomCongr σ with toFun := ⇑(∑ σ : Perm ι, σ.sign • m.domDomCongr σ),
      map_eq_zero_of_eq' := fun v i j hvij hij => alternization_map_eq_zero_of_eq_aux m v i j hij hvij }
  map_add' := fun a b => by
    ext
    simp only [← Finset.sum_add_distrib, ← smul_add, ← add_apply, ← dom_dom_congr_apply, ← AlternatingMap.add_apply, ←
      AlternatingMap.coe_mk, ← smul_apply, ← sum_apply]
  map_zero' := by
    ext
    simp only [← Finset.sum_const_zero, ← smul_zero, ← zero_apply, ← dom_dom_congr_apply, ← AlternatingMap.zero_apply, ←
      AlternatingMap.coe_mk, ← smul_apply, ← sum_apply]

theorem alternatization_def (m : MultilinearMap R (fun i : ι => M) N') :
    ⇑(alternatization m) = (∑ σ : Perm ι, σ.sign • m.domDomCongr σ : _) :=
  rfl

theorem alternatization_coe (m : MultilinearMap R (fun i : ι => M) N') :
    ↑m.alternatization = (∑ σ : Perm ι, σ.sign • m.domDomCongr σ : _) :=
  coe_injective rfl

theorem alternatization_apply (m : MultilinearMap R (fun i : ι => M) N') (v : ι → M) :
    alternatization m v = ∑ σ : Perm ι, σ.sign • m.domDomCongr σ v := by
  simp only [← alternatization_def, ← smul_apply, ← sum_apply]

end MultilinearMap

namespace AlternatingMap

/-- Alternatizing a multilinear map that is already alternating results in a scale factor of `n!`,
where `n` is the number of inputs. -/
theorem coe_alternatization [Fintype ι] (a : AlternatingMap R M N' ι) :
    (↑a : MultilinearMap R (fun ι => M) N').alternatization = Nat.factorial (Fintype.card ι) • a := by
  apply AlternatingMap.coe_injective
  simp_rw [MultilinearMap.alternatization_def, ← coe_dom_dom_congr, dom_dom_congr_perm, coe_smul, smul_smul,
    Int.units_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_perm, ← coe_multilinear_map,
    coe_smul]

end AlternatingMap

namespace LinearMap

variable {N'₂ : Type _} [AddCommGroupₓ N'₂] [Module R N'₂] [Fintype ι]

/-- Composition with a linear map before and after alternatization are equivalent. -/
theorem comp_multilinear_map_alternatization (g : N' →ₗ[R] N'₂) (f : MultilinearMap R (fun _ : ι => M) N') :
    (g.compMultilinearMap f).alternatization = g.compAlternatingMap f.alternatization := by
  ext
  simp [← MultilinearMap.alternatization_def]

end LinearMap

section Coprod

open BigOperators

open TensorProduct

variable {ιa ιb : Type _} [DecidableEq ιa] [DecidableEq ιb] [Fintype ιa] [Fintype ιb]

variable {R' : Type _} {Mᵢ N₁ N₂ : Type _} [CommSemiringₓ R'] [AddCommGroupₓ N₁] [Module R' N₁] [AddCommGroupₓ N₂]
  [Module R' N₂] [AddCommMonoidₓ Mᵢ] [Module R' Mᵢ]

namespace Equivₓ.Perm

/-- Elements which are considered equivalent if they differ only by swaps within α or β  -/
abbrev ModSumCongr (α β : Type _) :=
  _ ⧸ (Equivₓ.Perm.sumCongrHom α β).range

theorem ModSumCongr.swap_smul_involutive {α β : Type _} [DecidableEq (Sum α β)] (i j : Sum α β) :
    Function.Involutive (HasSmul.smul (Equivₓ.swap i j) : ModSumCongr α β → ModSumCongr α β) := fun σ => by
  apply σ.induction_on' fun σ => _
  exact _root_.congr_arg Quotientₓ.mk' (Equivₓ.swap_mul_involutive i j σ)

end Equivₓ.Perm

namespace AlternatingMap

open Equivₓ

/-- summand used in `alternating_map.dom_coprod` -/
def DomCoprod.summand (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) (σ : Perm.ModSumCongr ιa ιb) :
    MultilinearMap R' (fun _ : Sum ιa ιb => Mᵢ) (N₁ ⊗[R'] N₂) :=
  Quotientₓ.liftOn' σ
    (fun σ => σ.sign • (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ ⊗ N₂)).domDomCongr σ)
    fun σ₁ σ₂ H => by
    rw [QuotientGroup.left_rel_apply] at H
    obtain ⟨⟨sl, sr⟩, h⟩ := H
    ext v
    simp only [← MultilinearMap.dom_dom_congr_apply, ← MultilinearMap.dom_coprod_apply, ← coe_multilinear_map, ←
      MultilinearMap.smul_apply]
    replace h := inv_mul_eq_iff_eq_mul.mp h.symm
    have : (σ₁ * perm.sum_congr_hom _ _ (sl, sr)).sign = σ₁.sign * (sl.sign * sr.sign) := by
      simp
    rw [h, this, mul_smul, mul_smul, smul_left_cancel_iff, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [← Sum.map_inr, ← perm.sum_congr_hom_apply, ← perm.sum_congr_apply, ← Sum.map_inl, ← Function.comp_app, ←
      perm.coe_mul]
    rw [← a.map_congr_perm fun i => v (σ₁ _), ← b.map_congr_perm fun i => v (σ₁ _)]

theorem DomCoprod.summand_mk' (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb)
    (σ : Equivₓ.Perm (Sum ιa ιb)) :
    DomCoprod.summand a b (Quotientₓ.mk' σ) =
      σ.sign • (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ ⊗ N₂)).domDomCongr σ :=
  rfl

/-- Swapping elements in `σ` with equal values in `v` results in an addition that cancels -/
theorem DomCoprod.summand_add_swap_smul_eq_zero (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb)
    (σ : Perm.ModSumCongr ιa ιb) {v : Sum ιa ιb → Mᵢ} {i j : Sum ιa ιb} (hv : v i = v j) (hij : i ≠ j) :
    DomCoprod.summand a b σ v + DomCoprod.summand a b (swap i j • σ) v = 0 := by
  apply σ.induction_on' fun σ => _
  dsimp' only [← Quotientₓ.lift_on'_mk', ← Quotientₓ.map'_mk', ← MulAction.quotient.smul_mk, ← dom_coprod.summand]
  rw [smul_eq_mul, perm.sign_mul, perm.sign_swap hij]
  simp only [← one_mulₓ, ← neg_mul, ← Function.comp_app, ← Units.neg_smul, ← perm.coe_mul, ← Units.coe_neg, ←
    MultilinearMap.smul_apply, ← MultilinearMap.neg_apply, ← MultilinearMap.dom_dom_congr_apply, ←
    MultilinearMap.dom_coprod_apply]
  convert add_right_negₓ _ <;>
    · ext k
      rw [Equivₓ.apply_swap_eq_self hv]
      

/-- Swapping elements in `σ` with equal values in `v` result in zero if the swap has no effect
on the quotient. -/
theorem DomCoprod.summand_eq_zero_of_smul_invariant (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb)
    (σ : Perm.ModSumCongr ιa ιb) {v : Sum ιa ιb → Mᵢ} {i j : Sum ιa ιb} (hv : v i = v j) (hij : i ≠ j) :
    swap i j • σ = σ → DomCoprod.summand a b σ v = 0 := by
  apply σ.induction_on' fun σ => _
  dsimp' only [← Quotientₓ.lift_on'_mk', ← Quotientₓ.map'_mk', ← MultilinearMap.smul_apply, ←
    MultilinearMap.dom_dom_congr_apply, ← MultilinearMap.dom_coprod_apply, ← dom_coprod.summand]
  intro hσ
  with_cases
    cases hi : σ⁻¹ i <;> cases hj : σ⁻¹ j <;> rw [perm.inv_eq_iff_eq] at hi hj <;> substs hi hj
  case'' [Sum.inl, Sum.inr : i' j', Sum.inr, Sum.inl : i' j'] =>
    -- the term pairs with and cancels another term
    all_goals
      obtain ⟨⟨sl, sr⟩, hσ⟩ := quotient_group.left_rel_apply.mp (Quotientₓ.exact' hσ)
    on_goal 1 =>
      replace hσ := Equivₓ.congr_fun hσ (Sum.inl i')
    on_goal 2 =>
      replace hσ := Equivₓ.congr_fun hσ (Sum.inr i')
    all_goals
      rw [smul_eq_mul, ← mul_swap_eq_swap_mul, mul_inv_rev, swap_inv, inv_mul_cancel_right] at hσ
      simpa using hσ
  case'' [Sum.inr, Sum.inr : i' j', Sum.inl, Sum.inl : i' j'] =>
    -- the term does not pair but is zero
    all_goals
      convert smul_zero _
    on_goal 1 =>
      convert TensorProduct.tmul_zero _ _
    on_goal 2 =>
      convert TensorProduct.zero_tmul _ _
    all_goals
      exact AlternatingMap.map_eq_zero_of_eq _ _ hv fun hij' => hij (hij' ▸ rfl)

/-- Like `multilinear_map.dom_coprod`, but ensures the result is also alternating.

Note that this is usually defined (for instance, as used in Proposition 22.24 in [Gallier2011Notes])
over integer indices `ιa = fin n` and `ιb = fin m`, as
$$
(f \wedge g)(u_1, \ldots, u_{m+n}) =
  \sum_{\operatorname{shuffle}(m, n)} \operatorname{sign}(\sigma)
    f(u_{\sigma(1)}, \ldots, u_{\sigma(m)}) g(u_{\sigma(m+1)}, \ldots, u_{\sigma(m+n)}),
$$
where $\operatorname{shuffle}(m, n)$ consists of all permutations of $[1, m+n]$ such that
$\sigma(1) < \cdots < \sigma(m)$ and $\sigma(m+1) < \cdots < \sigma(m+n)$.

Here, we generalize this by replacing:
* the product in the sum with a tensor product
* the filtering of $[1, m+n]$ to shuffles with an isomorphic quotient
* the additions in the subscripts of $\sigma$ with an index of type `sum`

The specialized version can be obtained by combining this definition with `fin_sum_fin_equiv` and
`algebra.lmul'`.
-/
@[simps]
def domCoprod (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
    AlternatingMap R' Mᵢ (N₁ ⊗[R'] N₂) (Sum ιa ιb) :=
  { ∑ σ : Perm.ModSumCongr ιa ιb, DomCoprod.summand a b σ with
    toFun := fun v => (⇑(∑ σ : Perm.ModSumCongr ιa ιb, DomCoprod.summand a b σ)) v,
    map_eq_zero_of_eq' := fun v i j hv hij => by
      dsimp' only
      rw [MultilinearMap.sum_apply]
      exact
        Finset.sum_involution (fun σ _ => Equivₓ.swap i j • σ)
          (fun σ _ => dom_coprod.summand_add_swap_smul_eq_zero a b σ hv hij)
          (fun σ _ => mt <| dom_coprod.summand_eq_zero_of_smul_invariant a b σ hv hij) (fun σ _ => Finset.mem_univ _)
          fun σ _ => Equivₓ.Perm.ModSumCongr.swap_smul_involutive i j σ }

theorem dom_coprod_coe (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
    (↑(a.domCoprod b) : MultilinearMap R' (fun _ => Mᵢ) _) = ∑ σ : Perm.ModSumCongr ιa ιb, DomCoprod.summand a b σ :=
  MultilinearMap.ext fun _ => rfl

/-- A more bundled version of `alternating_map.dom_coprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`. -/
def domCoprod' :
    AlternatingMap R' Mᵢ N₁ ιa ⊗[R'] AlternatingMap R' Mᵢ N₂ ιb →ₗ[R'] AlternatingMap R' Mᵢ (N₁ ⊗[R'] N₂) (Sum ιa ιb) :=
  TensorProduct.lift <| by
    refine' LinearMap.mk₂ R' dom_coprod (fun m₁ m₂ n => _) (fun c m n => _) (fun m n₁ n₂ => _) fun c m n => _ <;>
      · ext
        simp only [← dom_coprod_apply, ← add_apply, ← smul_apply, Finset.sum_add_distrib, ← Finset.smul_sum, ←
          MultilinearMap.sum_apply, ← dom_coprod.summand]
        congr
        ext σ
        apply σ.induction_on' fun σ => _
        simp only [← Quotientₓ.lift_on'_mk', ← coe_add, ← coe_smul, ← MultilinearMap.smul_apply,
          MultilinearMap.dom_coprod'_apply]
        simp only [← TensorProduct.add_tmul, TensorProduct.smul_tmul', ← TensorProduct.tmul_add, ←
          TensorProduct.tmul_smul, ← LinearMap.map_add, ← LinearMap.map_smul]
        first |
          rw [← smul_add]|
          rw [smul_comm]
        congr
        

@[simp]
theorem dom_coprod'_apply (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
    domCoprod' (a ⊗ₜ[R'] b) = domCoprod a b := by
  simp only [← dom_coprod', ← TensorProduct.lift.tmul, ← LinearMap.mk₂_apply]

end AlternatingMap

open Equivₓ

/-- A helper lemma for `multilinear_map.dom_coprod_alternization`. -/
theorem MultilinearMap.dom_coprod_alternization_coe (a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁)
    (b : MultilinearMap R' (fun _ : ιb => Mᵢ) N₂) :
    MultilinearMap.domCoprod ↑a.alternatization ↑b.alternatization =
      ∑ (σa : Perm ιa) (σb : Perm ιb),
        σa.sign • σb.sign • MultilinearMap.domCoprod (a.domDomCongr σa) (b.domDomCongr σb) :=
  by
  simp_rw [← MultilinearMap.dom_coprod'_apply, MultilinearMap.alternatization_coe]
  simp_rw [TensorProduct.sum_tmul, TensorProduct.tmul_sum, LinearMap.map_sum, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, LinearMap.map_smul_of_tower]

open AlternatingMap

/-- Computing the `multilinear_map.alternatization` of the `multilinear_map.dom_coprod` is the same
as computing the `alternating_map.dom_coprod` of the `multilinear_map.alternatization`s.
-/
theorem MultilinearMap.dom_coprod_alternization (a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁)
    (b : MultilinearMap R' (fun _ : ιb => Mᵢ) N₂) :
    (MultilinearMap.domCoprod a b).alternatization = a.alternatization.domCoprod b.alternatization := by
  apply coe_multilinear_map_injective
  rw [dom_coprod_coe, MultilinearMap.alternatization_coe,
    Finset.sum_partition (QuotientGroup.leftRel (perm.sum_congr_hom ιa ιb).range)]
  congr 1
  ext1 σ
  apply σ.induction_on' fun σ => _
  -- unfold the quotient mess left by `finset.sum_partition`
  conv in _ = Quotientₓ.mk' _ => change Quotientₓ.mk' _ = Quotientₓ.mk' _ rw [QuotientGroup.eq']
  -- eliminate a multiplication
  have : @Finset.univ (perm (Sum ιa ιb)) _ = finset.univ.image ((· * ·) σ) :=
    (finset.eq_univ_iff_forall.mpr fun a =>
        let ⟨a', ha'⟩ := mul_left_surjective σ a
        finset.mem_image.mpr ⟨a', Finset.mem_univ _, ha'⟩).symm
  rw [this, Finset.image_filter]
  simp only [← Function.comp, ← mul_inv_rev, ← inv_mul_cancel_right, ← Subgroup.inv_mem_iff]
  simp only [← MonoidHom.mem_range]
  -- needs to be separate from the above `simp only`
  rw [Finset.filter_congr_decidable, Finset.univ_filter_exists (perm.sum_congr_hom ιa ιb),
    Finset.sum_image fun x _ y _ (h : _ = _) => mul_right_injective _ h,
    Finset.sum_image fun x _ y _ (h : _ = _) => perm.sum_congr_hom_injective h]
  dsimp' only
  -- now we're ready to clean up the RHS, pulling out the summation
  rw [dom_coprod.summand_mk', MultilinearMap.dom_coprod_alternization_coe, ← Finset.sum_product',
    Finset.univ_product_univ, ← MultilinearMap.dom_dom_congr_equiv_apply, AddEquiv.map_sum, Finset.smul_sum]
  congr 1
  ext1 ⟨al, ar⟩
  dsimp' only
  -- pull out the pair of smuls on the RHS, by rewriting to `_ →ₗ[ℤ] _` and back
  rw [← AddEquiv.coe_to_add_monoid_hom, ← AddMonoidHom.coe_to_int_linear_map, LinearMap.map_smul_of_tower,
    LinearMap.map_smul_of_tower, AddMonoidHom.coe_to_int_linear_map, AddEquiv.coe_to_add_monoid_hom,
    MultilinearMap.dom_dom_congr_equiv_apply]
  -- pick up the pieces
  rw [MultilinearMap.dom_dom_congr_mul, perm.sign_mul, perm.sum_congr_hom_apply,
    MultilinearMap.dom_coprod_dom_dom_congr_sum_congr, perm.sign_sum_congr, mul_smul, mul_smul]

/-- Taking the `multilinear_map.alternatization` of the `multilinear_map.dom_coprod` of two
`alternating_map`s gives a scaled version of the `alternating_map.coprod` of those maps.
-/
theorem MultilinearMap.dom_coprod_alternization_eq (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
    (MultilinearMap.domCoprod a b : MultilinearMap R' (fun _ : Sum ιa ιb => Mᵢ) (N₁ ⊗ N₂)).alternatization =
      ((Fintype.card ιa).factorial * (Fintype.card ιb).factorial) • a.domCoprod b :=
  by
  rw [MultilinearMap.dom_coprod_alternization, coe_alternatization, coe_alternatization, mul_smul, ← dom_coprod'_apply,
    ← dom_coprod'_apply, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, LinearMap.map_smul_of_tower dom_coprod',
    LinearMap.map_smul_of_tower dom_coprod']
  -- typeclass resolution is a little confused here
  infer_instance
  infer_instance

end Coprod

section Basis

open AlternatingMap

variable {ι₁ : Type _} [Fintype ι]

variable {R' : Type _} {N₁ N₂ : Type _} [CommSemiringₓ R'] [AddCommMonoidₓ N₁] [AddCommMonoidₓ N₂]

variable [Module R' N₁] [Module R' N₂]

/-- Two alternating maps indexed by a `fintype` are equal if they are equal when all arguments
are distinct basis vectors. -/
theorem Basis.ext_alternating {f g : AlternatingMap R' N₁ N₂ ι} (e : Basis ι₁ R' N₁)
    (h : ∀ v : ι → ι₁, Function.Injective v → (f fun i => e (v i)) = g fun i => e (v i)) : f = g := by
  refine' AlternatingMap.coe_multilinear_map_injective ((Basis.ext_multilinear e) fun v => _)
  by_cases' hi : Function.Injective v
  · exact h v hi
    
  · have : ¬Function.Injective fun i => e (v i) := hi.imp Function.Injective.of_comp
    rw [coe_multilinear_map, coe_multilinear_map, f.map_eq_zero_of_not_injective _ this,
      g.map_eq_zero_of_not_injective _ this]
    

end Basis

/-! ### Currying -/


section Currying

variable {R' : Type _} {M'' M₂'' N'' N₂'' : Type _} [CommSemiringₓ R'] [AddCommMonoidₓ M''] [AddCommMonoidₓ M₂'']
  [AddCommMonoidₓ N''] [AddCommMonoidₓ N₂''] [Module R' M''] [Module R' M₂''] [Module R' N''] [Module R' N₂'']

namespace AlternatingMap

/-- Given an alternating map `f` in `n+1` variables, split the first variable to obtain
a linear map into alternating maps in `n` variables, given by `x ↦ (m ↦ f (matrix.vec_cons x m))`.
It can be thought of as a map $Hom(\bigwedge^{n+1} M, N) \to Hom(M, Hom(\bigwedge^n M, N))$.

This is `multilinear_map.curry_left` for `alternating_map`. See also
`alternating_map.curry_left_linear_map`. -/
@[simps]
def curryLeft {n : ℕ} (f : AlternatingMap R' M'' N'' (Finₓ n.succ)) :
    M'' →ₗ[R'] AlternatingMap R' M'' N'' (Finₓ n) where
  toFun := fun m =>
    { f.toMultilinearMap.curryLeft m with toFun := fun v => f (Matrix.vecCons m v),
      map_eq_zero_of_eq' := fun v i j hv hij =>
        f.map_eq_zero_of_eq _
          (by
            rwa [Matrix.cons_val_succ, Matrix.cons_val_succ])
          ((Finₓ.succ_injective _).Ne hij) }
  map_add' := fun m₁ m₂ => ext fun v => f.map_vec_cons_add _ _ _
  map_smul' := fun r m => ext fun v => f.map_vec_cons_smul _ _ _

@[simp]
theorem curry_left_zero {n : ℕ} : curryLeft (0 : AlternatingMap R' M'' N'' (Finₓ n.succ)) = 0 :=
  rfl

@[simp]
theorem curry_left_add {n : ℕ} (f g : AlternatingMap R' M'' N'' (Finₓ n.succ)) :
    curryLeft (f + g) = curryLeft f + curryLeft g :=
  rfl

@[simp]
theorem curry_left_smul {n : ℕ} (r : R') (f : AlternatingMap R' M'' N'' (Finₓ n.succ)) :
    curryLeft (r • f) = r • curryLeft f :=
  rfl

/-- `alternating_map.curry_left` as a `linear_map`. This is a separate definition as dot notation
does not work for this version. -/
@[simps]
def curryLeftLinearMap {n : ℕ} :
    AlternatingMap R' M'' N'' (Finₓ n.succ) →ₗ[R'] M'' →ₗ[R'] AlternatingMap R' M'' N'' (Finₓ n) where
  toFun := fun f => f.curryLeft
  map_add' := curry_left_add
  map_smul' := curry_left_smul

/-- Currying with the same element twice gives the zero map. -/
@[simp]
theorem curry_left_same {n : ℕ} (f : AlternatingMap R' M'' N'' (Finₓ n.succ.succ)) (m : M'') :
    (f.curryLeft m).curryLeft m = 0 :=
  ext fun x =>
    f.map_eq_zero_of_eq _
      (by
        simp )
      Finₓ.zero_ne_one

@[simp]
theorem curry_left_comp_alternating_map {n : ℕ} (g : N'' →ₗ[R'] N₂'') (f : AlternatingMap R' M'' N'' (Finₓ n.succ))
    (m : M'') : (g.compAlternatingMap f).curryLeft m = g.compAlternatingMap (f.curryLeft m) :=
  rfl

@[simp]
theorem curry_left_comp_linear_map {n : ℕ} (g : M₂'' →ₗ[R'] M'') (f : AlternatingMap R' M'' N'' (Finₓ n.succ))
    (m : M₂'') : (f.compLinearMap g).curryLeft m = (f.curryLeft (g m)).compLinearMap g :=
  ext fun v =>
    congr_arg f <|
      funext <| by
        refine' Finₓ.cases _ _
        · rfl
          
        · simp
          

/-- The space of constant maps is equivalent to the space of maps that are alternating with respect
to an empty family. -/
@[simps]
def constLinearEquivOfIsEmpty [IsEmpty ι] : N'' ≃ₗ[R'] AlternatingMap R' M'' N'' ι where
  toFun := AlternatingMap.constOfIsEmpty R' M''
  map_add' := fun x y => rfl
  map_smul' := fun t x => rfl
  invFun := fun f => f 0
  left_inv := fun _ => rfl
  right_inv := fun f => ext fun x => AlternatingMap.congr_arg f <| Subsingleton.elimₓ _ _

end AlternatingMap

end Currying


/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle
-/
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.LinearAlgebra.Projection
import Mathbin.LinearAlgebra.SesquilinearForm
import Mathbin.RingTheory.Finiteness
import Mathbin.LinearAlgebra.FreeModule.Finite.Rank

/-!
# Dual vector spaces

The dual space of an R-module M is the R-module of linear maps `M → R`.

## Main definitions

* `dual R M` defines the dual space of M over R.
* Given a basis for an `R`-module `M`, `basis.to_dual` produces a map from `M` to `dual R M`.
* Given families of vectors `e` and `ε`, `dual_pair e ε` states that these families have the
  characteristic properties of a basis and a dual.
* `dual_annihilator W` is the submodule of `dual R M` where every element annihilates `W`.

## Main results

* `to_dual_equiv` : the linear equivalence between the dual module and primal module,
  given a finite basis.
* `dual_pair.basis` and `dual_pair.eq_dual`: if `e` and `ε` form a dual pair, `e` is a basis and
  `ε` is its dual basis.
* `quot_equiv_annihilator`: the quotient by a subspace is isomorphic to its dual annihilator.

## Notation

We sometimes use `V'` as local notation for `dual K V`.

## TODO

Erdös-Kaplansky theorem about the dimension of a dual vector space in case of infinite dimension.
-/


noncomputable section

namespace Module

variable (R : Type _) (M : Type _)

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M]

-- ./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module R
/-- The dual space of an R-module M is the R-module of linear maps `M → R`. -/
def Dual :=
  M →ₗ[R] R deriving AddCommMonoidₓ,
  «./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module R»

instance {S : Type _} [CommRingₓ S] {N : Type _} [AddCommGroupₓ N] [Module S N] : AddCommGroupₓ (Dual S N) :=
  LinearMap.addCommGroup

instance : LinearMapClass (Dual R M) R M R :=
  LinearMap.semilinearMapClass

/-- The canonical pairing of a vector space and its algebraic dual. -/
def dualPairing (R M) [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] : Module.Dual R M →ₗ[R] M →ₗ[R] R :=
  LinearMap.id

@[simp]
theorem dual_pairing_apply (v x) : dualPairing R M v x = v x :=
  rfl

namespace Dual

instance : Inhabited (Dual R M) :=
  LinearMap.inhabited

instance : CoeFun (Dual R M) fun _ => M → R :=
  ⟨LinearMap.toFun⟩

/-- Maps a module M to the dual of the dual of M. See `module.erange_coe` and
`module.eval_equiv`. -/
def eval : M →ₗ[R] Dual R (Dual R M) :=
  LinearMap.flip LinearMap.id

@[simp]
theorem eval_apply (v : M) (a : Dual R M) : eval R M v a = a v := by
  dunfold eval
  rw [LinearMap.flip_apply, LinearMap.id_apply]

variable {R M} {M' : Type _} [AddCommMonoidₓ M'] [Module R M']

/-- The transposition of linear maps, as a linear map from `M →ₗ[R] M'` to
`dual R M' →ₗ[R] dual R M`. -/
def transpose : (M →ₗ[R] M') →ₗ[R] Dual R M' →ₗ[R] Dual R M :=
  (LinearMap.llcomp R M M' R).flip

theorem transpose_apply (u : M →ₗ[R] M') (l : Dual R M') : transpose u l = l.comp u :=
  rfl

variable {M'' : Type _} [AddCommMonoidₓ M''] [Module R M'']

theorem transpose_comp (u : M' →ₗ[R] M'') (v : M →ₗ[R] M') : transpose (u.comp v) = (transpose v).comp (transpose u) :=
  rfl

end Dual

end Module

namespace Basis

universe u v w

open Module Module.Dual Submodule LinearMap Cardinal Function

open BigOperators

variable {R M K V ι : Type _}

section CommSemiringₓ

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] [DecidableEq ι]

variable (b : Basis ι R M)

/-- The linear map from a vector space equipped with basis to its dual vector space,
taking basis elements to corresponding dual basis elements. -/
def toDual : M →ₗ[R] Module.Dual R M :=
  (b.constr ℕ) fun v => (b.constr ℕ) fun w => if w = v then (1 : R) else 0

theorem to_dual_apply (i j : ι) : b.toDual (b i) (b j) = if i = j then 1 else 0 := by
  erw [constr_basis b, constr_basis b]
  ac_rfl

@[simp]
theorem to_dual_total_left (f : ι →₀ R) (i : ι) : b.toDual (Finsupp.total ι M R b f) (b i) = f i := by
  rw [Finsupp.total_apply, Finsupp.sum, LinearMap.map_sum, LinearMap.sum_apply]
  simp_rw [LinearMap.map_smul, LinearMap.smul_apply, to_dual_apply, smul_eq_mul, mul_boole, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
    
  · rw [finsupp.not_mem_support_iff.mp h]
    

@[simp]
theorem to_dual_total_right (f : ι →₀ R) (i : ι) : b.toDual (b i) (Finsupp.total ι M R b f) = f i := by
  rw [Finsupp.total_apply, Finsupp.sum, LinearMap.map_sum]
  simp_rw [LinearMap.map_smul, to_dual_apply, smul_eq_mul, mul_boole, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
    
  · rw [finsupp.not_mem_support_iff.mp h]
    

theorem to_dual_apply_left (m : M) (i : ι) : b.toDual m (b i) = b.repr m i := by
  rw [← b.to_dual_total_left, b.total_repr]

theorem to_dual_apply_right (i : ι) (m : M) : b.toDual (b i) m = b.repr m i := by
  rw [← b.to_dual_total_right, b.total_repr]

theorem coe_to_dual_self (i : ι) : b.toDual (b i) = b.Coord i := by
  ext
  apply to_dual_apply_right

/-- `h.to_dual_flip v` is the linear map sending `w` to `h.to_dual w v`. -/
def toDualFlip (m : M) : M →ₗ[R] R :=
  b.toDual.flip m

theorem to_dual_flip_apply (m₁ m₂ : M) : b.toDualFlip m₁ m₂ = b.toDual m₂ m₁ :=
  rfl

theorem to_dual_eq_repr (m : M) (i : ι) : b.toDual m (b i) = b.repr m i :=
  b.to_dual_apply_left m i

theorem to_dual_eq_equiv_fun [Fintype ι] (m : M) (i : ι) : b.toDual m (b i) = b.equivFun m i := by
  rw [b.equiv_fun_apply, to_dual_eq_repr]

theorem to_dual_inj (m : M) (a : b.toDual m = 0) : m = 0 := by
  rw [← mem_bot R, ← b.repr.ker, mem_ker, LinearEquiv.coe_coe]
  apply Finsupp.ext
  intro b
  rw [← to_dual_eq_repr, a]
  rfl

theorem to_dual_ker : b.toDual.ker = ⊥ :=
  ker_eq_bot'.mpr b.to_dual_inj

theorem to_dual_range [fin : Fintype ι] : b.toDual.range = ⊤ := by
  rw [eq_top_iff']
  intro f
  rw [LinearMap.mem_range]
  let lin_comb : ι →₀ R := Finsupp.onFinset fin.elems (fun i => f.to_fun (b i)) _
  · use Finsupp.total ι M R b lin_comb
    apply b.ext
    · intro i
      rw [b.to_dual_eq_repr _ i, repr_total b]
      · rfl
        
      
    
  · intro a _
    apply fin.complete
    

end CommSemiringₓ

section

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] [Fintype ι]

variable (b : Basis ι R M)

@[simp]
theorem sum_dual_apply_smul_coord (f : Module.Dual R M) : (∑ x, f (b x) • b.Coord x) = f := by
  ext m
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm (f _), ← smul_eq_mul, ← f.map_smul, ←
    f.map_sum, Basis.coord_apply, Basis.sum_repr]

end

section CommRingₓ

variable [CommRingₓ R] [AddCommGroupₓ M] [Module R M] [DecidableEq ι]

variable (b : Basis ι R M)

/-- A vector space is linearly equivalent to its dual space. -/
@[simps]
def toDualEquiv [Fintype ι] : M ≃ₗ[R] Dual R M :=
  LinearEquiv.ofBijective b.toDual (ker_eq_bot.mp b.to_dual_ker) (range_eq_top.mp b.to_dual_range)

/-- Maps a basis for `V` to a basis for the dual space. -/
def dualBasis [Fintype ι] : Basis ι R (Dual R M) :=
  b.map b.toDualEquiv

-- We use `j = i` to match `basis.repr_self`
theorem dual_basis_apply_self [Fintype ι] (i j : ι) : b.dualBasis i (b j) = if j = i then 1 else 0 := by
  convert b.to_dual_apply i j using 2
  rw [@eq_comm _ j i]

theorem total_dual_basis [Fintype ι] (f : ι →₀ R) (i : ι) : Finsupp.total ι (Dual R M) R b.dualBasis f (b i) = f i := by
  rw [Finsupp.total_apply, Finsupp.sum_fintype, LinearMap.sum_apply]
  · simp_rw [LinearMap.smul_apply, smul_eq_mul, dual_basis_apply_self, mul_boole, Finset.sum_ite_eq,
      if_pos (Finset.mem_univ i)]
    
  · intro
    rw [zero_smul]
    

theorem dual_basis_repr [Fintype ι] (l : Dual R M) (i : ι) : b.dualBasis.repr l i = l (b i) := by
  rw [← total_dual_basis b, Basis.total_repr b.dual_basis l]

theorem dual_basis_equiv_fun [Fintype ι] (l : Dual R M) (i : ι) : b.dualBasis.equivFun l i = l (b i) := by
  rw [Basis.equiv_fun_apply, dual_basis_repr]

theorem dual_basis_apply [Fintype ι] (i : ι) (m : M) : b.dualBasis i m = b.repr m i :=
  b.to_dual_apply_right i m

@[simp]
theorem coe_dual_basis [Fintype ι] : ⇑b.dualBasis = b.Coord := by
  ext i x
  apply dual_basis_apply

@[simp]
theorem to_dual_to_dual [Fintype ι] : b.dualBasis.toDual.comp b.toDual = Dual.eval R M := by
  refine' b.ext fun i => b.dual_basis.ext fun j => _
  rw [LinearMap.comp_apply, to_dual_apply_left, coe_to_dual_self, ← coe_dual_basis, dual.eval_apply, Basis.repr_self,
    Finsupp.single_apply, dual_basis_apply_self]

theorem eval_ker {ι : Type _} (b : Basis ι R M) : (Dual.eval R M).ker = ⊥ := by
  rw [ker_eq_bot']
  intro m hm
  simp_rw [LinearMap.ext_iff, dual.eval_apply, zero_apply] at hm
  exact (Basis.forall_coord_eq_zero_iff _).mp fun i => hm (b.coord i)

theorem eval_range {ι : Type _} [Fintype ι] (b : Basis ι R M) : (eval R M).range = ⊤ := by
  classical
  rw [← b.to_dual_to_dual, range_comp, b.to_dual_range, map_top, to_dual_range _]
  infer_instance

/-- A module with a basis is linearly equivalent to the dual of its dual space. -/
def evalEquiv {ι : Type _} [Fintype ι] (b : Basis ι R M) : M ≃ₗ[R] Dual R (Dual R M) :=
  LinearEquiv.ofBijective (eval R M) (ker_eq_bot.mp b.eval_ker) (range_eq_top.mp b.eval_range)

@[simp]
theorem eval_equiv_to_linear_map {ι : Type _} [Fintype ι] (b : Basis ι R M) : b.evalEquiv.toLinearMap = Dual.eval R M :=
  rfl

section

open Classical

variable [Finite R M] [Free R M] [Nontrivial R]

instance dual_free : Free R (Dual R M) :=
  Free.of_basis (Free.chooseBasis R M).dualBasis

instance dual_finite : Finite R (Dual R M) :=
  Finite.of_basis (Free.chooseBasis R M).dualBasis

end

end CommRingₓ

/-- `simp` normal form version of `total_dual_basis` -/
@[simp]
theorem total_coord [CommRingₓ R] [AddCommGroupₓ M] [Module R M] [Fintype ι] (b : Basis ι R M) (f : ι →₀ R) (i : ι) :
    Finsupp.total ι (Dual R M) R b.Coord f (b i) = f i := by
  have := Classical.decEq ι
  rw [← coe_dual_basis, total_dual_basis]

-- TODO(jmc): generalize to rings, once `module.rank` is generalized
theorem dual_dim_eq [Field K] [AddCommGroupₓ V] [Module K V] [Fintype ι] (b : Basis ι K V) :
    Cardinal.lift (Module.rank K V) = Module.rank K (Dual K V) := by
  classical
  have := LinearEquiv.lift_dim_eq b.to_dual_equiv
  simp only [← Cardinal.lift_umax] at this
  rw [this, ← Cardinal.lift_umax]
  apply Cardinal.lift_id

end Basis

namespace Module

variable {K V : Type _}

variable [Field K] [AddCommGroupₓ V] [Module K V]

open Module Module.Dual Submodule LinearMap Cardinal Basis FiniteDimensional

theorem eval_ker : (eval K V).ker = ⊥ := by
  classical
  exact (Basis.ofVectorSpace K V).eval_ker

-- TODO(jmc): generalize to rings, once `module.rank` is generalized
theorem dual_dim_eq [FiniteDimensional K V] : Cardinal.lift (Module.rank K V) = Module.rank K (Dual K V) :=
  (Basis.ofVectorSpace K V).dual_dim_eq

theorem erange_coe [FiniteDimensional K V] : (eval K V).range = ⊤ := by
  let this : IsNoetherian K V := IsNoetherian.iff_fg.2 inferInstance
  exact (Basis.ofVectorSpace K V).eval_range

variable (K V)

/-- A vector space is linearly equivalent to the dual of its dual space. -/
def evalEquiv [FiniteDimensional K V] : V ≃ₗ[K] Dual K (Dual K V) :=
  LinearEquiv.ofBijective (eval K V) (ker_eq_bot.mp eval_ker) (range_eq_top.mp erange_coe)

variable {K V}

@[simp]
theorem eval_equiv_to_linear_map [FiniteDimensional K V] : (evalEquiv K V).toLinearMap = Dual.eval K V :=
  rfl

end Module

section DualPair

open Module

variable {R M ι : Type _}

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] [DecidableEq ι]

/-- `e` and `ε` have characteristic properties of a basis and its dual -/
@[nolint has_inhabited_instance]
structure DualPair (e : ι → M) (ε : ι → Dual R M) where
  eval : ∀ i j : ι, ε i (e j) = if i = j then 1 else 0
  Total : ∀ {m : M}, (∀ i, ε i m = 0) → m = 0
  [Finite : ∀ m : M, Fintype { i | ε i m ≠ 0 }]

end DualPair

namespace DualPair

open Module Module.Dual LinearMap Function

variable {R M ι : Type _}

variable [CommRingₓ R] [AddCommGroupₓ M] [Module R M]

variable {e : ι → M} {ε : ι → Dual R M}

/-- The coefficients of `v` on the basis `e` -/
def coeffs [DecidableEq ι] (h : DualPair e ε) (m : M) : ι →₀ R where
  toFun := fun i => ε i m
  support := by
    have := h.finite m
    exact { i : ι | ε i m ≠ 0 }.toFinset
  mem_support_to_fun := by
    intro i
    rw [Set.mem_to_finset]
    exact Iff.rfl

@[simp]
theorem coeffs_apply [DecidableEq ι] (h : DualPair e ε) (m : M) (i : ι) : h.coeffs m i = ε i m :=
  rfl

/-- linear combinations of elements of `e`.
This is a convenient abbreviation for `finsupp.total _ M R e l` -/
def lc {ι} (e : ι → M) (l : ι →₀ R) : M :=
  l.Sum fun (i : ι) (a : R) => a • e i

theorem lc_def (e : ι → M) (l : ι →₀ R) : lc e l = Finsupp.total _ _ _ e l :=
  rfl

variable [DecidableEq ι] (h : DualPair e ε)

include h

theorem dual_lc (l : ι →₀ R) (i : ι) : ε i (DualPair.lc e l) = l i := by
  erw [LinearMap.map_sum]
  simp only [← h.eval, ← map_smul, ← smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
    
  · intro q q_in q_ne
    simp [← q_ne.symm]
    
  · intro p_not_in
    simp [← Finsupp.not_mem_support_iff.1 p_not_in]
    

@[simp]
theorem coeffs_lc (l : ι →₀ R) : h.coeffs (DualPair.lc e l) = l := by
  ext i
  rw [h.coeffs_apply, h.dual_lc]

/-- For any m : M n, \sum_{p ∈ Q n} (ε p m) • e p = m -/
@[simp]
theorem lc_coeffs (m : M) : DualPair.lc e (h.coeffs m) = m := by
  refine' eq_of_sub_eq_zero (h.total _)
  intro i
  simp [-sub_eq_add_neg, ← LinearMap.map_sub, ← h.dual_lc, ← sub_eq_zero]

/-- `(h : dual_pair e ε).basis` shows the family of vectors `e` forms a basis. -/
@[simps]
def basis : Basis ι R M :=
  Basis.of_repr
    { toFun := coeffs h, invFun := lc e, left_inv := lc_coeffs h, right_inv := coeffs_lc h,
      map_add' := fun v w => by
        ext i
        exact (ε i).map_add v w,
      map_smul' := fun c v => by
        ext i
        exact (ε i).map_smul c v }

@[simp]
theorem coe_basis : ⇑h.Basis = e := by
  ext i
  rw [Basis.apply_eq_iff]
  ext j
  rw [h.basis_repr_apply, coeffs_apply, h.eval, Finsupp.single_apply]
  convert if_congr eq_comm rfl rfl

-- `convert` to get rid of a `decidable_eq` mismatch
theorem mem_of_mem_span {H : Set ι} {x : M} (hmem : x ∈ Submodule.span R (e '' H)) : ∀ i : ι, ε i x ≠ 0 → i ∈ H := by
  intro i hi
  rcases(Finsupp.mem_span_image_iff_total _).mp hmem with ⟨l, supp_l, rfl⟩
  apply not_imp_comm.mp ((Finsupp.mem_supported' _ _).mp supp_l i)
  rwa [← lc_def, h.dual_lc] at hi

theorem coe_dual_basis [Fintype ι] : ⇑h.Basis.dualBasis = ε :=
  funext fun i =>
    h.Basis.ext fun j => by
      rw [h.basis.dual_basis_apply_self, h.coe_basis, h.eval, if_congr eq_comm rfl rfl]

end DualPair

namespace Submodule

universe u v w

variable {R : Type u} {M : Type v} [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M]

variable {W : Submodule R M}

/-- The `dual_restrict` of a submodule `W` of `M` is the linear map from the
  dual of `M` to the dual of `W` such that the domain of each linear map is
  restricted to `W`. -/
def dualRestrict (W : Submodule R M) : Module.Dual R M →ₗ[R] Module.Dual R W :=
  LinearMap.domRestrict' W

@[simp]
theorem dual_restrict_apply (W : Submodule R M) (φ : Module.Dual R M) (x : W) : W.dualRestrict φ x = φ (x : M) :=
  rfl

/-- The `dual_annihilator` of a submodule `W` is the set of linear maps `φ` such
  that `φ w = 0` for all `w ∈ W`. -/
def dualAnnihilator {R : Type u} {M : Type v} [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] (W : Submodule R M) :
    Submodule R <| Module.Dual R M :=
  W.dualRestrict.ker

@[simp]
theorem mem_dual_annihilator (φ : Module.Dual R M) : φ ∈ W.dualAnnihilator ↔ ∀, ∀ w ∈ W, ∀, φ w = 0 := by
  refine' linear_map.mem_ker.trans _
  simp_rw [LinearMap.ext_iff, dual_restrict_apply]
  exact ⟨fun h w hw => h ⟨w, hw⟩, fun h w => h w.1 w.2⟩

theorem dual_restrict_ker_eq_dual_annihilator (W : Submodule R M) : W.dualRestrict.ker = W.dualAnnihilator :=
  rfl

theorem dual_annihilator_sup_eq_inf_dual_annihilator (U V : Submodule R M) :
    (U⊔V).dualAnnihilator = U.dualAnnihilator⊓V.dualAnnihilator := by
  ext φ
  rw [mem_inf, mem_dual_annihilator, mem_dual_annihilator, mem_dual_annihilator]
  constructor <;> intro h
  · refine' ⟨_, _⟩ <;> intro x hx
    exact h x (mem_sup.2 ⟨x, hx, 0, zero_mem _, add_zeroₓ _⟩)
    exact h x (mem_sup.2 ⟨0, zero_mem _, x, hx, zero_addₓ _⟩)
    
  · simp_rw [mem_sup]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [LinearMap.map_add, h.1 _ hx, h.2 _ hy, add_zeroₓ]
    

/-- The pullback of a submodule in the dual space along the evaluation map. -/
def dualAnnihilatorComap (Φ : Submodule R (Module.Dual R M)) : Submodule R M :=
  Φ.dualAnnihilator.comap (Module.Dual.eval R M)

theorem mem_dual_annihilator_comap_iff {Φ : Submodule R (Module.Dual R M)} (x : M) :
    x ∈ Φ.dualAnnihilatorComap ↔ ∀, ∀ φ ∈ Φ, ∀, (φ x : R) = 0 := by
  simp_rw [dual_annihilator_comap, mem_comap, mem_dual_annihilator, Module.Dual.eval_apply]

end Submodule

namespace Subspace

open Submodule LinearMap

universe u v w

-- We work in vector spaces because `exists_is_compl` only hold for vector spaces
variable {K : Type u} {V : Type v} [Field K] [AddCommGroupₓ V] [Module K V]

/-- Given a subspace `W` of `V` and an element of its dual `φ`, `dual_lift W φ` is
the natural extension of `φ` to an element of the dual of `V`.
That is, `dual_lift W φ` sends `w ∈ W` to `φ x` and `x` in the complement of `W` to `0`. -/
noncomputable def dualLift (W : Subspace K V) : Module.Dual K W →ₗ[K] Module.Dual K V :=
  let h := Classical.indefiniteDescription _ W.exists_is_compl
  (LinearMap.ofIsComplProd h.2).comp (LinearMap.inl _ _ _)

variable {W : Subspace K V}

@[simp]
theorem dual_lift_of_subtype {φ : Module.Dual K W} (w : W) : W.dualLift φ (w : V) = φ w := by
  erw [of_is_compl_left_apply _ w]
  rfl

theorem dual_lift_of_mem {φ : Module.Dual K W} {w : V} (hw : w ∈ W) : W.dualLift φ w = φ ⟨w, hw⟩ := by
  convert dual_lift_of_subtype ⟨w, hw⟩

@[simp]
theorem dual_restrict_comp_dual_lift (W : Subspace K V) : W.dualRestrict.comp W.dualLift = 1 := by
  ext φ x
  simp

theorem dual_restrict_left_inverse (W : Subspace K V) : Function.LeftInverse W.dualRestrict W.dualLift := fun x =>
  show W.dualRestrict.comp W.dualLift x = x by
    rw [dual_restrict_comp_dual_lift]
    rfl

theorem dual_lift_right_inverse (W : Subspace K V) : Function.RightInverse W.dualLift W.dualRestrict :=
  W.dual_restrict_left_inverse

theorem dual_restrict_surjective : Function.Surjective W.dualRestrict :=
  W.dual_lift_right_inverse.Surjective

theorem dual_lift_injective : Function.Injective W.dualLift :=
  W.dual_restrict_left_inverse.Injective

/-- The quotient by the `dual_annihilator` of a subspace is isomorphic to the
  dual of that subspace. -/
noncomputable def quotAnnihilatorEquiv (W : Subspace K V) :
    (Module.Dual K V ⧸ W.dualAnnihilator) ≃ₗ[K] Module.Dual K W :=
  (quotEquivOfEq _ _ W.dual_restrict_ker_eq_dual_annihilator).symm.trans <|
    W.dualRestrict.quotKerEquivOfSurjective dual_restrict_surjective

/-- The natural isomorphism forom the dual of a subspace `W` to `W.dual_lift.range`. -/
noncomputable def dualEquivDual (W : Subspace K V) : Module.Dual K W ≃ₗ[K] W.dualLift.range :=
  LinearEquiv.ofInjective _ dual_lift_injective

theorem dual_equiv_dual_def (W : Subspace K V) : W.dualEquivDual.toLinearMap = W.dualLift.range_restrict :=
  rfl

@[simp]
theorem dual_equiv_dual_apply (φ : Module.Dual K W) : W.dualEquivDual φ = ⟨W.dualLift φ, mem_range.2 ⟨φ, rfl⟩⟩ :=
  rfl

section

open Classical

open FiniteDimensional

variable {V₁ : Type _} [AddCommGroupₓ V₁] [Module K V₁]

instance [H : FiniteDimensional K V] : FiniteDimensional K (Module.Dual K V) := by
  infer_instance

variable [FiniteDimensional K V] [FiniteDimensional K V₁]

@[simp]
theorem dual_finrank_eq : finrank K (Module.Dual K V) = finrank K V :=
  LinearEquiv.finrank_eq (Basis.ofVectorSpace K V).toDualEquiv.symm

/-- The quotient by the dual is isomorphic to its dual annihilator.  -/
noncomputable def quotDualEquivAnnihilator (W : Subspace K V) :
    (Module.Dual K V ⧸ W.dualLift.range) ≃ₗ[K] W.dualAnnihilator :=
  linear_equiv.quot_equiv_of_quot_equiv <| LinearEquiv.trans W.quotAnnihilatorEquiv W.dualEquivDual

/-- The quotient by a subspace is isomorphic to its dual annihilator. -/
noncomputable def quotEquivAnnihilator (W : Subspace K V) : (V ⧸ W) ≃ₗ[K] W.dualAnnihilator := by
  refine' _ ≪≫ₗ W.quot_dual_equiv_annihilator
  refine' linear_equiv.quot_equiv_of_equiv _ (Basis.ofVectorSpace K V).toDualEquiv
  exact (Basis.ofVectorSpace K W).toDualEquiv.trans W.dual_equiv_dual

open FiniteDimensional

@[simp]
theorem finrank_dual_annihilator_comap_eq {Φ : Subspace K (Module.Dual K V)} :
    finrank K Φ.dualAnnihilatorComap = finrank K Φ.dualAnnihilator := by
  rw [Submodule.dualAnnihilatorComap, ← Module.eval_equiv_to_linear_map]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofSubmodule' _ _)

theorem finrank_add_finrank_dual_annihilator_comap_eq (W : Subspace K (Module.Dual K V)) :
    finrank K W + finrank K W.dualAnnihilatorComap = finrank K V := by
  rw [finrank_dual_annihilator_comap_eq, W.quot_equiv_annihilator.finrank_eq.symm, add_commₓ,
    Submodule.finrank_quotient_add_finrank, Subspace.dual_finrank_eq]

end

end Subspace

open Module

section DualMap

variable {R : Type _} [CommSemiringₓ R] {M₁ : Type _} {M₂ : Type _}

variable [AddCommMonoidₓ M₁] [Module R M₁] [AddCommMonoidₓ M₂] [Module R M₂]

/-- Given a linear map `f : M₁ →ₗ[R] M₂`, `f.dual_map` is the linear map between the dual of
`M₂` and `M₁` such that it maps the functional `φ` to `φ ∘ f`. -/
def LinearMap.dualMap (f : M₁ →ₗ[R] M₂) : Dual R M₂ →ₗ[R] Dual R M₁ :=
  LinearMap.lcomp R R f

@[simp]
theorem LinearMap.dual_map_apply (f : M₁ →ₗ[R] M₂) (g : Dual R M₂) (x : M₁) : f.dualMap g x = g (f x) :=
  LinearMap.lcomp_apply f g x

@[simp]
theorem LinearMap.dual_map_id : (LinearMap.id : M₁ →ₗ[R] M₁).dualMap = LinearMap.id := by
  ext
  rfl

theorem LinearMap.dual_map_comp_dual_map {M₃ : Type _} [AddCommGroupₓ M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂)
    (g : M₂ →ₗ[R] M₃) : f.dualMap.comp g.dualMap = (g.comp f).dualMap :=
  rfl

/-- The `linear_equiv` version of `linear_map.dual_map`. -/
def LinearEquiv.dualMap (f : M₁ ≃ₗ[R] M₂) : Dual R M₂ ≃ₗ[R] Dual R M₁ :=
  { f.toLinearMap.dualMap with invFun := f.symm.toLinearMap.dualMap,
    left_inv := by
      intro φ
      ext x
      simp only [← LinearMap.dual_map_apply, ← LinearEquiv.coe_to_linear_map, ← LinearMap.to_fun_eq_coe, ←
        LinearEquiv.apply_symm_apply],
    right_inv := by
      intro φ
      ext x
      simp only [← LinearMap.dual_map_apply, ← LinearEquiv.coe_to_linear_map, ← LinearMap.to_fun_eq_coe, ←
        LinearEquiv.symm_apply_apply] }

@[simp]
theorem LinearEquiv.dual_map_apply (f : M₁ ≃ₗ[R] M₂) (g : Dual R M₂) (x : M₁) : f.dualMap g x = g (f x) :=
  LinearMap.lcomp_apply f g x

@[simp]
theorem LinearEquiv.dual_map_refl : (LinearEquiv.refl R M₁).dualMap = LinearEquiv.refl R (Dual R M₁) := by
  ext
  rfl

@[simp]
theorem LinearEquiv.dual_map_symm {f : M₁ ≃ₗ[R] M₂} : (LinearEquiv.dualMap f).symm = LinearEquiv.dualMap f.symm :=
  rfl

theorem LinearEquiv.dual_map_trans {M₃ : Type _} [AddCommGroupₓ M₃] [Module R M₃] (f : M₁ ≃ₗ[R] M₂) (g : M₂ ≃ₗ[R] M₃) :
    g.dualMap.trans f.dualMap = (f.trans g).dualMap :=
  rfl

end DualMap

namespace LinearMap

variable {R : Type _} [CommSemiringₓ R] {M₁ : Type _} {M₂ : Type _}

variable [AddCommMonoidₓ M₁] [Module R M₁] [AddCommMonoidₓ M₂] [Module R M₂]

variable (f : M₁ →ₗ[R] M₂)

theorem ker_dual_map_eq_dual_annihilator_range : f.dualMap.ker = f.range.dualAnnihilator := by
  ext φ
  constructor <;> intro hφ
  · rw [mem_ker] at hφ
    rw [Submodule.mem_dual_annihilator]
    rintro y ⟨x, rfl⟩
    rw [← dual_map_apply, hφ, zero_apply]
    
  · ext x
    rw [dual_map_apply]
    rw [Submodule.mem_dual_annihilator] at hφ
    exact hφ (f x) ⟨x, rfl⟩
    

theorem range_dual_map_le_dual_annihilator_ker : f.dualMap.range ≤ f.ker.dualAnnihilator := by
  rintro _ ⟨ψ, rfl⟩
  simp_rw [Submodule.mem_dual_annihilator, mem_ker]
  rintro x hx
  rw [dual_map_apply, hx, map_zero]

section FiniteDimensional

variable {K : Type _} [Field K] {V₁ : Type _} {V₂ : Type _}

variable [AddCommGroupₓ V₁] [Module K V₁] [AddCommGroupₓ V₂] [Module K V₂]

open FiniteDimensional

variable [FiniteDimensional K V₂]

@[simp]
theorem finrank_range_dual_map_eq_finrank_range (f : V₁ →ₗ[K] V₂) : finrank K f.dualMap.range = finrank K f.range := by
  have := Submodule.finrank_quotient_add_finrank f.range
  rw [(Subspace.quotEquivAnnihilator f.range).finrank_eq, ← ker_dual_map_eq_dual_annihilator_range] at this
  conv_rhs at this => rw [← Subspace.dual_finrank_eq]
  refine' add_left_injective (finrank K f.dual_map.ker) _
  change _ + _ = _ + _
  rw [finrank_range_add_finrank_ker f.dual_map, add_commₓ, this]

theorem range_dual_map_eq_dual_annihilator_ker [FiniteDimensional K V₁] (f : V₁ →ₗ[K] V₂) :
    f.dualMap.range = f.ker.dualAnnihilator := by
  refine' eq_of_le_of_finrank_eq f.range_dual_map_le_dual_annihilator_ker _
  have := Submodule.finrank_quotient_add_finrank f.ker
  rw [(Subspace.quotEquivAnnihilator f.ker).finrank_eq] at this
  refine' add_left_injective (finrank K f.ker) _
  simp_rw [this, finrank_range_dual_map_eq_finrank_range]
  exact finrank_range_add_finrank_ker f

end FiniteDimensional

section Field

variable {K V : Type _}

variable [Field K] [AddCommGroupₓ V] [Module K V]

theorem dual_pairing_nondegenerate : (dualPairing K V).Nondegenerate := by
  refine' ⟨separating_left_iff_ker_eq_bot.mpr ker_id, _⟩
  intro x
  contrapose
  rintro hx : x ≠ 0
  rw [not_forall]
  let f : V →ₗ[K] K := Classical.some (LinearPmap.mkSpanSingleton x 1 hx).toFun.exists_extend
  use f
  refine' ne_zero_of_eq_one _
  have h : f.comp (K∙x).Subtype = (LinearPmap.mkSpanSingleton x 1 hx).toFun :=
    Classical.some_spec (LinearPmap.mkSpanSingleton x (1 : K) hx).toFun.exists_extend
  exact (FunLike.congr_fun h _).trans (LinearPmap.mk_span_singleton_apply _ hx _)

end Field

end LinearMap

namespace TensorProduct

variable (R : Type _) (M : Type _) (N : Type _)

variable {ι κ : Type _}

variable [DecidableEq ι] [DecidableEq κ]

variable [Fintype ι] [Fintype κ]

open BigOperators

open TensorProduct

attribute [local ext] TensorProduct.ext

open TensorProduct

open LinearMap

section

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ N]

variable [Module R M] [Module R N]

/-- The canonical linear map from `dual M ⊗ dual N` to `dual (M ⊗ N)`,
sending `f ⊗ g` to the composition of `tensor_product.map f g` with
the natural isomorphism `R ⊗ R ≃ R`.
-/
def dualDistrib : Dual R M ⊗[R] Dual R N →ₗ[R] Dual R (M ⊗[R] N) :=
  compRight ↑(TensorProduct.lid R R) ∘ₗ homTensorHomMap R M N R R

variable {R M N}

@[simp]
theorem dual_distrib_apply (f : Dual R M) (g : Dual R N) (m : M) (n : N) :
    dualDistrib R M N (f ⊗ₜ g) (m ⊗ₜ n) = f m * g n := by
  simp only [← dual_distrib, ← coe_comp, ← Function.comp_app, ← hom_tensor_hom_map_apply, ← comp_right_apply, ←
    LinearEquiv.coe_coe, ← map_tmul, ← lid_tmul, ← Algebra.id.smul_eq_mul]

end

variable {R M N}

variable [CommRingₓ R] [AddCommGroupₓ M] [AddCommGroupₓ N]

variable [Module R M] [Module R N]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
/-- An inverse to `dual_tensor_dual_map` given bases.
-/
noncomputable def dualDistribInvOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R (M ⊗[R] N) →ₗ[R] Dual R M ⊗[R] Dual R N :=
  ∑ (i) (j),
    (ringLmapEquivSelf R ℕ _).symm (b.dualBasis i ⊗ₜ c.dualBasis j) ∘ₗ applyₗ (c j) ∘ₗ applyₗ (b i) ∘ₗ lcurry R M N R

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem dual_distrib_inv_of_basis_apply (b : Basis ι R M) (c : Basis κ R N) (f : Dual R (M ⊗[R] N)) :
    dualDistribInvOfBasis b c f = ∑ (i) (j), f (b i ⊗ₜ c j) • b.dualBasis i ⊗ₜ c.dualBasis j := by
  simp [← dual_distrib_inv_of_basis]

/-- A linear equivalence between `dual M ⊗ dual N` and `dual (M ⊗ N)` given bases for `M` and `N`.
It sends `f ⊗ g` to the composition of `tensor_product.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simps]
noncomputable def dualDistribEquivOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) := by
  refine' LinearEquiv.ofLinear (dual_distrib R M N) (dual_distrib_inv_of_basis b c) _ _
  · ext f m n
    have h : ∀ r s : R, r • s = s • r := IsCommutative.comm
    simp only [← compr₂_apply, ← mk_apply, ← comp_apply, ← id_apply, ← dual_distrib_inv_of_basis_apply, ←
      LinearMap.map_sum, ← map_smul, ← sum_apply, ← smul_apply, ← dual_distrib_apply, ← h (f _) _, f.map_smul,
      f.map_sum, smul_tmul_smul, tmul_sum, sum_tmul, ← Basis.coe_dual_basis, ← Basis.coord_apply, ← Basis.sum_repr]
    
  · ext f g
    simp only [← compr₂_apply, ← mk_apply, ← comp_apply, ← id_apply, ← dual_distrib_inv_of_basis_apply, ←
      dual_distrib_apply, smul_tmul_smul, tmul_sum, sum_tmul, ← Basis.coe_dual_basis, ← Basis.sum_dual_apply_smul_coord]
    

variable (R M N)

variable [Module.Finite R M] [Module.Finite R N] [Module.Free R M] [Module.Free R N]

variable [Nontrivial R]

open Classical

/-- A linear equivalence between `dual M ⊗ dual N` and `dual (M ⊗ N)` when `M` and `N` are finite free
modules. It sends `f ⊗ g` to the composition of `tensor_product.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simp]
noncomputable def dualDistribEquiv : Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) :=
  dualDistribEquivOfBasis (Module.Free.chooseBasis R M) (Module.Free.chooseBasis R N)

end TensorProduct


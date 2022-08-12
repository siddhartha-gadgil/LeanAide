/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Eric Wieser
-/
import Mathbin.LinearAlgebra.Basic
import Mathbin.Logic.Equiv.Fin

/-!
# Pi types of modules

This file defines constructors for linear maps whose domains or codomains are pi types.

It contains theorems relating these to each other, as well as to `linear_map.ker`.

## Main definitions

- pi types in the codomain:
  - `linear_map.pi`
  - `linear_map.single`
- pi types in the domain:
  - `linear_map.proj`
- `linear_map.diag`

-/


universe u v w x y z u' v' w' x' y'

variable {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}

variable {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x} {ι' : Type x'}

open Function Submodule

open BigOperators

namespace LinearMap

universe i

variable [Semiringₓ R] [AddCommMonoidₓ M₂] [Module R M₂] [AddCommMonoidₓ M₃] [Module R M₃] {φ : ι → Type i}
  [∀ i, AddCommMonoidₓ (φ i)] [∀ i, Module R (φ i)]

/-- `pi` construction for linear functions. From a family of linear functions it produces a linear
function into a family of modules. -/
def pi (f : ∀ i, M₂ →ₗ[R] φ i) : M₂ →ₗ[R] ∀ i, φ i where
  toFun := fun c i => f i c
  map_add' := fun c d => funext fun i => (f i).map_add _ _
  map_smul' := fun c d => funext fun i => (f i).map_smul _ _

@[simp]
theorem pi_apply (f : ∀ i, M₂ →ₗ[R] φ i) (c : M₂) (i : ι) : pi f c i = f i c :=
  rfl

theorem ker_pi (f : ∀ i, M₂ →ₗ[R] φ i) : ker (pi f) = ⨅ i : ι, ker (f i) := by
  ext c <;> simp [← funext_iff] <;> rfl

theorem pi_eq_zero (f : ∀ i, M₂ →ₗ[R] φ i) : pi f = 0 ↔ ∀ i, f i = 0 := by
  simp only [← LinearMap.ext_iff, ← pi_apply, ← funext_iff] <;> exact ⟨fun h a b => h b a, fun h a b => h b a⟩

theorem pi_zero : pi (fun i => 0 : ∀ i, M₂ →ₗ[R] φ i) = 0 := by
  ext <;> rfl

theorem pi_comp (f : ∀ i, M₂ →ₗ[R] φ i) (g : M₃ →ₗ[R] M₂) : (pi f).comp g = pi fun i => (f i).comp g :=
  rfl

/-- The projections from a family of modules are linear maps.

Note:  known here as `linear_map.proj`, this construction is in other categories called `eval`, for
example `pi.eval_monoid_hom`, `pi.eval_ring_hom`. -/
def proj (i : ι) : (∀ i, φ i) →ₗ[R] φ i where
  toFun := Function.eval i
  map_add' := fun f g => rfl
  map_smul' := fun c f => rfl

@[simp]
theorem coe_proj (i : ι) : ⇑(proj i : (∀ i, φ i) →ₗ[R] φ i) = Function.eval i :=
  rfl

theorem proj_apply (i : ι) (b : ∀ i, φ i) : (proj i : (∀ i, φ i) →ₗ[R] φ i) b = b i :=
  rfl

theorem proj_pi (f : ∀ i, M₂ →ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
  ext fun c => rfl

theorem infi_ker_proj : (⨅ i, ker (proj i) : Submodule R (∀ i, φ i)) = ⊥ :=
  bot_unique <|
    SetLike.le_def.2 fun a h => by
      simp only [← mem_infi, ← mem_ker, ← proj_apply] at h
      exact (mem_bot _).2 (funext fun i => h i)

/-- Linear map between the function spaces `I → M₂` and `I → M₃`, induced by a linear map `f`
between `M₂` and `M₃`. -/
@[simps]
protected def compLeft (f : M₂ →ₗ[R] M₃) (I : Type _) : (I → M₂) →ₗ[R] I → M₃ :=
  { f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h,
    map_smul' := fun c h => by
      ext x
      exact f.map_smul' c (h x) }

theorem apply_single [AddCommMonoidₓ M] [Module R M] [DecidableEq ι] (f : ∀ i, φ i →ₗ[R] M) (i j : ι) (x : φ i) :
    f j (Pi.single i x j) = Pi.single i (f i x) j :=
  Pi.apply_single (fun i => f i) (fun i => (f i).map_zero) _ _ _

/-- The `linear_map` version of `add_monoid_hom.single` and `pi.single`. -/
def single [DecidableEq ι] (i : ι) : φ i →ₗ[R] ∀ i, φ i :=
  { AddMonoidHom.single φ i with toFun := Pi.single i, map_smul' := Pi.single_smul i }

@[simp]
theorem coe_single [DecidableEq ι] (i : ι) : ⇑(single i : φ i →ₗ[R] ∀ i, φ i) = Pi.single i :=
  rfl

variable (R φ)

/-- The linear equivalence between linear functions on a finite product of modules and
families of functions on these modules. See note [bundled maps over different rings]. -/
@[simps]
def lsum (S) [AddCommMonoidₓ M] [Module R M] [Fintype ι] [DecidableEq ι] [Semiringₓ S] [Module S M]
    [SmulCommClass R S M] : (∀ i, φ i →ₗ[R] M) ≃ₗ[S] (∀ i, φ i) →ₗ[R] M where
  toFun := fun f => ∑ i : ι, (f i).comp (proj i)
  invFun := fun f i => f.comp (single i)
  map_add' := fun f g => by
    simp only [← Pi.add_apply, ← add_comp, ← Finset.sum_add_distrib]
  map_smul' := fun c f => by
    simp only [← Pi.smul_apply, ← smul_comp, ← Finset.smul_sum, ← RingHom.id_apply]
  left_inv := fun f => by
    ext i x
    simp [← apply_single]
  right_inv := fun f => by
    ext
    suffices f (∑ j, Pi.single j (x j)) = f x by
      simpa [← apply_single]
    rw [Finset.univ_sum_single]

variable {R φ}

section Ext

variable [Fintype ι] [DecidableEq ι] [AddCommMonoidₓ M] [Module R M] {f g : (∀ i, φ i) →ₗ[R] M}

theorem pi_ext (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) : f = g :=
  to_add_monoid_hom_injective <| AddMonoidHom.functions_ext _ _ _ h

theorem pi_ext_iff : f = g ↔ ∀ i x, f (Pi.single i x) = g (Pi.single i x) :=
  ⟨fun h i x => h ▸ rfl, pi_ext⟩

/-- This is used as the ext lemma instead of `linear_map.pi_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[ext]
theorem pi_ext' (h : ∀ i, f.comp (single i) = g.comp (single i)) : f = g := by
  refine' pi_ext fun i x => _
  convert LinearMap.congr_fun (h i) x

theorem pi_ext'_iff : f = g ↔ ∀ i, f.comp (single i) = g.comp (single i) :=
  ⟨fun h i => h ▸ rfl, pi_ext'⟩

end Ext

section

variable (R φ)

/-- If `I` and `J` are disjoint index sets, the product of the kernels of the `J`th projections of
`φ` is linearly equivalent to the product over `I`. -/
def infiKerProjEquiv {I J : Set ι} [DecidablePred fun i => i ∈ I] (hd : Disjoint I J) (hu : Set.Univ ⊆ I ∪ J) :
    (⨅ i ∈ J, ker (proj i) : Submodule R (∀ i, φ i)) ≃ₗ[R] ∀ i : I, φ i := by
  refine'
    LinearEquiv.ofLinear (pi fun i => (proj (i : ι)).comp (Submodule.subtype _))
      (cod_restrict _ (pi fun i => if h : i ∈ I then proj (⟨i, h⟩ : I) else 0) _) _ _
  · intro b
    simp only [← mem_infi, ← mem_ker, ← funext_iff, ← proj_apply, ← pi_apply]
    intro j hjJ
    have : j ∉ I := fun hjI => hd ⟨hjI, hjJ⟩
    rw [dif_neg this, zero_apply]
    
  · simp only [← pi_comp, ← comp_assoc, ← subtype_comp_cod_restrict, ← proj_pi, ← Subtype.coe_prop]
    ext b ⟨j, hj⟩
    simp only [← dif_pos, ← Function.comp_app, ← Function.eval_apply, ← LinearMap.cod_restrict_apply, ←
      LinearMap.coe_comp, ← LinearMap.coe_proj, ← LinearMap.pi_apply, ← Submodule.subtype_apply, ← Subtype.coe_prop]
    rfl
    
  · ext1 ⟨b, hb⟩
    apply Subtype.ext
    ext j
    have hb : ∀, ∀ i ∈ J, ∀, b i = 0 := by
      simpa only [← mem_infi, ← mem_ker, ← proj_apply] using (mem_infi _).1 hb
    simp only [← comp_apply, ← pi_apply, ← id_apply, ← proj_apply, ← subtype_apply, ← cod_restrict_apply]
    split_ifs
    · rfl
      
    · exact (hb _ <| (hu trivialₓ).resolve_left h).symm
      
    

end

section

variable [DecidableEq ι]

/-- `diag i j` is the identity map if `i = j`. Otherwise it is the constant 0 map. -/
def diag (i j : ι) : φ i →ₗ[R] φ j :=
  @Function.update ι (fun j => φ i →ₗ[R] φ j) _ 0 i id j

theorem update_apply (f : ∀ i, M₂ →ₗ[R] φ i) (c : M₂) (i j : ι) (b : M₂ →ₗ[R] φ i) :
    (update f i b j) c = update (fun i => f i c) i (b c) j := by
  by_cases' j = i
  · rw [h, update_same, update_same]
    
  · rw [update_noteq h, update_noteq h]
    

end

end LinearMap

namespace Submodule

variable [Semiringₓ R] {φ : ι → Type _} [∀ i, AddCommMonoidₓ (φ i)] [∀ i, Module R (φ i)]

open LinearMap

/-- A version of `set.pi` for submodules. Given an index set `I` and a family of submodules
`p : Π i, submodule R (φ i)`, `pi I s` is the submodule of dependent functions `f : Π i, φ i`
such that `f i` belongs to `p a` whenever `i ∈ I`. -/
def pi (I : Set ι) (p : ∀ i, Submodule R (φ i)) : Submodule R (∀ i, φ i) where
  Carrier := Set.Pi I fun i => p i
  zero_mem' := fun i hi => (p i).zero_mem
  add_mem' := fun x y hx hy i hi => (p i).add_mem (hx i hi) (hy i hi)
  smul_mem' := fun c x hx i hi => (p i).smul_mem c (hx i hi)

variable {I : Set ι} {p q : ∀ i, Submodule R (φ i)} {x : ∀ i, φ i}

@[simp]
theorem mem_pi : x ∈ pi I p ↔ ∀, ∀ i ∈ I, ∀, x i ∈ p i :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_pi : (pi I p : Set (∀ i, φ i)) = Set.Pi I fun i => p i :=
  rfl

@[simp]
theorem pi_empty (p : ∀ i, Submodule R (φ i)) : pi ∅ p = ⊤ :=
  SetLike.coe_injective <| Set.empty_pi _

@[simp]
theorem pi_top (s : Set ι) : (pi s fun i : ι => (⊤ : Submodule R (φ i))) = ⊤ :=
  SetLike.coe_injective <| Set.pi_univ _

theorem pi_mono {s : Set ι} (h : ∀, ∀ i ∈ s, ∀, p i ≤ q i) : pi s p ≤ pi s q :=
  Set.pi_mono h

theorem binfi_comap_proj : (⨅ i ∈ I, comap (proj i) (p i)) = pi I p := by
  ext x
  simp

theorem infi_comap_proj : (⨅ i, comap (proj i) (p i)) = pi Set.Univ p := by
  ext x
  simp

theorem supr_map_single [DecidableEq ι] [Fintype ι] : (⨆ i, map (LinearMap.single i) (p i)) = pi Set.Univ p := by
  refine' (supr_le fun i => _).antisymm _
  · rintro _ ⟨x, hx : x ∈ p i, rfl⟩ j -
    rcases em (j = i) with (rfl | hj) <;> simp [*]
    
  · intro x hx
    rw [← Finset.univ_sum_single x]
    exact sum_mem_supr fun i => mem_map_of_mem (hx i trivialₓ)
    

end Submodule

namespace LinearEquiv

variable [Semiringₓ R] {φ ψ χ : ι → Type _} [∀ i, AddCommMonoidₓ (φ i)] [∀ i, Module R (φ i)]

variable [∀ i, AddCommMonoidₓ (ψ i)] [∀ i, Module R (ψ i)]

variable [∀ i, AddCommMonoidₓ (χ i)] [∀ i, Module R (χ i)]

/-- Combine a family of linear equivalences into a linear equivalence of `pi`-types.

This is `equiv.Pi_congr_right` as a `linear_equiv` -/
@[simps apply]
def piCongrRight (e : ∀ i, φ i ≃ₗ[R] ψ i) : (∀ i, φ i) ≃ₗ[R] ∀ i, ψ i :=
  { AddEquiv.piCongrRight fun j => (e j).toAddEquiv with toFun := fun f i => e i (f i),
    invFun := fun f i => (e i).symm (f i),
    map_smul' := fun c f => by
      ext
      simp }

@[simp]
theorem Pi_congr_right_refl : (piCongrRight fun j => refl R (φ j)) = refl _ _ :=
  rfl

@[simp]
theorem Pi_congr_right_symm (e : ∀ i, φ i ≃ₗ[R] ψ i) : (piCongrRight e).symm = Pi_congr_right fun i => (e i).symm :=
  rfl

@[simp]
theorem Pi_congr_right_trans (e : ∀ i, φ i ≃ₗ[R] ψ i) (f : ∀ i, ψ i ≃ₗ[R] χ i) :
    (piCongrRight e).trans (piCongrRight f) = Pi_congr_right fun i => (e i).trans (f i) :=
  rfl

variable (R φ)

/-- Transport dependent functions through an equivalence of the base space.

This is `equiv.Pi_congr_left'` as a `linear_equiv`. -/
@[simps (config := { simpRhs := true })]
def piCongrLeft' (e : ι ≃ ι') : (∀ i', φ i') ≃ₗ[R] ∀ i, φ <| e.symm i :=
  { Equivₓ.piCongrLeft' φ e with map_add' := fun x y => rfl, map_smul' := fun x y => rfl }

/-- Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".

This is `equiv.Pi_congr_left` as a `linear_equiv` -/
def piCongrLeft (e : ι' ≃ ι) : (∀ i', φ (e i')) ≃ₗ[R] ∀ i, φ i :=
  (piCongrLeft' R φ e.symm).symm

/-- This is `equiv.pi_option_equiv_prod` as a `linear_equiv` -/
def piOptionEquivProd {ι : Type _} {M : Option ι → Type _} [∀ i, AddCommGroupₓ (M i)] [∀ i, Module R (M i)] :
    (∀ i : Option ι, M i) ≃ₗ[R] M none × ∀ i : ι, M (some i) :=
  { Equivₓ.piOptionEquivProd with
    map_add' := by
      simp [← Function.funext_iffₓ],
    map_smul' := by
      simp [← Function.funext_iffₓ] }

variable (ι R M) (S : Type _) [Fintype ι] [DecidableEq ι] [Semiringₓ S] [AddCommMonoidₓ M] [Module R M] [Module S M]
  [SmulCommClass R S M]

/-- Linear equivalence between linear functions `Rⁿ → M` and `Mⁿ`. The spaces `Rⁿ` and `Mⁿ`
are represented as `ι → R` and `ι → M`, respectively, where `ι` is a finite type.

This as an `S`-linear equivalence, under the assumption that `S` acts on `M` commuting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings]. -/
def piRing : ((ι → R) →ₗ[R] M) ≃ₗ[S] ι → M :=
  (LinearMap.lsum R (fun i : ι => R) S).symm.trans (Pi_congr_right fun i => LinearMap.ringLmapEquivSelf R S M)

variable {ι R M}

@[simp]
theorem pi_ring_apply (f : (ι → R) →ₗ[R] M) (i : ι) : piRing R M ι S f i = f (Pi.single i 1) :=
  rfl

@[simp]
theorem pi_ring_symm_apply (f : ι → M) (g : ι → R) : (piRing R M ι S).symm f g = ∑ i, g i • f i := by
  simp [← pi_ring, ← LinearMap.lsum]

/-- `equiv.sum_arrow_equiv_prod_arrow` as a linear equivalence.
-/
-- TODO additive version?
def sumArrowLequivProdArrow (α β R M : Type _) [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] :
    (Sum α β → M) ≃ₗ[R] (α → M) × (β → M) :=
  { Equivₓ.sumArrowEquivProdArrow α β M with
    map_add' := by
      intro f g
      ext <;> rfl,
    map_smul' := by
      intro r f
      ext <;> rfl }

@[simp]
theorem sum_arrow_lequiv_prod_arrow_apply_fst {α β} (f : Sum α β → M) (a : α) :
    (sumArrowLequivProdArrow α β R M f).1 a = f (Sum.inl a) :=
  rfl

@[simp]
theorem sum_arrow_lequiv_prod_arrow_apply_snd {α β} (f : Sum α β → M) (b : β) :
    (sumArrowLequivProdArrow α β R M f).2 b = f (Sum.inr b) :=
  rfl

@[simp]
theorem sum_arrow_lequiv_prod_arrow_symm_apply_inl {α β} (f : α → M) (g : β → M) (a : α) :
    ((sumArrowLequivProdArrow α β R M).symm (f, g)) (Sum.inl a) = f a :=
  rfl

@[simp]
theorem sum_arrow_lequiv_prod_arrow_symm_apply_inr {α β} (f : α → M) (g : β → M) (b : β) :
    ((sumArrowLequivProdArrow α β R M).symm (f, g)) (Sum.inr b) = g b :=
  rfl

/-- If `ι` has a unique element, then `ι → M` is linearly equivalent to `M`. -/
@[simps (config := { simpRhs := true, fullyApplied := false })]
def funUnique (ι R M : Type _) [Unique ι] [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : (ι → M) ≃ₗ[R] M :=
  { Equivₓ.funUnique ι M with map_add' := fun f g => rfl, map_smul' := fun c f => rfl }

variable (R M)

/-- Linear equivalence between dependent functions `Π i : fin 2, M i` and `M 0 × M 1`. -/
@[simps (config := { simpRhs := true, fullyApplied := false })]
def piFinTwo (M : Finₓ 2 → Type v) [∀ i, AddCommMonoidₓ (M i)] [∀ i, Module R (M i)] : (∀ i, M i) ≃ₗ[R] M 0 × M 1 :=
  { piFinTwoEquiv M with map_add' := fun f g => rfl, map_smul' := fun c f => rfl }

/-- Linear equivalence between vectors in `M² = fin 2 → M` and `M × M`. -/
@[simps (config := { simpRhs := true, fullyApplied := false })]
def finTwoArrow : (Finₓ 2 → M) ≃ₗ[R] M × M :=
  { finTwoArrowEquiv M, piFinTwo R fun _ => M with }

end LinearEquiv

section Extend

variable (R) {η : Type x} [Semiringₓ R] (s : ι → η)

/-- `function.extend s f 0` as a bundled linear map. -/
@[simps]
noncomputable def Function.ExtendByZero.linearMap : (ι → R) →ₗ[R] η → R :=
  { Function.ExtendByZero.hom R s with toFun := fun f => Function.extendₓ s f 0,
    map_smul' := fun r f => by
      simpa using Function.extend_smul r s f 0 }

end Extend

/-! ### Bundled versions of `matrix.vec_cons` and `matrix.vec_empty`

The idea of these definitions is to be able to define a map as `x ↦ ![f₁ x, f₂ x, f₃ x]`, where
`f₁ f₂ f₃` are already linear maps, as `f₁.vec_cons $ f₂.vec_cons $ f₃.vec_cons $ vec_empty`.

While the same thing could be achieved using `linear_map.pi ![f₁, f₂, f₃]`, this is not
definitionally equal to the result using `linear_map.vec_cons`, as `fin.cases` and function
application do not commute definitionally.

Versions for when `f₁ f₂ f₃` are bilinear maps are also provided.

-/


section Finₓ

section Semiringₓ

variable [Semiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

/-- The linear map defeq to `matrix.vec_empty` -/
def LinearMap.vecEmpty : M →ₗ[R] Finₓ 0 → M₃ where
  toFun := fun m => Matrix.vecEmpty
  map_add' := fun x y => Subsingleton.elimₓ _ _
  map_smul' := fun r x => Subsingleton.elimₓ _ _

@[simp]
theorem LinearMap.vec_empty_apply (m : M) : (LinearMap.vecEmpty : M →ₗ[R] Finₓ 0 → M₃) m = ![] :=
  rfl

/-- A linear map into `fin n.succ → M₃` can be built out of a map into `M₃` and a map into
`fin n → M₃`. -/
def LinearMap.vecCons {n} (f : M →ₗ[R] M₂) (g : M →ₗ[R] Finₓ n → M₂) : M →ₗ[R] Finₓ n.succ → M₂ where
  toFun := fun m => Matrix.vecCons (f m) (g m)
  map_add' := fun x y => by
    rw [f.map_add, g.map_add, Matrix.cons_add_cons (f x)]
  map_smul' := fun c x => by
    rw [f.map_smul, g.map_smul, RingHom.id_apply, Matrix.smul_cons c (f x)]

@[simp]
theorem LinearMap.vec_cons_apply {n} (f : M →ₗ[R] M₂) (g : M →ₗ[R] Finₓ n → M₂) (m : M) :
    f.vecCons g m = Matrix.vecCons (f m) (g m) :=
  rfl

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] [AddCommMonoidₓ M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

/-- The empty bilinear map defeq to `matrix.vec_empty` -/
@[simps]
def LinearMap.vecEmpty₂ : M →ₗ[R] M₂ →ₗ[R] Finₓ 0 → M₃ where
  toFun := fun m => LinearMap.vecEmpty
  map_add' := fun x y => LinearMap.ext fun z => Subsingleton.elimₓ _ _
  map_smul' := fun r x => LinearMap.ext fun z => Subsingleton.elimₓ _ _

/-- A bilinear map into `fin n.succ → M₃` can be built out of a map into `M₃` and a map into
`fin n → M₃` -/
@[simps]
def LinearMap.vecCons₂ {n} (f : M →ₗ[R] M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂ →ₗ[R] Finₓ n → M₃) :
    M →ₗ[R] M₂ →ₗ[R] Finₓ n.succ → M₃ where
  toFun := fun m => LinearMap.vecCons (f m) (g m)
  map_add' := fun x y =>
    LinearMap.ext fun z => by
      simp only [← f.map_add, ← g.map_add, ← LinearMap.add_apply, ← LinearMap.vec_cons_apply, ←
        Matrix.cons_add_cons (f x z)]
  map_smul' := fun r x =>
    LinearMap.ext fun z => by
      simp [← Matrix.smul_cons r (f x z)]

end CommSemiringₓ

end Finₓ


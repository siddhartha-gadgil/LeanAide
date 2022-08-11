/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import Mathbin.GroupTheory.QuotientGroup
import Mathbin.LinearAlgebra.Span

/-!
# Quotients by submodules

* If `p` is a submodule of `M`, `M ⧸ p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.

-/


-- For most of this file we work over a noncommutative ring
section Ringₓ

namespace Submodule

variable {R M : Type _} {r : R} {x y : M} [Ringₓ R] [AddCommGroupₓ M] [Module R M]

variable (p p' : Submodule R M)

open LinearMap QuotientAddGroup

/-- The equivalence relation associated to a submodule `p`, defined by `x ≈ y` iff `-x + y ∈ p`.

Note this is equivalent to `y - x ∈ p`, but defined this way to be be defeq to the `add_subgroup`
version, where commutativity can't be assumed. -/
def quotientRel : Setoidₓ M :=
  QuotientAddGroup.leftRel p.toAddSubgroup

theorem quotient_rel_r_def {x y : M} : @Setoidₓ.R _ p.quotientRel x y ↔ x - y ∈ p :=
  Iff.trans
    (by
      rw [left_rel_apply, sub_eq_add_neg, neg_add, neg_negₓ]
      rfl)
    neg_mem_iff

/-- The quotient of a module `M` by a submodule `p ⊆ M`. -/
instance hasQuotient : HasQuotient M (Submodule R M) :=
  ⟨fun p => Quotientₓ (quotientRel p)⟩

namespace Quotientₓ

/-- Map associating to an element of `M` the corresponding element of `M/p`,
when `p` is a submodule of `M`. -/
def mk {p : Submodule R M} : M → M ⧸ p :=
  Quotientₓ.mk'

@[simp]
theorem mk_eq_mk {p : Submodule R M} (x : M) : @Quotientₓ.mk _ (quotientRel p) x = mk x :=
  rfl

@[simp]
theorem mk'_eq_mk {p : Submodule R M} (x : M) : (Quotientₓ.mk' x : M ⧸ p) = mk x :=
  rfl

@[simp]
theorem quot_mk_eq_mk {p : Submodule R M} (x : M) : (Quot.mk _ x : M ⧸ p) = mk x :=
  rfl

protected theorem eq' {x y : M} : (mk x : M ⧸ p) = mk y ↔ -x + y ∈ p :=
  QuotientAddGroup.eq

protected theorem eq {x y : M} : (mk x : M ⧸ p) = mk y ↔ x - y ∈ p :=
  p.trans (left_rel_apply.symm.trans p.quotient_rel_r_def)

instance : Zero (M ⧸ p) :=
  ⟨mk 0⟩

instance : Inhabited (M ⧸ p) :=
  ⟨0⟩

@[simp]
theorem mk_zero : mk 0 = (0 : M ⧸ p) :=
  rfl

@[simp]
theorem mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x ∈ p := by
  simpa using (Quotientₓ.eq p : mk x = 0 ↔ _)

instance addCommGroup : AddCommGroupₓ (M ⧸ p) :=
  QuotientAddGroup.addCommGroup p.toAddSubgroup

@[simp]
theorem mk_add : (mk (x + y) : M ⧸ p) = mk x + mk y :=
  rfl

@[simp]
theorem mk_neg : (mk (-x) : M ⧸ p) = -mk x :=
  rfl

@[simp]
theorem mk_sub : (mk (x - y) : M ⧸ p) = mk x - mk y :=
  rfl

section HasSmul

variable {S : Type _} [HasSmul S R] [HasSmul S M] [IsScalarTower S R M] (P : Submodule R M)

instance hasSmul' : HasSmul S (M ⧸ P) :=
  ⟨fun a =>
    (Quotientₓ.map' ((· • ·) a)) fun x y h =>
      left_rel_apply.mpr <| by
        simpa [← smul_sub] using P.smul_mem (a • 1 : R) (left_rel_apply.mp h)⟩

/-- Shortcut to help the elaborator in the common case. -/
instance hasSmul : HasSmul R (M ⧸ P) :=
  Quotient.hasSmul' P

@[simp]
theorem mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ p) = r • mk x :=
  rfl

instance smul_comm_class (T : Type _) [HasSmul T R] [HasSmul T M] [IsScalarTower T R M] [SmulCommClass S T M] :
    SmulCommClass S T (M ⧸ P) where smul_comm := fun x y => Quotientₓ.ind' fun z => congr_arg mk (smul_comm _ _ _)

instance is_scalar_tower (T : Type _) [HasSmul T R] [HasSmul T M] [IsScalarTower T R M] [HasSmul S T]
    [IsScalarTower S T M] :
    IsScalarTower S T (M ⧸ P) where smul_assoc := fun x y => Quotientₓ.ind' fun z => congr_arg mk (smul_assoc _ _ _)

instance is_central_scalar [HasSmul Sᵐᵒᵖ R] [HasSmul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] :
    IsCentralScalar S
      (M ⧸ P) where op_smul_eq_smul := fun x => Quotientₓ.ind' fun z => congr_arg mk <| op_smul_eq_smul _ _

end HasSmul

section Module

variable {S : Type _}

instance mulAction' [Monoidₓ S] [HasSmul S R] [MulAction S M] [IsScalarTower S R M] (P : Submodule R M) :
    MulAction S (M ⧸ P) :=
  Function.Surjective.mulAction mk (surjective_quot_mk _) P

instance mulAction (P : Submodule R M) : MulAction R (M ⧸ P) :=
  Quotient.mulAction' P

instance distribMulAction' [Monoidₓ S] [HasSmul S R] [DistribMulAction S M] [IsScalarTower S R M] (P : Submodule R M) :
    DistribMulAction S (M ⧸ P) :=
  Function.Surjective.distribMulAction ⟨mk, rfl, fun _ _ => rfl⟩ (surjective_quot_mk _) P

instance distribMulAction (P : Submodule R M) : DistribMulAction R (M ⧸ P) :=
  Quotient.distribMulAction' P

instance module' [Semiringₓ S] [HasSmul S R] [Module S M] [IsScalarTower S R M] (P : Submodule R M) :
    Module S (M ⧸ P) :=
  Function.Surjective.module _ ⟨mk, rfl, fun _ _ => rfl⟩ (surjective_quot_mk _) P

instance module (P : Submodule R M) : Module R (M ⧸ P) :=
  Quotient.module' P

variable (S)

/-- The quotient of `P` as an `S`-submodule is the same as the quotient of `P` as an `R`-submodule,
where `P : submodule R M`.
-/
def restrictScalarsEquiv [Ringₓ S] [HasSmul S R] [Module S M] [IsScalarTower S R M] (P : Submodule R M) :
    (M ⧸ P.restrictScalars S) ≃ₗ[S] M ⧸ P :=
  { Quotientₓ.congrRight fun _ _ => Iff.rfl with map_add' := fun x y => Quotientₓ.induction_on₂' x y fun x' y' => rfl,
    map_smul' := fun c x => Quotientₓ.induction_on' x fun x' => rfl }

@[simp]
theorem restrict_scalars_equiv_mk [Ringₓ S] [HasSmul S R] [Module S M] [IsScalarTower S R M] (P : Submodule R M)
    (x : M) : restrictScalarsEquiv S P (mk x) = mk x :=
  rfl

@[simp]
theorem restrict_scalars_equiv_symm_mk [Ringₓ S] [HasSmul S R] [Module S M] [IsScalarTower S R M] (P : Submodule R M)
    (x : M) : (restrictScalarsEquiv S P).symm (mk x) = mk x :=
  rfl

end Module

theorem mk_surjective : Function.Surjective (@mk _ _ _ _ _ p) := by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

theorem nontrivial_of_lt_top (h : p < ⊤) : Nontrivial (M ⧸ p) := by
  obtain ⟨x, _, not_mem_s⟩ := SetLike.exists_of_lt h
  refine' ⟨⟨mk x, 0, _⟩⟩
  simpa using not_mem_s

end Quotientₓ

section

variable {M₂ : Type _} [AddCommGroupₓ M₂] [Module R M₂]

theorem quot_hom_ext ⦃f g : M ⧸ p →ₗ[R] M₂⦄ (h : ∀ x, f (Quotient.mk x) = g (Quotient.mk x)) : f = g :=
  LinearMap.ext fun x => Quotientₓ.induction_on' x h

/-- The map from a module `M` to the quotient of `M` by a submodule `p` as a linear map. -/
def mkq : M →ₗ[R] M ⧸ p where
  toFun := Quotient.mk
  map_add' := by
    simp
  map_smul' := by
    simp

@[simp]
theorem mkq_apply (x : M) : p.mkq x = Quotient.mk x :=
  rfl

theorem mkq_surjective (A : Submodule R M) : Function.Surjective A.mkq := by
  rintro ⟨x⟩ <;> exact ⟨x, rfl⟩

end

variable {R₂ M₂ : Type _} [Ringₓ R₂] [AddCommGroupₓ M₂] [Module R₂ M₂] {τ₁₂ : R →+* R₂}

/-- Two `linear_map`s from a quotient module are equal if their compositions with
`submodule.mkq` are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem linear_map_qext ⦃f g : M ⧸ p →ₛₗ[τ₁₂] M₂⦄ (h : f.comp p.mkq = g.comp p.mkq) : f = g :=
  LinearMap.ext fun x => Quotientₓ.induction_on' x <| (LinearMap.congr_fun h : _)

/-- The map from the quotient of `M` by a submodule `p` to `M₂` induced by a linear map `f : M → M₂`
vanishing on `p`, as a linear map. -/
def liftq (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ f.ker) : M ⧸ p →ₛₗ[τ₁₂] M₂ :=
  { QuotientAddGroup.lift p.toAddSubgroup f.toAddMonoidHom h with
    map_smul' := by
      rintro a ⟨x⟩ <;> exact f.map_smulₛₗ a x }

@[simp]
theorem liftq_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) : p.liftq f h (Quotient.mk x) = f x :=
  rfl

@[simp]
theorem liftq_mkq (f : M →ₛₗ[τ₁₂] M₂) (h) : (p.liftq f h).comp p.mkq = f := by
  ext <;> rfl

/-- Special case of `liftq` when `p` is the span of `x`. In this case, the condition on `f` simply
becomes vanishing at `x`.-/
def liftqSpanSingleton (x : M) (f : M →ₛₗ[τ₁₂] M₂) (h : f x = 0) : (M ⧸ R∙x) →ₛₗ[τ₁₂] M₂ :=
  (R∙x).liftq f <| by
    rw [span_singleton_le_iff_mem, LinearMap.mem_ker, h]

@[simp]
theorem liftq_span_singleton_apply (x : M) (f : M →ₛₗ[τ₁₂] M₂) (h : f x = 0) (y : M) :
    liftqSpanSingleton x f h (Quotient.mk y) = f y :=
  rfl

@[simp]
theorem range_mkq : p.mkq.range = ⊤ :=
  eq_top_iff'.2 <| by
    rintro ⟨x⟩ <;> exact ⟨x, rfl⟩

@[simp]
theorem ker_mkq : p.mkq.ker = p := by
  ext <;> simp

theorem le_comap_mkq (p' : Submodule R (M ⧸ p)) : p ≤ comap p.mkq p' := by
  simpa using (comap_mono bot_le : p.mkq.ker ≤ comap p.mkq p')

@[simp]
theorem mkq_map_self : map p.mkq p = ⊥ := by
  rw [eq_bot_iff, map_le_iff_le_comap, comap_bot, ker_mkq] <;> exact le_rfl

@[simp]
theorem comap_map_mkq : comap p.mkq (map p.mkq p') = p⊔p' := by
  simp [← comap_map_eq, ← sup_comm]

@[simp]
theorem map_mkq_eq_top : map p.mkq p' = ⊤ ↔ p⊔p' = ⊤ := by
  simp only [← map_eq_top_iff p.range_mkq, ← sup_comm, ← ker_mkq]

variable (q : Submodule R₂ M₂)

/-- The map from the quotient of `M` by submodule `p` to the quotient of `M₂` by submodule `q` along
`f : M → M₂` is linear. -/
def mapq (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) : M ⧸ p →ₛₗ[τ₁₂] M₂ ⧸ q :=
  p.liftq (q.mkq.comp f) <| by
    simpa [← ker_comp] using h

@[simp]
theorem mapq_apply (f : M →ₛₗ[τ₁₂] M₂) {h} (x : M) : mapq p q f h (Quotient.mk x) = Quotient.mk (f x) :=
  rfl

theorem mapq_mkq (f : M →ₛₗ[τ₁₂] M₂) {h} : (mapq p q f h).comp p.mkq = q.mkq.comp f := by
  ext x <;> rfl

@[simp]
theorem mapq_zero
    (h : p ≤ q.comap (0 : M →ₛₗ[τ₁₂] M₂) := by
      simp ) :
    p.mapq q (0 : M →ₛₗ[τ₁₂] M₂) h = 0 := by
  ext
  simp

/-- Given submodules `p ⊆ M`, `p₂ ⊆ M₂`, `p₃ ⊆ M₃` and maps `f : M → M₂`, `g : M₂ → M₃` inducing
`mapq f : M ⧸ p → M₂ ⧸ p₂` and `mapq g : M₂ ⧸ p₂ → M₃ ⧸ p₃` then
`mapq (g ∘ f) = (mapq g) ∘ (mapq f)`. -/
theorem mapq_comp {R₃ M₃ : Type _} [Ringₓ R₃] [AddCommGroupₓ M₃] [Module R₃ M₃] (p₂ : Submodule R₂ M₂)
    (p₃ : Submodule R₃ M₃) {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃} [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃] (f : M →ₛₗ[τ₁₂] M₂)
    (g : M₂ →ₛₗ[τ₂₃] M₃) (hf : p ≤ p₂.comap f) (hg : p₂ ≤ p₃.comap g) (h := hf.trans (comap_mono hg)) :
    p.mapq p₃ (g.comp f) h = (p₂.mapq p₃ g hg).comp (p.mapq p₂ f hf) := by
  ext
  simp

@[simp]
theorem mapq_id
    (h : p ≤ p.comap LinearMap.id := by
      simp ) :
    p.mapq p LinearMap.id h = LinearMap.id := by
  ext
  simp

theorem mapq_pow {f : M →ₗ[R] M} (h : p ≤ p.comap f) (k : ℕ)
    (h' : p ≤ p.comap (f ^ k) := p.le_comap_pow_of_le_comap h k) : p.mapq p (f ^ k) h' = p.mapq p f h ^ k := by
  induction' k with k ih
  · simp [← LinearMap.one_eq_id]
    
  · simp only [← LinearMap.iterate_succ, ih]
    apply p.mapq_comp
    

theorem comap_liftq (f : M →ₛₗ[τ₁₂] M₂) (h) : q.comap (p.liftq f h) = (q.comap f).map (mkq p) :=
  le_antisymmₓ
    (by
      rintro ⟨x⟩ hx <;> exact ⟨_, hx, rfl⟩)
    (by
      rw [map_le_iff_le_comap, ← comap_comp, liftq_mkq] <;> exact le_rfl)

theorem map_liftq [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (h) (q : Submodule R (M ⧸ p)) :
    q.map (p.liftq f h) = (q.comap p.mkq).map f :=
  le_antisymmₓ
    (by
      rintro _ ⟨⟨x⟩, hxq, rfl⟩ <;> exact ⟨x, hxq, rfl⟩)
    (by
      rintro _ ⟨x, hxq, rfl⟩ <;> exact ⟨Quotientₓ.mk x, hxq, rfl⟩)

theorem ker_liftq (f : M →ₛₗ[τ₁₂] M₂) (h) : ker (p.liftq f h) = (ker f).map (mkq p) :=
  comap_liftq _ _ _ _

theorem range_liftq [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (h) : range (p.liftq f h) = range f := by
  simpa only [← range_eq_map] using map_liftq _ _ _ _

theorem ker_liftq_eq_bot (f : M →ₛₗ[τ₁₂] M₂) (h) (h' : ker f ≤ p) : ker (p.liftq f h) = ⊥ := by
  rw [ker_liftq, le_antisymmₓ h h', mkq_map_self]

/-- The correspondence theorem for modules: there is an order isomorphism between submodules of the
quotient of `M` by `p`, and submodules of `M` larger than `p`. -/
def ComapMkq.relIso : Submodule R (M ⧸ p) ≃o { p' : Submodule R M // p ≤ p' } where
  toFun := fun p' => ⟨comap p.mkq p', le_comap_mkq p _⟩
  invFun := fun q => map p.mkq q
  left_inv := fun p' =>
    map_comap_eq_self <| by
      simp
  right_inv := fun ⟨q, hq⟩ =>
    Subtype.ext_val <| by
      simpa [← comap_map_mkq p]
  map_rel_iff' := fun p₁ p₂ => comap_le_comap_iff <| range_mkq _

/-- The ordering on submodules of the quotient of `M` by `p` embeds into the ordering on submodules
of `M`. -/
def ComapMkq.orderEmbedding : Submodule R (M ⧸ p) ↪o Submodule R M :=
  (RelIso.toRelEmbedding <| ComapMkq.relIso p).trans (Subtype.relEmbedding _ _)

@[simp]
theorem comap_mkq_embedding_eq (p' : Submodule R (M ⧸ p)) : ComapMkq.orderEmbedding p p' = comap p.mkq p' :=
  rfl

theorem span_preimage_eq [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {s : Set M₂} (h₀ : s.Nonempty) (h₁ : s ⊆ range f) :
    span R (f ⁻¹' s) = (span R₂ s).comap f := by
  suffices (span R₂ s).comap f ≤ span R (f ⁻¹' s) by
    exact le_antisymmₓ (span_preimage_le f s) this
  have hk : ker f ≤ span R (f ⁻¹' s) := by
    let y := Classical.some h₀
    have hy : y ∈ s := Classical.some_spec h₀
    rw [ker_le_iff]
    use y, h₁ hy
    rw [← Set.singleton_subset_iff] at hy
    exact Set.Subset.trans subset_span (span_mono (Set.preimage_mono hy))
  rw [← left_eq_sup] at hk
  rw [f.range_coe] at h₁
  rw [hk, ← LinearMap.map_le_map_iff, map_span, map_comap_eq, Set.image_preimage_eq_of_subset h₁]
  exact inf_le_right

end Submodule

open Submodule

namespace LinearMap

section Ringₓ

variable {R M R₂ M₂ R₃ M₃ : Type _}

variable [Ringₓ R] [Ringₓ R₂] [Ringₓ R₃]

variable [AddCommMonoidₓ M] [AddCommGroupₓ M₂] [AddCommMonoidₓ M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃] [RingHomSurjective τ₁₂]

theorem range_mkq_comp (f : M →ₛₗ[τ₁₂] M₂) : f.range.mkq.comp f = 0 :=
  LinearMap.ext fun x => by
    simp

theorem ker_le_range_iff {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₃] M₃} :
    g.ker ≤ f.range ↔ f.range.mkq.comp g.ker.Subtype = 0 := by
  rw [← range_le_ker_iff, Submodule.ker_mkq, Submodule.range_subtype]

/-- An epimorphism is surjective. -/
theorem range_eq_top_of_cancel {f : M →ₛₗ[τ₁₂] M₂} (h : ∀ u v : M₂ →ₗ[R₂] M₂ ⧸ f.range, u.comp f = v.comp f → u = v) :
    f.range = ⊤ := by
  have h₁ : (0 : M₂ →ₗ[R₂] M₂ ⧸ f.range).comp f = 0 := zero_comp _
  rw [← Submodule.ker_mkq f.range, ← h 0 f.range.mkq (Eq.trans h₁ (range_mkq_comp _).symm)]
  exact ker_zero

end Ringₓ

end LinearMap

open LinearMap

namespace Submodule

variable {R M : Type _} {r : R} {x y : M} [Ringₓ R] [AddCommGroupₓ M] [Module R M]

variable (p p' : Submodule R M)

/-- If `p = ⊥`, then `M / p ≃ₗ[R] M`. -/
def quotEquivOfEqBot (hp : p = ⊥) : (M ⧸ p) ≃ₗ[R] M :=
  LinearEquiv.ofLinear (p.liftq id <| hp.symm ▸ bot_le) p.mkq (liftq_mkq _ _ _) <| p.quot_hom_ext fun x => rfl

@[simp]
theorem quot_equiv_of_eq_bot_apply_mk (hp : p = ⊥) (x : M) : p.quotEquivOfEqBot hp (Quotient.mk x) = x :=
  rfl

@[simp]
theorem quot_equiv_of_eq_bot_symm_apply (hp : p = ⊥) (x : M) : (p.quotEquivOfEqBot hp).symm x = Quotient.mk x :=
  rfl

@[simp]
theorem coe_quot_equiv_of_eq_bot_symm (hp : p = ⊥) : ((p.quotEquivOfEqBot hp).symm : M →ₗ[R] M ⧸ p) = p.mkq :=
  rfl

/-- Quotienting by equal submodules gives linearly equivalent quotients. -/
def quotEquivOfEq (h : p = p') : (M ⧸ p) ≃ₗ[R] M ⧸ p' :=
  { (@Quotientₓ.congr _ _ (quotientRel p) (quotientRel p') (Equivₓ.refl _)) fun a b => by
      subst h
      rfl with
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl,
    map_smul' := by
      rintro x ⟨y⟩
      rfl }

@[simp]
theorem quot_equiv_of_eq_mk (h : p = p') (x : M) :
    Submodule.quotEquivOfEq p p' h (Submodule.Quotient.mk x) = Submodule.Quotient.mk x :=
  rfl

end Submodule

end Ringₓ

section CommRingₓ

variable {R M M₂ : Type _} {r : R} {x y : M} [CommRingₓ R] [AddCommGroupₓ M] [Module R M] [AddCommGroupₓ M₂]
  [Module R M₂] (p : Submodule R M) (q : Submodule R M₂)

namespace Submodule

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`,
the natural map $\{f ∈ Hom(M, M₂) | f(p) ⊆ q \} \to Hom(M/p, M₂/q)$ is linear. -/
def mapqLinear : compatibleMaps p q →ₗ[R] M ⧸ p →ₗ[R] M₂ ⧸ q where
  toFun := fun f => mapq _ _ f.val f.property
  map_add' := fun x y => by
    ext
    rfl
  map_smul' := fun c f => by
    ext
    rfl

end Submodule

end CommRingₓ


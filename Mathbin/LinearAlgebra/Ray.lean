/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathbin.LinearAlgebra.Basic

/-!
# Rays in modules

This file defines rays in modules.

## Main definitions

* `same_ray`: two vectors belong to the same ray if they are proportional with a nonnegative
  coefficient.

* `module.ray` is a type for the equivalence class of nonzero vectors in a module with some
common positive multiple.
-/


noncomputable section

open BigOperators

section OrderedCommSemiring

variable (R : Type _) [OrderedCommSemiring R]

variable {M : Type _} [AddCommMonoidₓ M] [Module R M]

variable {N : Type _} [AddCommMonoidₓ N] [Module R N]

variable (ι : Type _) [DecidableEq ι]

/-- Two vectors are in the same ray if either one of them is zero or some positive multiples of them
are equal (in the typical case over a field, this means one of them is a nonnegative multiple of
the other). -/
def SameRay (v₁ v₂ : M) : Prop :=
  v₁ = 0 ∨ v₂ = 0 ∨ ∃ r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • v₁ = r₂ • v₂

variable {R}

namespace SameRay

variable {x y z : M}

@[simp]
theorem zero_left (y : M) : SameRay R 0 y :=
  Or.inl rfl

@[simp]
theorem zero_right (x : M) : SameRay R x 0 :=
  Or.inr <| Or.inl rfl

@[nontriviality]
theorem of_subsingleton [Subsingleton M] (x y : M) : SameRay R x y := by
  rw [Subsingleton.elimₓ x 0]
  exact zero_left _

@[nontriviality]
theorem of_subsingleton' [Subsingleton R] (x y : M) : SameRay R x y := by
  have := Module.subsingleton R M
  exact of_subsingleton x y

/-- `same_ray` is reflexive. -/
@[refl]
theorem refl (x : M) : SameRay R x x := by
  nontriviality R
  exact Or.inr (Or.inr <| ⟨1, 1, zero_lt_one, zero_lt_one, rfl⟩)

protected theorem rfl : SameRay R x x :=
  refl _

/-- `same_ray` is symmetric. -/
@[symm]
theorem symm (h : SameRay R x y) : SameRay R y x :=
  (Or.left_comm.1 h).imp_right <| Or.imp_rightₓ fun ⟨r₁, r₂, h₁, h₂, h⟩ => ⟨r₂, r₁, h₂, h₁, h.symm⟩

/-- If `x` and `y` are nonzero vectors on the same ray, then there exist positive numbers `r₁ r₂`
such that `r₁ • x = r₂ • y`. -/
theorem exists_pos (h : SameRay R x y) (hx : x ≠ 0) (hy : y ≠ 0) : ∃ r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • x = r₂ • y :=
  (h.resolve_left hx).resolve_left hy

theorem _root_.same_ray_comm : SameRay R x y ↔ SameRay R y x :=
  ⟨SameRay.symm, SameRay.symm⟩

/-- `same_ray` is transitive unless the vector in the middle is zero and both other vectors are
nonzero. -/
theorem trans (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y = 0 → x = 0 ∨ z = 0) : SameRay R x z := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · exact zero_left z
    
  rcases eq_or_ne z 0 with (rfl | hz)
  · exact zero_right x
    
  rcases eq_or_ne y 0 with (rfl | hy)
  · exact (hy rfl).elim (fun h => (hx h).elim) fun h => (hz h).elim
    
  rcases hxy.exists_pos hx hy with ⟨r₁, r₂, hr₁, hr₂, h₁⟩
  rcases hyz.exists_pos hy hz with ⟨r₃, r₄, hr₃, hr₄, h₂⟩
  refine' Or.inr (Or.inr <| ⟨r₃ * r₁, r₂ * r₄, mul_pos hr₃ hr₁, mul_pos hr₂ hr₄, _⟩)
  rw [mul_smul, mul_smul, h₁, ← h₂, smul_comm]

/-- A vector is in the same ray as a nonnegative multiple of itself. -/
theorem _root_.same_ray_nonneg_smul_right (v : M) {r : R} (h : 0 ≤ r) : SameRay R v (r • v) :=
  Or.inr <|
    (h.eq_or_lt.imp fun h => h ▸ zero_smul R v) fun h =>
      ⟨r, 1, h, by
        nontriviality R
        exact zero_lt_one, (one_smul _ _).symm⟩

/-- A vector is in the same ray as a positive multiple of itself. -/
theorem _root_.same_ray_pos_smul_right (v : M) {r : R} (h : 0 < r) : SameRay R v (r • v) :=
  same_ray_nonneg_smul_right v h.le

/-- A vector is in the same ray as a nonnegative multiple of one it is in the same ray as. -/
theorem nonneg_smul_right {r : R} (h : SameRay R x y) (hr : 0 ≤ r) : SameRay R x (r • y) :=
  (h.trans (same_ray_nonneg_smul_right y hr)) fun hy =>
    Or.inr <| by
      rw [hy, smul_zero]

/-- A vector is in the same ray as a positive multiple of one it is in the same ray as. -/
theorem pos_smul_right {r : R} (h : SameRay R x y) (hr : 0 < r) : SameRay R x (r • y) :=
  h.nonneg_smul_right hr.le

/-- A nonnegative multiple of a vector is in the same ray as that vector. -/
theorem _root_.same_ray_nonneg_smul_left (v : M) {r : R} (h : 0 ≤ r) : SameRay R (r • v) v :=
  (same_ray_nonneg_smul_right v h).symm

/-- A positive multiple of a vector is in the same ray as that vector. -/
theorem _root_.same_ray_pos_smul_left (v : M) {r : R} (h : 0 < r) : SameRay R (r • v) v :=
  same_ray_nonneg_smul_left v h.le

/-- A nonnegative multiple of a vector is in the same ray as one it is in the same ray as. -/
theorem nonneg_smul_left {r : R} (h : SameRay R x y) (hr : 0 ≤ r) : SameRay R (r • x) y :=
  (h.symm.nonneg_smul_right hr).symm

/-- A positive multiple of a vector is in the same ray as one it is in the same ray as. -/
theorem pos_smul_left {r : R} (h : SameRay R x y) (hr : 0 < r) : SameRay R (r • x) y :=
  h.nonneg_smul_left hr.le

/-- If two vectors are on the same ray then they remain so after applying a linear map. -/
theorem map (f : M →ₗ[R] N) (h : SameRay R x y) : SameRay R (f x) (f y) :=
  (h.imp fun hx => by
      rw [hx, map_zero]) <|
    (Or.imp fun hy => by
        rw [hy, map_zero])
      fun ⟨r₁, r₂, hr₁, hr₂, h⟩ =>
      ⟨r₁, r₂, hr₁, hr₂, by
        rw [← f.map_smul, ← f.map_smul, h]⟩

/-- The images of two vectors under a linear equivalence are on the same ray if and only if the
original vectors are on the same ray. -/
@[simp]
theorem _root_.same_ray_map_iff (e : M ≃ₗ[R] N) : SameRay R (e x) (e y) ↔ SameRay R x y :=
  ⟨fun h => by
    simpa using SameRay.map e.symm.to_linear_map h, SameRay.map e.toLinearMap⟩

/-- If two vectors are on the same ray then both scaled by the same action are also on the same
ray. -/
theorem smul {S : Type _} [Monoidₓ S] [DistribMulAction S M] [SmulCommClass R S M] (h : SameRay R x y) (s : S) :
    SameRay R (s • x) (s • y) :=
  h.map (s • (LinearMap.id : M →ₗ[R] M))

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- If `x` and `y` are on the same ray as `z`, then so is `x + y`. -/
theorem add_left (hx : SameRay R x z) (hy : SameRay R y z) : SameRay R (x + y) z := by
  rcases eq_or_ne x 0 with (rfl | hx₀)
  · rwa [zero_addₓ]
    
  rcases eq_or_ne y 0 with (rfl | hy₀)
  · rwa [add_zeroₓ]
    
  rcases eq_or_ne z 0 with (rfl | hz₀)
  · apply zero_right
    
  rcases hx.exists_pos hx₀ hz₀ with ⟨rx, rz₁, hrx, hrz₁, Hx⟩
  rcases hy.exists_pos hy₀ hz₀ with ⟨ry, rz₂, hry, hrz₂, Hy⟩
  refine' Or.inr (Or.inr ⟨rx * ry, ry * rz₁ + rx * rz₂, mul_pos hrx hry, _, _⟩)
  · apply_rules [add_pos, mul_pos]
    
  · simp only [← mul_smul, ← smul_add, ← add_smul, Hx, Hy]
    rw [smul_comm]
    

/-- If `y` and `z` are on the same ray as `x`, then so is `y + z`. -/
theorem add_right (hy : SameRay R x y) (hz : SameRay R x z) : SameRay R x (y + z) :=
  (hy.symm.add_left hz.symm).symm

end SameRay

/-- Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that
`ray_vector.setoid` can be an instance. -/
@[nolint unused_arguments has_inhabited_instance]
def RayVector (R M : Type _) [Zero M] :=
  { v : M // v ≠ 0 }

instance RayVector.hasCoe {R M : Type _} [Zero M] : Coe (RayVector R M) M :=
  coeSubtype

instance {R M : Type _} [Zero M] [Nontrivial M] : Nonempty (RayVector R M) :=
  let ⟨x, hx⟩ := exists_ne (0 : M)
  ⟨⟨x, hx⟩⟩

variable (R M)

/-- The setoid of the `same_ray` relation for the subtype of nonzero vectors. -/
instance : Setoidₓ (RayVector R M) where
  R := fun x y => SameRay R (x : M) y
  iseqv := ⟨fun x => SameRay.refl _, fun x y h => h.symm, fun x y z hxy hyz => (hxy.trans hyz) fun hy => (y.2 hy).elim⟩

/-- A ray (equivalence class of nonzero vectors with common positive multiples) in a module. -/
@[nolint has_inhabited_instance]
def Module.Ray :=
  Quotientₓ (RayVector.setoid R M)

variable {R M}

/-- Equivalence of nonzero vectors, in terms of same_ray. -/
theorem equiv_iff_same_ray {v₁ v₂ : RayVector R M} : v₁ ≈ v₂ ↔ SameRay R (v₁ : M) v₂ :=
  Iff.rfl

variable (R)

/-- The ray given by a nonzero vector. -/
protected def rayOfNeZero (v : M) (h : v ≠ 0) : Module.Ray R M :=
  ⟦⟨v, h⟩⟧

/-- An induction principle for `module.ray`, used as `induction x using module.ray.ind`. -/
theorem Module.Ray.ind {C : Module.Ray R M → Prop} (h : ∀ (v) (hv : v ≠ 0), C (rayOfNeZero R v hv))
    (x : Module.Ray R M) : C x :=
  Quotientₓ.ind (Subtype.rec <| h) x

variable {R}

instance [Nontrivial M] : Nonempty (Module.Ray R M) :=
  Nonempty.map Quotientₓ.mk inferInstance

/-- The rays given by two nonzero vectors are equal if and only if those vectors
satisfy `same_ray`. -/
theorem ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    rayOfNeZero R _ hv₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂ :=
  Quotientₓ.eq

/-- The ray given by a positive multiple of a nonzero vector. -/
@[simp]
theorem ray_pos_smul {v : M} (h : v ≠ 0) {r : R} (hr : 0 < r) (hrv : r • v ≠ 0) :
    rayOfNeZero R (r • v) hrv = rayOfNeZero R v h :=
  (ray_eq_iff _ _).2 <| same_ray_pos_smul_left v hr

/-- An equivalence between modules implies an equivalence between ray vectors. -/
def RayVector.mapLinearEquiv (e : M ≃ₗ[R] N) : RayVector R M ≃ RayVector R N :=
  (Equivₓ.subtypeEquiv e.toEquiv) fun _ => e.map_ne_zero_iff.symm

/-- An equivalence between modules implies an equivalence between rays. -/
def Module.Ray.map (e : M ≃ₗ[R] N) : Module.Ray R M ≃ Module.Ray R N :=
  (Quotientₓ.congr (RayVector.mapLinearEquiv e)) fun ⟨a, ha⟩ ⟨b, hb⟩ => (same_ray_map_iff _).symm

@[simp]
theorem Module.Ray.map_apply (e : M ≃ₗ[R] N) (v : M) (hv : v ≠ 0) :
    Module.Ray.map e (rayOfNeZero _ v hv) = rayOfNeZero _ (e v) (e.map_ne_zero_iff.2 hv) :=
  rfl

@[simp]
theorem Module.Ray.map_refl : (Module.Ray.map <| LinearEquiv.refl R M) = Equivₓ.refl _ :=
  Equivₓ.ext <| (Module.Ray.ind R) fun _ _ => rfl

@[simp]
theorem Module.Ray.map_symm (e : M ≃ₗ[R] N) : (Module.Ray.map e).symm = Module.Ray.map e.symm :=
  rfl

section Action

variable {G : Type _} [Groupₓ G] [DistribMulAction G M]

/-- Any invertible action preserves the non-zeroness of ray vectors. This is primarily of interest
when `G = Rˣ` -/
instance {R : Type _} : MulAction G (RayVector R M) where
  smul := fun r => (Subtype.map ((· • ·) r)) fun a => (smul_ne_zero_iff_ne _).2
  mul_smul := fun a b m => Subtype.ext <| mul_smul a b _
  one_smul := fun m => Subtype.ext <| one_smul _ _

variable [SmulCommClass R G M]

/-- Any invertible action preserves the non-zeroness of rays. This is primarily of interest when
`G = Rˣ` -/
instance : MulAction G (Module.Ray R M) where
  smul := fun r => Quotientₓ.map ((· • ·) r) fun a b h => h.smul _
  mul_smul := fun a b => Quotientₓ.ind fun m => congr_arg Quotientₓ.mk <| mul_smul a b _
  one_smul := Quotientₓ.ind fun m => congr_arg Quotientₓ.mk <| one_smul _ _

/-- The action via `linear_equiv.apply_distrib_mul_action` corresponds to `module.ray.map`. -/
@[simp]
theorem Module.Ray.linear_equiv_smul_eq_map (e : M ≃ₗ[R] M) (v : Module.Ray R M) : e • v = Module.Ray.map e v :=
  rfl

@[simp]
theorem smul_ray_of_ne_zero (g : G) (v : M) (hv) :
    g • rayOfNeZero R v hv = rayOfNeZero R (g • v) ((smul_ne_zero_iff_ne _).2 hv) :=
  rfl

end Action

namespace Module.Ray

/-- Scaling by a positive unit is a no-op. -/
theorem units_smul_of_pos (u : Rˣ) (hu : 0 < (u : R)) (v : Module.Ray R M) : u • v = v := by
  induction v using Module.Ray.ind
  rw [smul_ray_of_ne_zero, ray_eq_iff]
  exact same_ray_pos_smul_left _ hu

/-- An arbitrary `ray_vector` giving a ray. -/
def someRayVector (x : Module.Ray R M) : RayVector R M :=
  Quotientₓ.out x

/-- The ray of `some_ray_vector`. -/
@[simp]
theorem some_ray_vector_ray (x : Module.Ray R M) : (⟦x.someRayVector⟧ : Module.Ray R M) = x :=
  Quotientₓ.out_eq _

/-- An arbitrary nonzero vector giving a ray. -/
def someVector (x : Module.Ray R M) : M :=
  x.someRayVector

/-- `some_vector` is nonzero. -/
@[simp]
theorem some_vector_ne_zero (x : Module.Ray R M) : x.someVector ≠ 0 :=
  x.someRayVector.property

/-- The ray of `some_vector`. -/
@[simp]
theorem some_vector_ray (x : Module.Ray R M) : rayOfNeZero R _ x.some_vector_ne_zero = x :=
  (congr_arg _ (Subtype.coe_eta _ _) : _).trans x.out_eq

end Module.Ray

end OrderedCommSemiring

section OrderedCommRing

variable {R : Type _} [OrderedCommRing R]

variable {M N : Type _} [AddCommGroupₓ M] [AddCommGroupₓ N] [Module R M] [Module R N] {x y : M}

/-- `same_ray.neg` as an `iff`. -/
@[simp]
theorem same_ray_neg_iff : SameRay R (-x) (-y) ↔ SameRay R x y := by
  simp only [← SameRay, ← neg_eq_zero, ← smul_neg, ← neg_inj]

alias same_ray_neg_iff ↔ SameRay.of_neg SameRay.neg

theorem same_ray_neg_swap : SameRay R (-x) y ↔ SameRay R x (-y) := by
  rw [← same_ray_neg_iff, neg_negₓ]

theorem eq_zero_of_same_ray_neg_smul_right [NoZeroSmulDivisors R M] {r : R} (hr : r < 0) (h : SameRay R x (r • x)) :
    x = 0 := by
  rcases h with (rfl | h₀ | ⟨r₁, r₂, hr₁, hr₂, h⟩)
  · rfl
    
  · simpa [← hr.ne] using h₀
    
  · rw [← sub_eq_zero, smul_smul, ← sub_smul, smul_eq_zero] at h
    refine' h.resolve_left (ne_of_gtₓ <| sub_pos.2 _)
    exact (mul_neg_of_pos_of_neg hr₂ hr).trans hr₁
    

/-- If a vector is in the same ray as its negation, that vector is zero. -/
theorem eq_zero_of_same_ray_self_neg [NoZeroSmulDivisors R M] (h : SameRay R x (-x)) : x = 0 := by
  nontriviality M
  have : Nontrivial R := Module.nontrivial R M
  refine' eq_zero_of_same_ray_neg_smul_right (neg_lt_zero.2 (@one_pos R _ _)) _
  rwa [neg_one_smul]

namespace RayVector

/-- Negating a nonzero vector. -/
instance {R : Type _} : Neg (RayVector R M) :=
  ⟨fun v => ⟨-v, neg_ne_zero.2 v.Prop⟩⟩

/-- Negating a nonzero vector commutes with coercion to the underlying module. -/
@[simp, norm_cast]
theorem coe_neg {R : Type _} (v : RayVector R M) : ↑(-v) = -(v : M) :=
  rfl

/-- Negating a nonzero vector twice produces the original vector. -/
instance {R : Type _} : HasInvolutiveNeg (RayVector R M) where
  neg := Neg.neg
  neg_neg := fun v => by
    rw [Subtype.ext_iff, coe_neg, coe_neg, neg_negₓ]

/-- If two nonzero vectors are equivalent, so are their negations. -/
@[simp]
theorem equiv_neg_iff {v₁ v₂ : RayVector R M} : -v₁ ≈ -v₂ ↔ v₁ ≈ v₂ :=
  same_ray_neg_iff

end RayVector

variable (R)

/-- Negating a ray. -/
instance : Neg (Module.Ray R M) :=
  ⟨Quotientₓ.map (fun v => -v) fun v₁ v₂ => RayVector.equiv_neg_iff.2⟩

/-- The ray given by the negation of a nonzero vector. -/
@[simp]
theorem neg_ray_of_ne_zero (v : M) (h : v ≠ 0) : -rayOfNeZero R _ h = rayOfNeZero R (-v) (neg_ne_zero.2 h) :=
  rfl

namespace Module.Ray

variable {R}

/-- Negating a ray twice produces the original ray. -/
instance : HasInvolutiveNeg (Module.Ray R M) where
  neg := Neg.neg
  neg_neg := fun x => Quotientₓ.ind (fun a => congr_arg Quotientₓ.mk <| neg_negₓ _) x

variable {R M}

/-- A ray does not equal its own negation. -/
theorem ne_neg_self [NoZeroSmulDivisors R M] (x : Module.Ray R M) : x ≠ -x := by
  induction' x using Module.Ray.ind with x hx
  rw [neg_ray_of_ne_zero, Ne.def, ray_eq_iff]
  exact mt eq_zero_of_same_ray_self_neg hx

theorem neg_units_smul (u : Rˣ) (v : Module.Ray R M) : -u • v = -(u • v) := by
  induction v using Module.Ray.ind
  simp only [← smul_ray_of_ne_zero, ← Units.smul_def, ← Units.coe_neg, ← neg_smul, ← neg_ray_of_ne_zero]

/-- Scaling by a negative unit is negation. -/
theorem units_smul_of_neg (u : Rˣ) (hu : (u : R) < 0) (v : Module.Ray R M) : u • v = -v := by
  rw [← neg_inj, neg_negₓ, ← neg_units_smul, units_smul_of_pos]
  rwa [Units.coe_neg, Right.neg_pos_iff]

end Module.Ray

end OrderedCommRing

section LinearOrderedCommRing

variable {R : Type _} [LinearOrderedCommRing R]

variable {M : Type _} [AddCommGroupₓ M] [Module R M]

/-- `same_ray` follows from membership of `mul_action.orbit` for the `units.pos_subgroup`. -/
theorem same_ray_of_mem_orbit {v₁ v₂ : M} (h : v₁ ∈ MulAction.Orbit (Units.posSubgroup R) v₂) : SameRay R v₁ v₂ := by
  rcases h with ⟨⟨r, hr : 0 < (r : R)⟩, rfl : r • v₂ = v₁⟩
  exact same_ray_pos_smul_left _ hr

/-- Scaling by an inverse unit is the same as scaling by itself. -/
@[simp]
theorem units_inv_smul (u : Rˣ) (v : Module.Ray R M) : u⁻¹ • v = u • v :=
  calc
    u⁻¹ • v = (u * u) • u⁻¹ • v := Eq.symm <| (u⁻¹ • v).units_smul_of_pos _ <| mul_self_pos.2 u.ne_zero
    _ = u • v := by
      rw [mul_smul, smul_inv_smul]
    

section

variable [NoZeroSmulDivisors R M]

@[simp]
theorem same_ray_smul_right_iff {v : M} {r : R} : SameRay R v (r • v) ↔ 0 ≤ r ∨ v = 0 :=
  ⟨fun hrv => or_iff_not_imp_left.2 fun hr => eq_zero_of_same_ray_neg_smul_right (not_leₓ.1 hr) hrv,
    or_imp_distrib.2 ⟨same_ray_nonneg_smul_right v, fun h => h.symm ▸ SameRay.zero_left _⟩⟩

/-- A nonzero vector is in the same ray as a multiple of itself if and only if that multiple
is positive. -/
theorem same_ray_smul_right_iff_of_ne {v : M} (hv : v ≠ 0) {r : R} (hr : r ≠ 0) : SameRay R v (r • v) ↔ 0 < r := by
  simp only [← same_ray_smul_right_iff, ← hv, ← or_falseₓ, ← hr.symm.le_iff_lt]

@[simp]
theorem same_ray_smul_left_iff {v : M} {r : R} : SameRay R (r • v) v ↔ 0 ≤ r ∨ v = 0 :=
  same_ray_comm.trans same_ray_smul_right_iff

/-- A multiple of a nonzero vector is in the same ray as that vector if and only if that multiple
is positive. -/
theorem same_ray_smul_left_iff_of_ne {v : M} (hv : v ≠ 0) {r : R} (hr : r ≠ 0) : SameRay R (r • v) v ↔ 0 < r :=
  same_ray_comm.trans (same_ray_smul_right_iff_of_ne hv hr)

@[simp]
theorem same_ray_neg_smul_right_iff {v : M} {r : R} : SameRay R (-v) (r • v) ↔ r ≤ 0 ∨ v = 0 := by
  rw [← same_ray_neg_iff, neg_negₓ, ← neg_smul, same_ray_smul_right_iff, neg_nonneg]

theorem same_ray_neg_smul_right_iff_of_ne {v : M} {r : R} (hv : v ≠ 0) (hr : r ≠ 0) : SameRay R (-v) (r • v) ↔ r < 0 :=
  by
  simp only [← same_ray_neg_smul_right_iff, ← hv, ← or_falseₓ, ← hr.le_iff_lt]

@[simp]
theorem same_ray_neg_smul_left_iff {v : M} {r : R} : SameRay R (r • v) (-v) ↔ r ≤ 0 ∨ v = 0 :=
  same_ray_comm.trans same_ray_neg_smul_right_iff

theorem same_ray_neg_smul_left_iff_of_ne {v : M} {r : R} (hv : v ≠ 0) (hr : r ≠ 0) : SameRay R (r • v) (-v) ↔ r < 0 :=
  same_ray_comm.trans <| same_ray_neg_smul_right_iff_of_ne hv hr

@[simp]
theorem units_smul_eq_self_iff {u : Rˣ} {v : Module.Ray R M} : u • v = v ↔ (0 : R) < u := by
  induction' v using Module.Ray.ind with v hv
  simp only [← smul_ray_of_ne_zero, ← ray_eq_iff, ← Units.smul_def, ← same_ray_smul_left_iff_of_ne hv u.ne_zero]

@[simp]
theorem units_smul_eq_neg_iff {u : Rˣ} {v : Module.Ray R M} : u • v = -v ↔ ↑u < (0 : R) := by
  rw [← neg_inj, neg_negₓ, ← Module.Ray.neg_units_smul, units_smul_eq_self_iff, Units.coe_neg, neg_pos]

end

end LinearOrderedCommRing

namespace SameRay

variable {R : Type _} [LinearOrderedField R]

variable {M : Type _} [AddCommGroupₓ M] [Module R M] {x y v₁ v₂ : M}

theorem exists_pos_left (h : SameRay R x y) (hx : x ≠ 0) (hy : y ≠ 0) : ∃ r : R, 0 < r ∧ r • x = y :=
  let ⟨r₁, r₂, hr₁, hr₂, h⟩ := h.exists_pos hx hy
  ⟨r₂⁻¹ * r₁, mul_pos (inv_pos.2 hr₂) hr₁, by
    rw [mul_smul, h, inv_smul_smul₀ hr₂.ne']⟩

theorem exists_pos_right (h : SameRay R x y) (hx : x ≠ 0) (hy : y ≠ 0) : ∃ r : R, 0 < r ∧ x = r • y :=
  (h.symm.exists_pos_left hy hx).imp fun _ => And.imp_right Eq.symm

/-- If a vector `v₂` is on the same ray as a nonzero vector `v₁`, then it is equal to `c • v₁` for
some nonnegative `c`. -/
theorem exists_nonneg_left (h : SameRay R x y) (hx : x ≠ 0) : ∃ r : R, 0 ≤ r ∧ r • x = y := by
  obtain rfl | hy := eq_or_ne y 0
  · exact ⟨0, le_rfl, zero_smul _ _⟩
    
  · exact (h.exists_pos_left hx hy).imp fun _ => And.imp_left le_of_ltₓ
    

/-- If a vector `v₁` is on the same ray as a nonzero vector `v₂`, then it is equal to `c • v₂` for
some nonnegative `c`. -/
theorem exists_nonneg_right (h : SameRay R x y) (hy : y ≠ 0) : ∃ r : R, 0 ≤ r ∧ x = r • y :=
  (h.symm.exists_nonneg_left hy).imp fun _ => And.imp_right Eq.symm

/-- If vectors `v₁` and `v₂` are on the same ray, then for some nonnegative `a b`, `a + b = 1`, we
have `v₁ = a • (v₁ + v₂)` and `v₂ = b • (v₁ + v₂)`. -/
theorem exists_eq_smul_add (h : SameRay R v₁ v₂) :
    ∃ a b : R, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ v₁ = a • (v₁ + v₂) ∧ v₂ = b • (v₁ + v₂) := by
  rcases h with (rfl | rfl | ⟨r₁, r₂, h₁, h₂, H⟩)
  · use 0, 1
    simp
    
  · use 1, 0
    simp
    
  · have h₁₂ : 0 < r₁ + r₂ := add_pos h₁ h₂
    refine' ⟨r₂ / (r₁ + r₂), r₁ / (r₁ + r₂), div_nonneg h₂.le h₁₂.le, div_nonneg h₁.le h₁₂.le, _, _, _⟩
    · rw [← add_div, add_commₓ, div_self h₁₂.ne']
      
    · rw [div_eq_inv_mul, mul_smul, smul_add, ← H, ← add_smul, add_commₓ r₂, inv_smul_smul₀ h₁₂.ne']
      
    · rw [div_eq_inv_mul, mul_smul, smul_add, H, ← add_smul, add_commₓ r₂, inv_smul_smul₀ h₁₂.ne']
      
    

/-- If vectors `v₁` and `v₂` are on the same ray, then they are nonnegative multiples of the same
vector. Actually, this vector can be assumed to be `v₁ + v₂`, see `same_ray.exists_eq_smul_add`. -/
theorem exists_eq_smul (h : SameRay R v₁ v₂) :
    ∃ (u : M)(a b : R), 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ v₁ = a • u ∧ v₂ = b • u :=
  ⟨v₁ + v₂, h.exists_eq_smul_add⟩

end SameRay


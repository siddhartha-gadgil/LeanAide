/-
Copyright (c) 2021 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.Algebra.GroupRingAction

/-!
# Conjugation action of a group on itself

This file defines the conjugation action of a group on itself. See also `mul_aut.conj` for
the definition of conjugation as a homomorphism into the automorphism group.

## Main definitions

A type alias `conj_act G` is introduced for a group `G`. The group `conj_act G` acts on `G`
by conjugation. The group `conj_act G` also acts on any normal subgroup of `G` by conjugation.

As a generalization, this also allows:
* `conj_act Mˣ` to act on `M`, when `M` is a `monoid`
* `conj_act G₀` to act on `G₀`, when `G₀` is a `group_with_zero`

## Implementation Notes

The scalar action in defined in this file can also be written using `mul_aut.conj g • h`. This
has the advantage of not using the type alias `conj_act`, but the downside of this approach
is that some theorems about the group actions will not apply when since this
`mul_aut.conj g • h` describes an action of `mul_aut G` on `G`, and not an action of `G`.

-/


variable (M G G₀ R K : Type _)

/-- A type alias for a group `G`. `conj_act G` acts on `G` by conjugation -/
def ConjAct : Type _ :=
  G

namespace ConjAct

open MulAction Subgroup

variable {M G G₀ R K}

instance : ∀ [Groupₓ G], Groupₓ (ConjAct G) :=
  id

instance : ∀ [DivInvMonoidₓ G], DivInvMonoidₓ (ConjAct G) :=
  id

instance : ∀ [GroupWithZeroₓ G], GroupWithZeroₓ (ConjAct G) :=
  id

instance : ∀ [Fintype G], Fintype (ConjAct G) :=
  id

@[simp]
theorem card [Fintype G] : Fintype.card (ConjAct G) = Fintype.card G :=
  rfl

section DivInvMonoidₓ

variable [DivInvMonoidₓ G]

instance : Inhabited (ConjAct G) :=
  ⟨1⟩

/-- Reinterpret `g : conj_act G` as an element of `G`. -/
def ofConjAct : ConjAct G ≃* G :=
  ⟨id, id, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

/-- Reinterpret `g : G` as an element of `conj_act G`. -/
def toConjAct : G ≃* ConjAct G :=
  ofConjAct.symm

/-- A recursor for `conj_act`, for use as `induction x using conj_act.rec` when `x : conj_act G`. -/
protected def rec {C : ConjAct G → Sort _} (h : ∀ g, C (toConjAct g)) : ∀ g, C g :=
  h

@[simp]
theorem of_mul_symm_eq : (@ofConjAct G _).symm = to_conj_act :=
  rfl

@[simp]
theorem to_mul_symm_eq : (@toConjAct G _).symm = of_conj_act :=
  rfl

@[simp]
theorem to_conj_act_of_conj_act (x : ConjAct G) : toConjAct (ofConjAct x) = x :=
  rfl

@[simp]
theorem of_conj_act_to_conj_act (x : G) : ofConjAct (toConjAct x) = x :=
  rfl

@[simp]
theorem of_conj_act_one : ofConjAct (1 : ConjAct G) = 1 :=
  rfl

@[simp]
theorem to_conj_act_one : toConjAct (1 : G) = 1 :=
  rfl

@[simp]
theorem of_conj_act_inv (x : ConjAct G) : ofConjAct x⁻¹ = (ofConjAct x)⁻¹ :=
  rfl

@[simp]
theorem to_conj_act_inv (x : G) : toConjAct x⁻¹ = (toConjAct x)⁻¹ :=
  rfl

@[simp]
theorem of_conj_act_mul (x y : ConjAct G) : ofConjAct (x * y) = ofConjAct x * ofConjAct y :=
  rfl

@[simp]
theorem to_conj_act_mul (x y : G) : toConjAct (x * y) = toConjAct x * toConjAct y :=
  rfl

instance : HasSmul (ConjAct G) G where smul := fun g h => ofConjAct g * h * (ofConjAct g)⁻¹

theorem smul_def (g : ConjAct G) (h : G) : g • h = ofConjAct g * h * (ofConjAct g)⁻¹ :=
  rfl

@[simp]
theorem forall (p : ConjAct G → Prop) : (∀ x : ConjAct G, p x) ↔ ∀ x : G, p (toConjAct x) :=
  Iff.rfl

end DivInvMonoidₓ

section Units

section Monoidₓ

variable [Monoidₓ M]

instance hasUnitsScalar : HasSmul (ConjAct Mˣ) M where smul := fun g h => ofConjAct g * h * ↑(ofConjAct g)⁻¹

theorem units_smul_def (g : ConjAct Mˣ) (h : M) : g • h = ofConjAct g * h * ↑(ofConjAct g)⁻¹ :=
  rfl

instance unitsMulDistribMulAction : MulDistribMulAction (ConjAct Mˣ) M where
  smul := (· • ·)
  one_smul := by
    simp [← units_smul_def]
  mul_smul := by
    simp [← units_smul_def, ← mul_assoc, ← mul_inv_rev]
  smul_mul := by
    simp [← units_smul_def, ← mul_assoc]
  smul_one := by
    simp [← units_smul_def]

end Monoidₓ

section Semiringₓ

variable [Semiringₓ R]

instance unitsMulSemiringAction : MulSemiringAction (ConjAct Rˣ) R :=
  { ConjAct.unitsMulDistribMulAction with smul := (· • ·),
    smul_zero := by
      simp [← units_smul_def],
    smul_add := by
      simp [← units_smul_def, ← mul_addₓ, ← add_mulₓ] }

end Semiringₓ

end Units

section GroupWithZeroₓ

variable [GroupWithZeroₓ G₀]

@[simp]
theorem of_conj_act_zero : ofConjAct (0 : ConjAct G₀) = 0 :=
  rfl

@[simp]
theorem to_conj_act_zero : toConjAct (0 : G₀) = 0 :=
  rfl

instance mulAction₀ : MulAction (ConjAct G₀) G₀ where
  smul := (· • ·)
  one_smul := by
    simp [← smul_def]
  mul_smul := by
    simp [← smul_def, ← mul_assoc, ← mul_inv_rev]

end GroupWithZeroₓ

section DivisionRing

variable [DivisionRing K]

instance distribMulAction₀ : DistribMulAction (ConjAct K) K :=
  { ConjAct.mulAction₀ with smul := (· • ·),
    smul_zero := by
      simp [← smul_def],
    smul_add := by
      simp [← smul_def, ← mul_addₓ, ← add_mulₓ] }

end DivisionRing

variable [Groupₓ G]

instance : MulDistribMulAction (ConjAct G) G where
  smul := (· • ·)
  smul_mul := by
    simp [← smul_def, ← mul_assoc]
  smul_one := by
    simp [← smul_def]
  one_smul := by
    simp [← smul_def]
  mul_smul := by
    simp [← smul_def, ← mul_assoc]

theorem smul_eq_mul_aut_conj (g : ConjAct G) (h : G) : g • h = MulAut.conj (ofConjAct g) h :=
  rfl

/-- The set of fixed points of the conjugation action of `G` on itself is the center of `G`. -/
theorem fixed_points_eq_center : FixedPoints (ConjAct G) G = center G := by
  ext x
  simp [← mem_center_iff, ← smul_def, ← mul_inv_eq_iff_eq_mul]

/-- As normal subgroups are closed under conjugation, they inherit the conjugation action
  of the underlying group. -/
instance Subgroup.conjAction {H : Subgroup G} [hH : H.Normal] : HasSmul (ConjAct G) H :=
  ⟨fun g h => ⟨g • h, hH.conj_mem h.1 h.2 (ofConjAct g)⟩⟩

theorem Subgroup.coe_conj_smul {H : Subgroup G} [hH : H.Normal] (g : ConjAct G) (h : H) : ↑(g • h) = g • (h : G) :=
  rfl

instance Subgroup.conjMulDistribMulAction {H : Subgroup G} [hH : H.Normal] : MulDistribMulAction (ConjAct G) H :=
  Subtype.coe_injective.MulDistribMulAction H.Subtype Subgroup.coe_conj_smul

/-- Group conjugation on a normal subgroup. Analogous to `mul_aut.conj`. -/
def _root_.mul_aut.conj_normal {H : Subgroup G} [hH : H.Normal] : G →* MulAut H :=
  (MulDistribMulAction.toMulAut (ConjAct G) H).comp toConjAct.toMonoidHom

@[simp]
theorem _root_.mul_aut.conj_normal_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑(MulAut.conjNormal g h) = g * h * g⁻¹ :=
  rfl

@[simp]
theorem _root_.mul_aut.conj_normal_symm_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑((MulAut.conjNormal g).symm h) = g⁻¹ * h * g := by
  change _ * _⁻¹⁻¹ = _
  rw [inv_invₓ]
  rfl

@[simp]
theorem _root_.mul_aut.conj_normal_inv_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑((MulAut.conjNormal g)⁻¹ h) = g⁻¹ * h * g :=
  MulAut.conj_normal_symm_apply g h

theorem _root_.mul_aut.conj_normal_coe {H : Subgroup G} [H.Normal] {h : H} : MulAut.conjNormal ↑h = MulAut.conj h :=
  MulEquiv.ext fun x => rfl

instance normal_of_characteristic_of_normal {H : Subgroup G} [hH : H.Normal] {K : Subgroup H} [h : K.Characteristic] :
    (K.map H.Subtype).Normal :=
  ⟨fun a ha b => by
    obtain ⟨a, ha, rfl⟩ := ha
    exact K.apply_coe_mem_map H.subtype ⟨_, (set_like.ext_iff.mp (h.fixed (MulAut.conjNormal b)) a).mpr ha⟩⟩

end ConjAct


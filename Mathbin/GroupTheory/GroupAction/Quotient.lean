/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.GroupTheory.QuotientGroup

/-!
# Properties of group actions involving quotient groups

This file proves properties of group actions which use the quotient group construction, notably
* the orbit-stabilizer theorem `card_orbit_mul_card_stabilizer_eq_card_group`
* the class formula `card_eq_sum_card_group_div_card_stabilizer'`
* Burnside's lemma `sum_card_fixed_by_eq_card_orbits_mul_card_group`
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Function

open BigOperators

namespace MulAction

variable [Groupₓ α]

section QuotientAction

open Subgroup MulOpposite QuotientGroup

variable (β) [Monoidₓ β] [MulAction β α] (H : Subgroup α)

/-- A typeclass for when a `mul_action β α` descends to the quotient `α ⧸ H`. -/
class QuotientAction : Prop where
  inv_mul_mem : ∀ (b : β) {a a' : α}, a⁻¹ * a' ∈ H → (b • a)⁻¹ * b • a' ∈ H

/-- A typeclass for when an `add_action β α` descends to the quotient `α ⧸ H`. -/
class _root_.add_action.quotient_action {α : Type _} (β : Type _) [AddGroupₓ α] [AddMonoidₓ β] [AddAction β α]
  (H : AddSubgroup α) : Prop where
  inv_mul_mem : ∀ (b : β) {a a' : α}, -a + a' ∈ H → -(b +ᵥ a) + (b +ᵥ a') ∈ H

attribute [to_additive AddAction.QuotientAction] MulAction.QuotientAction

@[to_additive]
instance left_quotient_action : QuotientAction α H :=
  ⟨fun _ _ _ _ => by
    rwa [smul_eq_mul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_leftₓ]⟩

@[to_additive]
instance right_quotient_action : QuotientAction H.normalizer.opposite H :=
  ⟨fun b c _ _ => by
    rwa [smul_def, smul_def, smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, ← mul_assoc,
      mem_normalizer_iff'.mp b.prop, mul_assoc, mul_inv_cancel_left]⟩

@[to_additive]
instance right_quotient_action' [hH : H.Normal] : QuotientAction αᵐᵒᵖ H :=
  ⟨fun _ _ _ _ => by
    rwa [smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, mul_assoc, hH.mem_comm_iff, mul_assoc, mul_inv_cancel_rightₓ]⟩

@[to_additive]
instance quotient [QuotientAction β H] : MulAction β (α ⧸ H) where
  smul := fun b =>
    Quotientₓ.map' ((· • ·) b) fun a a' h => left_rel_apply.mpr <| QuotientAction.inv_mul_mem b <| left_rel_apply.mp h
  one_smul := fun q => Quotientₓ.induction_on' q fun a => congr_arg Quotientₓ.mk' (one_smul β a)
  mul_smul := fun b b' q => Quotientₓ.induction_on' q fun a => congr_arg Quotientₓ.mk' (mul_smul b b' a)

variable {β}

@[simp, to_additive]
theorem quotient.smul_mk [QuotientAction β H] (b : β) (a : α) :
    (b • QuotientGroup.mk a : α ⧸ H) = QuotientGroup.mk (b • a) :=
  rfl

@[simp, to_additive]
theorem quotient.smul_coe [QuotientAction β H] (b : β) (a : α) : (b • a : α ⧸ H) = ↑(b • a) :=
  rfl

@[simp, to_additive]
theorem quotient.mk_smul_out' [QuotientAction β H] (b : β) (q : α ⧸ H) : QuotientGroup.mk (b • q.out') = b • q := by
  rw [← quotient.smul_mk, QuotientGroup.out_eq']

@[simp, to_additive]
theorem quotient.coe_smul_out' [QuotientAction β H] (b : β) (q : α ⧸ H) : ↑(b • q.out') = b • q :=
  quotient.mk_smul_out' H b q

end QuotientAction

open QuotientGroup

/-- The canonical map to the left cosets. -/
def _root_.mul_action_hom.to_quotient (H : Subgroup α) : α →[α] α ⧸ H :=
  ⟨coe, quotient.smul_coe H⟩

@[simp]
theorem _root_.mul_action_hom.to_quotient_apply (H : Subgroup α) (g : α) : MulActionHom.toQuotient H g = g :=
  rfl

@[to_additive]
instance mulLeftCosetsCompSubtypeVal (H I : Subgroup α) : MulAction I (α ⧸ H) :=
  MulAction.compHom (α ⧸ H) (Subgroup.subtype I)

variable (α) {β} [MulAction α β] (x : β)

/-- The canonical map from the quotient of the stabilizer to the set. -/
@[to_additive "The canonical map from the quotient of the stabilizer to the set. "]
def ofQuotientStabilizer (g : α ⧸ MulAction.stabilizer α x) : β :=
  (Quotientₓ.liftOn' g (· • x)) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_arg _ (left_rel_apply.mp H).symm
      _ = g2 • x := by
        rw [smul_smul, mul_inv_cancel_left]
      

@[simp, to_additive]
theorem of_quotient_stabilizer_mk (g : α) : ofQuotientStabilizer α x (QuotientGroup.mk g) = g • x :=
  rfl

@[to_additive]
theorem of_quotient_stabilizer_mem_orbit (g) : ofQuotientStabilizer α x g ∈ Orbit α x :=
  (Quotientₓ.induction_on' g) fun g => ⟨g, rfl⟩

@[to_additive]
theorem of_quotient_stabilizer_smul (g : α) (g' : α ⧸ MulAction.stabilizer α x) :
    ofQuotientStabilizer α x (g • g') = g • ofQuotientStabilizer α x g' :=
  (Quotientₓ.induction_on' g') fun _ => mul_smul _ _ _

@[to_additive]
theorem injective_of_quotient_stabilizer : Function.Injective (ofQuotientStabilizer α x) := fun y₁ y₂ =>
  (Quotientₓ.induction_on₂' y₁ y₂) fun g₁ g₂ (H : g₁ • x = g₂ • x) =>
    Quotientₓ.sound' <| by
      rw [left_rel_apply]
      show (g₁⁻¹ * g₂) • x = x
      rw [mul_smul, ← H, inv_smul_smul]

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
noncomputable def orbitEquivQuotientStabilizer (b : β) : Orbit α b ≃ α ⧸ stabilizer α b :=
  Equivₓ.symm <|
    Equivₓ.ofBijective (fun g => ⟨ofQuotientStabilizer α b g, of_quotient_stabilizer_mem_orbit α b g⟩)
      ⟨fun x y hxy =>
        injective_of_quotient_stabilizer α b
          (by
            convert congr_arg Subtype.val hxy),
        fun ⟨b, ⟨g, hgb⟩⟩ => ⟨g, Subtype.eq hgb⟩⟩

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
noncomputable def orbitProdStabilizerEquivGroup (b : β) : Orbit α b × stabilizer α b ≃ α :=
  (Equivₓ.prodCongr (orbitEquivQuotientStabilizer α _) (Equivₓ.refl _)).trans
    Subgroup.groupEquivQuotientTimesSubgroup.symm

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
theorem card_orbit_mul_card_stabilizer_eq_card_group (b : β) [Fintype α] [Fintype <| Orbit α b]
    [Fintype <| stabilizer α b] : Fintype.card (Orbit α b) * Fintype.card (stabilizer α b) = Fintype.card α := by
  rw [← Fintype.card_prod, Fintype.card_congr (orbit_prod_stabilizer_equiv_group α b)]

@[simp, to_additive]
theorem orbit_equiv_quotient_stabilizer_symm_apply (b : β) (a : α) :
    ((orbitEquivQuotientStabilizer α b).symm a : β) = a • b :=
  rfl

@[simp, to_additive]
theorem stabilizer_quotient {G} [Groupₓ G] (H : Subgroup G) : MulAction.stabilizer G ((1 : G) : G ⧸ H) = H := by
  ext
  simp [← QuotientGroup.eq]

variable (β)

-- mathport name: «exprΩ»
local notation "Ω" => Quotientₓ <| orbitRel α β

/-- **Class formula** : given `G` a group acting on `X` and `φ` a function mapping each orbit of `X`
under this action (that is, each element of the quotient of `X` by the relation `orbit_rel G X`) to
an element in this orbit, this gives a (noncomputable) bijection between `X` and the disjoint union
of `G/Stab(φ(ω))` over all orbits `ω`. In most cases you'll want `φ` to be `quotient.out'`, so we
provide `mul_action.self_equiv_sigma_orbits_quotient_stabilizer` as a special case. -/
@[to_additive
      "**Class formula** : given `G` an additive group acting on `X` and `φ` a function\nmapping each orbit of `X` under this action (that is, each element of the quotient of `X` by the\nrelation `orbit_rel G X`) to an element in this orbit, this gives a (noncomputable) bijection\nbetween `X` and the disjoint union of `G/Stab(φ(ω))` over all orbits `ω`. In most cases you'll want\n`φ` to be `quotient.out'`, so we provide `add_action.self_equiv_sigma_orbits_quotient_stabilizer`\nas a special case. "]
noncomputable def selfEquivSigmaOrbitsQuotientStabilizer' {φ : Ω → β} (hφ : LeftInverse Quotientₓ.mk' φ) :
    β ≃ Σω : Ω, α ⧸ stabilizer α (φ ω) :=
  calc
    β ≃ Σω : Ω, Orbit α (φ ω) := selfEquivSigmaOrbits' α β hφ
    _ ≃ Σω : Ω, α ⧸ stabilizer α (φ ω) := Equivₓ.sigmaCongrRight fun ω => orbitEquivQuotientStabilizer α (φ ω)
    

/-- **Class formula** for a finite group acting on a finite type. See
`mul_action.card_eq_sum_card_group_div_card_stabilizer` for a specialized version using
`quotient.out'`. -/
@[to_additive
      "**Class formula** for a finite group acting on a finite type. See\n`add_action.card_eq_sum_card_add_group_div_card_stabilizer` for a specialized version using\n`quotient.out'`."]
theorem card_eq_sum_card_group_div_card_stabilizer' [Fintype α] [Fintype β] [Fintype Ω]
    [∀ b : β, Fintype <| stabilizer α b] {φ : Ω → β} (hφ : LeftInverse Quotientₓ.mk' φ) :
    Fintype.card β = ∑ ω : Ω, Fintype.card α / Fintype.card (stabilizer α (φ ω)) := by
  classical
  have : ∀ ω : Ω, Fintype.card α / Fintype.card ↥(stabilizer α (φ ω)) = Fintype.card (α ⧸ stabilizer α (φ ω)) := by
    intro ω
    rw [Fintype.card_congr (@Subgroup.groupEquivQuotientTimesSubgroup α _ (stabilizer α <| φ ω)), Fintype.card_prod,
      Nat.mul_div_cancelₓ]
    exact
      fintype.card_pos_iff.mpr
        (by
          infer_instance)
  simp_rw [this, ← Fintype.card_sigma, Fintype.card_congr (self_equiv_sigma_orbits_quotient_stabilizer' α β hφ)]

/-- **Class formula**. This is a special case of
`mul_action.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = quotient.out'`. -/
@[to_additive
      "**Class formula**. This is a special case of\n`add_action.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = quotient.out'`. "]
noncomputable def selfEquivSigmaOrbitsQuotientStabilizer : β ≃ Σω : Ω, α ⧸ stabilizer α ω.out' :=
  selfEquivSigmaOrbitsQuotientStabilizer' α β Quotientₓ.out_eq'

/-- **Class formula** for a finite group acting on a finite type. -/
@[to_additive "**Class formula** for a finite group acting on a finite type."]
theorem card_eq_sum_card_group_div_card_stabilizer [Fintype α] [Fintype β] [Fintype Ω]
    [∀ b : β, Fintype <| stabilizer α b] :
    Fintype.card β = ∑ ω : Ω, Fintype.card α / Fintype.card (stabilizer α ω.out') :=
  card_eq_sum_card_group_div_card_stabilizer' α β Quotientₓ.out_eq'

/-- **Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all
`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is a group acting on `X` and
`X/G`denotes the quotient of `X` by the relation `orbit_rel G X`. -/
@[to_additive
      "**Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all\n`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is an additive group acting\non `X` and `X/G`denotes the quotient of `X` by the relation `orbit_rel G X`. "]
noncomputable def sigmaFixedByEquivOrbitsProdGroup : (Σa : α, FixedBy α β a) ≃ Ω × α :=
  calc
    (Σa : α, FixedBy α β a) ≃ { ab : α × β // ab.1 • ab.2 = ab.2 } := (Equivₓ.subtypeProdEquivSigmaSubtype _).symm
    _ ≃ { ba : β × α // ba.2 • ba.1 = ba.1 } := (Equivₓ.prodComm α β).subtypeEquiv fun ab => Iff.rfl
    _ ≃ Σb : β, stabilizer α b := Equivₓ.subtypeProdEquivSigmaSubtype fun (b : β) a => a ∈ stabilizer α b
    _ ≃ Σωb : Σω : Ω, Orbit α ω.out', stabilizer α (ωb.2 : β) := (selfEquivSigmaOrbits α β).sigmaCongrLeft'
    _ ≃ Σω : Ω, Σb : Orbit α ω.out', stabilizer α (b : β) :=
      Equivₓ.sigmaAssoc fun (ω : Ω) (b : Orbit α ω.out') => stabilizer α (b : β)
    _ ≃ Σω : Ω, Σb : Orbit α ω.out', stabilizer α ω.out' :=
      Equivₓ.sigmaCongrRight fun ω =>
        Equivₓ.sigmaCongrRight fun ⟨b, hb⟩ => (stabilizerEquivStabilizerOfOrbitRel hb).toEquiv
    _ ≃ Σω : Ω, Orbit α ω.out' × stabilizer α ω.out' := Equivₓ.sigmaCongrRight fun ω => Equivₓ.sigmaEquivProd _ _
    _ ≃ Σω : Ω, α := Equivₓ.sigmaCongrRight fun ω => orbitProdStabilizerEquivGroup α ω.out'
    _ ≃ Ω × α := Equivₓ.sigmaEquivProd Ω α
    

/-- **Burnside's lemma** : given a finite group `G` acting on a set `X`, the average number of
elements fixed by each `g ∈ G` is the number of orbits. -/
@[to_additive
      "**Burnside's lemma** : given a finite additive group `G` acting on a set `X`,\nthe average number of elements fixed by each `g ∈ G` is the number of orbits. "]
theorem sum_card_fixed_by_eq_card_orbits_mul_card_group [Fintype α] [∀ a, Fintype <| FixedBy α β a] [Fintype Ω] :
    (∑ a : α, Fintype.card (FixedBy α β a)) = Fintype.card Ω * Fintype.card α := by
  rw [← Fintype.card_prod, ← Fintype.card_sigma, Fintype.card_congr (sigma_fixed_by_equiv_orbits_prod_group α β)]

@[to_additive]
instance is_pretransitive_quotient (G) [Groupₓ G] (H : Subgroup G) :
    IsPretransitive G (G ⧸ H) where exists_smul_eq := by
    rintro ⟨x⟩ ⟨y⟩
    refine' ⟨y * x⁻¹, quotient_group.eq.mpr _⟩
    simp only [← smul_eq_mul, ← H.one_mem, ← mul_left_invₓ, ← inv_mul_cancel_right]

end MulAction

namespace Subgroup

variable {G : Type _} [Groupₓ G] (H : Subgroup G)

theorem normal_core_eq_ker : H.normalCore = (MulAction.toPermHom G (G ⧸ H)).ker := by
  refine'
    le_antisymmₓ
      (fun g hg =>
        Equivₓ.Perm.ext fun q =>
          QuotientGroup.induction_on q fun g' => (MulAction.quotient.smul_mk H g g').trans (quotient_group.eq.mpr _))
      (subgroup.normal_le_normal_core.mpr fun g hg => _)
  · rw [smul_eq_mul, mul_inv_rev, ← inv_invₓ g', inv_invₓ]
    exact H.normal_core.inv_mem hg g'⁻¹
    
  · rw [← H.inv_mem_iff, ← mul_oneₓ g⁻¹, ← QuotientGroup.eq, ← mul_oneₓ g]
    exact (MulAction.quotient.smul_mk H g 1).symm.trans (equiv.perm.ext_iff.mp hg (1 : G))
    

noncomputable instance fintypeQuotientNormalCore [Fintype (G ⧸ H)] : Fintype (G ⧸ H.normalCore) := by
  rw [H.normal_core_eq_ker]
  classical
  exact Fintype.ofEquiv _ (QuotientGroup.quotientKerEquivRange _).symm.toEquiv

end Subgroup


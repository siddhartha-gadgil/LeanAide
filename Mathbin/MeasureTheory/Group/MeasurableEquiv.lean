/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.MeasureTheory.Group.Arithmetic

/-!
# (Scalar) multiplication and (vector) addition as measurable equivalences

In this file we define the following measurable equivalences:

* `measurable_equiv.smul`: if a group `G` acts on `α` by measurable maps, then each element `c : G`
  defines a measurable automorphism of `α`;
* `measurable_equiv.vadd`: additive version of `measurable_equiv.smul`;
* `measurable_equiv.smul₀`: if a group with zero `G` acts on `α` by measurable maps, then each
  nonzero element `c : G` defines a measurable automorphism of `α`;
* `measurable_equiv.mul_left`: if `G` is a group with measurable multiplication, then left
  multiplication by `g : G` is a measurable automorphism of `G`;
* `measurable_equiv.add_left`: additive version of `measurable_equiv.mul_left`;
* `measurable_equiv.mul_right`: if `G` is a group with measurable multiplication, then right
  multiplication by `g : G` is a measurable automorphism of `G`;
* `measurable_equiv.add_right`: additive version of `measurable_equiv.mul_right`;
* `measurable_equiv.mul_left₀`, `measurable_equiv.mul_right₀`: versions of
  `measurable_equiv.mul_left` and `measurable_equiv.mul_right` for groups with zero;
* `measurable_equiv.inv`: `has_inv.inv` as a measurable automorphism
  of a group (or a group with zero);
* `measurable_equiv.neg`: negation as a measurable automorphism of an additive group.

We also deduce that the corresponding maps are measurable embeddings.

## Tags

measurable, equivalence, group action
-/


namespace MeasurableEquiv

variable {G G₀ α : Type _} [MeasurableSpace G] [MeasurableSpace G₀] [MeasurableSpace α] [Groupₓ G] [GroupWithZeroₓ G₀]
  [MulAction G α] [MulAction G₀ α] [HasMeasurableSmul G α] [HasMeasurableSmul G₀ α]

/-- If a group `G` acts on `α` by measurable maps, then each element `c : G` defines a measurable
automorphism of `α`. -/
@[to_additive
      "If an additive group `G` acts on `α` by measurable maps, then each element `c : G`\ndefines a measurable automorphism of `α`.",
  simps (config := { fullyApplied := false }) toEquiv apply]
def smul (c : G) : α ≃ᵐ α where
  toEquiv := MulAction.toPerm c
  measurable_to_fun := measurable_const_smul c
  measurable_inv_fun := measurable_const_smul c⁻¹

@[to_additive]
theorem _root_.measurable_embedding_const_smul (c : G) : MeasurableEmbedding ((· • ·) c : α → α) :=
  (smul c).MeasurableEmbedding

@[simp, to_additive]
theorem symm_smul (c : G) : (smul c : α ≃ᵐ α).symm = smul c⁻¹ :=
  ext rfl

/-- If a group with zero `G₀` acts on `α` by measurable maps, then each nonzero element `c : G₀`
defines a measurable automorphism of `α` -/
def smul₀ (c : G₀) (hc : c ≠ 0) : α ≃ᵐ α :=
  MeasurableEquiv.smul (Units.mk0 c hc)

@[simp]
theorem coe_smul₀ {c : G₀} (hc : c ≠ 0) : ⇑(smul₀ c hc : α ≃ᵐ α) = (· • ·) c :=
  rfl

@[simp]
theorem symm_smul₀ {c : G₀} (hc : c ≠ 0) : (smul₀ c hc : α ≃ᵐ α).symm = smul₀ c⁻¹ (inv_ne_zero hc) :=
  ext rfl

theorem _root_.measurable_embedding_const_smul₀ {c : G₀} (hc : c ≠ 0) : MeasurableEmbedding ((· • ·) c : α → α) :=
  (smul₀ c hc).MeasurableEmbedding

section Mul

variable [HasMeasurableMul G] [HasMeasurableMul G₀]

/-- If `G` is a group with measurable multiplication, then left multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[to_additive
      "If `G` is an additive group with measurable addition, then addition of `g : G`\non the left is a measurable automorphism of `G`."]
def mulLeft (g : G) : G ≃ᵐ G :=
  smul g

@[simp, to_additive]
theorem coe_mul_left (g : G) : ⇑(mulLeft g) = (· * ·) g :=
  rfl

@[simp, to_additive]
theorem symm_mul_left (g : G) : (mulLeft g).symm = mulLeft g⁻¹ :=
  ext rfl

@[simp, to_additive]
theorem to_equiv_mul_left (g : G) : (mulLeft g).toEquiv = Equivₓ.mulLeft g :=
  rfl

@[to_additive]
theorem _root_.measurable_embedding_mul_left (g : G) : MeasurableEmbedding ((· * ·) g) :=
  (mulLeft g).MeasurableEmbedding

/-- If `G` is a group with measurable multiplication, then right multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[to_additive
      "If `G` is an additive group with measurable addition, then addition of `g : G`\non the right is a measurable automorphism of `G`."]
def mulRight (g : G) : G ≃ᵐ G where
  toEquiv := Equivₓ.mulRight g
  measurable_to_fun := measurable_mul_const g
  measurable_inv_fun := measurable_mul_const g⁻¹

@[to_additive]
theorem _root_.measurable_embedding_mul_right (g : G) : MeasurableEmbedding fun x => x * g :=
  (mulRight g).MeasurableEmbedding

@[simp, to_additive]
theorem coe_mul_right (g : G) : ⇑(mulRight g) = fun x => x * g :=
  rfl

@[simp, to_additive]
theorem symm_mul_right (g : G) : (mulRight g).symm = mulRight g⁻¹ :=
  ext rfl

@[simp, to_additive]
theorem to_equiv_mul_right (g : G) : (mulRight g).toEquiv = Equivₓ.mulRight g :=
  rfl

/-- If `G₀` is a group with zero with measurable multiplication, then left multiplication by a
nonzero element `g : G₀` is a measurable automorphism of `G₀`. -/
def mulLeft₀ (g : G₀) (hg : g ≠ 0) : G₀ ≃ᵐ G₀ :=
  smul₀ g hg

theorem _root_.measurable_embedding_mul_left₀ {g : G₀} (hg : g ≠ 0) : MeasurableEmbedding ((· * ·) g) :=
  (mulLeft₀ g hg).MeasurableEmbedding

@[simp]
theorem coe_mul_left₀ {g : G₀} (hg : g ≠ 0) : ⇑(mulLeft₀ g hg) = (· * ·) g :=
  rfl

@[simp]
theorem symm_mul_left₀ {g : G₀} (hg : g ≠ 0) : (mulLeft₀ g hg).symm = mulLeft₀ g⁻¹ (inv_ne_zero hg) :=
  ext rfl

@[simp]
theorem to_equiv_mul_left₀ {g : G₀} (hg : g ≠ 0) : (mulLeft₀ g hg).toEquiv = Equivₓ.mulLeft₀ g hg :=
  rfl

/-- If `G₀` is a group with zero with measurable multiplication, then right multiplication by a
nonzero element `g : G₀` is a measurable automorphism of `G₀`. -/
def mulRight₀ (g : G₀) (hg : g ≠ 0) : G₀ ≃ᵐ G₀ where
  toEquiv := Equivₓ.mulRight₀ g hg
  measurable_to_fun := measurable_mul_const g
  measurable_inv_fun := measurable_mul_const g⁻¹

theorem _root_.measurable_embedding_mul_right₀ {g : G₀} (hg : g ≠ 0) : MeasurableEmbedding fun x => x * g :=
  (mulRight₀ g hg).MeasurableEmbedding

@[simp]
theorem coe_mul_right₀ {g : G₀} (hg : g ≠ 0) : ⇑(mulRight₀ g hg) = fun x => x * g :=
  rfl

@[simp]
theorem symm_mul_right₀ {g : G₀} (hg : g ≠ 0) : (mulRight₀ g hg).symm = mulRight₀ g⁻¹ (inv_ne_zero hg) :=
  ext rfl

@[simp]
theorem to_equiv_mul_right₀ {g : G₀} (hg : g ≠ 0) : (mulRight₀ g hg).toEquiv = Equivₓ.mulRight₀ g hg :=
  rfl

end Mul

/-- Inversion as a measurable automorphism of a group or group with zero. -/
@[to_additive "Negation as a measurable automorphism of an additive group.",
  simps (config := { fullyApplied := false }) toEquiv apply]
def inv (G) [MeasurableSpace G] [HasInvolutiveInv G] [HasMeasurableInv G] : G ≃ᵐ G where
  toEquiv := Equivₓ.inv G
  measurable_to_fun := measurable_inv
  measurable_inv_fun := measurable_inv

@[simp, to_additive]
theorem symm_inv {G} [MeasurableSpace G] [HasInvolutiveInv G] [HasMeasurableInv G] : (inv G).symm = inv G :=
  rfl

/-- `equiv.div_right` as a `measurable_equiv`. -/
@[to_additive " `equiv.sub_right` as a `measurable_equiv` "]
def divRight [HasMeasurableMul G] (g : G) : G ≃ᵐ G where
  toEquiv := Equivₓ.divRight g
  measurable_to_fun := measurable_div_const' g
  measurable_inv_fun := measurable_mul_const g

/-- `equiv.div_left` as a `measurable_equiv` -/
@[to_additive " `equiv.sub_left` as a `measurable_equiv` "]
def divLeft [HasMeasurableMul G] [HasMeasurableInv G] (g : G) : G ≃ᵐ G where
  toEquiv := Equivₓ.divLeft g
  measurable_to_fun := measurable_id.const_div g
  measurable_inv_fun := measurable_inv.mul_const g

end MeasurableEquiv


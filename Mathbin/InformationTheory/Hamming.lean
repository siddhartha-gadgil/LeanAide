/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import Mathbin.Analysis.NormedSpace.Basic

/-!
# Hamming spaces

The Hamming metric counts the number of places two members of a (finite) Pi type
differ. The Hamming norm is the same as the Hamming metric over additive groups, and
counts the number of places a member of a (finite) Pi type differs from zero.

This is a useful notion in various applications, but in particular it is relevant
in coding theory, in which it is fundamental for defining the minimum distance of a
code.

## Main definitions
* `hamming_dist x y`: the Hamming distance between `x` and `y`, the number of entries which differ.
* `hamming_norm x`: the Hamming norm of `x`, the number of non-zero entries.
* `hamming β`: a type synonym for `Π i, β i` with `dist` and `norm` provided by the above.
* `hamming.to_hamming`, `hamming.of_hamming`: functions for casting between `hamming β` and
`Π i, β i`.
* `hamming.normed_group`: the Hamming norm forms a normed group on `hamming β`.
-/


section HammingDistNorm

open Finset Function

variable {α ι : Type _} {β : ι → Type _} [Fintype ι] [∀ i, DecidableEq (β i)]

variable {γ : ι → Type _} [∀ i, DecidableEq (γ i)]

/-- The Hamming distance function to the naturals. -/
def hammingDist (x y : ∀ i, β i) : ℕ :=
  (univ.filter fun i => x i ≠ y i).card

/-- Corresponds to `dist_self`. -/
@[simp]
theorem hamming_dist_self (x : ∀ i, β i) : hammingDist x x = 0 := by
  rw [hammingDist, card_eq_zero, filter_eq_empty_iff]
  exact fun _ _ H => H rfl

/-- Corresponds to `dist_nonneg`. -/
theorem hamming_dist_nonneg {x y : ∀ i, β i} : 0 ≤ hammingDist x y :=
  zero_le _

/-- Corresponds to `dist_comm`. -/
theorem hamming_dist_comm (x y : ∀ i, β i) : hammingDist x y = hammingDist y x := by
  simp_rw [hammingDist, ne_comm]

/-- Corresponds to `dist_triangle`. -/
theorem hamming_dist_triangle (x y z : ∀ i, β i) : hammingDist x z ≤ hammingDist x y + hammingDist y z := by
  classical
  simp_rw [hammingDist]
  refine' le_transₓ (card_mono _) (card_union_le _ _)
  rw [← filter_or]
  refine' monotone_filter_right _ _
  intro i h
  by_contra' H
  exact h (Eq.trans H.1 H.2)

/-- Corresponds to `dist_triangle_left`. -/
theorem hamming_dist_triangle_left (x y z : ∀ i, β i) : hammingDist x y ≤ hammingDist z x + hammingDist z y := by
  rw [hamming_dist_comm z]
  exact hamming_dist_triangle _ _ _

/-- Corresponds to `dist_triangle_right`. -/
theorem hamming_dist_triangle_right (x y z : ∀ i, β i) : hammingDist x y ≤ hammingDist x z + hammingDist y z := by
  rw [hamming_dist_comm y]
  exact hamming_dist_triangle _ _ _

/-- Corresponds to `swap_dist`. -/
theorem swap_hamming_dist : swap (@hammingDist _ β _ _) = hammingDist := by
  funext x y
  exact hamming_dist_comm _ _

/-- Corresponds to `eq_of_dist_eq_zero`. -/
theorem eq_of_hamming_dist_eq_zero {x y : ∀ i, β i} : hammingDist x y = 0 → x = y := by
  simp_rw [hammingDist, card_eq_zero, filter_eq_empty_iff, not_not, funext_iff, mem_univ, forall_true_left, imp_self]

/-- Corresponds to `dist_eq_zero`. -/
@[simp]
theorem hamming_dist_eq_zero {x y : ∀ i, β i} : hammingDist x y = 0 ↔ x = y :=
  ⟨eq_of_hamming_dist_eq_zero, fun H => by
    rw [H]
    exact hamming_dist_self _⟩

/-- Corresponds to `zero_eq_dist`. -/
@[simp]
theorem hamming_zero_eq_dist {x y : ∀ i, β i} : 0 = hammingDist x y ↔ x = y := by
  rw [eq_comm, hamming_dist_eq_zero]

/-- Corresponds to `dist_ne_zero`. -/
theorem hamming_dist_ne_zero {x y : ∀ i, β i} : hammingDist x y ≠ 0 ↔ x ≠ y :=
  not_iff_not.mpr hamming_dist_eq_zero

/-- Corresponds to `dist_pos`. -/
theorem hamming_dist_pos {x y : ∀ i, β i} : 0 < hammingDist x y ↔ x ≠ y := by
  rw [← hamming_dist_ne_zero, iff_not_comm, not_ltₓ, Nat.le_zero_iffₓ]

@[simp]
theorem hamming_dist_lt_one {x y : ∀ i, β i} : hammingDist x y < 1 ↔ x = y := by
  rw [Nat.lt_one_iff]
  exact hamming_dist_eq_zero

theorem hamming_dist_le_card_fintype {x y : ∀ i, β i} : hammingDist x y ≤ Fintype.card ι :=
  card_le_univ _

theorem hamming_dist_comp_le_hamming_dist (f : ∀ i, γ i → β i) {x y : ∀ i, γ i} :
    (hammingDist (fun i => f i (x i)) fun i => f i (y i)) ≤ hammingDist x y :=
  card_mono ((monotone_filter_right _) fun i H1 H2 => H1 <| congr_arg (f i) H2)

theorem hamming_dist_comp (f : ∀ i, γ i → β i) {x y : ∀ i, γ i} (hf : ∀ i, Injective (f i)) :
    (hammingDist (fun i => f i (x i)) fun i => f i (y i)) = hammingDist x y := by
  refine' le_antisymmₓ (hamming_dist_comp_le_hamming_dist _) _
  exact card_mono ((monotone_filter_right _) fun i H1 H2 => H1 <| hf i H2)

theorem hamming_dist_smul_le_hamming_dist [∀ i, HasSmul α (β i)] {k : α} {x y : ∀ i, β i} :
    hammingDist (k • x) (k • y) ≤ hammingDist x y :=
  hamming_dist_comp_le_hamming_dist fun i => (· • ·) k

/-- Corresponds to `dist_smul` with the discrete norm on `α`. -/
theorem hamming_dist_smul [∀ i, HasSmul α (β i)] {k : α} {x y : ∀ i, β i} (hk : ∀ i, IsSmulRegular (β i) k) :
    hammingDist (k • x) (k • y) = hammingDist x y :=
  hamming_dist_comp (fun i => (· • ·) k) hk

section Zero

variable [∀ i, Zero (β i)] [∀ i, Zero (γ i)]

/-- The Hamming weight function to the naturals. -/
def hammingNorm (x : ∀ i, β i) : ℕ :=
  hammingDist x 0

/-- Corresponds to `dist_zero_right`. -/
theorem hamming_dist_zero_right (x : ∀ i, β i) : hammingDist x 0 = hammingNorm x :=
  rfl

/-- Corresponds to `dist_zero_left`. -/
theorem hamming_dist_zero_left : hammingDist (0 : ∀ i, β i) = hammingNorm :=
  funext fun x => by
    rw [hamming_dist_comm, hamming_dist_zero_right]

/-- Corresponds to `norm_nonneg`. -/
theorem hamming_norm_nonneg {x : ∀ i, β i} : 0 ≤ hammingNorm x :=
  hamming_dist_nonneg

/-- Corresponds to `norm_zero`. -/
@[simp]
theorem hamming_norm_zero : hammingNorm (0 : ∀ i, β i) = 0 :=
  hamming_dist_self _

/-- Corresponds to `norm_eq_zero`. -/
@[simp]
theorem hamming_norm_eq_zero {x : ∀ i, β i} : hammingNorm x = 0 ↔ x = 0 :=
  hamming_dist_eq_zero

/-- Corresponds to `norm_ne_zero_iff`. -/
theorem hamming_norm_ne_zero_iff {x : ∀ i, β i} : hammingNorm x ≠ 0 ↔ x ≠ 0 :=
  hamming_dist_ne_zero

/-- Corresponds to `norm_pos_iff`. -/
theorem hamming_norm_pos_iff {x : ∀ i, β i} : 0 < hammingNorm x ↔ x ≠ 0 :=
  hamming_dist_pos

@[simp]
theorem hamming_norm_lt_one {x : ∀ i, β i} : hammingNorm x < 1 ↔ x = 0 :=
  hamming_dist_lt_one

theorem hamming_norm_le_card_fintype {x : ∀ i, β i} : hammingNorm x ≤ Fintype.card ι :=
  hamming_dist_le_card_fintype

theorem hamming_norm_comp_le_hamming_norm (f : ∀ i, γ i → β i) {x : ∀ i, γ i} (hf : ∀ i, f i 0 = 0) :
    (hammingNorm fun i => f i (x i)) ≤ hammingNorm x := by
  refine' Eq.trans_le _ (hamming_dist_comp_le_hamming_dist f)
  simp_rw [hammingNorm, Pi.zero_def, hf]

theorem hamming_norm_comp (f : ∀ i, γ i → β i) {x : ∀ i, γ i} (hf₁ : ∀ i, Injective (f i)) (hf₂ : ∀ i, f i 0 = 0) :
    (hammingNorm fun i => f i (x i)) = hammingNorm x := by
  simp_rw [← hamming_dist_zero_right]
  convert hamming_dist_comp f hf₁
  simp_rw [Pi.zero_apply, hf₂]
  rfl

theorem hamming_norm_smul_le_hamming_norm [Zero α] [∀ i, SmulWithZero α (β i)] {k : α} {x : ∀ i, β i} :
    hammingNorm (k • x) ≤ hammingNorm x :=
  hamming_norm_comp_le_hamming_norm (fun i (c : β i) => k • c) fun i => by
    simp_rw [smul_zero']

theorem hamming_norm_smul [Zero α] [∀ i, SmulWithZero α (β i)] {k : α} (hk : ∀ i, IsSmulRegular (β i) k)
    (x : ∀ i, β i) : hammingNorm (k • x) = hammingNorm x :=
  hamming_norm_comp (fun i (c : β i) => k • c) hk fun i => by
    simp_rw [smul_zero']

end Zero

/-- Corresponds to `dist_eq_norm`. -/
theorem hamming_dist_eq_hamming_norm [∀ i, AddGroupₓ (β i)] (x y : ∀ i, β i) : hammingDist x y = hammingNorm (x - y) :=
  by
  simp_rw [← hamming_dist_zero_right, hammingDist, Pi.sub_apply, Pi.zero_apply, sub_ne_zero]

end HammingDistNorm

/-! ### The `hamming` type synonym -/


/-- Type synonym for a Pi type which inherits the usual algebraic instances, but is equipped with
the Hamming metric and norm, instead of `pi.normed_group` which uses the sup norm. -/
def Hamming {ι : Type _} (β : ι → Type _) : Type _ :=
  ∀ i, β i

namespace Hamming

variable {α ι : Type _} {β : ι → Type _}

/-! Instances inherited from normal Pi types. -/


instance [∀ i, Inhabited (β i)] : Inhabited (Hamming β) :=
  ⟨fun i => default⟩

instance [DecidableEq ι] [Fintype ι] [∀ i, Fintype (β i)] : Fintype (Hamming β) :=
  Pi.fintype

instance [Inhabited ι] [∀ i, Nonempty (β i)] [Nontrivial (β default)] : Nontrivial (Hamming β) :=
  Pi.nontrivial

instance [Fintype ι] [∀ i, DecidableEq (β i)] : DecidableEq (Hamming β) :=
  Fintype.decidablePiFintype

instance [∀ i, Zero (β i)] : Zero (Hamming β) :=
  Pi.hasZero

instance [∀ i, Neg (β i)] : Neg (Hamming β) :=
  Pi.hasNeg

instance [∀ i, Add (β i)] : Add (Hamming β) :=
  Pi.hasAdd

instance [∀ i, Sub (β i)] : Sub (Hamming β) :=
  Pi.hasSub

instance [∀ i, HasSmul α (β i)] : HasSmul α (Hamming β) :=
  Pi.hasSmul

instance [Zero α] [∀ i, Zero (β i)] [∀ i, SmulWithZero α (β i)] : SmulWithZero α (Hamming β) :=
  Pi.smulWithZero _

instance [∀ i, AddMonoidₓ (β i)] : AddMonoidₓ (Hamming β) :=
  Pi.addMonoid

instance [∀ i, AddCommMonoidₓ (β i)] : AddCommMonoidₓ (Hamming β) :=
  Pi.addCommMonoid

instance [∀ i, AddCommGroupₓ (β i)] : AddCommGroupₓ (Hamming β) :=
  Pi.addCommGroup

instance (α) [Semiringₓ α] (β : ι → Type _) [∀ i, AddCommMonoidₓ (β i)] [∀ i, Module α (β i)] : Module α (Hamming β) :=
  Pi.module _ _ _

/-! API to/from the type synonym. -/


/-- `to_hamming` is the identity function to the `hamming` of a type.  -/
@[matchPattern]
def toHamming : (∀ i, β i) ≃ Hamming β :=
  Equivₓ.refl _

/-- `of_hamming` is the identity function from the `hamming` of a type.  -/
@[matchPattern]
def ofHamming : Hamming β ≃ ∀ i, β i :=
  Equivₓ.refl _

@[simp]
theorem to_hamming_symm_eq : (@toHamming _ β).symm = of_hamming :=
  rfl

@[simp]
theorem of_hamming_symm_eq : (@ofHamming _ β).symm = to_hamming :=
  rfl

@[simp]
theorem to_hamming_of_hamming (x : Hamming β) : toHamming (ofHamming x) = x :=
  rfl

@[simp]
theorem of_hamming_to_hamming (x : ∀ i, β i) : ofHamming (toHamming x) = x :=
  rfl

@[simp]
theorem to_hamming_inj {x y : ∀ i, β i} : toHamming x = toHamming y ↔ x = y :=
  Iff.rfl

@[simp]
theorem of_hamming_inj {x y : Hamming β} : ofHamming x = ofHamming y ↔ x = y :=
  Iff.rfl

@[simp]
theorem to_hamming_zero [∀ i, Zero (β i)] : toHamming (0 : ∀ i, β i) = 0 :=
  rfl

@[simp]
theorem of_hamming_zero [∀ i, Zero (β i)] : ofHamming (0 : Hamming β) = 0 :=
  rfl

@[simp]
theorem to_hamming_neg [∀ i, Neg (β i)] {x : ∀ i, β i} : toHamming (-x) = -toHamming x :=
  rfl

@[simp]
theorem of_hamming_neg [∀ i, Neg (β i)] {x : Hamming β} : ofHamming (-x) = -ofHamming x :=
  rfl

@[simp]
theorem to_hamming_add [∀ i, Add (β i)] {x y : ∀ i, β i} : toHamming (x + y) = toHamming x + toHamming y :=
  rfl

@[simp]
theorem of_hamming_add [∀ i, Add (β i)] {x y : Hamming β} : ofHamming (x + y) = ofHamming x + ofHamming y :=
  rfl

@[simp]
theorem to_hamming_sub [∀ i, Sub (β i)] {x y : ∀ i, β i} : toHamming (x - y) = toHamming x - toHamming y :=
  rfl

@[simp]
theorem of_hamming_sub [∀ i, Sub (β i)] {x y : Hamming β} : ofHamming (x - y) = ofHamming x - ofHamming y :=
  rfl

@[simp]
theorem to_hamming_smul [∀ i, HasSmul α (β i)] {r : α} {x : ∀ i, β i} : toHamming (r • x) = r • toHamming x :=
  rfl

@[simp]
theorem of_hamming_smul [∀ i, HasSmul α (β i)] {r : α} {x : Hamming β} : ofHamming (r • x) = r • ofHamming x :=
  rfl

section

/-! Instances equipping `hamming` with `hamming_norm` and `hamming_dist`. -/


variable [Fintype ι] [∀ i, DecidableEq (β i)]

instance : HasDist (Hamming β) :=
  ⟨fun x y => hammingDist (ofHamming x) (ofHamming y)⟩

@[simp, push_cast]
theorem dist_eq_hamming_dist (x y : Hamming β) : dist x y = hammingDist (ofHamming x) (ofHamming y) :=
  rfl

instance : PseudoMetricSpace (Hamming β) :=
  { Hamming.hasDist with
    dist_self := by
      push_cast
      exact_mod_cast hamming_dist_self,
    dist_comm := by
      push_cast
      exact_mod_cast hamming_dist_comm,
    dist_triangle := by
      push_cast
      exact_mod_cast hamming_dist_triangle,
    toUniformSpace := ⊥,
    uniformity_dist :=
      (uniformity_dist_of_mem_uniformity _ _) fun s => by
        push_cast
        constructor
        · refine' fun hs => ⟨1, zero_lt_one, fun _ _ hab => _⟩
          rw_mod_cast[hamming_dist_lt_one]  at hab
          rw [of_hamming_inj, ← mem_id_rel] at hab
          exact hs hab
          
        · rintro ⟨_, hε, hs⟩ ⟨_, _⟩ hab
          rw [mem_id_rel] at hab
          rw [hab]
          refine' hs (lt_of_eq_of_lt _ hε)
          exact_mod_cast hamming_dist_self _
          ,
    toBornology := ⟨⊥, bot_le⟩,
    cobounded_sets := by
      ext
      push_cast
      refine' iff_of_true (filter.mem_sets.mpr Filter.mem_bot) ⟨Fintype.card ι, fun _ _ _ _ => _⟩
      exact_mod_cast hamming_dist_le_card_fintype }

@[simp, push_cast]
theorem nndist_eq_hamming_dist (x y : Hamming β) : nndist x y = hammingDist (ofHamming x) (ofHamming y) :=
  rfl

instance : MetricSpace (Hamming β) :=
  { Hamming.pseudoMetricSpace with
    eq_of_dist_eq_zero := by
      push_cast
      exact_mod_cast @eq_of_hamming_dist_eq_zero _ _ _ _ }

instance [∀ i, Zero (β i)] : HasNorm (Hamming β) :=
  ⟨fun x => hammingNorm (ofHamming x)⟩

@[simp, push_cast]
theorem norm_eq_hamming_norm [∀ i, Zero (β i)] (x : Hamming β) : ∥x∥ = hammingNorm (ofHamming x) :=
  rfl

instance [∀ i, AddCommGroupₓ (β i)] : SemiNormedGroup (Hamming β) :=
  { Pi.addCommGroup with
    dist_eq := by
      push_cast
      exact_mod_cast hamming_dist_eq_hamming_norm }

@[simp, push_cast]
theorem nnnorm_eq_hamming_norm [∀ i, AddCommGroupₓ (β i)] (x : Hamming β) : ∥x∥₊ = hammingNorm (ofHamming x) :=
  rfl

instance [∀ i, AddCommGroupₓ (β i)] : NormedGroup (Hamming β) :=
  { Hamming.semiNormedGroup with }

end

end Hamming


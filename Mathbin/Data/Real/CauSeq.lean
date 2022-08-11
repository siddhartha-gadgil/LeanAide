/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Algebra.Order.AbsoluteValue
import Mathbin.Algebra.BigOperators.Order

/-!
# Cauchy sequences

A basic theory of Cauchy sequences, used in the construction of the reals and p-adic numbers. Where
applicable, lemmas that will be reused in other contexts have been stated in extra generality.

There are other "versions" of Cauchyness in the library, in particular Cauchy filters in topology.
This is a concrete implementation that is useful for simplicity and computability reasons.

## Important definitions

* `is_cau_seq`: a predicate that says `f : ℕ → β` is Cauchy.
* `cau_seq`: the type of Cauchy sequences valued in type `β` with respect to an absolute value
  function `abv`.

## Tags

sequence, cauchy, abs val, absolute value
-/


open BigOperators

open IsAbsoluteValue

theorem exists_forall_ge_and {α} [LinearOrderₓ α] {P Q : α → Prop} :
    (∃ i, ∀, ∀ j ≥ i, ∀, P j) → (∃ i, ∀, ∀ j ≥ i, ∀, Q j) → ∃ i, ∀, ∀ j ≥ i, ∀, P j ∧ Q j
  | ⟨a, h₁⟩, ⟨b, h₂⟩ =>
    let ⟨c, ac, bc⟩ := exists_ge_of_linear a b
    ⟨c, fun j hj => ⟨h₁ _ (le_transₓ ac hj), h₂ _ (le_transₓ bc hj)⟩⟩

section

variable {α : Type _} [LinearOrderedField α] {β : Type _} [Ringₓ β] (abv : β → α) [IsAbsoluteValue abv]

theorem rat_add_continuous_lemma {ε : α} (ε0 : 0 < ε) :
    ∃ δ > 0, ∀ {a₁ a₂ b₁ b₂ : β}, abv (a₁ - b₁) < δ → abv (a₂ - b₂) < δ → abv (a₁ + a₂ - (b₁ + b₂)) < ε :=
  ⟨ε / 2, half_pos ε0, fun a₁ a₂ b₁ b₂ h₁ h₂ => by
    simpa [← add_halves, ← sub_eq_add_neg, ← add_commₓ, ← add_left_commₓ, ← add_assocₓ] using
      lt_of_le_of_ltₓ (abv_add abv _ _) (add_lt_add h₁ h₂)⟩

theorem rat_mul_continuous_lemma {ε K₁ K₂ : α} (ε0 : 0 < ε) :
    ∃ δ > 0,
      ∀ {a₁ a₂ b₁ b₂ : β},
        abv a₁ < K₁ → abv b₂ < K₂ → abv (a₁ - b₁) < δ → abv (a₂ - b₂) < δ → abv (a₁ * a₂ - b₁ * b₂) < ε :=
  by
  have K0 : (0 : α) < max 1 (max K₁ K₂) := lt_of_lt_of_leₓ zero_lt_one (le_max_leftₓ _ _)
  have εK := div_pos (half_pos ε0) K0
  refine' ⟨_, εK, fun a₁ a₂ b₁ b₂ ha₁ hb₂ h₁ h₂ => _⟩
  replace ha₁ := lt_of_lt_of_leₓ ha₁ (le_transₓ (le_max_leftₓ _ K₂) (le_max_rightₓ 1 _))
  replace hb₂ := lt_of_lt_of_leₓ hb₂ (le_transₓ (le_max_rightₓ K₁ _) (le_max_rightₓ 1 _))
  have :=
    add_lt_add (mul_lt_mul' (le_of_ltₓ h₁) hb₂ (abv_nonneg abv _) εK)
      (mul_lt_mul' (le_of_ltₓ h₂) ha₁ (abv_nonneg abv _) εK)
  rw [← abv_mul abv, mul_comm, div_mul_cancel _ (ne_of_gtₓ K0), ← abv_mul abv, add_halves] at this
  simpa [← mul_addₓ, ← add_mulₓ, ← sub_eq_add_neg, ← add_commₓ, ← add_left_commₓ] using
    lt_of_le_of_ltₓ (abv_add abv _ _) this

theorem rat_inv_continuous_lemma {β : Type _} [Field β] (abv : β → α) [IsAbsoluteValue abv] {ε K : α} (ε0 : 0 < ε)
    (K0 : 0 < K) : ∃ δ > 0, ∀ {a b : β}, K ≤ abv a → K ≤ abv b → abv (a - b) < δ → abv (a⁻¹ - b⁻¹) < ε := by
  have KK := mul_pos K0 K0
  have εK := mul_pos ε0 KK
  refine' ⟨_, εK, fun a b ha hb h => _⟩
  have a0 := lt_of_lt_of_leₓ K0 ha
  have b0 := lt_of_lt_of_leₓ K0 hb
  rw [inv_sub_inv ((abv_pos abv).1 a0) ((abv_pos abv).1 b0), abv_div abv, abv_mul abv, mul_comm, abv_sub abv, ←
    mul_div_cancel ε (ne_of_gtₓ KK)]
  exact div_lt_div h (mul_le_mul hb ha (le_of_ltₓ K0) (abv_nonneg abv _)) (le_of_ltₓ <| mul_pos ε0 KK) KK

end

/-- A sequence is Cauchy if the distance between its entries tends to zero. -/
def IsCauSeq {α : Type _} [LinearOrderedField α] {β : Type _} [Ringₓ β] (abv : β → α) (f : ℕ → β) : Prop :=
  ∀, ∀ ε > 0, ∀, ∃ i, ∀, ∀ j ≥ i, ∀, abv (f j - f i) < ε

namespace IsCauSeq

variable {α : Type _} [LinearOrderedField α] {β : Type _} [Ringₓ β] {abv : β → α} [IsAbsoluteValue abv] {f : ℕ → β}

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j k «expr ≥ » i)
-- see Note [nolint_ge]
@[nolint ge_or_gt]
theorem cauchy₂ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ (j k) (_ : j ≥ i) (_ : k ≥ i), abv (f j - f k) < ε := by
  refine' (hf _ (half_pos ε0)).imp fun i hi j ij k ik => _
  rw [← add_halves ε]
  refine' lt_of_le_of_ltₓ (abv_sub_le abv _ _ _) (add_lt_add (hi _ ij) _)
  rw [abv_sub abv]
  exact hi _ ik

theorem cauchy₃ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) : ∃ i, ∀, ∀ j ≥ i, ∀, ∀, ∀ k ≥ j, ∀, abv (f k - f j) < ε :=
  let ⟨i, H⟩ := hf.cauchy₂ ε0
  ⟨i, fun j ij k jk => H _ (le_transₓ ij jk) _ ij⟩

end IsCauSeq

/-- `cau_seq β abv` is the type of `β`-valued Cauchy sequences, with respect to the absolute value
function `abv`. -/
def CauSeq {α : Type _} [LinearOrderedField α] (β : Type _) [Ringₓ β] (abv : β → α) : Type _ :=
  { f : ℕ → β // IsCauSeq abv f }

namespace CauSeq

variable {α : Type _} [LinearOrderedField α]

section Ringₓ

variable {β : Type _} [Ringₓ β] {abv : β → α}

instance : CoeFun (CauSeq β abv) fun _ => ℕ → β :=
  ⟨Subtype.val⟩

@[simp]
theorem mk_to_fun (f) (hf : IsCauSeq abv f) : @coeFn (CauSeq β abv) _ _ ⟨f, hf⟩ = f :=
  rfl

theorem ext {f g : CauSeq β abv} (h : ∀ i, f i = g i) : f = g :=
  Subtype.eq (funext h)

theorem is_cau (f : CauSeq β abv) : IsCauSeq abv f :=
  f.2

theorem cauchy (f : CauSeq β abv) : ∀ {ε}, 0 < ε → ∃ i, ∀, ∀ j ≥ i, ∀, abv (f j - f i) < ε :=
  f.2

/-- Given a Cauchy sequence `f`, create a Cauchy sequence from a sequence `g` with
the same values as `f`. -/
def ofEq (f : CauSeq β abv) (g : ℕ → β) (e : ∀ i, f i = g i) : CauSeq β abv :=
  ⟨g, fun ε => by
    rw [show g = f from (funext e).symm] <;> exact f.cauchy⟩

variable [IsAbsoluteValue abv]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j k «expr ≥ » i)
-- see Note [nolint_ge]
@[nolint ge_or_gt]
theorem cauchy₂ (f : CauSeq β abv) {ε} : 0 < ε → ∃ i, ∀ (j k) (_ : j ≥ i) (_ : k ≥ i), abv (f j - f k) < ε :=
  f.2.cauchy₂

theorem cauchy₃ (f : CauSeq β abv) {ε} : 0 < ε → ∃ i, ∀, ∀ j ≥ i, ∀, ∀, ∀ k ≥ j, ∀, abv (f k - f j) < ε :=
  f.2.cauchy₃

theorem bounded (f : CauSeq β abv) : ∃ r, ∀ i, abv (f i) < r := by
  cases' f.cauchy zero_lt_one with i h
  let R := ∑ j in Finset.range (i + 1), abv (f j)
  have : ∀, ∀ j ≤ i, ∀, abv (f j) ≤ R := by
    intro j ij
    change (fun j => abv (f j)) j ≤ R
    apply Finset.single_le_sum
    · intros
      apply abv_nonneg abv
      
    · rwa [Finset.mem_range, Nat.lt_succ_iffₓ]
      
  refine' ⟨R + 1, fun j => _⟩
  cases' lt_or_leₓ j i with ij ij
  · exact lt_of_le_of_ltₓ (this _ (le_of_ltₓ ij)) (lt_add_one _)
    
  · have := lt_of_le_of_ltₓ (abv_add abv _ _) (add_lt_add_of_le_of_lt (this _ le_rfl) (h _ ij))
    rw [add_sub, add_commₓ] at this
    simpa
    

theorem bounded' (f : CauSeq β abv) (x : α) : ∃ r > x, ∀ i, abv (f i) < r :=
  let ⟨r, h⟩ := f.Bounded
  ⟨max r (x + 1), lt_of_lt_of_leₓ (lt_add_one _) (le_max_rightₓ _ _), fun i => lt_of_lt_of_leₓ (h i) (le_max_leftₓ _ _)⟩

instance : Add (CauSeq β abv) :=
  ⟨fun f g =>
    ⟨fun i => (f i + g i : β), fun ε ε0 =>
      let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abv ε0
      let ⟨i, H⟩ := exists_forall_ge_and (f.cauchy₃ δ0) (g.cauchy₃ δ0)
      ⟨i, fun j ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        Hδ (H₁ _ ij) (H₂ _ ij)⟩⟩⟩

@[simp]
theorem add_apply (f g : CauSeq β abv) (i : ℕ) : (f + g) i = f i + g i :=
  rfl

variable (abv)

/-- The constant Cauchy sequence. -/
def const (x : β) : CauSeq β abv :=
  ⟨fun i => x, fun ε ε0 =>
    ⟨0, fun j ij => by
      simpa [← abv_zero abv] using ε0⟩⟩

variable {abv}

-- mathport name: «exprconst»
local notation "const" => const abv

@[simp]
theorem const_apply (x : β) (i : ℕ) : (const x : ℕ → β) i = x :=
  rfl

theorem const_inj {x y : β} : (const x : CauSeq β abv) = const y ↔ x = y :=
  ⟨fun h => congr_arg (fun f : CauSeq β abv => (f : ℕ → β) 0) h, congr_arg _⟩

instance : Zero (CauSeq β abv) :=
  ⟨const 0⟩

instance : One (CauSeq β abv) :=
  ⟨const 1⟩

instance : Inhabited (CauSeq β abv) :=
  ⟨0⟩

@[simp]
theorem zero_apply (i) : (0 : CauSeq β abv) i = 0 :=
  rfl

@[simp]
theorem one_apply (i) : (1 : CauSeq β abv) i = 1 :=
  rfl

@[simp]
theorem const_zero : const 0 = 0 :=
  rfl

theorem const_add (x y : β) : const (x + y) = const x + const y :=
  rfl

instance : Mul (CauSeq β abv) :=
  ⟨fun f g =>
    ⟨fun i => (f i * g i : β), fun ε ε0 =>
      let ⟨F, F0, hF⟩ := f.bounded' 0
      let ⟨G, G0, hG⟩ := g.bounded' 0
      let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abv ε0
      let ⟨i, H⟩ := exists_forall_ge_and (f.cauchy₃ δ0) (g.cauchy₃ δ0)
      ⟨i, fun j ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        Hδ (hF j) (hG i) (H₁ _ ij) (H₂ _ ij)⟩⟩⟩

@[simp]
theorem mul_apply (f g : CauSeq β abv) (i : ℕ) : (f * g) i = f i * g i :=
  rfl

theorem const_mul (x y : β) : const (x * y) = const x * const y :=
  ext fun i => rfl

instance : Neg (CauSeq β abv) :=
  ⟨fun f =>
    ofEq (const (-1) * f) (fun x => -f x) fun i => by
      simp ⟩

@[simp]
theorem neg_apply (f : CauSeq β abv) (i) : (-f) i = -f i :=
  rfl

theorem const_neg (x : β) : const (-x) = -const x :=
  ext fun i => rfl

instance : Sub (CauSeq β abv) :=
  ⟨fun f g =>
    ofEq (f + -g) (fun x => f x - g x) fun i => by
      simp [← sub_eq_add_neg]⟩

@[simp]
theorem sub_apply (f g : CauSeq β abv) (i : ℕ) : (f - g) i = f i - g i :=
  rfl

theorem const_sub (x y : β) : const (x - y) = const x - const y :=
  ext fun i => rfl

instance : AddGroupₓ (CauSeq β abv) := by
  refine_struct
      { add := (· + ·), neg := Neg.neg, zero := (0 : CauSeq β abv), sub := Sub.sub,
        zsmul := @zsmulRec (CauSeq β abv) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩, nsmul := @nsmulRec (CauSeq β abv) ⟨0⟩ ⟨(· + ·)⟩ } <;>
    intros <;>
      try
          rfl <;>
        apply ext <;> simp [← add_commₓ, ← add_left_commₓ, ← sub_eq_add_neg]

instance : AddGroupWithOneₓ (CauSeq β abv) :=
  { CauSeq.addGroup with one := 1, natCast := fun n => const n, nat_cast_zero := congr_arg const Nat.cast_zeroₓ,
    nat_cast_succ := fun n => congr_arg const (Nat.cast_succₓ n), intCast := fun n => const n,
    int_cast_of_nat := fun n => congr_arg const (Int.cast_of_nat n),
    int_cast_neg_succ_of_nat := fun n => congr_arg const (Int.cast_neg_succ_of_nat n) }

instance : Ringₓ (CauSeq β abv) := by
  refine_struct
      { CauSeq.addGroupWithOne with add := (· + ·), zero := (0 : CauSeq β abv), mul := (· * ·), one := 1,
        npow := @npowRec (CauSeq β abv) ⟨1⟩ ⟨(· * ·)⟩ } <;>
    intros <;>
      try
          rfl <;>
        apply ext <;> simp [← mul_addₓ, ← mul_assoc, ← add_mulₓ, ← add_commₓ, ← add_left_commₓ, ← sub_eq_add_neg]

instance {β : Type _} [CommRingₓ β] {abv : β → α} [IsAbsoluteValue abv] : CommRingₓ (CauSeq β abv) :=
  { CauSeq.ring with
    mul_comm := by
      intros <;> apply ext <;> simp [← mul_left_commₓ, ← mul_comm] }

/-- `lim_zero f` holds when `f` approaches 0. -/
def LimZero {abv : β → α} (f : CauSeq β abv) : Prop :=
  ∀, ∀ ε > 0, ∀, ∃ i, ∀, ∀ j ≥ i, ∀, abv (f j) < ε

theorem add_lim_zero {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g) : LimZero (f + g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ <| half_pos ε0) (hg _ <| half_pos ε0)).imp fun i H j ij => by
      let ⟨H₁, H₂⟩ := H _ ij
      simpa [← add_halves ε] using lt_of_le_of_ltₓ (abv_add abv _ _) (add_lt_add H₁ H₂)

theorem mul_lim_zero_right (f : CauSeq β abv) {g} (hg : LimZero g) : LimZero (f * g)
  | ε, ε0 =>
    let ⟨F, F0, hF⟩ := f.bounded' 0
    (hg _ <| div_pos ε0 F0).imp fun i H j ij => by
      have := mul_lt_mul' (le_of_ltₓ <| hF j) (H _ ij) (abv_nonneg abv _) F0 <;>
        rwa [mul_comm F, div_mul_cancel _ (ne_of_gtₓ F0), ← abv_mul abv] at this

theorem mul_lim_zero_left {f} (g : CauSeq β abv) (hg : LimZero f) : LimZero (f * g)
  | ε, ε0 =>
    let ⟨G, G0, hG⟩ := g.bounded' 0
    (hg _ <| div_pos ε0 G0).imp fun i H j ij => by
      have := mul_lt_mul'' (H _ ij) (hG j) (abv_nonneg abv _) (abv_nonneg abv _) <;>
        rwa [div_mul_cancel _ (ne_of_gtₓ G0), ← abv_mul abv] at this

theorem neg_lim_zero {f : CauSeq β abv} (hf : LimZero f) : LimZero (-f) := by
  rw [← neg_one_mul] <;> exact mul_lim_zero_right _ hf

theorem sub_lim_zero {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g) : LimZero (f - g) := by
  simpa only [← sub_eq_add_neg] using add_lim_zero hf (neg_lim_zero hg)

theorem lim_zero_sub_rev {f g : CauSeq β abv} (hfg : LimZero (f - g)) : LimZero (g - f) := by
  simpa using neg_lim_zero hfg

theorem zero_lim_zero : LimZero (0 : CauSeq β abv)
  | ε, ε0 =>
    ⟨0, fun j ij => by
      simpa [← abv_zero abv] using ε0⟩

theorem const_lim_zero {x : β} : LimZero (const x) ↔ x = 0 :=
  ⟨fun H =>
    (abv_eq_zero abv).1 <|
      (eq_of_le_of_forall_le_of_dense (abv_nonneg abv _)) fun ε ε0 =>
        let ⟨i, hi⟩ := H _ ε0
        le_of_ltₓ <| hi _ le_rfl,
    fun e => e.symm ▸ zero_lim_zero⟩

instance equiv : Setoidₓ (CauSeq β abv) :=
  ⟨fun f g => LimZero (f - g),
    ⟨fun f => by
      simp [← zero_lim_zero], fun f g h => by
      simpa using neg_lim_zero h, fun f g h fg gh => by
      simpa [← sub_eq_add_neg, ← add_assocₓ] using add_lim_zero fg gh⟩⟩

theorem add_equiv_add {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) : f1 + g1 ≈ f2 + g2 := by
  change lim_zero (f1 + g1 - _)
  convert add_lim_zero hf hg using 1
  simp only [← sub_eq_add_neg, ← add_assocₓ]
  rw [add_commₓ (-f2)]
  simp only [← add_assocₓ]
  congr 2
  simp

theorem neg_equiv_neg {f g : CauSeq β abv} (hf : f ≈ g) : -f ≈ -g := by
  show lim_zero (-f - -g)
  rw [← neg_sub']
  exact neg_lim_zero hf

theorem equiv_def₃ {f g : CauSeq β abv} (h : f ≈ g) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀, ∀ j ≥ i, ∀, ∀, ∀ k ≥ j, ∀, abv (f k - g j) < ε :=
  (exists_forall_ge_and (h _ <| half_pos ε0) (f.cauchy₃ <| half_pos ε0)).imp fun i H j ij k jk => by
    let ⟨h₁, h₂⟩ := H _ ij
    have := lt_of_le_of_ltₓ (abv_add abv (f j - g j) _) (add_lt_add h₁ (h₂ _ jk)) <;>
      rwa [sub_add_sub_cancel', add_halves] at this

theorem lim_zero_congr {f g : CauSeq β abv} (h : f ≈ g) : LimZero f ↔ LimZero g :=
  ⟨fun l => by
    simpa using add_lim_zero (Setoidₓ.symm h) l, fun l => by
    simpa using add_lim_zero h l⟩

theorem abv_pos_of_not_lim_zero {f : CauSeq β abv} (hf : ¬LimZero f) : ∃ K > 0, ∃ i, ∀, ∀ j ≥ i, ∀, K ≤ abv (f j) := by
  have := Classical.propDecidable
  by_contra nk
  refine' hf fun ε ε0 => _
  simp [← not_forall] at nk
  cases' f.cauchy₃ (half_pos ε0) with i hi
  rcases nk _ (half_pos ε0) i with ⟨j, ij, hj⟩
  refine' ⟨j, fun k jk => _⟩
  have := lt_of_le_of_ltₓ (abv_add abv _ _) (add_lt_add (hi j ij k jk) hj)
  rwa [sub_add_cancel, add_halves] at this

theorem of_near (f : ℕ → β) (g : CauSeq β abv) (h : ∀, ∀ ε > 0, ∀, ∃ i, ∀, ∀ j ≥ i, ∀, abv (f j - g j) < ε) :
    IsCauSeq abv f
  | ε, ε0 =>
    let ⟨i, hi⟩ := exists_forall_ge_and (h _ (half_pos <| half_pos ε0)) (g.cauchy₃ <| half_pos ε0)
    ⟨i, fun j ij => by
      cases' hi _ le_rfl with h₁ h₂
      rw [abv_sub abv] at h₁
      have := lt_of_le_of_ltₓ (abv_add abv _ _) (add_lt_add (hi _ ij).1 h₁)
      have := lt_of_le_of_ltₓ (abv_add abv _ _) (add_lt_add this (h₂ _ ij))
      rwa [add_halves, add_halves, add_right_commₓ, sub_add_sub_cancel, sub_add_sub_cancel] at this⟩

theorem not_lim_zero_of_not_congr_zero {f : CauSeq _ abv} (hf : ¬f ≈ 0) : ¬LimZero f := fun this : LimZero f =>
  have : LimZero (f - 0) := by
    simpa
  hf this

theorem mul_equiv_zero (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : g * f ≈ 0 :=
  have : LimZero (f - 0) := hf
  have : LimZero (g * f) :=
    mul_lim_zero_right _ <| by
      simpa
  show LimZero (g * f - 0) by
    simpa

theorem mul_not_equiv_zero {f g : CauSeq _ abv} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) : ¬f * g ≈ 0 :=
  fun this : LimZero (f * g - 0) => by
  have hlz : LimZero (f * g) := by
    simpa
  have hf' : ¬LimZero f := by
    simpa using show ¬lim_zero (f - 0) from hf
  have hg' : ¬LimZero g := by
    simpa using show ¬lim_zero (g - 0) from hg
  rcases abv_pos_of_not_lim_zero hf' with ⟨a1, ha1, N1, hN1⟩
  rcases abv_pos_of_not_lim_zero hg' with ⟨a2, ha2, N2, hN2⟩
  have : 0 < a1 * a2 := mul_pos ha1 ha2
  cases' hlz _ this with N hN
  let i := max N (max N1 N2)
  have hN' := hN i (le_max_leftₓ _ _)
  have hN1' := hN1 i (le_transₓ (le_max_leftₓ _ _) (le_max_rightₓ _ _))
  have hN1' := hN2 i (le_transₓ (le_max_rightₓ _ _) (le_max_rightₓ _ _))
  apply not_le_of_lt hN'
  change _ ≤ abv (_ * _)
  rw [IsAbsoluteValue.abv_mul abv]
  apply mul_le_mul <;>
    try
      assumption
  · apply le_of_ltₓ ha2
    
  · apply IsAbsoluteValue.abv_nonneg abv
    

theorem const_equiv {x y : β} : const x ≈ const y ↔ x = y :=
  show LimZero _ ↔ _ by
    rw [← const_sub, const_lim_zero, sub_eq_zero]

end Ringₓ

section CommRingₓ

variable {β : Type _} [CommRingₓ β] {abv : β → α} [IsAbsoluteValue abv]

theorem mul_equiv_zero' (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : f * g ≈ 0 := by
  rw [mul_comm] <;> apply mul_equiv_zero _ hf

end CommRingₓ

section IsDomain

variable {β : Type _} [Ringₓ β] [IsDomain β] (abv : β → α) [IsAbsoluteValue abv]

theorem one_not_equiv_zero : ¬const abv 1 ≈ const abv 0 := fun h =>
  have : ∀, ∀ ε > 0, ∀, ∃ i, ∀ k, i ≤ k → abv (1 - 0) < ε := h
  have h1 : abv 1 ≤ 0 :=
    le_of_not_gtₓ fun h2 : 0 < abv 1 =>
      (Exists.elim (this _ h2)) fun i hi =>
        lt_irreflₓ (abv 1) <| by
          simpa using hi _ le_rfl
  have h2 : 0 ≤ abv 1 := IsAbsoluteValue.abv_nonneg _ _
  have : abv 1 = 0 := le_antisymmₓ h1 h2
  have : (1 : β) = 0 := (IsAbsoluteValue.abv_eq_zero abv).1 this
  absurd this one_ne_zero

end IsDomain

section Field

variable {β : Type _} [Field β] {abv : β → α} [IsAbsoluteValue abv]

theorem inv_aux {f : CauSeq β abv} (hf : ¬LimZero f) : ∀, ∀ ε > 0, ∀, ∃ i, ∀, ∀ j ≥ i, ∀, abv ((f j)⁻¹ - (f i)⁻¹) < ε
  | ε, ε0 =>
    let ⟨K, K0, HK⟩ := abv_pos_of_not_lim_zero hf
    let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abv ε0 K0
    let ⟨i, H⟩ := exists_forall_ge_and HK (f.cauchy₃ δ0)
    ⟨i, fun j ij =>
      let ⟨iK, H'⟩ := H _ le_rfl
      Hδ (H _ ij).1 iK (H' _ ij)⟩

/-- Given a Cauchy sequence `f` with nonzero limit, create a Cauchy sequence with values equal to
the inverses of the values of `f`. -/
def inv (f : CauSeq β abv) (hf : ¬LimZero f) : CauSeq β abv :=
  ⟨_, inv_aux hf⟩

@[simp]
theorem inv_apply {f : CauSeq β abv} (hf i) : inv f hf i = (f i)⁻¹ :=
  rfl

theorem inv_mul_cancel {f : CauSeq β abv} (hf) : inv f hf * f ≈ 1 := fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := abv_pos_of_not_lim_zero hf
  ⟨i, fun j ij => by
    simpa [← (abv_pos abv).1 (lt_of_lt_of_leₓ K0 (H _ ij)), ← abv_zero abv] using ε0⟩

theorem const_inv {x : β} (hx : x ≠ 0) :
    const abv x⁻¹ =
      inv (const abv x)
        (by
          rwa [const_lim_zero]) :=
  ext fun n => by
    simp [← inv_apply, ← const_apply]

end Field

section Abs

-- mathport name: «exprconst»
local notation "const" => const abs

/-- The entries of a positive Cauchy sequence eventually have a positive lower bound. -/
def Pos (f : CauSeq α abs) : Prop :=
  ∃ K > 0, ∃ i, ∀, ∀ j ≥ i, ∀, K ≤ f j

theorem not_lim_zero_of_pos {f : CauSeq α abs} : Pos f → ¬LimZero f
  | ⟨F, F0, hF⟩, H =>
    let ⟨i, h⟩ := exists_forall_ge_and hF (H _ F0)
    let ⟨h₁, h₂⟩ := h _ le_rfl
    not_lt_of_le h₁ (abs_lt.1 h₂).2

theorem const_pos {x : α} : Pos (const x) ↔ 0 < x :=
  ⟨fun ⟨K, K0, i, h⟩ => lt_of_lt_of_leₓ K0 (h _ le_rfl), fun h => ⟨x, h, 0, fun j _ => le_rfl⟩⟩

theorem add_pos {f g : CauSeq α abs} : Pos f → Pos g → Pos (f + g)
  | ⟨F, F0, hF⟩, ⟨G, G0, hG⟩ =>
    let ⟨i, h⟩ := exists_forall_ge_and hF hG
    ⟨_, add_pos F0 G0, i, fun j ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      add_le_add h₁ h₂⟩

theorem pos_add_lim_zero {f g : CauSeq α abs} : Pos f → LimZero g → Pos (f + g)
  | ⟨F, F0, hF⟩, H =>
    let ⟨i, h⟩ := exists_forall_ge_and hF (H _ (half_pos F0))
    ⟨_, half_pos F0, i, fun j ij => by
      cases' h j ij with h₁ h₂
      have := add_le_add h₁ (le_of_ltₓ (abs_lt.1 h₂).1)
      rwa [← sub_eq_add_neg, sub_self_div_two] at this⟩

protected theorem mul_pos {f g : CauSeq α abs} : Pos f → Pos g → Pos (f * g)
  | ⟨F, F0, hF⟩, ⟨G, G0, hG⟩ =>
    let ⟨i, h⟩ := exists_forall_ge_and hF hG
    ⟨_, mul_pos F0 G0, i, fun j ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      mul_le_mul h₁ h₂ (le_of_ltₓ G0) (le_transₓ (le_of_ltₓ F0) h₁)⟩

theorem trichotomy (f : CauSeq α abs) : Pos f ∨ LimZero f ∨ Pos (-f) := by
  cases Classical.em (lim_zero f) <;> simp [*]
  rcases abv_pos_of_not_lim_zero h with ⟨K, K0, hK⟩
  rcases exists_forall_ge_and hK (f.cauchy₃ K0) with ⟨i, hi⟩
  refine' (le_totalₓ 0 (f i)).imp _ _ <;>
    refine' fun h => ⟨K, K0, i, fun j ij => _⟩ <;> have := (hi _ ij).1 <;> cases' hi _ le_rfl with h₁ h₂
  · rwa [abs_of_nonneg] at this
    rw [abs_of_nonneg h] at h₁
    exact (le_add_iff_nonneg_right _).1 (le_transₓ h₁ <| neg_le_sub_iff_le_add'.1 <| le_of_ltₓ (abs_lt.1 <| h₂ _ ij).1)
    
  · rwa [abs_of_nonpos] at this
    rw [abs_of_nonpos h] at h₁
    rw [← sub_le_sub_iff_right, zero_sub]
    exact le_transₓ (le_of_ltₓ (abs_lt.1 <| h₂ _ ij).2) h₁
    

instance : LT (CauSeq α abs) :=
  ⟨fun f g => Pos (g - f)⟩

instance : LE (CauSeq α abs) :=
  ⟨fun f g => f < g ∨ f ≈ g⟩

theorem lt_of_lt_of_eq {f g h : CauSeq α abs} (fg : f < g) (gh : g ≈ h) : f < h :=
  show Pos (h - f) by
    simpa [← sub_eq_add_neg, ← add_commₓ, ← add_left_commₓ] using pos_add_lim_zero fg (neg_lim_zero gh)

theorem lt_of_eq_of_lt {f g h : CauSeq α abs} (fg : f ≈ g) (gh : g < h) : f < h := by
  have := pos_add_lim_zero gh (neg_lim_zero fg) <;> rwa [← sub_eq_add_neg, sub_sub_sub_cancel_right] at this

theorem lt_trans {f g h : CauSeq α abs} (fg : f < g) (gh : g < h) : f < h :=
  show Pos (h - f) by
    simpa [← sub_eq_add_neg, ← add_commₓ, ← add_left_commₓ] using add_pos fg gh

theorem lt_irrefl {f : CauSeq α abs} : ¬f < f
  | h =>
    not_lim_zero_of_pos h
      (by
        simp [← zero_lim_zero])

theorem le_of_eq_of_le {f g h : CauSeq α abs} (hfg : f ≈ g) (hgh : g ≤ h) : f ≤ h :=
  hgh.elim (Or.inl ∘ CauSeq.lt_of_eq_of_lt hfg) (Or.inr ∘ Setoidₓ.trans hfg)

theorem le_of_le_of_eq {f g h : CauSeq α abs} (hfg : f ≤ g) (hgh : g ≈ h) : f ≤ h :=
  hfg.elim (fun h => Or.inl (CauSeq.lt_of_lt_of_eq h hgh)) fun h => Or.inr (Setoidₓ.trans h hgh)

instance : Preorderₓ (CauSeq α abs) where
  lt := (· < ·)
  le := fun f g => f < g ∨ f ≈ g
  le_refl := fun f => Or.inr (Setoidₓ.refl _)
  le_trans := fun f g h fg =>
    match fg with
    | Or.inl fg, Or.inl gh => Or.inl <| lt_trans fg gh
    | Or.inl fg, Or.inr gh => Or.inl <| lt_of_lt_of_eq fg gh
    | Or.inr fg, Or.inl gh => Or.inl <| lt_of_eq_of_lt fg gh
    | Or.inr fg, Or.inr gh => Or.inr <| Setoidₓ.trans fg gh
  lt_iff_le_not_le := fun f g =>
    ⟨fun h => ⟨Or.inl h, not_orₓ (mt (lt_trans h) lt_irrefl) (not_lim_zero_of_pos h)⟩, fun ⟨h₁, h₂⟩ =>
      h₁.resolve_right (mt (fun h => Or.inr (Setoidₓ.symm h)) h₂)⟩

theorem le_antisymm {f g : CauSeq α abs} (fg : f ≤ g) (gf : g ≤ f) : f ≈ g :=
  fg.resolve_left (not_lt_of_le gf)

theorem lt_total (f g : CauSeq α abs) : f < g ∨ f ≈ g ∨ g < f :=
  (trichotomy (g - f)).imp_right fun h =>
    h.imp (fun h => Setoidₓ.symm h) fun h => by
      rwa [neg_sub] at h

theorem le_total (f g : CauSeq α abs) : f ≤ g ∨ g ≤ f :=
  (Or.assoc.2 (lt_total f g)).imp_right Or.inl

theorem const_lt {x y : α} : const x < const y ↔ x < y :=
  show Pos _ ↔ _ by
    rw [← const_sub, const_pos, sub_pos]

theorem const_le {x y : α} : const x ≤ const y ↔ x ≤ y := by
  rw [le_iff_lt_or_eqₓ] <;> exact or_congr const_lt const_equiv

theorem le_of_exists {f g : CauSeq α abs} (h : ∃ i, ∀, ∀ j ≥ i, ∀, f j ≤ g j) : f ≤ g :=
  let ⟨i, hi⟩ := h
  (Or.assoc.2 (CauSeq.lt_total f g)).elim id fun hgf =>
    False.elim
      (let ⟨K, hK0, j, hKj⟩ := hgf
      not_lt_of_geₓ (hi (max i j) (le_max_leftₓ _ _)) (sub_pos.1 (lt_of_lt_of_leₓ hK0 (hKj _ (le_max_rightₓ _ _)))))

theorem exists_gt (f : CauSeq α abs) : ∃ a : α, f < const a :=
  let ⟨K, H⟩ := f.Bounded
  ⟨K + 1, 1, zero_lt_one, 0, fun i _ => by
    rw [sub_apply, const_apply, le_sub_iff_add_le', add_le_add_iff_right]
    exact le_of_ltₓ (abs_lt.1 (H _)).2⟩

theorem exists_lt (f : CauSeq α abs) : ∃ a : α, const a < f :=
  let ⟨a, h⟩ := (-f).exists_gt
  ⟨-a,
    show Pos _ by
      rwa [const_neg, sub_neg_eq_add, add_commₓ, ← sub_neg_eq_add]⟩

end Abs

end CauSeq


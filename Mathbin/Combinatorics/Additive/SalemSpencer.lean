/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathbin.Algebra.Hom.Freiman
import Mathbin.Analysis.Asymptotics.Asymptotics
import Mathbin.Analysis.Convex.StrictConvexSpace

/-!
# Salem-Spencer sets and Roth numbers

This file defines Salem-Spencer sets and the Roth number of a set.

A Salem-Spencer set is a set without arithmetic progressions of length `3`. Equivalently, the
average of any two distinct elements is not in the set.

The Roth number of a finset is the size of its biggest Salem-Spencer subset. This is a more general
definition than the one often found in mathematical litterature, where the `n`-th Roth number is
the size of the biggest Salem-Spencer subset of `{0, ..., n - 1}`.

## Main declarations

* `mul_salem_spencer`: Predicate for a set to be multiplicative Salem-Spencer.
* `add_salem_spencer`: Predicate for a set to be additive Salem-Spencer.
* `mul_roth_number`: The multiplicative Roth number of a finset.
* `add_roth_number`: The additive Roth number of a finset.
* `roth_number_nat`: The Roth number of a natural. This corresponds to
  `add_roth_number (finset.range n)`.

## TODO

* Can `add_salem_spencer_iff_eq_right` be made more general?
* Generalize `mul_salem_spencer.image` to Freiman homs

## Tags

Salem-Spencer, Roth, arithmetic progression, average, three-free
-/


open Finset Function Metric Nat

open Pointwise

variable {F α β 𝕜 E : Type _}

section SalemSpencer

open Set

section Monoidₓ

variable [Monoidₓ α] [Monoidₓ β] (s t : Set α)

/-- A multiplicative Salem-Spencer, aka non averaging, set `s` in a monoid is a set such that the
multiplicative average of any two distinct elements is not in the set. -/
@[to_additive
      "A Salem-Spencer, aka non averaging, set `s` in an additive monoid\nis a set such that the average of any two distinct elements is not in the set."]
def MulSalemSpencer : Prop :=
  ∀ ⦃a b c⦄, a ∈ s → b ∈ s → c ∈ s → a * b = c * c → a = b

/-- Whether a given finset is Salem-Spencer is decidable. -/
@[to_additive]
instance {α : Type _} [DecidableEq α] [Monoidₓ α] {s : Finset α} : Decidable (MulSalemSpencer (s : Set α)) :=
  decidableOfIff (∀, ∀ a ∈ s, ∀, ∀, ∀ b ∈ s, ∀, ∀, ∀ c ∈ s, ∀, a * b = c * c → a = b)
    ⟨fun h a b c ha hb hc => h a ha b hb c hc, fun h a ha b hb c hc => h ha hb hc⟩

variable {s t}

@[to_additive]
theorem MulSalemSpencer.mono (h : t ⊆ s) (hs : MulSalemSpencer s) : MulSalemSpencer t := fun a b c ha hb hc =>
  hs (h ha) (h hb) (h hc)

@[simp, to_additive]
theorem mul_salem_spencer_empty : MulSalemSpencer (∅ : Set α) := fun a _ _ ha => ha.elim

@[to_additive]
theorem Set.Subsingleton.mul_salem_spencer (hs : s.Subsingleton) : MulSalemSpencer s := fun a b _ ha hb _ _ => hs ha hb

@[simp, to_additive]
theorem mul_salem_spencer_singleton (a : α) : MulSalemSpencer ({a} : Set α) :=
  subsingleton_singleton.MulSalemSpencer

@[to_additive AddSalemSpencer.prod]
theorem MulSalemSpencer.prod {t : Set β} (hs : MulSalemSpencer s) (ht : MulSalemSpencer t) : MulSalemSpencer (s ×ˢ t) :=
  fun a b c ha hb hc h => Prod.extₓ (hs ha.1 hb.1 hc.1 (Prod.ext_iff.1 h).1) (ht ha.2 hb.2 hc.2 (Prod.ext_iff.1 h).2)

@[to_additive]
theorem mul_salem_spencer_pi {ι : Type _} {α : ι → Type _} [∀ i, Monoidₓ (α i)] {s : ∀ i, Set (α i)}
    (hs : ∀ i, MulSalemSpencer (s i)) : MulSalemSpencer ((Univ : Set ι).pi s) := fun a b c ha hb hc h =>
  funext fun i => hs i (ha i trivialₓ) (hb i trivialₓ) (hc i trivialₓ) <| congr_fun h i

end Monoidₓ

section CommMonoidₓ

variable [CommMonoidₓ α] [CommMonoidₓ β] {s : Set α} {a : α}

@[to_additive]
theorem MulSalemSpencer.of_image [FunLike F α fun _ => β] [FreimanHomClass F s β 2] (f : F) (hf : s.InjOn f)
    (h : MulSalemSpencer (f '' s)) : MulSalemSpencer s := fun a b c ha hb hc habc =>
  hf ha hb <|
    h (mem_image_of_mem _ ha) (mem_image_of_mem _ hb) (mem_image_of_mem _ hc) <|
      map_mul_map_eq_map_mul_map f ha hb hc hc habc

-- TODO: Generalize to Freiman homs
@[to_additive]
theorem MulSalemSpencer.image [MulHomClass F α β] (f : F) (hf : (s * s).InjOn f) (h : MulSalemSpencer s) :
    MulSalemSpencer (f '' s) := by
  rintro _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ habc
  rw
    [h ha hb hc
      (hf (mul_mem_mul ha hb) (mul_mem_mul hc hc) <| by
        rwa [map_mul, map_mul])]

end CommMonoidₓ

section CancelCommMonoid

variable [CancelCommMonoid α] {s : Set α} {a : α}

@[to_additive]
theorem mul_salem_spencer_insert :
    MulSalemSpencer (insert a s) ↔
      MulSalemSpencer s ∧
        (∀ ⦃b c⦄, b ∈ s → c ∈ s → a * b = c * c → a = b) ∧ ∀ ⦃b c⦄, b ∈ s → c ∈ s → b * c = a * a → b = c :=
  by
  refine'
    ⟨fun hs =>
      ⟨hs.mono (subset_insert _ _), fun b c hb hc => hs (Or.inl rfl) (Or.inr hb) (Or.inr hc), fun b c hb hc =>
        hs (Or.inr hb) (Or.inr hc) (Or.inl rfl)⟩,
      _⟩
  rintro ⟨hs, ha, ha'⟩ b c d hb hc hd h
  rw [mem_insert_iff] at hb hc hd
  obtain rfl | hb := hb <;> obtain rfl | hc := hc
  · rfl
    
  all_goals
    obtain rfl | hd := hd
  · exact (mul_left_cancelₓ h).symm
    
  · exact ha hc hd h
    
  · exact mul_right_cancelₓ h
    
  · exact (ha hb hd <| (mul_comm _ _).trans h).symm
    
  · exact ha' hb hc h
    
  · exact hs hb hc hd h
    

@[simp, to_additive]
theorem mul_salem_spencer_pair (a b : α) : MulSalemSpencer ({a, b} : Set α) := by
  rw [mul_salem_spencer_insert]
  refine' ⟨mul_salem_spencer_singleton _, _, _⟩
  · rintro c d (rfl : c = b) (rfl : d = c)
    exact mul_right_cancelₓ
    
  · rintro c d (rfl : c = b) (rfl : d = c) _
    rfl
    

@[to_additive]
theorem MulSalemSpencer.mul_left (hs : MulSalemSpencer s) : MulSalemSpencer ((· * ·) a '' s) := by
  rintro _ _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h
  rw [mul_mul_mul_commₓ, mul_mul_mul_commₓ a d] at h
  rw [hs hb hc hd (mul_left_cancelₓ h)]

@[to_additive]
theorem MulSalemSpencer.mul_right (hs : MulSalemSpencer s) : MulSalemSpencer ((· * a) '' s) := by
  rintro _ _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h
  rw [mul_mul_mul_commₓ, mul_mul_mul_commₓ d] at h
  rw [hs hb hc hd (mul_right_cancelₓ h)]

@[to_additive]
theorem mul_salem_spencer_mul_left_iff : MulSalemSpencer ((· * ·) a '' s) ↔ MulSalemSpencer s :=
  ⟨fun hs b c d hb hc hd h =>
    mul_left_cancelₓ
      (hs (mem_image_of_mem _ hb) (mem_image_of_mem _ hc) (mem_image_of_mem _ hd) <| by
        rw [mul_mul_mul_commₓ, h, mul_mul_mul_commₓ]),
    MulSalemSpencer.mul_left⟩

@[to_additive]
theorem mul_salem_spencer_mul_right_iff : MulSalemSpencer ((· * a) '' s) ↔ MulSalemSpencer s :=
  ⟨fun hs b c d hb hc hd h =>
    mul_right_cancelₓ
      (hs (Set.mem_image_of_mem _ hb) (Set.mem_image_of_mem _ hc) (Set.mem_image_of_mem _ hd) <| by
        rw [mul_mul_mul_commₓ, h, mul_mul_mul_commₓ]),
    MulSalemSpencer.mul_right⟩

end CancelCommMonoid

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] {s : Set α} {a : α}

@[to_additive]
theorem mul_salem_spencer_insert_of_lt (hs : ∀, ∀ i ∈ s, ∀, i < a) :
    MulSalemSpencer (insert a s) ↔ MulSalemSpencer s ∧ ∀ ⦃b c⦄, b ∈ s → c ∈ s → a * b = c * c → a = b := by
  refine' mul_salem_spencer_insert.trans _
  rw [← and_assoc]
  exact and_iff_left fun b c hb hc h => ((mul_lt_mul_of_lt_of_lt (hs _ hb) (hs _ hc)).Ne h).elim

end OrderedCancelCommMonoid

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α] [NoZeroDivisors α] {s : Set α} {a : α}

theorem MulSalemSpencer.mul_left₀ (hs : MulSalemSpencer s) (ha : a ≠ 0) : MulSalemSpencer ((· * ·) a '' s) := by
  rintro _ _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h
  rw [mul_mul_mul_commₓ, mul_mul_mul_commₓ a d] at h
  rw [hs hb hc hd (mul_left_cancel₀ (mul_ne_zero ha ha) h)]

theorem MulSalemSpencer.mul_right₀ (hs : MulSalemSpencer s) (ha : a ≠ 0) : MulSalemSpencer ((· * a) '' s) := by
  rintro _ _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩ h
  rw [mul_mul_mul_commₓ, mul_mul_mul_commₓ d] at h
  rw [hs hb hc hd (mul_right_cancel₀ (mul_ne_zero ha ha) h)]

theorem mul_salem_spencer_mul_left_iff₀ (ha : a ≠ 0) : MulSalemSpencer ((· * ·) a '' s) ↔ MulSalemSpencer s :=
  ⟨fun hs b c d hb hc hd h =>
    mul_left_cancel₀ ha
      (hs (Set.mem_image_of_mem _ hb) (Set.mem_image_of_mem _ hc) (Set.mem_image_of_mem _ hd) <| by
        rw [mul_mul_mul_commₓ, h, mul_mul_mul_commₓ]),
    fun hs => hs.mulLeft₀ ha⟩

theorem mul_salem_spencer_mul_right_iff₀ (ha : a ≠ 0) : MulSalemSpencer ((· * a) '' s) ↔ MulSalemSpencer s :=
  ⟨fun hs b c d hb hc hd h =>
    mul_right_cancel₀ ha
      (hs (Set.mem_image_of_mem _ hb) (Set.mem_image_of_mem _ hc) (Set.mem_image_of_mem _ hd) <| by
        rw [mul_mul_mul_commₓ, h, mul_mul_mul_commₓ]),
    fun hs => hs.mulRight₀ ha⟩

end CancelCommMonoidWithZero

section Nat

theorem add_salem_spencer_iff_eq_right {s : Set ℕ} :
    AddSalemSpencer s ↔ ∀ ⦃a b c⦄, a ∈ s → b ∈ s → c ∈ s → a + b = c + c → a = c := by
  refine' forall₄_congrₓ fun a b c _ => forall₃_congrₓ fun _ _ habc => ⟨_, _⟩
  · rintro rfl
    simp_rw [← two_mul] at habc
    exact mul_left_cancel₀ two_ne_zero habc
    
  · rintro rfl
    exact (add_left_cancelₓ habc).symm
    

end Nat

/-- The frontier of a closed strictly convex set only contains trivial arithmetic progressions.
The idea is that an arithmetic progression is contained on a line and the frontier of a strictly
convex set does not contain lines. -/
theorem add_salem_spencer_frontier [LinearOrderedField 𝕜] [TopologicalSpace E] [AddCommMonoidₓ E] [Module 𝕜 E]
    {s : Set E} (hs₀ : IsClosed s) (hs₁ : StrictConvex 𝕜 s) : AddSalemSpencer (Frontier s) := by
  intro a b c ha hb hc habc
  obtain rfl : (1 / 2 : 𝕜) • a + (1 / 2 : 𝕜) • b = c := by
    rwa [← smul_add, one_div,
      inv_smul_eq_iff₀
        (show (2 : 𝕜) ≠ 0 by
          norm_num),
      two_smul]
  exact hs₁.eq (hs₀.frontier_subset ha) (hs₀.frontier_subset hb) one_half_pos one_half_pos (add_halves _) hc.2

theorem add_salem_spencer_sphere [NormedGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E] (x : E) (r : ℝ) :
    AddSalemSpencer (Sphere x r) := by
  obtain rfl | hr := eq_or_ne r 0
  · rw [sphere_zero]
    exact add_salem_spencer_singleton _
    
  · convert add_salem_spencer_frontier is_closed_ball (strict_convex_closed_ball ℝ x r)
    exact (frontier_closed_ball _ hr).symm
    

end SalemSpencer

open Finset

section RothNumber

variable [DecidableEq α]

section Monoidₓ

variable [Monoidₓ α] [DecidableEq β] [Monoidₓ β] (s t : Finset α)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
/-- The multiplicative Roth number of a finset is the cardinality of its biggest multiplicative
Salem-Spencer subset. -/
@[to_additive
      "The additive Roth number of a finset is the cardinality of its biggest additive\nSalem-Spencer subset. The usual Roth number corresponds to `add_roth_number (finset.range n)`, see\n`roth_number_nat`. "]
def mulRothNumber : Finset α →o ℕ :=
  ⟨fun s => Nat.findGreatest (fun m => ∃ (t : _)(_ : t ⊆ s), t.card = m ∧ MulSalemSpencer (t : Set α)) s.card, by
    rintro t u htu
    refine' Nat.find_greatest_mono (fun m => _) (card_le_of_subset htu)
    rintro ⟨v, hvt, hv⟩
    exact ⟨v, hvt.trans htu, hv⟩⟩

@[to_additive]
theorem mul_roth_number_le : mulRothNumber s ≤ s.card := by
  convert Nat.find_greatest_le s.card

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
@[to_additive]
theorem mul_roth_number_spec : ∃ (t : _)(_ : t ⊆ s), t.card = mulRothNumber s ∧ MulSalemSpencer (t : Set α) :=
  @Nat.find_greatest_spec _ (fun m => ∃ (t : _)(_ : t ⊆ s), t.card = m ∧ MulSalemSpencer (t : Set α)) _ _
    (Nat.zero_leₓ _) ⟨∅, empty_subset _, card_empty, mul_salem_spencer_empty⟩

variable {s t} {n : ℕ}

@[to_additive]
theorem MulSalemSpencer.le_mul_roth_number (hs : MulSalemSpencer (s : Set α)) (h : s ⊆ t) : s.card ≤ mulRothNumber t :=
  le_find_greatest (card_le_of_subset h) ⟨s, h, rfl, hs⟩

@[to_additive]
theorem MulSalemSpencer.roth_number_eq (hs : MulSalemSpencer (s : Set α)) : mulRothNumber s = s.card :=
  (mul_roth_number_le _).antisymm <| hs.le_mul_roth_number <| Subset.refl _

@[simp, to_additive]
theorem mul_roth_number_empty : mulRothNumber (∅ : Finset α) = 0 :=
  Nat.eq_zero_of_le_zeroₓ <| (mul_roth_number_le _).trans card_empty.le

@[simp, to_additive]
theorem mul_roth_number_singleton (a : α) : mulRothNumber ({a} : Finset α) = 1 := by
  convert MulSalemSpencer.roth_number_eq _
  rw [coe_singleton]
  exact mul_salem_spencer_singleton a

@[to_additive]
theorem mul_roth_number_union_le (s t : Finset α) : mulRothNumber (s ∪ t) ≤ mulRothNumber s + mulRothNumber t :=
  let ⟨u, hus, hcard, hu⟩ := mul_roth_number_spec (s ∪ t)
  calc
    mulRothNumber (s ∪ t) = u.card := hcard.symm
    _ = (u ∩ s ∪ u ∩ t).card := by
      rw [← inter_distrib_left, (inter_eq_left_iff_subset _ _).2 hus]
    _ ≤ (u ∩ s).card + (u ∩ t).card := card_union_le _ _
    _ ≤ mulRothNumber s + mulRothNumber t :=
      add_le_add ((hu.mono <| inter_subset_left _ _).le_mul_roth_number <| inter_subset_right _ _)
        ((hu.mono <| inter_subset_left _ _).le_mul_roth_number <| inter_subset_right _ _)
    

@[to_additive]
theorem le_mul_roth_number_product (s : Finset α) (t : Finset β) :
    mulRothNumber s * mulRothNumber t ≤ mulRothNumber (s.product t) := by
  obtain ⟨u, hus, hucard, hu⟩ := mul_roth_number_spec s
  obtain ⟨v, hvt, hvcard, hv⟩ := mul_roth_number_spec t
  rw [← hucard, ← hvcard, ← card_product]
  refine' MulSalemSpencer.le_mul_roth_number _ (product_subset_product hus hvt)
  rw [coe_product]
  exact hu.prod hv

@[to_additive]
theorem mul_roth_number_lt_of_forall_not_mul_salem_spencer
    (h : ∀, ∀ t ∈ powersetLen n s, ∀, ¬MulSalemSpencer ((t : Finset α) : Set α)) : mulRothNumber s < n := by
  obtain ⟨t, hts, hcard, ht⟩ := mul_roth_number_spec s
  rw [← hcard, ← not_leₓ]
  intro hn
  obtain ⟨u, hut, rfl⟩ := exists_smaller_set t n hn
  exact h _ (mem_powerset_len.2 ⟨hut.trans hts, rfl⟩) (ht.mono hut)

end Monoidₓ

section CancelCommMonoid

variable [CancelCommMonoid α] (s : Finset α) (a : α)

@[simp, to_additive]
theorem mul_roth_number_map_mul_left : mulRothNumber (s.map <| mulLeftEmbedding a) = mulRothNumber s := by
  refine' le_antisymmₓ _ _
  · obtain ⟨u, hus, hcard, hu⟩ := mul_roth_number_spec (s.map <| mulLeftEmbedding a)
    rw [subset_map_iff] at hus
    obtain ⟨u, hus, rfl⟩ := hus
    rw [coe_map] at hu
    rw [← hcard, card_map]
    exact (mul_salem_spencer_mul_left_iff.1 hu).le_mul_roth_number hus
    
  · obtain ⟨u, hus, hcard, hu⟩ := mul_roth_number_spec s
    have h : MulSalemSpencer (u.map <| mulLeftEmbedding a : Set α) := by
      rw [coe_map]
      exact hu.mul_left
    convert h.le_mul_roth_number (map_subset_map.2 hus)
    rw [card_map, hcard]
    

@[simp, to_additive]
theorem mul_roth_number_map_mul_right : mulRothNumber (s.map <| mulRightEmbedding a) = mulRothNumber s := by
  rw [← mul_left_embedding_eq_mul_right_embedding, mul_roth_number_map_mul_left s a]

end CancelCommMonoid

end RothNumber

section rothNumberNat

variable {s : Finset ℕ} {k n : ℕ}

/-- The Roth number of a natural `N` is the largest integer `m` for which there is a subset of
`range N` of size `m` with no arithmetic progression of length 3.
Trivially, `roth_number_nat N ≤ N`, but Roth's theorem (proved in 1953) shows that
`roth_number_nat N = o(N)` and the construction by Behrend gives a lower bound of the form
`N * exp(-C sqrt(log(N))) ≤ roth_number_nat N`.
A significant refinement of Roth's theorem by Bloom and Sisask announced in 2020 gives
`roth_number_nat N = O(N / (log N)^(1+c))` for an absolute constant `c`. -/
def rothNumberNat : ℕ →o ℕ :=
  ⟨fun n => addRothNumber (range n), addRothNumber.mono.comp range_mono⟩

theorem roth_number_nat_def (n : ℕ) : rothNumberNat n = addRothNumber (range n) :=
  rfl

theorem roth_number_nat_le (N : ℕ) : rothNumberNat N ≤ N :=
  (add_roth_number_le _).trans (card_range _).le

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » range n)
theorem roth_number_nat_spec (n : ℕ) :
    ∃ (t : _)(_ : t ⊆ range n), t.card = rothNumberNat n ∧ AddSalemSpencer (t : Set ℕ) :=
  add_roth_number_spec _

/-- A verbose specialization of `add_salem_spencer.le_add_roth_number`, sometimes convenient in
practice. -/
theorem AddSalemSpencer.le_roth_number_nat (s : Finset ℕ) (hs : AddSalemSpencer (s : Set ℕ))
    (hsn : ∀, ∀ x ∈ s, ∀, x < n) (hsk : s.card = k) : k ≤ rothNumberNat n :=
  hsk.Ge.trans <| hs.le_add_roth_number fun x hx => mem_range.2 <| hsn x hx

/-- The Roth number is a subadditive function. Note that by Fekete's lemma this shows that
the limit `roth_number_nat N / N` exists, but Roth's theorem gives the stronger result that this
limit is actually `0`. -/
theorem roth_number_nat_add_le (M N : ℕ) : rothNumberNat (M + N) ≤ rothNumberNat M + rothNumberNat N := by
  simp_rw [roth_number_nat_def]
  rw [range_add_eq_union, ← add_roth_number_map_add_left (range N) M]
  exact add_roth_number_union_le _ _

@[simp]
theorem roth_number_nat_zero : rothNumberNat 0 = 0 :=
  rfl

theorem add_roth_number_Ico (a b : ℕ) : addRothNumber (ico a b) = rothNumberNat (b - a) := by
  obtain h | h := le_totalₓ b a
  · rw [tsub_eq_zero_of_le h, Ico_eq_empty_of_le h, roth_number_nat_zero, add_roth_number_empty]
    
  convert add_roth_number_map_add_left _ a
  rw [range_eq_Ico, map_eq_image]
  convert (image_add_left_Ico 0 (b - a) _).symm
  exact (add_tsub_cancel_of_le h).symm

open Asymptotics Filter

theorem roth_number_nat_is_O_with_id : IsOWith 1 atTop (fun N => (rothNumberNat N : ℝ)) fun N => (N : ℝ) :=
  is_O_with_of_le _ <| by
    simpa only [← Real.norm_coe_nat, ← Nat.cast_le] using roth_number_nat_le

/-- The Roth number has the trivial bound `roth_number_nat N = O(N)`. -/
theorem roth_number_nat_is_O_id : (fun N => (rothNumberNat N : ℝ)) =O[at_top] fun N => (N : ℝ) :=
  roth_number_nat_is_O_with_id.IsO

end rothNumberNat


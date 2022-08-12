/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import Mathbin.GroupTheory.Submonoid.Operations
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.FreeMonoid
import Mathbin.Data.Finset.NoncommProd

/-!
# Submonoids: membership criteria

In this file we prove various facts about membership in a submonoid:

* `list_prod_mem`, `multiset_prod_mem`, `prod_mem`: if each element of a collection belongs
  to a multiplicative submonoid, then so does their product;
* `list_sum_mem`, `multiset_sum_mem`, `sum_mem`: if each element of a collection belongs
  to an additive submonoid, then so does their sum;
* `pow_mem`, `nsmul_mem`: if `x ∈ S` where `S` is a multiplicative (resp., additive) submonoid and
  `n` is a natural number, then `x^n` (resp., `n • x`) belongs to `S`;
* `mem_supr_of_directed`, `coe_supr_of_directed`, `mem_Sup_of_directed_on`,
  `coe_Sup_of_directed_on`: the supremum of a directed collection of submonoid is their union.
* `sup_eq_range`, `mem_sup`: supremum of two submonoids `S`, `T` of a commutative monoid is the set
  of products;
* `closure_singleton_eq`, `mem_closure_singleton`, `mem_closure_pair`: the multiplicative (resp.,
  additive) closure of `{x}` consists of powers (resp., natural multiples) of `x`, and a similar
  result holds for the closure of `{x, y}`.

## Tags
submonoid, submonoids
-/


open BigOperators

variable {M A B : Type _}

section Assoc

variable [Monoidₓ M] [SetLike B M] [SubmonoidClass B M] {S : B}

namespace SubmonoidClass

@[simp, norm_cast, to_additive]
theorem coe_list_prod (l : List S) : (l.Prod : M) = (l.map coe).Prod :=
  (SubmonoidClass.subtype S : _ →* M).map_list_prod l

@[simp, norm_cast, to_additive]
theorem coe_multiset_prod {M} [CommMonoidₓ M] [SetLike B M] [SubmonoidClass B M] (m : Multiset S) :
    (m.Prod : M) = (m.map coe).Prod :=
  (SubmonoidClass.subtype S : _ →* M).map_multiset_prod m

@[simp, norm_cast, to_additive]
theorem coe_finset_prod {ι M} [CommMonoidₓ M] [SetLike B M] [SubmonoidClass B M] (f : ι → S) (s : Finset ι) :
    ↑(∏ i in s, f i) = (∏ i in s, f i : M) :=
  (SubmonoidClass.subtype S : _ →* M).map_prod f s

end SubmonoidClass

open SubmonoidClass

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `add_submonoid` is in the `add_submonoid`."]
theorem list_prod_mem {l : List M} (hl : ∀, ∀ x ∈ l, ∀, x ∈ S) : l.Prod ∈ S := by
  lift l to List S using hl
  rw [← coe_list_prod]
  exact l.prod.coe_prop

/-- Product of a multiset of elements in a submonoid of a `comm_monoid` is in the submonoid. -/
@[to_additive "Sum of a multiset of elements in an `add_submonoid` of an `add_comm_monoid` is\nin the `add_submonoid`."]
theorem multiset_prod_mem {M} [CommMonoidₓ M] [SetLike B M] [SubmonoidClass B M] (m : Multiset M)
    (hm : ∀, ∀ a ∈ m, ∀, a ∈ S) : m.Prod ∈ S := by
  lift m to Multiset S using hm
  rw [← coe_multiset_prod]
  exact m.prod.coe_prop

/-- Product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is in the
    submonoid. -/
@[to_additive
      "Sum of elements in an `add_submonoid` of an `add_comm_monoid` indexed by a `finset`\nis in the `add_submonoid`."]
theorem prod_mem {M : Type _} [CommMonoidₓ M] [SetLike B M] [SubmonoidClass B M] {ι : Type _} {t : Finset ι} {f : ι → M}
    (h : ∀, ∀ c ∈ t, ∀, f c ∈ S) : (∏ c in t, f c) ∈ S :=
  (multiset_prod_mem (t.1.map f)) fun x hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi

namespace Submonoid

variable (s : Submonoid M)

@[simp, norm_cast, to_additive]
theorem coe_list_prod (l : List s) : (l.Prod : M) = (l.map coe).Prod :=
  s.Subtype.map_list_prod l

@[simp, norm_cast, to_additive]
theorem coe_multiset_prod {M} [CommMonoidₓ M] (S : Submonoid M) (m : Multiset S) : (m.Prod : M) = (m.map coe).Prod :=
  S.Subtype.map_multiset_prod m

@[simp, norm_cast, to_additive]
theorem coe_finset_prod {ι M} [CommMonoidₓ M] (S : Submonoid M) (f : ι → S) (s : Finset ι) :
    ↑(∏ i in s, f i) = (∏ i in s, f i : M) :=
  S.Subtype.map_prod f s

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `add_submonoid` is in the `add_submonoid`."]
theorem list_prod_mem {l : List M} (hl : ∀, ∀ x ∈ l, ∀, x ∈ s) : l.Prod ∈ s := by
  lift l to List s using hl
  rw [← coe_list_prod]
  exact l.prod.coe_prop

/-- Product of a multiset of elements in a submonoid of a `comm_monoid` is in the submonoid. -/
@[to_additive "Sum of a multiset of elements in an `add_submonoid` of an `add_comm_monoid` is\nin the `add_submonoid`."]
theorem multiset_prod_mem {M} [CommMonoidₓ M] (S : Submonoid M) (m : Multiset M) (hm : ∀, ∀ a ∈ m, ∀, a ∈ S) :
    m.Prod ∈ S := by
  lift m to Multiset S using hm
  rw [← coe_multiset_prod]
  exact m.prod.coe_prop

@[to_additive]
theorem multiset_noncomm_prod_mem (S : Submonoid M) (m : Multiset M) (comm : ∀, ∀ x ∈ m, ∀, ∀ y ∈ m, ∀, Commute x y)
    (h : ∀, ∀ x ∈ m, ∀, x ∈ S) : m.noncommProd comm ∈ S := by
  induction' m using Quotientₓ.induction_on with l
  simp only [← Multiset.quot_mk_to_coe, ← Multiset.noncomm_prod_coe]
  exact Submonoid.list_prod_mem _ h

/-- Product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is in the
    submonoid. -/
@[to_additive
      "Sum of elements in an `add_submonoid` of an `add_comm_monoid` indexed by a `finset`\nis in the `add_submonoid`."]
theorem prod_mem {M : Type _} [CommMonoidₓ M] (S : Submonoid M) {ι : Type _} {t : Finset ι} {f : ι → M}
    (h : ∀, ∀ c ∈ t, ∀, f c ∈ S) : (∏ c in t, f c) ∈ S :=
  (S.multiset_prod_mem (t.1.map f)) fun x hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi

@[to_additive]
theorem noncomm_prod_mem (S : Submonoid M) {ι : Type _} (t : Finset ι) (f : ι → M)
    (comm : ∀, ∀ x ∈ t, ∀, ∀ y ∈ t, ∀, Commute (f x) (f y)) (h : ∀, ∀ c ∈ t, ∀, f c ∈ S) : t.noncommProd f comm ∈ S :=
  by
  apply multiset_noncomm_prod_mem
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx

end Submonoid

end Assoc

section NonAssoc

variable [MulOneClassₓ M]

open Set

namespace Submonoid

-- TODO: this section can be generalized to `[submonoid_class B M] [complete_lattice B]`
-- such that `complete_lattice.le` coincides with `set_like.le`
@[to_additive]
theorem mem_supr_of_directed {ι} [hι : Nonempty ι] {S : ι → Submonoid M} (hS : Directed (· ≤ ·) S) {x : M} :
    (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine' ⟨_, fun ⟨i, hi⟩ => (SetLike.le_def.1 <| le_supr S i) hi⟩
  suffices x ∈ closure (⋃ i, (S i : Set M)) → ∃ i, x ∈ S i by
    simpa only [← closure_Union, ← closure_eq (S _)] using this
  refine' fun hx => closure_induction hx (fun _ => mem_Union.1) _ _
  · exact hι.elim fun i => ⟨i, (S i).one_mem⟩
    
  · rintro x y ⟨i, hi⟩ ⟨j, hj⟩
    rcases hS i j with ⟨k, hki, hkj⟩
    exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩
    

@[to_additive]
theorem coe_supr_of_directed {ι} [Nonempty ι] {S : ι → Submonoid M} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Submonoid M) : Set M) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by
    simp [← mem_supr_of_directed hS]

@[to_additive]
theorem mem_Sup_of_directed_on {S : Set (Submonoid M)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S) {x : M} :
    x ∈ sup S ↔ ∃ s ∈ S, x ∈ s := by
  have : Nonempty S := Sne.to_subtype
  simp only [← Sup_eq_supr', ← mem_supr_of_directed hS.directed_coe, ← SetCoe.exists, ← Subtype.coe_mk]

@[to_additive]
theorem coe_Sup_of_directed_on {S : Set (Submonoid M)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S) :
    (↑(sup S) : Set M) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by
    simp [← mem_Sup_of_directed_on Sne hS]

@[to_additive]
theorem mem_sup_left {S T : Submonoid M} : ∀ {x : M}, x ∈ S → x ∈ S⊔T :=
  show S ≤ S⊔T from le_sup_left

@[to_additive]
theorem mem_sup_right {S T : Submonoid M} : ∀ {x : M}, x ∈ T → x ∈ S⊔T :=
  show T ≤ S⊔T from le_sup_right

@[to_additive]
theorem mul_mem_sup {S T : Submonoid M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S⊔T :=
  (S⊔T).mul_mem (mem_sup_left hx) (mem_sup_right hy)

@[to_additive]
theorem mem_supr_of_mem {ι : Sort _} {S : ι → Submonoid M} (i : ι) : ∀ {x : M}, x ∈ S i → x ∈ supr S :=
  show S i ≤ supr S from le_supr _ _

@[to_additive]
theorem mem_Sup_of_mem {S : Set (Submonoid M)} {s : Submonoid M} (hs : s ∈ S) : ∀ {x : M}, x ∈ s → x ∈ sup S :=
  show s ≤ sup S from le_Sup hs

/-- An induction principle for elements of `⨆ i, S i`.
If `C` holds for `1` and all elements of `S i` for all `i`, and is preserved under multiplication,
then it holds for all elements of the supremum of `S`. -/
@[elab_as_eliminator,
  to_additive
      " An induction principle for elements of `⨆ i, S i`.\nIf `C` holds for `0` and all elements of `S i` for all `i`, and is preserved under addition,\nthen it holds for all elements of the supremum of `S`. "]
theorem supr_induction {ι : Sort _} (S : ι → Submonoid M) {C : M → Prop} {x : M} (hx : x ∈ ⨆ i, S i)
    (hp : ∀ (i), ∀ x ∈ S i, ∀, C x) (h1 : C 1) (hmul : ∀ x y, C x → C y → C (x * y)) : C x := by
  rw [supr_eq_closure] at hx
  refine' closure_induction hx (fun x hx => _) h1 hmul
  obtain ⟨i, hi⟩ := set.mem_Union.mp hx
  exact hp _ _ hi

/-- A dependent version of `submonoid.supr_induction`. -/
@[elab_as_eliminator, to_additive "A dependent version of `add_submonoid.supr_induction`. "]
theorem supr_induction' {ι : Sort _} (S : ι → Submonoid M) {C : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    (hp : ∀ (i), ∀ x ∈ S i, ∀, C x (mem_supr_of_mem i ‹_›)) (h1 : C 1 (one_mem _))
    (hmul : ∀ x y hx hy, C x hx → C y hy → C (x * y) (mul_mem ‹_› ‹_›)) {x : M} (hx : x ∈ ⨆ i, S i) : C x hx := by
  refine' Exists.elim _ fun (hx : x ∈ ⨆ i, S i) (hc : C x hx) => hc
  refine' supr_induction S hx (fun i x hx => _) _ fun x y => _
  · exact ⟨_, hp _ _ hx⟩
    
  · exact ⟨_, h1⟩
    
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    refine' ⟨_, hmul _ _ _ _ Cx Cy⟩
    

end Submonoid

end NonAssoc

namespace FreeMonoid

variable {α : Type _}

open Submonoid

@[to_additive]
theorem closure_range_of : closure (Set.Range <| @of α) = ⊤ :=
  eq_top_iff.2 fun x hx =>
    (FreeMonoid.recOn x (one_mem _)) fun x xs hxs => mul_mem (subset_closure <| Set.mem_range_self _) hxs

end FreeMonoid

namespace Submonoid

variable [Monoidₓ M]

open MonoidHom

theorem closure_singleton_eq (x : M) : closure ({x} : Set M) = (powersHom M x).mrange :=
  (closure_eq_of_le (Set.singleton_subset_iff.2 ⟨Multiplicative.ofAdd 1, pow_oneₓ x⟩)) fun x ⟨n, hn⟩ =>
    hn ▸ pow_mem (subset_closure <| Set.mem_singleton _) _

/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
theorem mem_closure_singleton {x y : M} : y ∈ closure ({x} : Set M) ↔ ∃ n : ℕ, x ^ n = y := by
  rw [closure_singleton_eq, mem_mrange] <;> rfl

theorem mem_closure_singleton_self {y : M} : y ∈ closure ({y} : Set M) :=
  mem_closure_singleton.2 ⟨1, pow_oneₓ y⟩

theorem closure_singleton_one : closure ({1} : Set M) = ⊥ := by
  simp [← eq_bot_iff_forall, ← mem_closure_singleton]

@[to_additive]
theorem closure_eq_mrange (s : Set M) : closure s = (FreeMonoid.lift (coe : s → M)).mrange := by
  rw [mrange_eq_map, ← FreeMonoid.closure_range_of, map_mclosure, ← Set.range_comp, FreeMonoid.lift_comp_of,
    Subtype.range_coe]

@[to_additive]
theorem closure_eq_image_prod (s : Set M) : (closure s : Set M) = List.prod '' { l : List M | ∀, ∀ x ∈ l, ∀, x ∈ s } :=
  by
  rw [closure_eq_mrange, coe_mrange, ← List.range_map_coe, ← Set.range_comp]
  rfl

@[to_additive]
theorem exists_list_of_mem_closure {s : Set M} {x : M} (hx : x ∈ closure s) :
    ∃ (l : List M)(hl : ∀, ∀ y ∈ l, ∀, y ∈ s), l.Prod = x := by
  rwa [← SetLike.mem_coe, closure_eq_image_prod, Set.mem_image_iff_bex] at hx

@[to_additive]
theorem exists_multiset_of_mem_closure {M : Type _} [CommMonoidₓ M] {s : Set M} {x : M} (hx : x ∈ closure s) :
    ∃ (l : Multiset M)(hl : ∀, ∀ y ∈ l, ∀, y ∈ s), l.Prod = x := by
  obtain ⟨l, h1, h2⟩ := exists_list_of_mem_closure hx
  exact ⟨l, h1, (Multiset.coe_prod l).trans h2⟩

@[to_additive]
theorem closure_induction_left {s : Set M} {p : M → Prop} {x : M} (h : x ∈ closure s) (H1 : p 1)
    (Hmul : ∀, ∀ x ∈ s, ∀ (y), p y → p (x * y)) : p x := by
  rw [closure_eq_mrange] at h
  obtain ⟨l, rfl⟩ := h
  induction' l using FreeMonoid.recOn with x y ih
  · exact H1
    
  · simpa only [← map_mul, ← FreeMonoid.lift_eval_of] using Hmul _ x.prop _ ih
    

@[to_additive]
theorem closure_induction_right {s : Set M} {p : M → Prop} {x : M} (h : x ∈ closure s) (H1 : p 1)
    (Hmul : ∀ (x), ∀ y ∈ s, ∀, p x → p (x * y)) : p x :=
  @closure_induction_left _ _ (MulOpposite.unop ⁻¹' s) (p ∘ MulOpposite.unop) (MulOpposite.op x)
    (closure_induction h (fun x hx => subset_closure hx) (one_mem _) fun x y hx hy => mul_mem hy hx) H1 fun x hx y =>
    Hmul _ _ hx

/-- The submonoid generated by an element. -/
def powers (n : M) : Submonoid M :=
  Submonoid.copy (powersHom M n).mrange (Set.Range ((· ^ ·) n : ℕ → M)) <|
    Set.ext fun n =>
      exists_congr fun i => by
        simp <;> rfl

@[simp]
theorem mem_powers (n : M) : n ∈ powers n :=
  ⟨1, pow_oneₓ _⟩

theorem mem_powers_iff (x z : M) : x ∈ powers z ↔ ∃ n : ℕ, z ^ n = x :=
  Iff.rfl

theorem powers_eq_closure (n : M) : powers n = closure {n} := by
  ext
  exact mem_closure_singleton.symm

theorem powers_subset {n : M} {P : Submonoid M} (h : n ∈ P) : powers n ≤ P := fun x hx =>
  match x, hx with
  | _, ⟨i, rfl⟩ => pow_mem h i

/-- Exponentiation map from natural numbers to powers. -/
@[simps]
def pow (n : M) (m : ℕ) : powers n :=
  (powersHom M n).mrangeRestrict (Multiplicative.ofAdd m)

theorem pow_apply (n : M) (m : ℕ) : Submonoid.pow n m = ⟨n ^ m, m, rfl⟩ :=
  rfl

/-- Logarithms from powers to natural numbers. -/
def log [DecidableEq M] {n : M} (p : powers n) : ℕ :=
  Nat.findₓ <| (mem_powers_iff p.val n).mp p.Prop

@[simp]
theorem pow_log_eq_self [DecidableEq M] {n : M} (p : powers n) : pow n (log p) = p :=
  Subtype.ext <| Nat.find_specₓ p.Prop

theorem pow_right_injective_iff_pow_injective {n : M} :
    (Function.Injective fun m : ℕ => n ^ m) ↔ Function.Injective (pow n) :=
  Subtype.coe_injective.of_comp_iff (pow n)

@[simp]
theorem log_pow_eq_self [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m) (m : ℕ) :
    log (pow n m) = m :=
  pow_right_injective_iff_pow_injective.mp h <| pow_log_eq_self _

/-- The exponentiation map is an isomorphism from the additive monoid on natural numbers to powers
when it is injective. The inverse is given by the logarithms. -/
@[simps]
def powLogEquiv [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m) : Multiplicative ℕ ≃* powers n where
  toFun := fun m => pow n m.toAdd
  invFun := fun m => Multiplicative.ofAdd (log m)
  left_inv := log_pow_eq_self h
  right_inv := pow_log_eq_self
  map_mul' := fun _ _ => by
    simp only [← pow, ← map_mul, ← of_add_add, ← to_add_mul]

theorem log_mul [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m) (x y : powers (n : M)) :
    log (x * y) = log x + log y :=
  (powLogEquiv h).symm.map_mul x y

theorem log_pow_int_eq_self {x : ℤ} (h : 1 < x.natAbs) (m : ℕ) : log (pow x m) = m :=
  (powLogEquiv (Int.pow_right_injective h)).symm_apply_apply _

@[simp]
theorem map_powers {N : Type _} {F : Type _} [Monoidₓ N] [MonoidHomClass F M N] (f : F) (m : M) :
    (powers m).map f = powers (f m) := by
  simp only [← powers_eq_closure, ← map_mclosure f, ← Set.image_singleton]

/-- If all the elements of a set `s` commute, then `closure s` is a commutative monoid. -/
@[to_additive "If all the elements of a set `s` commute, then `closure s` forms an additive\ncommutative monoid."]
def closureCommMonoidOfComm {s : Set M} (hcomm : ∀, ∀ a ∈ s, ∀, ∀ b ∈ s, ∀, a * b = b * a) : CommMonoidₓ (closure s) :=
  { (closure s).toMonoid with
    mul_comm := fun x y => by
      ext
      simp only [← Submonoid.coe_mul]
      exact
        closure_induction₂ x.prop y.prop hcomm
          (fun x => by
            simp only [← mul_oneₓ, ← one_mulₓ])
          (fun x => by
            simp only [← mul_oneₓ, ← one_mulₓ])
          (fun x y z h₁ h₂ => by
            rw [mul_assoc, h₂, ← mul_assoc, h₁, mul_assoc])
          fun x y z h₁ h₂ => by
          rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc] }

end Submonoid

namespace Submonoid

variable {N : Type _} [CommMonoidₓ N]

open MonoidHom

@[to_additive]
theorem sup_eq_range (s t : Submonoid N) : s⊔t = (s.Subtype.coprod t.Subtype).mrange := by
  rw [mrange_eq_map, ← mrange_inl_sup_mrange_inr, map_sup, map_mrange, coprod_comp_inl, map_mrange, coprod_comp_inr,
    range_subtype, range_subtype]

@[to_additive]
theorem mem_sup {s t : Submonoid N} {x : N} : x ∈ s⊔t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  simp only [← sup_eq_range, ← mem_mrange, ← coprod_apply, ← Prod.exists, ← SetLike.exists, ← coeSubtype, ←
    Subtype.coe_mk]

end Submonoid

namespace AddSubmonoid

variable [AddMonoidₓ A]

open Set

theorem closure_singleton_eq (x : A) : closure ({x} : Set A) = (multiplesHom A x).mrange :=
  (closure_eq_of_le (Set.singleton_subset_iff.2 ⟨1, one_nsmul x⟩)) fun x ⟨n, hn⟩ =>
    hn ▸ nsmul_mem (subset_closure <| Set.mem_singleton _) _

/-- The `add_submonoid` generated by an element of an `add_monoid` equals the set of
natural number multiples of the element. -/
theorem mem_closure_singleton {x y : A} : y ∈ closure ({x} : Set A) ↔ ∃ n : ℕ, n • x = y := by
  rw [closure_singleton_eq, AddMonoidHom.mem_mrange] <;> rfl

theorem closure_singleton_zero : closure ({0} : Set A) = ⊥ := by
  simp [← eq_bot_iff_forall, ← mem_closure_singleton, ← nsmul_zero]

/-- The additive submonoid generated by an element. -/
def multiples (x : A) : AddSubmonoid A :=
  AddSubmonoid.copy (multiplesHom A x).mrange (Set.Range (fun i => i • x : ℕ → A)) <|
    Set.ext fun n =>
      exists_congr fun i => by
        simp <;> rfl

@[simp]
theorem mem_multiples (x : A) : x ∈ multiples x :=
  ⟨1, one_nsmul _⟩

theorem mem_multiples_iff (x z : A) : x ∈ multiples z ↔ ∃ n : ℕ, n • z = x :=
  Iff.rfl

theorem multiples_eq_closure (x : A) : multiples x = closure {x} := by
  ext
  exact mem_closure_singleton.symm

theorem multiples_subset {x : A} {P : AddSubmonoid A} (h : x ∈ P) : multiples x ≤ P := fun x hx =>
  match x, hx with
  | _, ⟨i, rfl⟩ => nsmul_mem h i

attribute [to_additive AddSubmonoid.multiples] Submonoid.powers

attribute [to_additive AddSubmonoid.mem_multiples] Submonoid.mem_powers

attribute [to_additive AddSubmonoid.mem_multiples_iff] Submonoid.mem_powers_iff

attribute [to_additive AddSubmonoid.multiples_eq_closure] Submonoid.powers_eq_closure

attribute [to_additive AddSubmonoid.multiples_subset] Submonoid.powers_subset

end AddSubmonoid

/-! Lemmas about additive closures of `subsemigroup`. -/


namespace MulMemClass

variable {R : Type _} [NonUnitalNonAssocSemiringₓ R] [SetLike M R] [MulMemClass M R] {S : M} {a b : R}

/-- The product of an element of the additive closure of a multiplicative subsemigroup `M`
and an element of `M` is contained in the additive closure of `M`. -/
theorem mul_right_mem_add_closure (ha : a ∈ AddSubmonoid.closure (S : Set R)) (hb : b ∈ S) :
    a * b ∈ AddSubmonoid.closure (S : Set R) := by
  revert b
  refine' AddSubmonoid.closure_induction ha _ _ _ <;> clear ha a
  · exact fun r hr b hb => add_submonoid.mem_closure.mpr fun y hy => hy (mul_mem hr hb)
    
  · exact fun b hb => by
      simp only [← zero_mul, ← (AddSubmonoid.closure (S : Set R)).zero_mem]
    
  · simp_rw [add_mulₓ]
    exact fun r s hr hs b hb => (AddSubmonoid.closure (S : Set R)).add_mem (hr hb) (hs hb)
    

/-- The product of two elements of the additive closure of a submonoid `M` is an element of the
additive closure of `M`. -/
theorem mul_mem_add_closure (ha : a ∈ AddSubmonoid.closure (S : Set R)) (hb : b ∈ AddSubmonoid.closure (S : Set R)) :
    a * b ∈ AddSubmonoid.closure (S : Set R) := by
  revert a
  refine' AddSubmonoid.closure_induction hb _ _ _ <;> clear hb b
  · exact fun r hr b hb => MulMemClass.mul_right_mem_add_closure hb hr
    
  · exact fun b hb => by
      simp only [← mul_zero, ← (AddSubmonoid.closure (S : Set R)).zero_mem]
    
  · simp_rw [mul_addₓ]
    exact fun r s hr hs b hb => (AddSubmonoid.closure (S : Set R)).add_mem (hr hb) (hs hb)
    

/-- The product of an element of `S` and an element of the additive closure of a multiplicative
submonoid `S` is contained in the additive closure of `S`. -/
theorem mul_left_mem_add_closure (ha : a ∈ S) (hb : b ∈ AddSubmonoid.closure (S : Set R)) :
    a * b ∈ AddSubmonoid.closure (S : Set R) :=
  mul_mem_add_closure (AddSubmonoid.mem_closure.mpr fun sT hT => hT ha) hb

end MulMemClass

namespace Submonoid

/-- An element is in the closure of a two-element set if it is a linear combination of those two
elements. -/
@[to_additive "An element is in the closure of a two-element set if it is a linear combination of\nthose two elements."]
theorem mem_closure_pair {A : Type _} [CommMonoidₓ A] (a b c : A) :
    c ∈ Submonoid.closure ({a, b} : Set A) ↔ ∃ m n : ℕ, a ^ m * b ^ n = c := by
  rw [← Set.singleton_union, Submonoid.closure_union, mem_sup]
  simp_rw [exists_prop, mem_closure_singleton, exists_exists_eq_and]

end Submonoid

section mul_addₓ

theorem of_mul_image_powers_eq_multiples_of_mul [Monoidₓ M] {x : M} :
    Additive.ofMul '' (Submonoid.powers x : Set M) = AddSubmonoid.multiples (Additive.ofMul x) := by
  ext
  constructor
  · rintro ⟨y, ⟨n, hy1⟩, hy2⟩
    use n
    simpa [of_mul_pow, ← hy1]
    
  · rintro ⟨n, hn⟩
    refine' ⟨x ^ n, ⟨n, rfl⟩, _⟩
    rwa [of_mul_pow]
    

theorem of_add_image_multiples_eq_powers_of_add [AddMonoidₓ A] {x : A} :
    Multiplicative.ofAdd '' (AddSubmonoid.multiples x : Set A) = Submonoid.powers (Multiplicative.ofAdd x) := by
  symm
  rw [Equivₓ.eq_image_iff_symm_image_eq]
  exact of_mul_image_powers_eq_multiples_of_mul

end mul_addₓ


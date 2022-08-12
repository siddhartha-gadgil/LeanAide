/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.Algebra.Operations
import Mathbin.Algebra.Ring.Equiv
import Mathbin.Data.Nat.Choose.Sum
import Mathbin.RingTheory.Coprime.Lemmas
import Mathbin.RingTheory.Ideal.Quotient
import Mathbin.RingTheory.NonZeroDivisors

/-!
# More operations on modules and ideals
-/


universe u v w x

open BigOperators Pointwise

namespace Submodule

variable {R : Type u} {M : Type v} {F : Type _} {G : Type _}

section CommSemiringₓ

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M]

open Pointwise

instance hasSmul' : HasSmul (Ideal R) (Submodule R M) :=
  ⟨Submodule.map₂ (LinearMap.lsmul R M)⟩

/-- This duplicates the global `smul_eq_mul`, but doesn't have to unfold anywhere near as much to
apply. -/
protected theorem _root_.ideal.smul_eq_mul (I J : Ideal R) : I • J = I * J :=
  rfl

/-- `N.annihilator` is the ideal of all elements `r : R` such that `r • N = 0`. -/
def annihilator (N : Submodule R M) : Ideal R :=
  (LinearMap.lsmul R N).ker

variable {I J : Ideal R} {N P : Submodule R M}

theorem mem_annihilator {r} : r ∈ N.annihilator ↔ ∀, ∀ n ∈ N, ∀, r • n = (0 : M) :=
  ⟨fun hr n hn => congr_arg Subtype.val (LinearMap.ext_iff.1 (LinearMap.mem_ker.1 hr) ⟨n, hn⟩), fun h =>
    LinearMap.mem_ker.2 <| LinearMap.ext fun n => Subtype.eq <| h n.1 n.2⟩

theorem mem_annihilator' {r} : r ∈ N.annihilator ↔ N ≤ comap (r • LinearMap.id) ⊥ :=
  mem_annihilator.trans ⟨fun H n hn => (mem_bot R).2 <| H n hn, fun H n hn => (mem_bot R).1 <| H hn⟩

theorem mem_annihilator_span (s : Set M) (r : R) : r ∈ (Submodule.span R s).annihilator ↔ ∀ n : s, r • (n : M) = 0 := by
  rw [Submodule.mem_annihilator]
  constructor
  · intro h n
    exact h _ (Submodule.subset_span n.prop)
    
  · intro h n hn
    apply Submodule.span_induction hn
    · intro x hx
      exact h ⟨x, hx⟩
      
    · exact smul_zero _
      
    · intro x y hx hy
      rw [smul_add, hx, hy, zero_addₓ]
      
    · intro a x hx
      rw [smul_comm, hx, smul_zero]
      
    

theorem mem_annihilator_span_singleton (g : M) (r : R) : r ∈ (Submodule.span R ({g} : Set M)).annihilator ↔ r • g = 0 :=
  by
  simp [← mem_annihilator_span]

theorem annihilator_bot : (⊥ : Submodule R M).annihilator = ⊤ :=
  (Ideal.eq_top_iff_one _).2 <| mem_annihilator'.2 bot_le

theorem annihilator_eq_top_iff : N.annihilator = ⊤ ↔ N = ⊥ :=
  ⟨fun H =>
    eq_bot_iff.2 fun (n : M) hn =>
      (mem_bot R).2 <| one_smul R n ▸ mem_annihilator.1 ((Ideal.eq_top_iff_one _).1 H) n hn,
    fun H => H.symm ▸ annihilator_bot⟩

theorem annihilator_mono (h : N ≤ P) : P.annihilator ≤ N.annihilator := fun r hrp =>
  mem_annihilator.2 fun n hn => mem_annihilator.1 hrp n <| h hn

theorem annihilator_supr (ι : Sort w) (f : ι → Submodule R M) : annihilator (⨆ i, f i) = ⨅ i, annihilator (f i) :=
  le_antisymmₓ (le_infi fun i => annihilator_mono <| le_supr _ _) fun r H =>
    mem_annihilator'.2 <|
      supr_le fun i =>
        have := (mem_infi _).1 H i
        mem_annihilator'.1 this

theorem smul_mem_smul {r} {n} (hr : r ∈ I) (hn : n ∈ N) : r • n ∈ I • N :=
  apply_mem_map₂ _ hr hn

theorem smul_le {P : Submodule R M} : I • N ≤ P ↔ ∀, ∀ r ∈ I, ∀, ∀ n ∈ N, ∀, r • n ∈ P :=
  map₂_le

@[elab_as_eliminator]
theorem smul_induction_on {p : M → Prop} {x} (H : x ∈ I • N) (Hb : ∀, ∀ r ∈ I, ∀, ∀ n ∈ N, ∀, p (r • n))
    (H1 : ∀ x y, p x → p y → p (x + y)) : p x := by
  have H0 : p 0 := by
    simpa only [← zero_smul] using Hb 0 I.zero_mem 0 N.zero_mem
  refine' Submodule.supr_induction _ H _ H0 H1
  rintro ⟨i, hi⟩ m ⟨j, hj, rfl : i • _ = m⟩
  exact Hb _ hi _ hj

theorem mem_smul_span_singleton {I : Ideal R} {m : M} {x : M} : x ∈ I • span R ({m} : Set M) ↔ ∃ y ∈ I, y • m = x :=
  ⟨fun hx =>
    smul_induction_on hx
      (fun r hri n hnm =>
        let ⟨s, hs⟩ := mem_span_singleton.1 hnm
        ⟨r * s, I.mul_mem_right _ hri, hs ▸ mul_smul r s m⟩)
      fun m1 m2 ⟨y1, hyi1, hy1⟩ ⟨y2, hyi2, hy2⟩ =>
      ⟨y1 + y2, I.add_mem hyi1 hyi2, by
        rw [add_smul, hy1, hy2]⟩,
    fun ⟨y, hyi, hy⟩ => hy ▸ smul_mem_smul hyi (subset_span <| Set.mem_singleton m)⟩

theorem smul_le_right : I • N ≤ N :=
  smul_le.2 fun r hr n => N.smul_mem r

theorem smul_mono (hij : I ≤ J) (hnp : N ≤ P) : I • N ≤ J • P :=
  map₂_le_map₂ hij hnp

theorem smul_mono_left (h : I ≤ J) : I • N ≤ J • N :=
  map₂_le_map₂_left h

theorem smul_mono_right (h : N ≤ P) : I • N ≤ I • P :=
  map₂_le_map₂_right h

theorem map_le_smul_top (I : Ideal R) (f : R →ₗ[R] M) : Submodule.map f I ≤ I • (⊤ : Submodule R M) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [← mul_oneₓ y, ← smul_eq_mul, f.map_smul]
  exact smul_mem_smul hy mem_top

@[simp]
theorem annihilator_smul (N : Submodule R M) : annihilator N • N = ⊥ :=
  eq_bot_iff.2 (smul_le.2 fun r => mem_annihilator.1)

@[simp]
theorem annihilator_mul (I : Ideal R) : annihilator I * I = ⊥ :=
  annihilator_smul I

@[simp]
theorem mul_annihilator (I : Ideal R) : I * annihilator I = ⊥ := by
  rw [mul_comm, annihilator_mul]

variable (I J N P)

@[simp]
theorem smul_bot : I • (⊥ : Submodule R M) = ⊥ :=
  map₂_bot_right _ _

@[simp]
theorem bot_smul : (⊥ : Ideal R) • N = ⊥ :=
  map₂_bot_left _ _

@[simp]
theorem top_smul : (⊤ : Ideal R) • N = N :=
  (le_antisymmₓ smul_le_right) fun r hri => one_smul R r ▸ smul_mem_smul mem_top hri

theorem smul_sup : I • (N⊔P) = I • N⊔I • P :=
  map₂_sup_right _ _ _ _

theorem sup_smul : (I⊔J) • N = I • N⊔J • N :=
  map₂_sup_left _ _ _ _

protected theorem smul_assoc : (I • J) • N = I • J • N :=
  le_antisymmₓ
    (smul_le.2 fun rs hrsij t htn =>
      smul_induction_on hrsij
        (fun r hr s hs => (@smul_eq_mul R _ r s).symm ▸ smul_smul r s t ▸ smul_mem_smul hr (smul_mem_smul hs htn))
        fun x y => (add_smul x y t).symm ▸ Submodule.add_mem _)
    (smul_le.2 fun r hr sn hsn =>
      suffices J • N ≤ Submodule.comap (r • LinearMap.id) ((I • J) • N) from this hsn
      smul_le.2 fun s hs n hn =>
        show r • s • n ∈ (I • J) • N from mul_smul r s n ▸ smul_mem_smul (smul_mem_smul hr hs) hn)

theorem smul_inf_le (M₁ M₂ : Submodule R M) : I • (M₁⊓M₂) ≤ I • M₁⊓I • M₂ :=
  le_inf (Submodule.smul_mono_right inf_le_left) (Submodule.smul_mono_right inf_le_right)

theorem smul_supr {ι : Sort _} {I : Ideal R} {t : ι → Submodule R M} : I • supr t = ⨆ i, I • t i :=
  map₂_supr_right _ _ _

theorem smul_infi_le {ι : Sort _} {I : Ideal R} {t : ι → Submodule R M} : I • infi t ≤ ⨅ i, I • t i :=
  le_infi fun i => smul_mono_right (infi_le _ _)

variable (S : Set R) (T : Set M)

theorem span_smul_span : Ideal.span S • span R T = span R (⋃ (s ∈ S) (t ∈ T), {s • t}) :=
  (map₂_span_span _ _ _ _).trans <| congr_arg _ <| Set.image2_eq_Union _ _ _

theorem ideal_span_singleton_smul (r : R) (N : Submodule R M) : (Ideal.span {r} : Ideal R) • N = r • N := by
  have : span R (⋃ (t : M) (x : t ∈ N), {r • t}) = r • N := by
    convert span_eq _
    exact (Set.image_eq_Union _ (N : Set M)).symm
  conv_lhs => rw [← span_eq N, span_smul_span]
  simpa

theorem span_smul_eq (r : R) (s : Set M) : span R (r • s) = r • span R s := by
  rw [← ideal_span_singleton_smul, span_smul_span, ← Set.image2_eq_Union, Set.image2_singleton_left, Set.image_smul]

theorem mem_of_span_top_of_smul_mem (M' : Submodule R M) (s : Set R) (hs : Ideal.span s = ⊤) (x : M)
    (H : ∀ r : s, (r : R) • x ∈ M') : x ∈ M' := by
  suffices (⊤ : Ideal R) • span R ({x} : Set M) ≤ M' by
    rw [top_smul] at this
    exact this (subset_span (Set.mem_singleton x))
  rw [← hs, span_smul_span, span_le]
  simpa using H

/-- Given `s`, a generating set of `R`, to check that an `x : M` falls in a
submodule `M'` of `x`, we only need to show that `r ^ n • x ∈ M'` for some `n` for each `r : s`. -/
theorem mem_of_span_eq_top_of_smul_pow_mem (M' : Submodule R M) (s : Set R) (hs : Ideal.span s = ⊤) (x : M)
    (H : ∀ r : s, ∃ n : ℕ, (r ^ n : R) • x ∈ M') : x ∈ M' := by
  obtain ⟨s', hs₁, hs₂⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
  replace H : ∀ r : s', ∃ n : ℕ, (r ^ n : R) • x ∈ M' := fun r => H ⟨_, hs₁ r.Prop⟩
  choose n₁ n₂ using H
  let N := s'.attach.sup n₁
  have hs' := Ideal.span_pow_eq_top (s' : Set R) hs₂ N
  apply M'.mem_of_span_top_of_smul_mem _ hs'
  rintro ⟨_, r, hr, rfl⟩
  convert M'.smul_mem (r ^ (N - n₁ ⟨r, hr⟩)) (n₂ ⟨r, hr⟩) using 1
  simp only [← Subtype.coe_mk, ← smul_smul, pow_addₓ]
  rw [tsub_add_cancel_of_le (Finset.le_sup (s'.mem_attach _) : n₁ ⟨r, hr⟩ ≤ N)]

variable {M' : Type w} [AddCommMonoidₓ M'] [Module R M']

theorem map_smul'' (f : M →ₗ[R] M') : (I • N).map f = I • N.map f :=
  le_antisymmₓ
      (map_le_iff_le_comap.2 <|
        smul_le.2 fun r hr n hn =>
          show f (r • n) ∈ I • N.map f from (f.map_smul r n).symm ▸ smul_mem_smul hr (mem_map_of_mem hn)) <|
    smul_le.2 fun r hr n hn =>
      let ⟨p, hp, hfp⟩ := mem_map.1 hn
      hfp ▸ f.map_smul r p ▸ mem_map_of_mem (smul_mem_smul hr hp)

variable {I}

theorem mem_smul_span {s : Set M} {x : M} :
    x ∈ I • Submodule.span R s ↔ x ∈ Submodule.span R (⋃ (a ∈ I) (b ∈ s), ({a • b} : Set M)) := by
  rw [← I.span_eq, Submodule.span_smul_span, I.span_eq] <;> rfl

variable (I)

/-- If `x` is an `I`-multiple of the submodule spanned by `f '' s`,
then we can write `x` as an `I`-linear combination of the elements of `f '' s`. -/
theorem exists_sum_of_mem_ideal_smul_span {ι : Type _} (s : Set ι) (f : ι → M) (x : M) (hx : x ∈ I • span R (f '' s)) :
    ∃ (a : s →₀ R)(ha : ∀ i, a i ∈ I), (a.Sum fun i c => c • f i) = x := by
  refine' span_induction (mem_smul_span.mp hx) _ _ _ _
  · simp only [← Set.mem_Union, ← Set.mem_range, ← Set.mem_singleton_iff]
    rintro x ⟨y, hy, x, ⟨i, hi, rfl⟩, rfl⟩
    refine' ⟨Finsupp.single ⟨i, hi⟩ y, fun j => _, _⟩
    · let this := Classical.decEq s
      rw [Finsupp.single_apply]
      split_ifs
      · assumption
        
      · exact I.zero_mem
        
      
    refine' @Finsupp.sum_single_index s R M _ _ ⟨i, hi⟩ _ (fun i y => y • f i) _
    simp
    
  · exact ⟨0, fun i => I.zero_mem, Finsupp.sum_zero_index⟩
    
  · rintro x y ⟨ax, hax, rfl⟩ ⟨ay, hay, rfl⟩
    refine' ⟨ax + ay, fun i => I.add_mem (hax i) (hay i), Finsupp.sum_add_index _ _⟩ <;>
      intros <;> simp only [← zero_smul, ← add_smul]
    
  · rintro c x ⟨a, ha, rfl⟩
    refine' ⟨c • a, fun i => I.mul_mem_left c (ha i), _⟩
    rw [Finsupp.sum_smul_index, Finsupp.smul_sum] <;> intros <;> simp only [← zero_smul, ← mul_smul]
    

@[simp]
theorem smul_comap_le_comap_smul (f : M →ₗ[R] M') (S : Submodule R M') (I : Ideal R) :
    I • S.comap f ≤ (I • S).comap f := by
  refine' submodule.smul_le.mpr fun r hr x hx => _
  rw [Submodule.mem_comap] at hx⊢
  rw [f.map_smul]
  exact Submodule.smul_mem_smul hr hx

end CommSemiringₓ

section CommRingₓ

variable [CommRingₓ R] [AddCommGroupₓ M] [Module R M]

variable {N N₁ N₂ P P₁ P₂ : Submodule R M}

/-- `N.colon P` is the ideal of all elements `r : R` such that `r • P ⊆ N`. -/
def colon (N P : Submodule R M) : Ideal R :=
  annihilator (P.map N.mkq)

theorem mem_colon {r} : r ∈ N.colon P ↔ ∀, ∀ p ∈ P, ∀, r • p ∈ N :=
  mem_annihilator.trans
    ⟨fun H p hp => (Quotient.mk_eq_zero N).1 (H (Quotient.mk p) (mem_map_of_mem hp)), fun H m ⟨p, hp, hpm⟩ =>
      hpm ▸ N.mkq.map_smul r p ▸ (Quotient.mk_eq_zero N).2 <| H p hp⟩

theorem mem_colon' {r} : r ∈ N.colon P ↔ P ≤ comap (r • LinearMap.id) N :=
  mem_colon

theorem colon_mono (hn : N₁ ≤ N₂) (hp : P₁ ≤ P₂) : N₁.colon P₂ ≤ N₂.colon P₁ := fun r hrnp =>
  mem_colon.2 fun p₁ hp₁ => hn <| mem_colon.1 hrnp p₁ <| hp hp₁

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem infi_colon_supr (ι₁ : Sort w) (f : ι₁ → Submodule R M) (ι₂ : Sort x) (g : ι₂ → Submodule R M) :
    (⨅ i, f i).colon (⨆ j, g j) = ⨅ (i) (j), (f i).colon (g j) :=
  le_antisymmₓ (le_infi fun i => le_infi fun j => colon_mono (infi_le _ _) (le_supr _ _)) fun r H =>
    mem_colon'.2 <|
      supr_le fun j =>
        map_le_iff_le_comap.1 <|
          le_infi fun i =>
            map_le_iff_le_comap.2 <|
              mem_colon'.1 <|
                have := (mem_infi _).1 H i
                have := (mem_infi _).1 this j
                this

end CommRingₓ

end Submodule

namespace Ideal

section Add

variable {R : Type u} [Semiringₓ R]

@[simp]
theorem add_eq_sup {I J : Ideal R} : I + J = I⊔J :=
  rfl

@[simp]
theorem zero_eq_bot : (0 : Ideal R) = ⊥ :=
  rfl

end Add

section MulAndRadical

variable {R : Type u} {ι : Type _} [CommSemiringₓ R]

variable {I J K L : Ideal R}

instance : Mul (Ideal R) :=
  ⟨(· • ·)⟩

@[simp]
theorem one_eq_top : (1 : Ideal R) = ⊤ := by
  erw [Submodule.one_eq_range, LinearMap.range_id]

theorem mul_mem_mul {r s} (hr : r ∈ I) (hs : s ∈ J) : r * s ∈ I * J :=
  Submodule.smul_mem_smul hr hs

theorem mul_mem_mul_rev {r s} (hr : r ∈ I) (hs : s ∈ J) : s * r ∈ I * J :=
  mul_comm r s ▸ mul_mem_mul hr hs

theorem pow_mem_pow {x : R} (hx : x ∈ I) (n : ℕ) : x ^ n ∈ I ^ n :=
  Submodule.pow_mem_pow _ hx _

theorem prod_mem_prod {ι : Type _} {s : Finset ι} {I : ι → Ideal R} {x : ι → R} :
    (∀, ∀ i ∈ s, ∀, x i ∈ I i) → (∏ i in s, x i) ∈ ∏ i in s, I i := by
  classical
  apply Finset.induction_on s
  · intro
    rw [Finset.prod_empty, Finset.prod_empty, one_eq_top]
    exact Submodule.mem_top
    
  · intro a s ha IH h
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_mem_mul (h a <| Finset.mem_insert_self a s) (IH fun i hi => h i <| Finset.mem_insert_of_mem hi)
    

theorem mul_le : I * J ≤ K ↔ ∀, ∀ r ∈ I, ∀, ∀ s ∈ J, ∀, r * s ∈ K :=
  Submodule.smul_le

theorem mul_le_left : I * J ≤ J :=
  Ideal.mul_le.2 fun r hr s => J.mul_mem_left _

theorem mul_le_right : I * J ≤ I :=
  Ideal.mul_le.2 fun r hr s hs => I.mul_mem_right _ hr

@[simp]
theorem sup_mul_right_self : I⊔I * J = I :=
  sup_eq_left.2 Ideal.mul_le_right

@[simp]
theorem sup_mul_left_self : I⊔J * I = I :=
  sup_eq_left.2 Ideal.mul_le_left

@[simp]
theorem mul_right_self_sup : I * J⊔I = I :=
  sup_eq_right.2 Ideal.mul_le_right

@[simp]
theorem mul_left_self_sup : J * I⊔I = I :=
  sup_eq_right.2 Ideal.mul_le_left

variable (I J K)

protected theorem mul_comm : I * J = J * I :=
  le_antisymmₓ (mul_le.2 fun r hrI s hsJ => mul_mem_mul_rev hsJ hrI)
    (mul_le.2 fun r hrJ s hsI => mul_mem_mul_rev hsI hrJ)

protected theorem mul_assoc : I * J * K = I * (J * K) :=
  Submodule.smul_assoc I J K

theorem span_mul_span (S T : Set R) : span S * span T = span (⋃ (s ∈ S) (t ∈ T), {s * t}) :=
  Submodule.span_smul_span S T

variable {I J K}

theorem span_mul_span' (S T : Set R) : span S * span T = span (S * T) := by
  unfold span
  rw [Submodule.span_mul_span]

theorem span_singleton_mul_span_singleton (r s : R) : span {r} * span {s} = (span {r * s} : Ideal R) := by
  unfold span
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

theorem span_singleton_pow (s : R) (n : ℕ) : span {s} ^ n = (span {s ^ n} : Ideal R) := by
  induction' n with n ih
  · simp [← Set.singleton_one]
    
  simp only [← pow_succₓ, ← ih, ← span_singleton_mul_span_singleton]

theorem mem_mul_span_singleton {x y : R} {I : Ideal R} : x ∈ I * span {y} ↔ ∃ z ∈ I, z * y = x :=
  Submodule.mem_smul_span_singleton

theorem mem_span_singleton_mul {x y : R} {I : Ideal R} : x ∈ span {y} * I ↔ ∃ z ∈ I, y * z = x := by
  simp only [← mul_comm, ← mem_mul_span_singleton]

theorem le_span_singleton_mul_iff {x : R} {I J : Ideal R} : I ≤ span {x} * J ↔ ∀, ∀ zI ∈ I, ∀, ∃ zJ ∈ J, x * zJ = zI :=
  show (∀ {zI} (hzI : zI ∈ I), zI ∈ span {x} * J) ↔ ∀, ∀ zI ∈ I, ∀, ∃ zJ ∈ J, x * zJ = zI by
    simp only [← mem_span_singleton_mul]

theorem span_singleton_mul_le_iff {x : R} {I J : Ideal R} : span {x} * I ≤ J ↔ ∀, ∀ z ∈ I, ∀, x * z ∈ J := by
  simp only [← mul_le, ← mem_span_singleton_mul, ← mem_span_singleton]
  constructor
  · intro h zI hzI
    exact h x (dvd_refl x) zI hzI
    
  · rintro h _ ⟨z, rfl⟩ zI hzI
    rw [mul_comm x z, mul_assoc]
    exact J.mul_mem_left _ (h zI hzI)
    

theorem span_singleton_mul_le_span_singleton_mul {x y : R} {I J : Ideal R} :
    span {x} * I ≤ span {y} * J ↔ ∀, ∀ zI ∈ I, ∀, ∃ zJ ∈ J, x * zI = y * zJ := by
  simp only [← span_singleton_mul_le_iff, ← mem_span_singleton_mul, ← eq_comm]

theorem eq_span_singleton_mul {x : R} (I J : Ideal R) :
    I = span {x} * J ↔ (∀, ∀ zI ∈ I, ∀, ∃ zJ ∈ J, x * zJ = zI) ∧ ∀, ∀ z ∈ J, ∀, x * z ∈ I := by
  simp only [← le_antisymm_iffₓ, ← le_span_singleton_mul_iff, ← span_singleton_mul_le_iff]

theorem span_singleton_mul_eq_span_singleton_mul {x y : R} (I J : Ideal R) :
    span {x} * I = span {y} * J ↔
      (∀, ∀ zI ∈ I, ∀, ∃ zJ ∈ J, x * zI = y * zJ) ∧ ∀, ∀ zJ ∈ J, ∀, ∃ zI ∈ I, x * zI = y * zJ :=
  by
  simp only [← le_antisymm_iffₓ, ← span_singleton_mul_le_span_singleton_mul, ← eq_comm]

theorem prod_span {ι : Type _} (s : Finset ι) (I : ι → Set R) :
    (∏ i in s, Ideal.span (I i)) = Ideal.span (∏ i in s, I i) :=
  Submodule.prod_span s I

theorem prod_span_singleton {ι : Type _} (s : Finset ι) (I : ι → R) :
    (∏ i in s, Ideal.span ({I i} : Set R)) = Ideal.span {∏ i in s, I i} :=
  Submodule.prod_span_singleton s I

theorem finset_inf_span_singleton {ι : Type _} (s : Finset ι) (I : ι → R) (hI : Set.Pairwise (↑s) (IsCoprime on I)) :
    (s.inf fun i => Ideal.span ({I i} : Set R)) = Ideal.span {∏ i in s, I i} := by
  ext x
  simp only [← Submodule.mem_finset_inf, ← Ideal.mem_span_singleton]
  exact ⟨Finset.prod_dvd_of_coprime hI, fun h i hi => (Finset.dvd_prod_of_mem _ hi).trans h⟩

theorem infi_span_singleton {ι : Type _} [Fintype ι] (I : ι → R) (hI : ∀ (i j) (hij : i ≠ j), IsCoprime (I i) (I j)) :
    (⨅ i, Ideal.span ({I i} : Set R)) = Ideal.span {∏ i, I i} := by
  rw [← Finset.inf_univ_eq_infi, finset_inf_span_singleton]
  rwa [Finset.coe_univ, Set.pairwise_univ]

theorem sup_eq_top_iff_is_coprime {R : Type _} [CommSemiringₓ R] (x y : R) :
    span ({x} : Set R)⊔span {y} = ⊤ ↔ IsCoprime x y := by
  rw [eq_top_iff_one, Submodule.mem_sup]
  constructor
  · rintro ⟨u, hu, v, hv, h1⟩
    rw [mem_span_singleton'] at hu hv
    rw [← hu.some_spec, ← hv.some_spec] at h1
    exact ⟨_, _, h1⟩
    
  · exact fun ⟨u, v, h1⟩ => ⟨_, mem_span_singleton'.mpr ⟨_, rfl⟩, _, mem_span_singleton'.mpr ⟨_, rfl⟩, h1⟩
    

theorem mul_le_inf : I * J ≤ I⊓J :=
  mul_le.2 fun r hri s hsj => ⟨I.mul_mem_right s hri, J.mul_mem_left r hsj⟩

theorem multiset_prod_le_inf {s : Multiset (Ideal R)} : s.Prod ≤ s.inf := by
  classical
  refine' s.induction_on _ _
  · rw [Multiset.inf_zero]
    exact le_top
    
  intro a s ih
  rw [Multiset.prod_cons, Multiset.inf_cons]
  exact le_transₓ mul_le_inf (inf_le_inf le_rfl ih)

theorem prod_le_inf {s : Finset ι} {f : ι → Ideal R} : s.Prod f ≤ s.inf f :=
  multiset_prod_le_inf

theorem mul_eq_inf_of_coprime (h : I⊔J = ⊤) : I * J = I⊓J :=
  (le_antisymmₓ mul_le_inf) fun r ⟨hri, hrj⟩ =>
    let ⟨s, hsi, t, htj, hst⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 h)
    mul_oneₓ r ▸ hst ▸ (mul_addₓ r s t).symm ▸ Ideal.add_mem (I * J) (mul_mem_mul_rev hsi hrj) (mul_mem_mul hri htj)

theorem sup_mul_eq_of_coprime_left (h : I⊔J = ⊤) : I⊔J * K = I⊔K :=
  (le_antisymmₓ (sup_le_sup_left mul_le_left _)) fun i hi => by
    rw [eq_top_iff_one] at h
    rw [Submodule.mem_sup] at h hi⊢
    obtain ⟨i1, hi1, j, hj, h⟩ := h
    obtain ⟨i', hi', k, hk, hi⟩ := hi
    refine' ⟨_, add_mem hi' (mul_mem_right k _ hi1), _, mul_mem_mul hj hk, _⟩
    rw [add_assocₓ, ← add_mulₓ, h, one_mulₓ, hi]

theorem sup_mul_eq_of_coprime_right (h : I⊔K = ⊤) : I⊔J * K = I⊔J := by
  rw [mul_comm]
  exact sup_mul_eq_of_coprime_left h

theorem mul_sup_eq_of_coprime_left (h : I⊔J = ⊤) : I * K⊔J = K⊔J := by
  rw [sup_comm] at h
  rw [sup_comm, sup_mul_eq_of_coprime_left h, sup_comm]

theorem mul_sup_eq_of_coprime_right (h : K⊔J = ⊤) : I * K⊔J = I⊔J := by
  rw [sup_comm] at h
  rw [sup_comm, sup_mul_eq_of_coprime_right h, sup_comm]

theorem sup_prod_eq_top {s : Finset ι} {J : ι → Ideal R} (h : ∀ i, i ∈ s → I⊔J i = ⊤) : (I⊔∏ i in s, J i) = ⊤ :=
  Finset.prod_induction _ (fun J => I⊔J = ⊤) (fun J K hJ hK => (sup_mul_eq_of_coprime_left hJ).trans hK)
    (by
      rw [one_eq_top, sup_top_eq])
    h

theorem sup_infi_eq_top {s : Finset ι} {J : ι → Ideal R} (h : ∀ i, i ∈ s → I⊔J i = ⊤) : (I⊔⨅ i ∈ s, J i) = ⊤ :=
  eq_top_iff.mpr <|
    le_of_eq_of_le (sup_prod_eq_top h).symm <| sup_le_sup_left (le_of_le_of_eq prod_le_inf <| Finset.inf_eq_infi _ _) _

theorem prod_sup_eq_top {s : Finset ι} {J : ι → Ideal R} (h : ∀ i, i ∈ s → J i⊔I = ⊤) : (∏ i in s, J i)⊔I = ⊤ :=
  sup_comm.trans (sup_prod_eq_top fun i hi => sup_comm.trans <| h i hi)

theorem infi_sup_eq_top {s : Finset ι} {J : ι → Ideal R} (h : ∀ i, i ∈ s → J i⊔I = ⊤) : (⨅ i ∈ s, J i)⊔I = ⊤ :=
  sup_comm.trans (sup_infi_eq_top fun i hi => sup_comm.trans <| h i hi)

theorem sup_pow_eq_top {n : ℕ} (h : I⊔J = ⊤) : I⊔J ^ n = ⊤ := by
  rw [← Finset.card_range n, ← Finset.prod_const]
  exact sup_prod_eq_top fun _ _ => h

theorem pow_sup_eq_top {n : ℕ} (h : I⊔J = ⊤) : I ^ n⊔J = ⊤ := by
  rw [← Finset.card_range n, ← Finset.prod_const]
  exact prod_sup_eq_top fun _ _ => h

theorem pow_sup_pow_eq_top {m n : ℕ} (h : I⊔J = ⊤) : I ^ m⊔J ^ n = ⊤ :=
  sup_pow_eq_top (pow_sup_eq_top h)

variable (I)

@[simp]
theorem mul_bot : I * ⊥ = ⊥ :=
  Submodule.smul_bot I

@[simp]
theorem bot_mul : ⊥ * I = ⊥ :=
  Submodule.bot_smul I

@[simp]
theorem mul_top : I * ⊤ = I :=
  Ideal.mul_comm ⊤ I ▸ Submodule.top_smul I

@[simp]
theorem top_mul : ⊤ * I = I :=
  Submodule.top_smul I

variable {I}

theorem mul_mono (hik : I ≤ K) (hjl : J ≤ L) : I * J ≤ K * L :=
  Submodule.smul_mono hik hjl

theorem mul_mono_left (h : I ≤ J) : I * K ≤ J * K :=
  Submodule.smul_mono_left h

theorem mul_mono_right (h : J ≤ K) : I * J ≤ I * K :=
  Submodule.smul_mono_right h

variable (I J K)

theorem mul_sup : I * (J⊔K) = I * J⊔I * K :=
  Submodule.smul_sup I J K

theorem sup_mul : (I⊔J) * K = I * K⊔J * K :=
  Submodule.sup_smul I J K

variable {I J K}

theorem pow_le_pow {m n : ℕ} (h : m ≤ n) : I ^ n ≤ I ^ m := by
  cases' Nat.exists_eq_add_of_le h with k hk
  rw [hk, pow_addₓ]
  exact le_transₓ mul_le_inf inf_le_left

theorem pow_le_self {n : ℕ} (hn : n ≠ 0) : I ^ n ≤ I :=
  calc
    I ^ n ≤ I ^ 1 := pow_le_pow (Nat.pos_of_ne_zeroₓ hn)
    _ = I := pow_oneₓ _
    

theorem mul_eq_bot {R : Type _} [CommSemiringₓ R] [NoZeroDivisors R] {I J : Ideal R} : I * J = ⊥ ↔ I = ⊥ ∨ J = ⊥ :=
  ⟨fun hij =>
    or_iff_not_imp_left.mpr fun I_ne_bot =>
      J.eq_bot_iff.mpr fun j hj =>
        let ⟨i, hi, ne0⟩ := I.ne_bot_iff.mp I_ne_bot
        Or.resolve_left (mul_eq_zero.mp ((I * J).eq_bot_iff.mp hij _ (mul_mem_mul hi hj))) ne0,
    fun h => by
    cases h <;> rw [← Ideal.mul_bot, h, Ideal.mul_comm]⟩

instance {R : Type _} [CommSemiringₓ R] [NoZeroDivisors R] :
    NoZeroDivisors (Ideal R) where eq_zero_or_eq_zero_of_mul_eq_zero := fun I J => mul_eq_bot.1

/-- A product of ideals in an integral domain is zero if and only if one of the terms is zero. -/
theorem prod_eq_bot {R : Type _} [CommRingₓ R] [IsDomain R] {s : Multiset (Ideal R)} : s.Prod = ⊥ ↔ ∃ I ∈ s, I = ⊥ :=
  prod_zero_iff_exists_zero

/-- The radical of an ideal `I` consists of the elements `r` such that `r^n ∈ I` for some `n`. -/
def radical (I : Ideal R) : Ideal R where
  Carrier := { r | ∃ n : ℕ, r ^ n ∈ I }
  zero_mem' := ⟨1, (pow_oneₓ (0 : R)).symm ▸ I.zero_mem⟩
  add_mem' := fun x y ⟨m, hxmi⟩ ⟨n, hyni⟩ =>
    ⟨m + n,
      (add_pow x y (m + n)).symm ▸ I.sum_mem <|
        show ∀, ∀ c ∈ Finset.range (Nat.succ (m + n)), ∀, x ^ c * y ^ (m + n - c) * Nat.choose (m + n) c ∈ I from
          fun c hc =>
          Or.cases_on (le_totalₓ c m)
            (fun hcm =>
              I.mul_mem_right _ <|
                I.mul_mem_left _ <|
                  Nat.add_comm n m ▸
                    (add_tsub_assoc_of_le hcm n).symm ▸ (pow_addₓ y n (m - c)).symm ▸ I.mul_mem_right _ hyni)
            fun hmc =>
            I.mul_mem_right _ <|
              I.mul_mem_right _ <| add_tsub_cancel_of_le hmc ▸ (pow_addₓ x m (c - m)).symm ▸ I.mul_mem_right _ hxmi⟩
  smul_mem' := fun r s ⟨n, hsni⟩ => ⟨n, (mul_powₓ r s n).symm ▸ I.mul_mem_left (r ^ n) hsni⟩

theorem le_radical : I ≤ radical I := fun r hri => ⟨1, (pow_oneₓ r).symm ▸ hri⟩

variable (R)

theorem radical_top : (radical ⊤ : Ideal R) = ⊤ :=
  (eq_top_iff_one _).2 ⟨0, Submodule.mem_top⟩

variable {R}

theorem radical_mono (H : I ≤ J) : radical I ≤ radical J := fun r ⟨n, hrni⟩ => ⟨n, H hrni⟩

variable (I)

@[simp]
theorem radical_idem : radical (radical I) = radical I :=
  le_antisymmₓ (fun r ⟨n, k, hrnki⟩ => ⟨n * k, (pow_mulₓ r n k).symm ▸ hrnki⟩) le_radical

variable {I}

theorem radical_le_radical_iff : radical I ≤ radical J ↔ I ≤ radical J :=
  ⟨fun h => le_transₓ le_radical h, fun h => radical_idem J ▸ radical_mono h⟩

theorem radical_eq_top : radical I = ⊤ ↔ I = ⊤ :=
  ⟨fun h =>
    (eq_top_iff_one _).2 <|
      let ⟨n, hn⟩ := (eq_top_iff_one _).1 h
      @one_pow R _ n ▸ hn,
    fun h => h.symm ▸ radical_top R⟩

theorem IsPrime.radical (H : IsPrime I) : radical I = I :=
  le_antisymmₓ (fun r ⟨n, hrni⟩ => H.mem_of_pow_mem n hrni) le_radical

variable (I J)

theorem radical_sup : radical (I⊔J) = radical (radical I⊔radical J) :=
  (le_antisymmₓ (radical_mono <| sup_le_sup le_radical le_radical)) fun r ⟨n, hrnij⟩ =>
    let ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 hrnij
    @radical_idem _ _ (I⊔J) ▸ ⟨n, hst ▸ Ideal.add_mem _ (radical_mono le_sup_left hs) (radical_mono le_sup_right ht)⟩

theorem radical_inf : radical (I⊓J) = radical I⊓radical J :=
  le_antisymmₓ (le_inf (radical_mono inf_le_left) (radical_mono inf_le_right)) fun r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩ =>
    ⟨m + n, (pow_addₓ r m n).symm ▸ I.mul_mem_right _ hrm, (pow_addₓ r m n).symm ▸ J.mul_mem_left _ hrn⟩

theorem radical_mul : radical (I * J) = radical I⊓radical J :=
  le_antisymmₓ (radical_inf I J ▸ radical_mono <| @mul_le_inf _ _ I J) fun r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩ =>
    ⟨m + n, (pow_addₓ r m n).symm ▸ mul_mem_mul hrm hrn⟩

variable {I J}

theorem IsPrime.radical_le_iff (hj : IsPrime J) : radical I ≤ J ↔ I ≤ J :=
  ⟨le_transₓ le_radical, fun hij r ⟨n, hrni⟩ => hj.mem_of_pow_mem n <| hij hrni⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ∉ » m)
theorem radical_eq_Inf (I : Ideal R) : radical I = inf { J : Ideal R | I ≤ J ∧ IsPrime J } :=
  (le_antisymmₓ (le_Inf fun J hJ => hJ.2.radical_le_iff.2 hJ.1)) fun r hr =>
    Classical.by_contradiction fun hri =>
      let ⟨m, (hrm : r ∉ radical m), him, hm⟩ :=
        zorn_nonempty_partial_order₀ { K : Ideal R | r ∉ radical K }
          (fun c hc hcc y hyc =>
            ⟨sup c, fun ⟨n, hrnc⟩ =>
              let ⟨y, hyc, hrny⟩ := (Submodule.mem_Sup_of_directed ⟨y, hyc⟩ hcc.DirectedOn).1 hrnc
              hc hyc ⟨n, hrny⟩,
              fun z => le_Sup⟩)
          I hri
      have : ∀ (x) (_ : x ∉ m), r ∈ radical (m⊔span {x}) := fun x hxm =>
        Classical.by_contradiction fun hrmx =>
          hxm <| hm (m⊔span {x}) hrmx le_sup_left ▸ (le_sup_right : _ ≤ m⊔span {x}) (subset_span <| Set.mem_singleton _)
      have : IsPrime m :=
        ⟨by
          rintro rfl <;> rw [radical_top] at hrm <;> exact hrm trivialₓ, fun x y hxym =>
          or_iff_not_imp_left.2 fun hxm =>
            Classical.by_contradiction fun hym =>
              let ⟨n, hrn⟩ := this _ hxm
              let ⟨p, hpm, q, hq, hpqrn⟩ := Submodule.mem_sup.1 hrn
              let ⟨c, hcxq⟩ := mem_span_singleton'.1 hq
              let ⟨k, hrk⟩ := this _ hym
              let ⟨f, hfm, g, hg, hfgrk⟩ := Submodule.mem_sup.1 hrk
              let ⟨d, hdyg⟩ := mem_span_singleton'.1 hg
              hrm
                ⟨n + k, by
                  rw [pow_addₓ, ← hpqrn, ← hcxq, ← hfgrk, ← hdyg, add_mulₓ, mul_addₓ (c * x), mul_assoc c x (d * y),
                      mul_left_commₓ x, ← mul_assoc] <;>
                    refine'
                      m.add_mem (m.mul_mem_right _ hpm) (m.add_mem (m.mul_mem_left _ hfm) (m.mul_mem_left _ hxym))⟩⟩
      hrm <| this.radical.symm ▸ (Inf_le ⟨him, this⟩ : inf { J : Ideal R | I ≤ J ∧ IsPrime J } ≤ m) hr

@[simp]
theorem radical_bot_of_is_domain {R : Type u} [CommSemiringₓ R] [NoZeroDivisors R] : radical (⊥ : Ideal R) = ⊥ :=
  eq_bot_iff.2 fun x hx => hx.recOn fun n hn => pow_eq_zero hn

instance : CommSemiringₓ (Ideal R) :=
  Submodule.commSemiring

variable (R)

theorem top_pow (n : ℕ) : (⊤ ^ n : Ideal R) = ⊤ :=
  (Nat.recOn n one_eq_top) fun n ih => by
    rw [pow_succₓ, ih, top_mul]

variable {R}

variable (I)

theorem radical_pow (n : ℕ) (H : n > 0) : radical (I ^ n) = radical I :=
  Nat.recOn n
    (Not.elim
      (by
        decide))
    (fun n ih H =>
      Or.cases_on (lt_or_eq_of_leₓ <| Nat.le_of_lt_succₓ H)
        (fun H =>
          calc
            radical (I ^ (n + 1)) = radical I⊓radical (I ^ n) := by
              rw [pow_succₓ]
              exact radical_mul _ _
            _ = radical I⊓radical I := by
              rw [ih H]
            _ = radical I := inf_idem
            )
        fun H => H ▸ (pow_oneₓ I).symm ▸ rfl)
    H

theorem IsPrime.mul_le {I J P : Ideal R} (hp : IsPrime P) : I * J ≤ P ↔ I ≤ P ∨ J ≤ P :=
  ⟨fun h =>
    or_iff_not_imp_left.2 fun hip j hj =>
      let ⟨i, hi, hip⟩ := Set.not_subset.1 hip
      (hp.mem_or_mem <| h <| mul_mem_mul hi hj).resolve_left hip,
    fun h =>
    Or.cases_on h (le_transₓ <| le_transₓ mul_le_inf inf_le_left) (le_transₓ <| le_transₓ mul_le_inf inf_le_right)⟩

theorem IsPrime.inf_le {I J P : Ideal R} (hp : IsPrime P) : I⊓J ≤ P ↔ I ≤ P ∨ J ≤ P :=
  ⟨fun h => hp.mul_le.1 <| le_transₓ mul_le_inf h, fun h =>
    Or.cases_on h (le_transₓ inf_le_left) (le_transₓ inf_le_right)⟩

theorem IsPrime.multiset_prod_le {s : Multiset (Ideal R)} {P : Ideal R} (hp : IsPrime P) (hne : s ≠ 0) :
    s.Prod ≤ P ↔ ∃ I ∈ s, I ≤ P := by
  suffices s.Prod ≤ P → ∃ I ∈ s, I ≤ P from
    ⟨this, fun ⟨i, his, hip⟩ => le_transₓ multiset_prod_le_inf <| le_transₓ (Multiset.inf_le his) hip⟩
  classical
  obtain ⟨b, hb⟩ : ∃ b, b ∈ s := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨t, rfl⟩ : ∃ t, s = b ::ₘ t
  exact ⟨s.erase b, (Multiset.cons_erase hb).symm⟩
  refine' t.induction_on _ _
  · simp only [← exists_prop, Multiset.singleton_eq_cons, ← Multiset.prod_singleton, ← Multiset.mem_singleton, ←
      exists_eq_left, ← imp_self]
    
  intro a s ih h
  rw [Multiset.cons_swap, Multiset.prod_cons, hp.mul_le] at h
  rw [Multiset.cons_swap]
  cases h
  · exact ⟨a, Multiset.mem_cons_self a _, h⟩
    
  obtain ⟨I, hI, ih⟩ : ∃ I ∈ b ::ₘ s, I ≤ P := ih h
  exact ⟨I, Multiset.mem_cons_of_mem hI, ih⟩

theorem IsPrime.multiset_prod_map_le {s : Multiset ι} (f : ι → Ideal R) {P : Ideal R} (hp : IsPrime P) (hne : s ≠ 0) :
    (s.map f).Prod ≤ P ↔ ∃ i ∈ s, f i ≤ P := by
  rw [hp.multiset_prod_le (mt multiset.map_eq_zero.mp hne)]
  simp_rw [exists_prop, Multiset.mem_map, exists_exists_and_eq_and]

theorem IsPrime.prod_le {s : Finset ι} {f : ι → Ideal R} {P : Ideal R} (hp : IsPrime P) (hne : s.Nonempty) :
    s.Prod f ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
  hp.multiset_prod_map_le f (mt Finset.val_eq_zero.mp hne.ne_empty)

theorem IsPrime.inf_le' {s : Finset ι} {f : ι → Ideal R} {P : Ideal R} (hp : IsPrime P) (hsne : s.Nonempty) :
    s.inf f ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
  ⟨fun h => (hp.prod_le hsne).1 <| le_transₓ prod_le_inf h, fun ⟨i, his, hip⟩ => le_transₓ (Finset.inf_le his) hip⟩

theorem subset_union {R : Type u} [Ringₓ R] {I J K : Ideal R} : (I : Set R) ⊆ J ∪ K ↔ I ≤ J ∨ I ≤ K :=
  ⟨fun h =>
    or_iff_not_imp_left.2 fun hij s hsi =>
      let ⟨r, hri, hrj⟩ := Set.not_subset.1 hij
      Classical.by_contradiction fun hsk =>
        Or.cases_on (h <| I.add_mem hri hsi)
          (fun hj => hrj <| add_sub_cancel r s ▸ J.sub_mem hj ((h hsi).resolve_right hsk)) fun hk =>
          hsk <| add_sub_cancel' r s ▸ K.sub_mem hk ((h hri).resolve_left hrj),
    fun h =>
    Or.cases_on h (fun h => Set.Subset.trans h <| Set.subset_union_left J K) fun h =>
      Set.Subset.trans h <| Set.subset_union_right J K⟩

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:494:6: unsupported: specialize @hyp
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:494:6: unsupported: specialize @hyp
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:494:6: unsupported: specialize @hyp
theorem subset_union_prime' {R : Type u} [CommRingₓ R] {s : Finset ι} {f : ι → Ideal R} {a b : ι}
    (hp : ∀, ∀ i ∈ s, ∀, IsPrime (f i)) {I : Ideal R} :
    ((I : Set R) ⊆ f a ∪ f b ∪ ⋃ i ∈ (↑s : Set ι), f i) ↔ I ≤ f a ∨ I ≤ f b ∨ ∃ i ∈ s, I ≤ f i := by
  suffices ((I : Set R) ⊆ f a ∪ f b ∪ ⋃ i ∈ (↑s : Set ι), f i) → I ≤ f a ∨ I ≤ f b ∨ ∃ i ∈ s, I ≤ f i from
    ⟨this, fun h =>
      (Or.cases_on h fun h =>
          Set.Subset.trans h <| Set.Subset.trans (Set.subset_union_left _ _) (Set.subset_union_left _ _))
        fun h =>
        (Or.cases_on h fun h =>
            Set.Subset.trans h <| Set.Subset.trans (Set.subset_union_right _ _) (Set.subset_union_left _ _))
          fun ⟨i, his, hi⟩ => by
          refine' Set.Subset.trans hi <| Set.Subset.trans _ <| Set.subset_union_right _ _ <;>
            exact Set.subset_bUnion_of_mem (Finset.mem_coe.2 his)⟩
  generalize hn : s.card = n
  intro h
  induction' n with n ih generalizing a b s
  · clear hp
    rw [Finset.card_eq_zero] at hn
    subst hn
    rw [Finset.coe_empty, Set.bUnion_empty, Set.union_empty, subset_union] at h
    simpa only [← exists_prop, ← Finset.not_mem_empty, ← false_andₓ, ← exists_false, ← or_falseₓ]
    
  classical
  replace hn : ∃ (i : ι)(t : Finset ι), i ∉ t ∧ insert i t = s ∧ t.card = n := Finset.card_eq_succ.1 hn
  rcases hn with ⟨i, t, hit, rfl, hn⟩
  replace hp : is_prime (f i) ∧ ∀, ∀ x ∈ t, ∀, is_prime (f x) := (t.forall_mem_insert _ _).1 hp
  by_cases' Ht : ∃ j ∈ t, f j ≤ f i
  · obtain ⟨j, hjt, hfji⟩ : ∃ j ∈ t, f j ≤ f i := Ht
    obtain ⟨u, hju, rfl⟩ : ∃ u, j ∉ u ∧ insert j u = t := ⟨t.erase j, t.not_mem_erase j, Finset.insert_erase hjt⟩
    have hp' : ∀, ∀ k ∈ insert i u, ∀, is_prime (f k) := by
      rw [Finset.forall_mem_insert] at hp⊢
      exact ⟨hp.1, hp.2.2⟩
    have hiu : i ∉ u := mt Finset.mem_insert_of_mem hit
    have hn' : (insert i u).card = n := by
      rwa [Finset.card_insert_of_not_mem] at hn⊢
      exacts[hiu, hju]
    have h' : (I : Set R) ⊆ f a ∪ f b ∪ ⋃ k ∈ (↑(insert i u) : Set ι), f k := by
      rw [Finset.coe_insert] at h⊢
      rw [Finset.coe_insert] at h
      simp only [← Set.bUnion_insert] at h⊢
      rw [← Set.union_assoc ↑(f i)] at h
      erw [Set.union_eq_self_of_subset_right hfji] at h
      exact h
    specialize ih a b (insert i u) hp' hn' h'
    refine' ih.imp id (Or.imp id (exists_imp_exists fun k => _))
    simp only [← exists_prop]
    exact And.imp (fun hk => Finset.insert_subset_insert i (Finset.subset_insert j u) hk) id
    
  by_cases' Ha : f a ≤ f i
  · have h' : (I : Set R) ⊆ f i ∪ f b ∪ ⋃ j ∈ (↑t : Set ι), f j := by
      rw [Finset.coe_insert, Set.bUnion_insert, ← Set.union_assoc, Set.union_right_comm ↑(f a)] at h
      erw [Set.union_eq_self_of_subset_left Ha] at h
      exact h
    specialize ih i b t hp.2 hn h'
    right
    rcases ih with (ih | ih | ⟨k, hkt, ih⟩)
    · exact Or.inr ⟨i, Finset.mem_insert_self i t, ih⟩
      
    · exact Or.inl ih
      
    · exact Or.inr ⟨k, Finset.mem_insert_of_mem hkt, ih⟩
      
    
  by_cases' Hb : f b ≤ f i
  · have h' : (I : Set R) ⊆ f a ∪ f i ∪ ⋃ j ∈ (↑t : Set ι), f j := by
      rw [Finset.coe_insert, Set.bUnion_insert, ← Set.union_assoc, Set.union_assoc ↑(f a)] at h
      erw [Set.union_eq_self_of_subset_left Hb] at h
      exact h
    specialize ih a i t hp.2 hn h'
    rcases ih with (ih | ih | ⟨k, hkt, ih⟩)
    · exact Or.inl ih
      
    · exact Or.inr (Or.inr ⟨i, Finset.mem_insert_self i t, ih⟩)
      
    · exact Or.inr (Or.inr ⟨k, Finset.mem_insert_of_mem hkt, ih⟩)
      
    
  by_cases' Hi : I ≤ f i
  · exact Or.inr (Or.inr ⟨i, Finset.mem_insert_self i t, Hi⟩)
    
  have : ¬I⊓f a⊓f b⊓t.inf f ≤ f i := by
    rcases t.eq_empty_or_nonempty with (rfl | hsne)
    · rw [Finset.inf_empty, inf_top_eq, hp.1.inf_le, hp.1.inf_le, not_or_distrib, not_or_distrib]
      exact ⟨⟨Hi, Ha⟩, Hb⟩
      
    simp only [← hp.1.inf_le, ← hp.1.inf_le' hsne, ← not_or_distrib]
    exact ⟨⟨⟨Hi, Ha⟩, Hb⟩, Ht⟩
  rcases Set.not_subset.1 this with ⟨r, ⟨⟨⟨hrI, hra⟩, hrb⟩, hr⟩, hri⟩
  by_cases' HI : (I : Set R) ⊆ f a ∪ f b ∪ ⋃ j ∈ (↑t : Set ι), f j
  · specialize ih hp.2 hn HI
    rcases ih with (ih | ih | ⟨k, hkt, ih⟩)
    · left
      exact ih
      
    · right
      left
      exact ih
      
    · right
      right
      exact ⟨k, Finset.mem_insert_of_mem hkt, ih⟩
      
    
  exfalso
  rcases Set.not_subset.1 HI with ⟨s, hsI, hs⟩
  rw [Finset.coe_insert, Set.bUnion_insert] at h
  have hsi : s ∈ f i := ((h hsI).resolve_left (mt Or.inl hs)).resolve_right (mt Or.inr hs)
  rcases h (I.add_mem hrI hsI) with (⟨ha | hb⟩ | hi | ht)
  · exact hs (Or.inl <| Or.inl <| add_sub_cancel' r s ▸ (f a).sub_mem ha hra)
    
  · exact hs (Or.inl <| Or.inr <| add_sub_cancel' r s ▸ (f b).sub_mem hb hrb)
    
  · exact hri (add_sub_cancel r s ▸ (f i).sub_mem hi hsi)
    
  · rw [Set.mem_Union₂] at ht
    rcases ht with ⟨j, hjt, hj⟩
    simp only [← Finset.inf_eq_infi, ← SetLike.mem_coe, ← Submodule.mem_infi] at hr
    exact hs (Or.inr <| Set.mem_bUnion hjt <| add_sub_cancel' r s ▸ (f j).sub_mem hj <| hr j hjt)
    

/-- Prime avoidance. Atiyah-Macdonald 1.11, Eisenbud 3.3, Stacks 00DS, Matsumura Ex.1.6. -/
theorem subset_union_prime {R : Type u} [CommRingₓ R] {s : Finset ι} {f : ι → Ideal R} (a b : ι)
    (hp : ∀, ∀ i ∈ s, ∀, i ≠ a → i ≠ b → IsPrime (f i)) {I : Ideal R} :
    ((I : Set R) ⊆ ⋃ i ∈ (↑s : Set ι), f i) ↔ ∃ i ∈ s, I ≤ f i :=
  suffices ((I : Set R) ⊆ ⋃ i ∈ (↑s : Set ι), f i) → ∃ i, i ∈ s ∧ I ≤ f i from
    ⟨fun h => bex_def.2 <| this h, fun ⟨i, his, hi⟩ =>
      Set.Subset.trans hi <| Set.subset_bUnion_of_mem <| show i ∈ (↑s : Set ι) from his⟩
  fun h : (I : Set R) ⊆ ⋃ i ∈ (↑s : Set ι), f i => by
  classical
  by_cases' has : a ∈ s
  · obtain ⟨t, hat, rfl⟩ : ∃ t, a ∉ t ∧ insert a t = s := ⟨s.erase a, Finset.not_mem_erase a s, Finset.insert_erase has⟩
    by_cases' hbt : b ∈ t
    · obtain ⟨u, hbu, rfl⟩ : ∃ u, b ∉ u ∧ insert b u = t :=
        ⟨t.erase b, Finset.not_mem_erase b t, Finset.insert_erase hbt⟩
      have hp' : ∀, ∀ i ∈ u, ∀, is_prime (f i) := by
        intro i hiu
        refine' hp i (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hiu)) _ _ <;>
          rintro rfl <;> solve_by_elim only [← Finset.mem_insert_of_mem, *]
      rw [Finset.coe_insert, Finset.coe_insert, Set.bUnion_insert, Set.bUnion_insert, ← Set.union_assoc,
        subset_union_prime' hp', bex_def] at h
      rwa [Finset.exists_mem_insert, Finset.exists_mem_insert]
      
    · have hp' : ∀, ∀ j ∈ t, ∀, is_prime (f j) := by
        intro j hj
        refine' hp j (Finset.mem_insert_of_mem hj) _ _ <;>
          rintro rfl <;> solve_by_elim only [← Finset.mem_insert_of_mem, *]
      rw [Finset.coe_insert, Set.bUnion_insert, ← Set.union_self (f a : Set R), subset_union_prime' hp', ← or_assoc,
        or_selfₓ, bex_def] at h
      rwa [Finset.exists_mem_insert]
      
    
  · by_cases' hbs : b ∈ s
    · obtain ⟨t, hbt, rfl⟩ : ∃ t, b ∉ t ∧ insert b t = s :=
        ⟨s.erase b, Finset.not_mem_erase b s, Finset.insert_erase hbs⟩
      have hp' : ∀, ∀ j ∈ t, ∀, is_prime (f j) := by
        intro j hj
        refine' hp j (Finset.mem_insert_of_mem hj) _ _ <;>
          rintro rfl <;> solve_by_elim only [← Finset.mem_insert_of_mem, *]
      rw [Finset.coe_insert, Set.bUnion_insert, ← Set.union_self (f b : Set R), subset_union_prime' hp', ← or_assoc,
        or_selfₓ, bex_def] at h
      rwa [Finset.exists_mem_insert]
      
    cases' s.eq_empty_or_nonempty with hse hsne
    · subst hse
      rw [Finset.coe_empty, Set.bUnion_empty, Set.subset_empty_iff] at h
      have : (I : Set R) ≠ ∅ := Set.Nonempty.ne_empty (Set.nonempty_of_mem I.zero_mem)
      exact absurd h this
      
    · cases' hsne.bex with i his
      obtain ⟨t, hit, rfl⟩ : ∃ t, i ∉ t ∧ insert i t = s :=
        ⟨s.erase i, Finset.not_mem_erase i s, Finset.insert_erase his⟩
      have hp' : ∀, ∀ j ∈ t, ∀, is_prime (f j) := by
        intro j hj
        refine' hp j (Finset.mem_insert_of_mem hj) _ _ <;>
          rintro rfl <;> solve_by_elim only [← Finset.mem_insert_of_mem, *]
      rw [Finset.coe_insert, Set.bUnion_insert, ← Set.union_self (f i : Set R), subset_union_prime' hp', ← or_assoc,
        or_selfₓ, bex_def] at h
      rwa [Finset.exists_mem_insert]
      
    

section Dvd

/-- If `I` divides `J`, then `I` contains `J`.

In a Dedekind domain, to divide and contain are equivalent, see `ideal.dvd_iff_le`.
-/
theorem le_of_dvd {I J : Ideal R} : I ∣ J → J ≤ I
  | ⟨K, h⟩ => h.symm ▸ le_transₓ mul_le_inf inf_le_left

theorem is_unit_iff {I : Ideal R} : IsUnit I ↔ I = ⊤ :=
  is_unit_iff_dvd_one.trans
    ((@one_eq_top R _).symm ▸
      ⟨fun h => eq_top_iff.mpr (Ideal.le_of_dvd h), fun h =>
        ⟨⊤, by
          rw [mul_top, h]⟩⟩)

instance uniqueUnits : Unique (Ideal R)ˣ where
  default := 1
  uniq := fun u =>
    Units.ext
      (show (u : Ideal R) = 1 by
        rw [is_unit_iff.mp u.is_unit, one_eq_top])

end Dvd

end MulAndRadical

section MapAndComap

variable {R : Type u} {S : Type v}

section Semiringₓ

variable {F : Type _} [Semiringₓ R] [Semiringₓ S]

variable [rc : RingHomClass F R S]

variable (f : F)

variable {I J : Ideal R} {K L : Ideal S}

include rc

/-- `I.map f` is the span of the image of the ideal `I` under `f`, which may be bigger than
  the image itself. -/
def map (I : Ideal R) : Ideal S :=
  span (f '' I)

/-- `I.comap f` is the preimage of `I` under `f`. -/
def comap (I : Ideal S) : Ideal R where
  Carrier := f ⁻¹' I
  add_mem' := fun x y hx hy => by
    simp only [← Set.mem_preimage, ← SetLike.mem_coe, ← map_add, ← add_mem hx hy] at *
  zero_mem' := by
    simp only [← Set.mem_preimage, ← map_zero, ← SetLike.mem_coe, ← Submodule.zero_mem]
  smul_mem' := fun c x hx => by
    simp only [← smul_eq_mul, ← Set.mem_preimage, ← map_mul, ← SetLike.mem_coe] at *
    exact mul_mem_left I _ hx

variable {f}

theorem map_mono (h : I ≤ J) : map f I ≤ map f J :=
  span_mono <| Set.image_subset _ h

theorem mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : x ∈ I) : f x ∈ map f I :=
  subset_span ⟨x, h, rfl⟩

theorem apply_coe_mem_map (f : F) (I : Ideal R) (x : I) : f x ∈ I.map f :=
  mem_map_of_mem f x.Prop

theorem map_le_iff_le_comap : map f I ≤ K ↔ I ≤ comap f K :=
  span_le.trans Set.image_subset_iff

@[simp]
theorem mem_comap {x} : x ∈ comap f K ↔ f x ∈ K :=
  Iff.rfl

theorem comap_mono (h : K ≤ L) : comap f K ≤ comap f L :=
  Set.preimage_mono fun x hx => h hx

variable (f)

theorem comap_ne_top (hK : K ≠ ⊤) : comap f K ≠ ⊤ :=
  (ne_top_iff_one _).2 <| by
    rw [mem_comap, map_one] <;> exact (ne_top_iff_one _).1 hK

variable {G : Type _} [rcg : RingHomClass G S R]

include rcg

theorem map_le_comap_of_inv_on (g : G) (I : Ideal R) (hf : Set.LeftInvOn g f I) : I.map f ≤ I.comap g := by
  refine' Ideal.span_le.2 _
  rintro x ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_comap, hf hx]
  exact hx

theorem comap_le_map_of_inv_on (g : G) (I : Ideal S) (hf : Set.LeftInvOn g f (f ⁻¹' I)) : I.comap f ≤ I.map g :=
  fun x (hx : f x ∈ I) => hf hx ▸ Ideal.mem_map_of_mem g hx

/-- The `ideal` version of `set.image_subset_preimage_of_inverse`. -/
theorem map_le_comap_of_inverse (g : G) (I : Ideal R) (h : Function.LeftInverse g f) : I.map f ≤ I.comap g :=
  map_le_comap_of_inv_on _ _ _ <| h.LeftInvOn _

/-- The `ideal` version of `set.preimage_subset_image_of_inverse`. -/
theorem comap_le_map_of_inverse (g : G) (I : Ideal S) (h : Function.LeftInverse g f) : I.comap f ≤ I.map g :=
  comap_le_map_of_inv_on _ _ _ <| h.LeftInvOn _

omit rcg

instance IsPrime.comap [hK : K.IsPrime] : (comap f K).IsPrime :=
  ⟨comap_ne_top _ hK.1, fun x y => by
    simp only [← mem_comap, ← map_mul] <;> apply hK.2⟩

variable (I J K L)

theorem map_top : map f ⊤ = ⊤ :=
  (eq_top_iff_one _).2 <| subset_span ⟨1, trivialₓ, map_one f⟩

variable (f)

theorem gc_map_comap : GaloisConnection (Ideal.map f) (Ideal.comap f) := fun I J => Ideal.map_le_iff_le_comap

omit rc

@[simp]
theorem comap_id : I.comap (RingHom.id R) = I :=
  Ideal.ext fun _ => Iff.rfl

@[simp]
theorem map_id : I.map (RingHom.id R) = I :=
  (gc_map_comap (RingHom.id R)).l_unique GaloisConnection.id comap_id

theorem comap_comap {T : Type _} [Semiringₓ T] {I : Ideal T} (f : R →+* S) (g : S →+* T) :
    (I.comap g).comap f = I.comap (g.comp f) :=
  rfl

theorem map_map {T : Type _} [Semiringₓ T] {I : Ideal R} (f : R →+* S) (g : S →+* T) :
    (I.map f).map g = I.map (g.comp f) :=
  ((gc_map_comap f).compose (gc_map_comap g)).l_unique (gc_map_comap (g.comp f)) fun _ => comap_comap _ _

include rc

theorem map_span (f : F) (s : Set R) : map f (span s) = span (f '' s) :=
  symm <|
    Submodule.span_eq_of_le _ (fun y ⟨x, hy, x_eq⟩ => x_eq ▸ mem_map_of_mem f (subset_span hy))
      (map_le_iff_le_comap.2 <| span_le.2 <| Set.image_subset_iff.1 subset_span)

variable {f I J K L}

theorem map_le_of_le_comap : I ≤ K.comap f → I.map f ≤ K :=
  (gc_map_comap f).l_le

theorem le_comap_of_map_le : I.map f ≤ K → I ≤ K.comap f :=
  (gc_map_comap f).le_u

theorem le_comap_map : I ≤ (I.map f).comap f :=
  (gc_map_comap f).le_u_l _

theorem map_comap_le : (K.comap f).map f ≤ K :=
  (gc_map_comap f).l_u_le _

@[simp]
theorem comap_top : (⊤ : Ideal S).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[simp]
theorem comap_eq_top_iff {I : Ideal S} : I.comap f = ⊤ ↔ I = ⊤ :=
  ⟨fun h => I.eq_top_iff_one.mpr (map_one f ▸ mem_comap.mp ((I.comap f).eq_top_iff_one.mp h)), fun h => by
    rw [h, comap_top]⟩

@[simp]
theorem map_bot : (⊥ : Ideal R).map f = ⊥ :=
  (gc_map_comap f).l_bot

variable (f I J K L)

@[simp]
theorem map_comap_map : ((I.map f).comap f).map f = I.map f :=
  (gc_map_comap f).l_u_l_eq_l I

@[simp]
theorem comap_map_comap : ((K.comap f).map f).comap f = K.comap f :=
  (gc_map_comap f).u_l_u_eq_u K

theorem map_sup : (I⊔J).map f = I.map f⊔J.map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

theorem comap_inf : comap f (K⊓L) = comap f K⊓comap f L :=
  rfl

variable {ι : Sort _}

theorem map_supr (K : ι → Ideal R) : (supr K).map f = ⨆ i, (K i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_supr

theorem comap_infi (K : ι → Ideal S) : (infi K).comap f = ⨅ i, (K i).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_infi

theorem map_Sup (s : Set (Ideal R)) : (sup s).map f = ⨆ I ∈ s, (I : Ideal R).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_Sup

theorem comap_Inf (s : Set (Ideal S)) : (inf s).comap f = ⨅ I ∈ s, (I : Ideal S).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_Inf

theorem comap_Inf' (s : Set (Ideal S)) : (inf s).comap f = ⨅ I ∈ comap f '' s, I :=
  trans (comap_Inf f s)
    (by
      rw [infi_image])

theorem comap_is_prime [H : IsPrime K] : IsPrime (comap f K) :=
  ⟨comap_ne_top f H.ne_top, fun x y h =>
    H.mem_or_mem <| by
      rwa [mem_comap, map_mul] at h⟩

variable {I J K L}

theorem map_inf_le : map f (I⊓J) ≤ map f I⊓map f J :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_l.map_inf_le _ _

theorem le_comap_sup : comap f K⊔comap f L ≤ comap f (K⊔L) :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_u.le_map_sup _ _

omit rc

@[simp]
theorem smul_top_eq_map {R S : Type _} [CommSemiringₓ R] [CommSemiringₓ S] [Algebra R S] (I : Ideal R) :
    I • (⊤ : Submodule R S) = (I.map (algebraMap R S)).restrictScalars R := by
  refine' le_antisymmₓ (submodule.smul_le.mpr fun r hr y _ => _) fun x hx => Submodule.span_induction hx _ _ _ _
  · rw [Algebra.smul_def]
    exact mul_mem_right _ _ (mem_map_of_mem _ hr)
    
  · rintro _ ⟨x, hx, rfl⟩
    rw [← mul_oneₓ (algebraMap R S x), ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hx Submodule.mem_top
    
  · exact Submodule.zero_mem _
    
  · intro x y
    exact Submodule.add_mem _
    
  intro a x hx
  refine' Submodule.smul_induction_on hx _ _
  · intro r hr s hs
    rw [smul_comm]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
    
  · intro x y hx hy
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
    

section Surjective

variable (hf : Function.Surjective f)

include hf

open Function

theorem map_comap_of_surjective (I : Ideal S) : map f (comap f I) = I :=
  le_antisymmₓ (map_le_iff_le_comap.2 le_rfl) fun s hsi =>
    let ⟨r, hfrs⟩ := hf s
    hfrs ▸ (mem_map_of_mem f <| show f r ∈ I from hfrs.symm ▸ hsi)

/-- `map` and `comap` are adjoint, and the composition `map f ∘ comap f` is the
  identity -/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  GaloisInsertion.monotoneIntro (gc_map_comap f).monotone_u (gc_map_comap f).monotone_l (fun _ => le_comap_map)
    (map_comap_of_surjective _ hf)

theorem map_surjective_of_surjective : Surjective (map f) :=
  (giMapComap f hf).l_surjective

theorem comap_injective_of_surjective : Injective (comap f) :=
  (giMapComap f hf).u_injective

theorem map_sup_comap_of_surjective (I J : Ideal S) : (I.comap f⊔J.comap f).map f = I⊔J :=
  (giMapComap f hf).l_sup_u _ _

theorem map_supr_comap_of_surjective (K : ι → Ideal S) : (⨆ i, (K i).comap f).map f = supr K :=
  (giMapComap f hf).l_supr_u _

theorem map_inf_comap_of_surjective (I J : Ideal S) : (I.comap f⊓J.comap f).map f = I⊓J :=
  (giMapComap f hf).l_inf_u _ _

theorem map_infi_comap_of_surjective (K : ι → Ideal S) : (⨅ i, (K i).comap f).map f = infi K :=
  (giMapComap f hf).l_infi_u _

theorem mem_image_of_mem_map_of_surjective {I : Ideal R} {y} (H : y ∈ map f I) : y ∈ f '' I :=
  Submodule.span_induction H (fun _ => id) ⟨0, I.zero_mem, map_zero f⟩
    (fun y1 y2 ⟨x1, hx1i, hxy1⟩ ⟨x2, hx2i, hxy2⟩ => ⟨x1 + x2, I.add_mem hx1i hx2i, hxy1 ▸ hxy2 ▸ map_add f _ _⟩)
    fun c y ⟨x, hxi, hxy⟩ =>
    let ⟨d, hdc⟩ := hf c
    ⟨d * x, I.mul_mem_left _ hxi, hdc ▸ hxy ▸ map_mul f _ _⟩

theorem mem_map_iff_of_surjective {I : Ideal R} {y} : y ∈ map f I ↔ ∃ x, x ∈ I ∧ f x = y :=
  ⟨fun h => (Set.mem_image _ _ _).2 (mem_image_of_mem_map_of_surjective f hf h), fun ⟨x, hx⟩ =>
    hx.right ▸ mem_map_of_mem f hx.left⟩

theorem le_map_of_comap_le_of_surjective : comap f K ≤ I → K ≤ map f I := fun h =>
  map_comap_of_surjective f hf K ▸ map_mono h

end Surjective

section Injective

variable (hf : Function.Injective f)

include hf

theorem comap_bot_le_of_injective : comap f ⊥ ≤ I := by
  refine' le_transₓ (fun x hx => _) bot_le
  rw [mem_comap, Submodule.mem_bot, ← map_zero f] at hx
  exact Eq.symm (hf hx) ▸ Submodule.zero_mem ⊥

end Injective

end Semiringₓ

section Ringₓ

variable {F : Type _} [Ringₓ R] [Ringₓ S]

variable [RingHomClass F R S] (f : F) {I : Ideal R}

section Surjective

variable (hf : Function.Surjective f)

include hf

theorem comap_map_of_surjective (I : Ideal R) : comap f (map f I) = I⊔comap f ⊥ :=
  le_antisymmₓ
    (fun r h =>
      let ⟨s, hsi, hfsr⟩ := mem_image_of_mem_map_of_surjective f hf h
      Submodule.mem_sup.2
        ⟨s, hsi, r - s,
          (Submodule.mem_bot S).2 <| by
            rw [map_sub, hfsr, sub_self],
          add_sub_cancel'_right s r⟩)
    (sup_le (map_le_iff_le_comap.1 le_rfl) (comap_mono bot_le))

/-- Correspondence theorem -/
def relIsoOfSurjective : Ideal S ≃o { p : Ideal R // comap f ⊥ ≤ p } where
  toFun := fun J => ⟨comap f J, comap_mono bot_le⟩
  invFun := fun I => map f I.1
  left_inv := fun J => map_comap_of_surjective f hf J
  right_inv := fun I =>
    Subtype.eq <|
      show comap f (map f I.1) = I.1 from
        (comap_map_of_surjective f hf I).symm ▸ le_antisymmₓ (sup_le le_rfl I.2) le_sup_left
  map_rel_iff' := fun I1 I2 =>
    ⟨fun H => map_comap_of_surjective f hf I1 ▸ map_comap_of_surjective f hf I2 ▸ map_mono H, comap_mono⟩

/-- The map on ideals induced by a surjective map preserves inclusion. -/
def orderEmbeddingOfSurjective : Ideal S ↪o Ideal R :=
  (relIsoOfSurjective f hf).toRelEmbedding.trans (Subtype.relEmbedding _ _)

theorem map_eq_top_or_is_maximal_of_surjective {I : Ideal R} (H : IsMaximal I) : map f I = ⊤ ∨ IsMaximal (map f I) := by
  refine' or_iff_not_imp_left.2 fun ne_top => ⟨⟨fun h => ne_top h, fun J hJ => _⟩⟩
  · refine'
      (rel_iso_of_surjective f hf).Injective
        (Subtype.ext_iff.2 (Eq.trans (H.1.2 (comap f J) (lt_of_le_of_neₓ _ _)) comap_top.symm))
    · exact map_le_iff_le_comap.1 (le_of_ltₓ hJ)
      
    · exact fun h => hJ.right (le_map_of_comap_le_of_surjective f hf (le_of_eqₓ h.symm))
      
    

theorem comap_is_maximal_of_surjective {K : Ideal S} [H : IsMaximal K] : IsMaximal (comap f K) := by
  refine' ⟨⟨comap_ne_top _ H.1.1, fun J hJ => _⟩⟩
  suffices map f J = ⊤ by
    replace this := congr_arg (comap f) this
    rw [comap_top, comap_map_of_surjective _ hf, eq_top_iff] at this
    rw [eq_top_iff]
    exact le_transₓ this (sup_le (le_of_eqₓ rfl) (le_transₓ (comap_mono bot_le) (le_of_ltₓ hJ)))
  refine'
    H.1.2 (map f J)
      (lt_of_le_of_neₓ (le_map_of_comap_le_of_surjective _ hf (le_of_ltₓ hJ)) fun h =>
        ne_of_ltₓ hJ (trans (congr_arg (comap f) h) _))
  rw [comap_map_of_surjective _ hf, sup_eq_left]
  exact le_transₓ (comap_mono bot_le) (le_of_ltₓ hJ)

theorem comap_le_comap_iff_of_surjective (I J : Ideal S) : comap f I ≤ comap f J ↔ I ≤ J :=
  ⟨fun h => (map_comap_of_surjective f hf I).symm.le.trans (map_le_of_le_comap h), fun h =>
    le_comap_of_map_le ((map_comap_of_surjective f hf I).le.trans h)⟩

end Surjective

/-- If `f : R ≃+* S` is a ring isomorphism and `I : ideal R`, then `map f (map f.symm) = I`. -/
@[simp]
theorem map_of_equiv (I : Ideal R) (f : R ≃+* S) : (I.map (f : R →+* S)).map (f.symm : S →+* R) = I := by
  simp [RingEquiv.to_ring_hom_eq_coe, ← map_map]

/-- If `f : R ≃+* S` is a ring isomorphism and `I : ideal R`, then `comap f.symm (comap f) = I`. -/
@[simp]
theorem comap_of_equiv (I : Ideal R) (f : R ≃+* S) : (I.comap (f.symm : S →+* R)).comap (f : R →+* S) = I := by
  simp [RingEquiv.to_ring_hom_eq_coe, ← comap_comap]

/-- If `f : R ≃+* S` is a ring isomorphism and `I : ideal R`, then `map f I = comap f.symm I`. -/
theorem map_comap_of_equiv (I : Ideal R) (f : R ≃+* S) : I.map (f : R →+* S) = I.comap f.symm :=
  le_antisymmₓ (le_comap_of_map_le (map_of_equiv I f).le)
    (le_map_of_comap_le_of_surjective _ f.Surjective (comap_of_equiv I f).le)

section Bijective

variable (hf : Function.Bijective f)

include hf

/-- Special case of the correspondence theorem for isomorphic rings -/
def relIsoOfBijective : Ideal S ≃o Ideal R where
  toFun := comap f
  invFun := map f
  left_inv := (relIsoOfSurjective f hf.right).left_inv
  right_inv := fun J =>
    Subtype.ext_iff.1 ((relIsoOfSurjective f hf.right).right_inv ⟨J, comap_bot_le_of_injective f hf.left⟩)
  map_rel_iff' := (relIsoOfSurjective f hf.right).map_rel_iff'

theorem comap_le_iff_le_map {I : Ideal R} {K : Ideal S} : comap f K ≤ I ↔ K ≤ map f I :=
  ⟨fun h => le_map_of_comap_le_of_surjective f hf.right h, fun h => (relIsoOfBijective f hf).right_inv I ▸ comap_mono h⟩

theorem map.is_maximal {I : Ideal R} (H : IsMaximal I) : IsMaximal (map f I) := by
  refine' or_iff_not_imp_left.1 (map_eq_top_or_is_maximal_of_surjective f hf.right H) fun h => H.1.1 _ <;>
    calc I = comap f (map f I) := ((rel_iso_of_bijective f hf).right_inv I).symm _ = comap f ⊤ := by
        rw [h]_ = ⊤ := by
        rw [comap_top]

end Bijective

theorem RingEquiv.bot_maximal_iff (e : R ≃+* S) : (⊥ : Ideal R).IsMaximal ↔ (⊥ : Ideal S).IsMaximal :=
  ⟨fun h => @map_bot _ _ _ _ _ _ e.toRingHom ▸ map.is_maximal e.toRingHom e.Bijective h, fun h =>
    @map_bot _ _ _ _ _ _ e.symm.toRingHom ▸ map.is_maximal e.symm.toRingHom e.symm.Bijective h⟩

end Ringₓ

section CommRingₓ

variable {F : Type _} [CommRingₓ R] [CommRingₓ S]

variable [rc : RingHomClass F R S]

variable (f : F)

variable {I J : Ideal R} {K L : Ideal S}

variable (I J K L)

include rc

theorem map_mul : map f (I * J) = map f I * map f J :=
  le_antisymmₓ
    (map_le_iff_le_comap.2 <|
      mul_le.2 fun r hri s hsj =>
        show f (r * s) ∈ _ by
          rw [map_mul] <;> exact mul_mem_mul (mem_map_of_mem f hri) (mem_map_of_mem f hsj))
    (trans_rel_right _ (span_mul_span _ _) <|
      span_le.2 <|
        Set.Union₂_subset fun i ⟨r, hri, hfri⟩ =>
          Set.Union₂_subset fun j ⟨s, hsj, hfsj⟩ =>
            Set.singleton_subset_iff.2 <|
              hfri ▸
                hfsj ▸ by
                  rw [← map_mul] <;> exact mem_map_of_mem f (mul_mem_mul hri hsj))

/-- The pushforward `ideal.map` as a monoid-with-zero homomorphism. -/
@[simps]
def mapHom : Ideal R →*₀ Ideal S where
  toFun := map f
  map_mul' := fun I J => Ideal.map_mul f I J
  map_one' := by
    convert Ideal.map_top f <;> exact one_eq_top
  map_zero' := Ideal.map_bot

protected theorem map_pow (n : ℕ) : map f (I ^ n) = map f I ^ n :=
  map_pow (mapHom f) I n

theorem comap_radical : comap f (radical K) = radical (comap f K) :=
  le_antisymmₓ (fun r ⟨n, hfrnk⟩ => ⟨n, show f (r ^ n) ∈ K from (map_pow f r n).symm ▸ hfrnk⟩) fun r ⟨n, hfrnk⟩ =>
    ⟨n, map_pow f r n ▸ hfrnk⟩

omit rc

@[simp]
theorem map_quotient_self : map (Quotient.mk I) I = ⊥ :=
  eq_bot_iff.2 <|
    Ideal.map_le_iff_le_comap.2 fun x hx => (Submodule.mem_bot (R ⧸ I)).2 <| Ideal.Quotient.eq_zero_iff_mem.2 hx

variable {I J K L}

include rc

theorem map_radical_le : map f (radical I) ≤ radical (map f I) :=
  map_le_iff_le_comap.2 fun r ⟨n, hrni⟩ => ⟨n, map_pow f r n ▸ mem_map_of_mem f hrni⟩

theorem le_comap_mul : comap f K * comap f L ≤ comap f (K * L) :=
  map_le_iff_le_comap.1 <|
    (map_mul f (comap f K) (comap f L)).symm ▸
      mul_mono (map_le_iff_le_comap.2 <| le_rfl) (map_le_iff_le_comap.2 <| le_rfl)

omit rc

end CommRingₓ

end MapAndComap

section IsPrimary

variable {R : Type u} [CommSemiringₓ R]

/-- A proper ideal `I` is primary iff `xy ∈ I` implies `x ∈ I` or `y ∈ radical I`. -/
def IsPrimary (I : Ideal R) : Prop :=
  I ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ I → x ∈ I ∨ y ∈ radical I

theorem IsPrime.is_primary {I : Ideal R} (hi : IsPrime I) : IsPrimary I :=
  ⟨hi.1, fun x y hxy => ((hi.mem_or_mem hxy).imp id) fun hyi => le_radical hyi⟩

theorem mem_radical_of_pow_mem {I : Ideal R} {x : R} {m : ℕ} (hx : x ^ m ∈ radical I) : x ∈ radical I :=
  radical_idem I ▸ ⟨m, hx⟩

theorem is_prime_radical {I : Ideal R} (hi : IsPrimary I) : IsPrime (radical I) :=
  ⟨mt radical_eq_top.1 hi.1, fun x y ⟨m, hxy⟩ => by
    rw [mul_powₓ] at hxy
    cases hi.2 hxy
    · exact Or.inl ⟨m, h⟩
      
    · exact Or.inr (mem_radical_of_pow_mem h)
      ⟩

theorem is_primary_inf {I J : Ideal R} (hi : IsPrimary I) (hj : IsPrimary J) (hij : radical I = radical J) :
    IsPrimary (I⊓J) :=
  ⟨ne_of_ltₓ <| lt_of_le_of_ltₓ inf_le_left (lt_top_iff_ne_top.2 hi.1), fun x y ⟨hxyi, hxyj⟩ => by
    rw [radical_inf, hij, inf_idem]
    cases' hi.2 hxyi with hxi hyi
    cases' hj.2 hxyj with hxj hyj
    · exact Or.inl ⟨hxi, hxj⟩
      
    · exact Or.inr hyj
      
    · rw [hij] at hyi
      exact Or.inr hyi
      ⟩

end IsPrimary

end Ideal

theorem Associates.mk_ne_zero' {R : Type _} [CommSemiringₓ R] {r : R} :
    Associates.mk (Ideal.span {r} : Ideal R) ≠ 0 ↔ r ≠ 0 := by
  rw [Associates.mk_ne_zero, Ideal.zero_eq_bot, Ne.def, Ideal.span_singleton_eq_bot]

namespace RingHom

variable {R : Type u} {S : Type v} {T : Type v}

section Semiringₓ

variable {F : Type _} {G : Type _} [Semiringₓ R] [Semiringₓ S] [Semiringₓ T]

variable [rcf : RingHomClass F R S] [rcg : RingHomClass G T S] (f : F) (g : G)

include rcf

/-- Kernel of a ring homomorphism as an ideal of the domain. -/
def ker : Ideal R :=
  Ideal.comap f ⊥

/-- An element is in the kernel if and only if it maps to zero.-/
theorem mem_ker {r} : r ∈ ker f ↔ f r = 0 := by
  rw [ker, Ideal.mem_comap, Submodule.mem_bot]

theorem ker_eq : (ker f : Set R) = Set.Preimage f {0} :=
  rfl

theorem ker_eq_comap_bot (f : F) : ker f = Ideal.comap f ⊥ :=
  rfl

omit rcf

theorem comap_ker (f : S →+* R) (g : T →+* S) : f.ker.comap g = (f.comp g).ker := by
  rw [RingHom.ker_eq_comap_bot, Ideal.comap_comap, RingHom.ker_eq_comap_bot]

include rcf

/-- If the target is not the zero ring, then one is not in the kernel.-/
theorem not_one_mem_ker [Nontrivial S] (f : F) : (1 : R) ∉ ker f := by
  rw [mem_ker, map_one]
  exact one_ne_zero

theorem ker_ne_top [Nontrivial S] (f : F) : ker f ≠ ⊤ :=
  (Ideal.ne_top_iff_one _).mpr <| not_one_mem_ker f

omit rcf

end Semiringₓ

section Ringₓ

variable {F : Type _} [Ringₓ R] [Semiringₓ S] [rc : RingHomClass F R S] (f : F)

include rc

theorem injective_iff_ker_eq_bot : Function.Injective f ↔ ker f = ⊥ := by
  rw [SetLike.ext'_iff, ker_eq, Set.ext_iff]
  exact injective_iff_map_eq_zero' f

theorem ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ ∀ x, f x = 0 → x = 0 := by
  rw [← injective_iff_map_eq_zero f, injective_iff_ker_eq_bot]

omit rc

@[simp]
theorem ker_coe_equiv (f : R ≃+* S) : ker (f : R →+* S) = ⊥ := by
  simpa only [injective_iff_ker_eq_bot] using EquivLike.injective f

@[simp]
theorem ker_equiv {F' : Type _} [RingEquivClass F' R S] (f : F') : ker f = ⊥ := by
  simpa only [injective_iff_ker_eq_bot] using EquivLike.injective f

end Ringₓ

section CommRingₓ

variable [CommRingₓ R] [CommRingₓ S] (f : R →+* S)

/-- The induced map from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotient_ker_equiv_of_right_inverse`) /
is surjective (`quotient_ker_equiv_of_surjective`).
-/
def kerLift (f : R →+* S) : R ⧸ f.ker →+* S :=
  (Ideal.Quotient.lift _ f) fun r => f.mem_ker.mp

@[simp]
theorem ker_lift_mk (f : R →+* S) (r : R) : kerLift f (Ideal.Quotient.mk f.ker r) = f r :=
  Ideal.Quotient.lift_mk _ _ _

/-- The induced map from the quotient by the kernel is injective. -/
theorem ker_lift_injective (f : R →+* S) : Function.Injective (kerLift f) := fun a b =>
  (Quotientₓ.induction_on₂' a b) fun a b (h : f a = f b) =>
    Ideal.Quotient.eq.2 <|
      show a - b ∈ ker f by
        rw [mem_ker, map_sub, h, sub_self]

variable {f}

/-- The **first isomorphism theorem** for commutative rings, computable version. -/
def quotientKerEquivOfRightInverse {g : S → R} (hf : Function.RightInverse g f) : R ⧸ f.ker ≃+* S :=
  { kerLift f with toFun := kerLift f, invFun := Ideal.Quotient.mk f.ker ∘ g,
    left_inv := by
      rintro ⟨x⟩
      apply ker_lift_injective
      simp [← hf (f x)],
    right_inv := hf }

@[simp]
theorem quotientKerEquivOfRightInverse.apply {g : S → R} (hf : Function.RightInverse g f) (x : R ⧸ f.ker) :
    quotientKerEquivOfRightInverse hf x = kerLift f x :=
  rfl

@[simp]
theorem quotientKerEquivOfRightInverse.Symm.apply {g : S → R} (hf : Function.RightInverse g f) (x : S) :
    (quotientKerEquivOfRightInverse hf).symm x = Ideal.Quotient.mk f.ker (g x) :=
  rfl

/-- The **first isomorphism theorem** for commutative rings. -/
noncomputable def quotientKerEquivOfSurjective (hf : Function.Surjective f) : R ⧸ f.ker ≃+* S :=
  quotientKerEquivOfRightInverse (Classical.some_spec hf.HasRightInverse)

end CommRingₓ

/-- The kernel of a homomorphism to a domain is a prime ideal. -/
theorem ker_is_prime {F : Type _} [Ringₓ R] [Ringₓ S] [IsDomain S] [RingHomClass F R S] (f : F) : (ker f).IsPrime :=
  ⟨by
    rw [Ne.def, Ideal.eq_top_iff_one]
    exact not_one_mem_ker f, fun x y => by
    simpa only [← mem_ker, ← map_mul] using @eq_zero_or_eq_zero_of_mul_eq_zero S _ _ _ _ _⟩

/-- The kernel of a homomorphism to a field is a maximal ideal. -/
theorem ker_is_maximal_of_surjective {R K F : Type _} [Ringₓ R] [Field K] [RingHomClass F R K] (f : F)
    (hf : Function.Surjective f) : (ker f).IsMaximal := by
  refine'
    ideal.is_maximal_iff.mpr ⟨fun h1 => @one_ne_zero K _ _ <| map_one f ▸ (mem_ker f).mp h1, fun J x hJ hxf hxJ => _⟩
  obtain ⟨y, hy⟩ := hf (f x)⁻¹
  have H : 1 = y * x - (y * x - 1) := (sub_sub_cancel _ _).symm
  rw [H]
  refine' J.sub_mem (J.mul_mem_left _ hxJ) (hJ _)
  rw [mem_ker]
  simp only [← hy, ← map_sub, ← map_one, ← map_mul, ← inv_mul_cancel (mt (mem_ker f).mpr hxf), ← sub_self]

end RingHom

namespace Ideal

variable {R : Type _} {S : Type _} {F : Type _}

section Semiringₓ

variable [Semiringₓ R] [Semiringₓ S] [rc : RingHomClass F R S]

include rc

theorem map_eq_bot_iff_le_ker {I : Ideal R} (f : F) : I.map f = ⊥ ↔ I ≤ RingHom.ker f := by
  rw [RingHom.ker, eq_bot_iff, map_le_iff_le_comap]

theorem ker_le_comap {K : Ideal S} (f : F) : RingHom.ker f ≤ comap f K := fun x hx =>
  mem_comap.2 (((RingHom.mem_ker f).1 hx).symm ▸ K.zero_mem)

end Semiringₓ

section Ringₓ

variable [Ringₓ R] [Ringₓ S] [rc : RingHomClass F R S]

include rc

theorem map_Inf {A : Set (Ideal R)} {f : F} (hf : Function.Surjective f) :
    (∀, ∀ J ∈ A, ∀, RingHom.ker f ≤ J) → map f (inf A) = inf (map f '' A) := by
  refine' fun h => le_antisymmₓ (le_Inf _) _
  · intro j hj y hy
    cases' (mem_map_iff_of_surjective f hf).1 hy with x hx
    cases' (Set.mem_image _ _ _).mp hj with J hJ
    rw [← hJ.right, ← hx.right]
    exact mem_map_of_mem f (Inf_le_of_le hJ.left (le_of_eqₓ rfl) hx.left)
    
  · intro y hy
    cases' hf y with x hx
    refine' hx ▸ mem_map_of_mem f _
    have : ∀, ∀ I ∈ A, ∀, y ∈ map f I := by
      simpa using hy
    rw [Submodule.mem_Inf]
    intro J hJ
    rcases(mem_map_iff_of_surjective f hf).1 (this J hJ) with ⟨x', hx', rfl⟩
    have : x - x' ∈ J := by
      apply h J hJ
      rw [RingHom.mem_ker, map_sub, hx, sub_self]
    simpa only [← sub_add_cancel] using J.add_mem this hx'
    

theorem map_is_prime_of_surjective {f : F} (hf : Function.Surjective f) {I : Ideal R} [H : IsPrime I]
    (hk : RingHom.ker f ≤ I) : IsPrime (map f I) := by
  refine' ⟨fun h => H.ne_top (eq_top_iff.2 _), fun x y => _⟩
  · replace h := congr_arg (comap f) h
    rw [comap_map_of_surjective _ hf, comap_top] at h
    exact h ▸ sup_le (le_of_eqₓ rfl) hk
    
  · refine' fun hxy => (hf x).recOn fun a ha => (hf y).recOn fun b hb => _
    rw [← ha, ← hb, ← _root_.map_mul f, mem_map_iff_of_surjective _ hf] at hxy
    rcases hxy with ⟨c, hc, hc'⟩
    rw [← sub_eq_zero, ← map_sub] at hc'
    have : a * b ∈ I := by
      convert I.sub_mem hc (hk (hc' : c - a * b ∈ RingHom.ker f))
      abel
    exact (H.mem_or_mem this).imp (fun h => ha ▸ mem_map_of_mem f h) fun h => hb ▸ mem_map_of_mem f h
    

omit rc

theorem map_is_prime_of_equiv {F' : Type _} [RingEquivClass F' R S] (f : F') {I : Ideal R} [IsPrime I] :
    IsPrime (map f I) :=
  map_is_prime_of_surjective (EquivLike.surjective f) <| by
    simp only [← RingHom.ker_equiv, ← bot_le]

end Ringₓ

section CommRingₓ

variable [CommRingₓ R] [CommRingₓ S]

@[simp]
theorem mk_ker {I : Ideal R} : (Quotient.mk I).ker = I := by
  ext <;> rw [RingHom.ker, mem_comap, Submodule.mem_bot, quotient.eq_zero_iff_mem]

theorem map_mk_eq_bot_of_le {I J : Ideal R} (h : I ≤ J) : I.map J = ⊥ := by
  rw [map_eq_bot_iff_le_ker, mk_ker]
  exact h

theorem ker_quotient_lift {S : Type v} [CommRingₓ S] {I : Ideal R} (f : R →+* S) (H : I ≤ f.ker) :
    (Ideal.Quotient.lift I f H).ker = f.ker.map I := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := quotient.mk_surjective x
    rw [RingHom.mem_ker, ← hy, Ideal.Quotient.lift_mk, ← RingHom.mem_ker] at hx
    rw [← hy, mem_map_iff_of_surjective I quotient.mk_surjective]
    exact ⟨y, hx, rfl⟩
    
  · intro hx
    rw [mem_map_iff_of_surjective I quotient.mk_surjective] at hx
    obtain ⟨y, hy⟩ := hx
    rw [RingHom.mem_ker, ← hy.right, Ideal.Quotient.lift_mk, ← RingHom.mem_ker f]
    exact hy.left
    

theorem map_eq_iff_sup_ker_eq_of_surjective {I J : Ideal R} (f : R →+* S) (hf : Function.Surjective f) :
    map f I = map f J ↔ I⊔f.ker = J⊔f.ker := by
  rw [← (comap_injective_of_surjective f hf).eq_iff, comap_map_of_surjective f hf, comap_map_of_surjective f hf,
    RingHom.ker_eq_comap_bot]

theorem map_radical_of_surjective {f : R →+* S} (hf : Function.Surjective f) {I : Ideal R} (h : RingHom.ker f ≤ I) :
    map f I.radical = (map f I).radical := by
  rw [radical_eq_Inf, radical_eq_Inf]
  have : ∀, ∀ J ∈ { J : Ideal R | I ≤ J ∧ J.IsPrime }, ∀, f.ker ≤ J := fun J hJ => le_transₓ h hJ.left
  convert map_Inf hf this
  refine' funext fun j => propext ⟨_, _⟩
  · rintro ⟨hj, hj'⟩
    have : j.is_prime := hj'
    exact ⟨comap f j, ⟨⟨map_le_iff_le_comap.1 hj, comap_is_prime f j⟩, map_comap_of_surjective f hf j⟩⟩
    
  · rintro ⟨J, ⟨hJ, hJ'⟩⟩
    have : J.is_prime := hJ.right
    refine' ⟨hJ' ▸ map_mono hJ.left, hJ' ▸ map_is_prime_of_surjective hf (le_transₓ h hJ.left)⟩
    

@[simp]
theorem bot_quotient_is_maximal_iff (I : Ideal R) : (⊥ : Ideal (R ⧸ I)).IsMaximal ↔ I.IsMaximal :=
  ⟨fun hI => @mk_ker _ _ I ▸ @comap_is_maximal_of_surjective _ _ _ _ _ _ (Quotient.mk I) Quotient.mk_surjective ⊥ hI,
    fun hI => @bot_is_maximal _ (@Field.toDivisionRing _ (@Quotient.field _ _ I hI))⟩

/-- See also `ideal.mem_quotient_iff_mem` in case `I ≤ J`. -/
@[simp]
theorem mem_quotient_iff_mem_sup {I J : Ideal R} {x : R} : Quotient.mk I x ∈ J.map (Quotient.mk I) ↔ x ∈ J⊔I := by
  rw [← mem_comap, comap_map_of_surjective (Quotientₓ.mk I) quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, mk_ker]

/-- See also `ideal.mem_quotient_iff_mem_sup` if the assumption `I ≤ J` is not available. -/
theorem mem_quotient_iff_mem {I J : Ideal R} (hIJ : I ≤ J) {x : R} : Quotient.mk I x ∈ J.map (Quotient.mk I) ↔ x ∈ J :=
  by
  rw [mem_quotient_iff_mem_sup, sup_eq_left.mpr hIJ]

section QuotientAlgebra

variable (R₁ R₂ : Type _) {A B : Type _}

variable [CommSemiringₓ R₁] [CommSemiringₓ R₂] [CommRingₓ A] [CommRingₓ B]

variable [Algebra R₁ A] [Algebra R₂ A] [Algebra R₁ B]

/-- The `R₁`-algebra structure on `A/I` for an `R₁`-algebra `A` -/
instance Quotient.algebra {I : Ideal A} : Algebra R₁ (A ⧸ I) :=
  { RingHom.comp (Ideal.Quotient.mk I) (algebraMap R₁ A) with toFun := fun x => Ideal.Quotient.mk I (algebraMap R₁ A x),
    smul := (· • ·),
    smul_def' := fun r x =>
      (Quotientₓ.induction_on' x) fun x =>
        ((Quotient.mk I).congr_arg <| Algebra.smul_def _ _).trans (RingHom.map_mul _ _ _),
    commutes' := fun _ _ => mul_comm _ _ }

-- Lean can struggle to find this instance later if we don't provide this shortcut
instance Quotient.is_scalar_tower [HasSmul R₁ R₂] [IsScalarTower R₁ R₂ A] (I : Ideal A) : IsScalarTower R₁ R₂ (A ⧸ I) :=
  by
  infer_instance

/-- The canonical morphism `A →ₐ[R₁] A ⧸ I` as morphism of `R₁`-algebras, for `I` an ideal of
`A`, where `A` is an `R₁`-algebra. -/
def Quotient.mkₐ (I : Ideal A) : A →ₐ[R₁] A ⧸ I :=
  ⟨fun a => Submodule.Quotient.mk a, rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem Quotient.alg_map_eq (I : Ideal A) : algebraMap R₁ (A ⧸ I) = (algebraMap A (A ⧸ I)).comp (algebraMap R₁ A) :=
  rfl

theorem Quotient.mkₐ_to_ring_hom (I : Ideal A) : (Quotient.mkₐ R₁ I).toRingHom = Ideal.Quotient.mk I :=
  rfl

@[simp]
theorem Quotient.mkₐ_eq_mk (I : Ideal A) : ⇑(Quotient.mkₐ R₁ I) = Ideal.Quotient.mk I :=
  rfl

@[simp]
theorem Quotient.algebra_map_eq (I : Ideal R) : algebraMap R (R ⧸ I) = I :=
  rfl

@[simp]
theorem Quotient.mk_comp_algebra_map (I : Ideal A) : (Quotient.mk I).comp (algebraMap R₁ A) = algebraMap R₁ (A ⧸ I) :=
  rfl

@[simp]
theorem Quotient.mk_algebra_map (I : Ideal A) (x : R₁) : Quotient.mk I (algebraMap R₁ A x) = algebraMap R₁ (A ⧸ I) x :=
  rfl

/-- The canonical morphism `A →ₐ[R₁] I.quotient` is surjective. -/
theorem Quotient.mkₐ_surjective (I : Ideal A) : Function.Surjective (Quotient.mkₐ R₁ I) :=
  surjective_quot_mk _

/-- The kernel of `A →ₐ[R₁] I.quotient` is `I`. -/
@[simp]
theorem Quotient.mkₐ_ker (I : Ideal A) : (Quotient.mkₐ R₁ I : A →+* A ⧸ I).ker = I :=
  Ideal.mk_ker

variable {R₁}

theorem KerLift.map_smul (f : A →ₐ[R₁] B) (r : R₁) (x : A ⧸ f.toRingHom.ker) :
    f.toRingHom.kerLift (r • x) = r • f.toRingHom.kerLift x := by
  obtain ⟨a, rfl⟩ := quotient.mkₐ_surjective R₁ _ x
  rw [← AlgHom.map_smul, quotient.mkₐ_eq_mk, RingHom.ker_lift_mk]
  exact f.map_smul _ _

/-- The induced algebras morphism from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotient_ker_alg_equiv_of_right_inverse`) /
is surjective (`quotient_ker_alg_equiv_of_surjective`).
-/
def kerLiftAlg (f : A →ₐ[R₁] B) : A ⧸ f.toRingHom.ker →ₐ[R₁] B :=
  AlgHom.mk' f.toRingHom.kerLift fun _ _ => KerLift.map_smul f _ _

@[simp]
theorem ker_lift_alg_mk (f : A →ₐ[R₁] B) (a : A) : kerLiftAlg f (Quotient.mk f.toRingHom.ker a) = f a :=
  rfl

@[simp]
theorem ker_lift_alg_to_ring_hom (f : A →ₐ[R₁] B) : (kerLiftAlg f).toRingHom = RingHom.kerLift f :=
  rfl

/-- The induced algebra morphism from the quotient by the kernel is injective. -/
theorem ker_lift_alg_injective (f : A →ₐ[R₁] B) : Function.Injective (kerLiftAlg f) :=
  RingHom.ker_lift_injective f

/-- The **first isomorphism** theorem for algebras, computable version. -/
def quotientKerAlgEquivOfRightInverse {f : A →ₐ[R₁] B} {g : B → A} (hf : Function.RightInverse g f) :
    (A ⧸ f.toRingHom.ker) ≃ₐ[R₁] B :=
  { RingHom.quotientKerEquivOfRightInverse fun x => show f.toRingHom (g x) = x from hf x, kerLiftAlg f with }

@[simp]
theorem quotientKerAlgEquivOfRightInverse.apply {f : A →ₐ[R₁] B} {g : B → A} (hf : Function.RightInverse g f)
    (x : A ⧸ f.toRingHom.ker) : quotientKerAlgEquivOfRightInverse hf x = kerLiftAlg f x :=
  rfl

@[simp]
theorem QuotientKerAlgEquivOfRightInverseSymm.apply {f : A →ₐ[R₁] B} {g : B → A} (hf : Function.RightInverse g f)
    (x : B) : (quotientKerAlgEquivOfRightInverse hf).symm x = Quotient.mkₐ R₁ f.toRingHom.ker (g x) :=
  rfl

/-- The **first isomorphism theorem** for algebras. -/
noncomputable def quotientKerAlgEquivOfSurjective {f : A →ₐ[R₁] B} (hf : Function.Surjective f) :
    (A ⧸ f.toRingHom.ker) ≃ₐ[R₁] B :=
  quotientKerAlgEquivOfRightInverse (Classical.some_spec hf.HasRightInverse)

/-- The ring hom `R/I →+* S/J` induced by a ring hom `f : R →+* S` with `I ≤ f⁻¹(J)` -/
def quotientMap {I : Ideal R} (J : Ideal S) (f : R →+* S) (hIJ : I ≤ J.comap f) : R ⧸ I →+* S ⧸ J :=
  Quotient.lift I ((Quotient.mk J).comp f) fun _ ha => by
    simpa [← Function.comp_app, ← RingHom.coe_comp, ← quotient.eq_zero_iff_mem] using hIJ ha

@[simp]
theorem quotient_map_mk {J : Ideal R} {I : Ideal S} {f : R →+* S} {H : J ≤ I.comap f} {x : R} :
    quotientMap I f H (Quotient.mk J x) = Quotient.mk I (f x) :=
  Quotient.lift_mk J _ _

@[simp]
theorem quotient_map_algebra_map {J : Ideal A} {I : Ideal S} {f : A →+* S} {H : J ≤ I.comap f} {x : R₁} :
    quotientMap I f H (algebraMap R₁ (A ⧸ J) x) = Quotient.mk I (f (algebraMap _ _ x)) :=
  Quotient.lift_mk J _ _

theorem quotient_map_comp_mk {J : Ideal R} {I : Ideal S} {f : R →+* S} (H : J ≤ I.comap f) :
    (quotientMap I f H).comp (Quotient.mk J) = (Quotient.mk I).comp f :=
  RingHom.ext fun x => by
    simp only [← Function.comp_app, ← RingHom.coe_comp, ← Ideal.quotient_map_mk]

/-- The ring equiv `R/I ≃+* S/J` induced by a ring equiv `f : R ≃+** S`,  where `J = f(I)`. -/
@[simps]
def quotientEquiv (I : Ideal R) (J : Ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S)) : R ⧸ I ≃+* S ⧸ J :=
  { quotientMap J (↑f)
      (by
        rw [hIJ]
        exact @le_comap_map _ S _ _ _ _ _ _) with
    invFun :=
      quotientMap I (↑f.symm)
        (by
          rw [hIJ]
          exact le_of_eqₓ (map_comap_of_equiv I f)),
    left_inv := by
      rintro ⟨r⟩
      simp ,
    right_inv := by
      rintro ⟨s⟩
      simp }

@[simp]
theorem quotient_equiv_mk (I : Ideal R) (J : Ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S)) (x : R) :
    quotientEquiv I J f hIJ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (f x) :=
  rfl

@[simp]
theorem quotient_equiv_symm_mk (I : Ideal R) (J : Ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S)) (x : S) :
    (quotientEquiv I J f hIJ).symm (Ideal.Quotient.mk J x) = Ideal.Quotient.mk I (f.symm x) :=
  rfl

/-- `H` and `h` are kept as separate hypothesis since H is used in constructing the quotient map. -/
theorem quotient_map_injective' {J : Ideal R} {I : Ideal S} {f : R →+* S} {H : J ≤ I.comap f} (h : I.comap f ≤ J) :
    Function.Injective (quotientMap I f H) := by
  refine' (injective_iff_map_eq_zero (quotient_map I f H)).2 fun a ha => _
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a
  rw [quotient_map_mk, quotient.eq_zero_iff_mem] at ha
  exact quotient.eq_zero_iff_mem.mpr (h ha)

/-- If we take `J = I.comap f` then `quotient_map` is injective automatically. -/
theorem quotient_map_injective {I : Ideal S} {f : R →+* S} : Function.Injective (quotientMap I f le_rfl) :=
  quotient_map_injective' le_rfl

theorem quotient_map_surjective {J : Ideal R} {I : Ideal S} {f : R →+* S} {H : J ≤ I.comap f}
    (hf : Function.Surjective f) : Function.Surjective (quotientMap I f H) := fun x =>
  let ⟨x, hx⟩ := Quotient.mk_surjective x
  let ⟨y, hy⟩ := hf x
  ⟨(Quotient.mk J) y, by
    simp [← hx, ← hy]⟩

/-- Commutativity of a square is preserved when taking quotients by an ideal. -/
theorem comp_quotient_map_eq_of_comp_eq {R' S' : Type _} [CommRingₓ R'] [CommRingₓ S'] {f : R →+* S} {f' : R' →+* S'}
    {g : R →+* R'} {g' : S →+* S'} (hfg : f'.comp g = g'.comp f) (I : Ideal S') :
    (quotientMap I g' le_rfl).comp (quotientMap (I.comap g') f le_rfl) =
      (quotientMap I f' le_rfl).comp
        (quotientMap (I.comap f') g (le_of_eqₓ (trans (comap_comap f g') (hfg ▸ comap_comap g f')))) :=
  by
  refine' RingHom.ext fun a => _
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a
  simp only [← RingHom.comp_apply, ← quotient_map_mk]
  exact congr_arg (Quotientₓ.mk I) (trans (g'.comp_apply f r).symm (hfg ▸ f'.comp_apply g r))

/-- The algebra hom `A/I →+* B/J` induced by an algebra hom `f : A →ₐ[R₁] B` with `I ≤ f⁻¹(J)`. -/
def quotientMapₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (hIJ : I ≤ J.comap f) : A ⧸ I →ₐ[R₁] B ⧸ J :=
  { quotientMap J (f : A →+* B) hIJ with
    commutes' := fun r => by
      simp }

@[simp]
theorem quotient_map_mkₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) {x : A} :
    quotientMapₐ J f H (Quotient.mk I x) = Quotient.mkₐ R₁ J (f x) :=
  rfl

theorem quotient_map_comp_mkₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) :
    (quotientMapₐ J f H).comp (Quotient.mkₐ R₁ I) = (Quotient.mkₐ R₁ J).comp f :=
  AlgHom.ext fun x => by
    simp only [← quotient_map_mkₐ, ← quotient.mkₐ_eq_mk, ← AlgHom.comp_apply]

/-- The algebra equiv `A/I ≃ₐ[R] B/J` induced by an algebra equiv `f : A ≃ₐ[R] B`,
where`J = f(I)`. -/
def quotientEquivAlg (I : Ideal A) (J : Ideal B) (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) :
    (A ⧸ I) ≃ₐ[R₁] B ⧸ J :=
  { quotientEquiv I J (f : A ≃+* B) hIJ with
    commutes' := fun r => by
      simp }

instance (priority := 100) quotientAlgebra {I : Ideal A} [Algebra R A] :
    Algebra (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) :=
  (quotientMap I (algebraMap R A) (le_of_eqₓ rfl)).toAlgebra

theorem algebra_map_quotient_injective {I : Ideal A} [Algebra R A] :
    Function.Injective (algebraMap (R ⧸ I.comap (algebraMap R A)) (A ⧸ I)) := by
  rintro ⟨a⟩ ⟨b⟩ hab
  replace hab := quotient.eq.mp hab
  rw [← RingHom.map_sub] at hab
  exact quotient.eq.mpr hab

end QuotientAlgebra

end CommRingₓ

end Ideal

namespace Submodule

variable {R : Type u} {M : Type v}

variable [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M]

-- TODO: show `[algebra R A] : algebra (ideal R) A` too
instance moduleSubmodule : Module (Ideal R) (Submodule R M) where
  smul_add := smul_sup
  add_smul := sup_smul
  mul_smul := Submodule.smul_assoc
  one_smul := by
    simp
  zero_smul := bot_smul
  smul_zero := smul_bot

end Submodule

namespace RingHom

variable {A B C : Type _} [Ringₓ A] [Ringₓ B] [Ringₓ C]

variable (f : A →+* B) (f_inv : B → A)

/-- Auxiliary definition used to define `lift_of_right_inverse` -/
def liftOfRightInverseAux (hf : Function.RightInverse f_inv f) (g : A →+* C) (hg : f.ker ≤ g.ker) : B →+* C :=
  { AddMonoidHom.liftOfRightInverse f.toAddMonoidHom f_inv hf ⟨g.toAddMonoidHom, hg⟩ with toFun := fun b => g (f_inv b),
    map_one' := by
      rw [← g.map_one, ← sub_eq_zero, ← g.map_sub, ← g.mem_ker]
      apply hg
      rw [f.mem_ker, f.map_sub, sub_eq_zero, f.map_one]
      exact hf 1,
    map_mul' := by
      intro x y
      rw [← g.map_mul, ← sub_eq_zero, ← g.map_sub, ← g.mem_ker]
      apply hg
      rw [f.mem_ker, f.map_sub, sub_eq_zero, f.map_mul]
      simp only [← hf _] }

@[simp]
theorem lift_of_right_inverse_aux_comp_apply (hf : Function.RightInverse f_inv f) (g : A →+* C) (hg : f.ker ≤ g.ker)
    (a : A) : (f.liftOfRightInverseAux f_inv hf g hg) (f a) = g a :=
  f.toAddMonoidHom.lift_of_right_inverse_comp_apply f_inv hf ⟨g.toAddMonoidHom, hg⟩ a

/-- `lift_of_right_inverse f hf g hg` is the unique ring homomorphism `φ`

* such that `φ.comp f = g` (`ring_hom.lift_of_right_inverse_comp`),
* where `f : A →+* B` is has a right_inverse `f_inv` (`hf`),
* and `g : B →+* C` satisfies `hg : f.ker ≤ g.ker`.

See `ring_hom.eq_lift_of_right_inverse` for the uniqueness lemma.

```
   A .
   |  \
 f |   \ g
   |    \
   v     \⌟
   B ----> C
      ∃!φ
```
-/
def liftOfRightInverse (hf : Function.RightInverse f_inv f) : { g : A →+* C // f.ker ≤ g.ker } ≃ (B →+* C) where
  toFun := fun g => f.liftOfRightInverseAux f_inv hf g.1 g.2
  invFun := fun φ =>
    ⟨φ.comp f, fun x hx =>
      (mem_ker _).mpr <| by
        simp [← (mem_ker _).mp hx]⟩
  left_inv := fun g => by
    ext
    simp only [← comp_apply, ← lift_of_right_inverse_aux_comp_apply, ← Subtype.coe_mk, ← Subtype.val_eq_coe]
  right_inv := fun φ => by
    ext b
    simp [← lift_of_right_inverse_aux, ← hf b]

/-- A non-computable version of `ring_hom.lift_of_right_inverse` for when no computable right
inverse is available, that uses `function.surj_inv`. -/
@[simp]
noncomputable abbrev liftOfSurjective (hf : Function.Surjective f) : { g : A →+* C // f.ker ≤ g.ker } ≃ (B →+* C) :=
  f.liftOfRightInverse (Function.surjInv hf) (Function.right_inverse_surj_inv hf)

theorem lift_of_right_inverse_comp_apply (hf : Function.RightInverse f_inv f) (g : { g : A →+* C // f.ker ≤ g.ker })
    (x : A) : (f.liftOfRightInverse f_inv hf g) (f x) = g x :=
  f.lift_of_right_inverse_aux_comp_apply f_inv hf g.1 g.2 x

theorem lift_of_right_inverse_comp (hf : Function.RightInverse f_inv f) (g : { g : A →+* C // f.ker ≤ g.ker }) :
    (f.liftOfRightInverse f_inv hf g).comp f = g :=
  RingHom.ext <| f.lift_of_right_inverse_comp_apply f_inv hf g

theorem eq_lift_of_right_inverse (hf : Function.RightInverse f_inv f) (g : A →+* C) (hg : f.ker ≤ g.ker) (h : B →+* C)
    (hh : h.comp f = g) : h = f.liftOfRightInverse f_inv hf ⟨g, hg⟩ := by
  simp_rw [← hh]
  exact ((f.lift_of_right_inverse f_inv hf).apply_symm_apply _).symm

end RingHom

namespace DoubleQuot

open Ideal

variable {R : Type u} [CommRingₓ R] (I J : Ideal R)

/-- The obvious ring hom `R/I → R/(I ⊔ J)` -/
def quotLeftToQuotSup : R ⧸ I →+* R ⧸ I⊔J :=
  Ideal.Quotient.factor I (I⊔J) le_sup_left

/-- The kernel of `quot_left_to_quot_sup` -/
theorem ker_quot_left_to_quot_sup : (quotLeftToQuotSup I J).ker = J.map (Ideal.Quotient.mk I) := by
  simp only [← mk_ker, ← sup_idem, ← sup_comm, ← quot_left_to_quot_sup, ← quotient.factor, ← ker_quotient_lift, ←
    map_eq_iff_sup_ker_eq_of_surjective I quotient.mk_surjective, sup_assoc]

/-- The ring homomorphism `(R/I)/J' -> R/(I ⊔ J)` induced by `quot_left_to_quot_sup` where `J'`
  is the image of `J` in `R/I`-/
def quotQuotToQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) →+* R ⧸ I⊔J :=
  Ideal.Quotient.lift (J.map (Ideal.Quotient.mk I)) (quot_left_to_quot_sup I J) (ker_quot_left_to_quot_sup I J).symm.le

/-- The composite of the maps `R → (R/I)` and `(R/I) → (R/I)/J'` -/
def quotQuotMk : R →+* (R ⧸ I) ⧸ J.map I :=
  (J.map I).comp I

/-- The kernel of `quot_quot_mk` -/
theorem ker_quot_quot_mk : (quotQuotMk I J).ker = I⊔J := by
  rw [RingHom.ker_eq_comap_bot, quot_quot_mk, ← comap_comap, ← RingHom.ker, mk_ker,
    comap_map_of_surjective (Ideal.Quotient.mk I) quotient.mk_surjective, ← RingHom.ker, mk_ker, sup_comm]

/-- The ring homomorphism `R/(I ⊔ J) → (R/I)/J' `induced by `quot_quot_mk` -/
def liftSupQuotQuotMk (I J : Ideal R) : R ⧸ I⊔J →+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) :=
  Ideal.Quotient.lift (I⊔J) (quotQuotMk I J) (ker_quot_quot_mk I J).symm.le

/-- `quot_quot_to_quot_add` and `lift_sup_double_qot_mk` are inverse isomorphisms -/
def quotQuotEquivQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ I⊔J :=
  RingEquiv.ofHomInv (quotQuotToQuotSup I J) (liftSupQuotQuotMk I J)
    (by
      ext z
      rfl)
    (by
      ext z
      rfl)

@[simp]
theorem quot_quot_equiv_quot_sup_quot_quot_mk (x : R) :
    quotQuotEquivQuotSup I J (quotQuotMk I J x) = Ideal.Quotient.mk (I⊔J) x :=
  rfl

@[simp]
theorem quot_quot_equiv_quot_sup_symm_quot_quot_mk (x : R) :
    (quotQuotEquivQuotSup I J).symm (Ideal.Quotient.mk (I⊔J) x) = quotQuotMk I J x :=
  rfl

/-- The obvious isomorphism `(R/I)/J' → (R/J)/I' `   -/
def quotQuotEquivComm : (R ⧸ I) ⧸ J.map I ≃+* (R ⧸ J) ⧸ I.map J :=
  ((quotQuotEquivQuotSup I J).trans (quotEquivOfEq sup_comm)).trans (quotQuotEquivQuotSup J I).symm

@[simp]
theorem quot_quot_equiv_comm_quot_quot_mk (x : R) : quotQuotEquivComm I J (quotQuotMk I J x) = quotQuotMk J I x :=
  rfl

@[simp]
theorem quot_quot_equiv_comm_comp_quot_quot_mk :
    RingHom.comp (↑(quotQuotEquivComm I J)) (quotQuotMk I J) = quotQuotMk J I :=
  RingHom.ext <| quot_quot_equiv_comm_quot_quot_mk I J

@[simp]
theorem quot_quot_equiv_comm_symm : (quotQuotEquivComm I J).symm = quotQuotEquivComm J I :=
  rfl

end DoubleQuot


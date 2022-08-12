/-
Copyright (c) 2018 Violeta Hernández Palacios, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro
-/
import Mathbin.SetTheory.Ordinal.Arithmetic

/-!
# Fixed points of normal functions

We prove various statements about the fixed points of normal ordinal functions. We state them in
three forms: as statements about type-indexed families of normal functions, as statements about
ordinal-indexed families of normal functions, and as statements about a single normal function. For
the most part, the first case encompasses the others.

Moreover, we prove some lemmas about the fixed points of specific normal functions.

## Main definitions and results

* `nfp_family`, `nfp_bfamily`, `nfp`: the next fixed point of a (family of) normal function(s).
* `fp_family_unbounded`, `fp_bfamily_unbounded`, `fp_unbounded`: the (common) fixed points of a
  (family of) normal function(s) are unbounded in the ordinals.
* `deriv_add_eq_mul_omega_add`: a characterization of the derivative of addition.
* `deriv_mul_eq_opow_omega_mul`: a characterization of the derivative of multiplication.
-/


noncomputable section

universe u v

open Function Order

namespace Ordinal

/-! ### Fixed points of type-indexed families of ordinals -/


section

variable {ι : Type u} {f : ι → Ordinal.{max u v} → Ordinal.{max u v}}

/-- The next common fixed point, at least `a`, for a family of normal functions.

`ordinal.nfp_family_fp` shows this is a fixed point, `ordinal.le_nfp_family` shows it's at
least `a`, and `ordinal.nfp_family_le_fp` shows this is the least ordinal with these properties. -/
def nfpFamily (f : ι → Ordinal → Ordinal) (a) : Ordinal :=
  sup (List.foldr f a)

theorem nfp_family_eq_sup (f : ι → Ordinal → Ordinal) (a) : nfpFamily f a = sup (List.foldr f a) :=
  rfl

theorem foldr_le_nfp_family (f : ι → Ordinal → Ordinal) (a l) : List.foldr f a l ≤ nfpFamily f a :=
  le_sup _ _

theorem le_nfp_family (f : ι → Ordinal → Ordinal) (a) : a ≤ nfpFamily f a :=
  le_sup _ []

theorem lt_nfp_family {a b} : a < nfpFamily f b ↔ ∃ l, a < List.foldr f b l :=
  lt_sup

theorem nfp_family_le_iff {a b} : nfpFamily f a ≤ b ↔ ∀ l, List.foldr f a l ≤ b :=
  sup_le_iff

theorem nfp_family_le {a b} : (∀ l, List.foldr f a l ≤ b) → nfpFamily f a ≤ b :=
  sup_le

theorem nfp_family_monotone (hf : ∀ i, Monotone (f i)) : Monotone (nfpFamily f) := fun a b h =>
  sup_le fun l => (List.foldr_monotone hf l h).trans (le_sup _ l)

theorem apply_lt_nfp_family (H : ∀ i, IsNormal (f i)) {a b} (hb : b < nfpFamily f a) (i) : f i b < nfpFamily f a :=
  let ⟨l, hl⟩ := lt_nfp_family.1 hb
  lt_sup.2 ⟨i :: l, (H i).StrictMono hl⟩

theorem apply_lt_nfp_family_iff [Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b < nfpFamily f a) ↔ b < nfpFamily f a :=
  ⟨fun h =>
    lt_nfp_family.2 <|
      let ⟨l, hl⟩ := lt_sup.1 (h (Classical.arbitrary ι))
      ⟨l, ((H _).self_le b).trans_lt hl⟩,
    apply_lt_nfp_family H⟩

theorem nfp_family_le_apply [Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∃ i, nfpFamily f a ≤ f i b) ↔ nfpFamily f a ≤ b := by
  rw [← not_iff_not]
  push_neg
  exact apply_lt_nfp_family_iff H

theorem nfp_family_le_fp (H : ∀ i, Monotone (f i)) {a b} (ab : a ≤ b) (h : ∀ i, f i b ≤ b) : nfpFamily f a ≤ b :=
  sup_le fun l => by
    by_cases' hι : IsEmpty ι
    · rwa [@Unique.eq_default _ (@List.uniqueOfIsEmpty ι hι) l]
      
    · have := not_is_empty_iff.1 hι
      induction' l with i l IH generalizing a
      · exact ab
        
      exact (H i (IH ab)).trans (h i)
      

theorem nfp_family_fp {i} (H : IsNormal (f i)) (a) : f i (nfpFamily f a) = nfpFamily f a := by
  unfold nfp_family
  rw [@is_normal.sup _ H _ _ ⟨[]⟩]
  apply le_antisymmₓ <;> refine' Ordinal.sup_le fun l => _
  · exact le_sup _ (i :: l)
    
  · exact (H.self_le _).trans (le_sup _ _)
    

theorem apply_le_nfp_family [hι : Nonempty ι] {f : ι → Ordinal → Ordinal} (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b ≤ nfpFamily f a) ↔ b ≤ nfpFamily f a := by
  refine' ⟨fun h => _, fun h i => _⟩
  · cases' hι with i
    exact ((H i).self_le b).trans (h i)
    
  rw [← nfp_family_fp (H i)]
  exact (H i).Monotone h

theorem nfp_family_eq_self {f : ι → Ordinal → Ordinal} {a} (h : ∀ i, f i a = a) : nfpFamily f a = a :=
  le_antisymmₓ
    (sup_le fun l => by
      rw [List.foldr_fixed' h l])
    (le_nfp_family f a)

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_family_unbounded (H : ∀ i, IsNormal (f i)) : (⋂ i, Function.FixedPoints (f i)).Unbounded (· < ·) := fun a =>
  ⟨_, fun s ⟨i, hi⟩ => by
    rw [← hi]
    exact nfp_family_fp (H i) a, (le_nfp_family f a).not_lt⟩

/-- The derivative of a family of normal functions is the sequence of their common fixed points. -/
def derivFamily (f : ι → Ordinal → Ordinal) (o : Ordinal) : Ordinal :=
  limitRecOn o (nfpFamily f 0) (fun a IH => nfpFamily f (succ IH)) fun a l => bsup.{max u v, u} a

@[simp]
theorem deriv_family_zero (f : ι → Ordinal → Ordinal) : derivFamily f 0 = nfpFamily f 0 :=
  limit_rec_on_zero _ _ _

@[simp]
theorem deriv_family_succ (f : ι → Ordinal → Ordinal) (o) :
    derivFamily f (succ o) = nfpFamily f (succ (derivFamily f o)) :=
  limit_rec_on_succ _ _ _ _

theorem deriv_family_limit (f : ι → Ordinal → Ordinal) {o} :
    IsLimit o → derivFamily f o = bsup.{max u v, u} o fun a _ => derivFamily f a :=
  limit_rec_on_limit _ _ _ _

theorem deriv_family_is_normal (f : ι → Ordinal → Ordinal) : IsNormal (derivFamily f) :=
  ⟨fun o => by
    rw [deriv_family_succ, ← succ_le_iff] <;> apply le_nfp_family, fun o l a => by
    rw [deriv_family_limit _ l, bsup_le_iff]⟩

theorem deriv_family_fp {i} (H : IsNormal (f i)) (o : Ordinal.{max u v}) : f i (derivFamily f o) = derivFamily f o := by
  refine' limit_rec_on o _ (fun o IH => _) _
  · rw [deriv_family_zero]
    exact nfp_family_fp H 0
    
  · rw [deriv_family_succ]
    exact nfp_family_fp H _
    
  · intro o l IH
    rw [deriv_family_limit _ l, IsNormal.bsup.{max u v, u, max u v} H (fun a _ => deriv_family f a) l.1]
    refine' eq_of_forall_ge_iff fun c => _
    simp (config := { contextual := true })only [← bsup_le_iff, ← IH]
    

theorem le_iff_deriv_family (H : ∀ i, IsNormal (f i)) {a} : (∀ i, f i a ≤ a) ↔ ∃ o, derivFamily f o = a :=
  ⟨fun ha => by
    suffices : ∀ (o) (_ : a ≤ deriv_family f o), ∃ o, deriv_family f o = a
    exact this a ((deriv_family_is_normal _).self_le _)
    refine' fun o => limit_rec_on o (fun h₁ => ⟨0, le_antisymmₓ _ h₁⟩) (fun o IH h₁ => _) fun o l IH h₁ => _
    · rw [deriv_family_zero]
      exact nfp_family_le_fp (fun i => (H i).Monotone) (Ordinal.zero_le _) ha
      
    · cases le_or_ltₓ a (deriv_family f o)
      · exact IH h
        
      refine' ⟨succ o, le_antisymmₓ _ h₁⟩
      rw [deriv_family_succ]
      exact nfp_family_le_fp (fun i => (H i).Monotone) (succ_le_of_lt h) ha
      
    · cases eq_or_lt_of_le h₁
      · exact ⟨_, h.symm⟩
        
      rw [deriv_family_limit _ l, ← not_leₓ, bsup_le_iff, not_ball] at h
      exact
        let ⟨o', h, hl⟩ := h
        IH o' h (le_of_not_leₓ hl)
      ,
    fun ⟨o, e⟩ i => e ▸ le_of_eqₓ (deriv_family_fp (H i) _)⟩

theorem fp_iff_deriv_family (H : ∀ i, IsNormal (f i)) {a} : (∀ i, f i a = a) ↔ ∃ o, derivFamily f o = a :=
  Iff.trans ⟨fun h i => le_of_eqₓ (h i), fun h i => (H i).le_iff_eq.1 (h i)⟩ (le_iff_deriv_family H)

theorem deriv_family_eq_enum_ord (H : ∀ i, IsNormal (f i)) :
    derivFamily f = enumOrd (⋂ i, Function.FixedPoints (f i)) := by
  rw [← eq_enum_ord _ (fp_family_unbounded H)]
  use (deriv_family_is_normal f).StrictMono
  rw [Set.range_eq_iff]
  refine' ⟨_, fun a ha => _⟩
  · rintro a S ⟨i, hi⟩
    rw [← hi]
    exact deriv_family_fp (H i) a
    
  rw [Set.mem_Inter] at ha
  rwa [← fp_iff_deriv_family H]

end

/-! ### Fixed points of ordinal-indexed families of ordinals -/


section

variable {o : Ordinal.{u}} {f : ∀, ∀ b < o, ∀, Ordinal.{max u v} → Ordinal.{max u v}}

/-- The next common fixed point, at least `a`, for a family of normal functions indexed by ordinals.
-/
def nfpBfamily (o : Ordinal) (f : ∀, ∀ b < o, ∀, Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily (familyOfBfamily o f)

theorem nfp_bfamily_eq_nfp_family {o : Ordinal} (f : ∀, ∀ b < o, ∀, Ordinal → Ordinal) :
    nfpBfamily o f = nfpFamily (familyOfBfamily o f) :=
  rfl

theorem foldr_le_nfp_bfamily {o : Ordinal} (f : ∀, ∀ b < o, ∀, Ordinal → Ordinal) (a l) :
    List.foldr (familyOfBfamily o f) a l ≤ nfpBfamily o f a :=
  le_sup _ _

theorem le_nfp_bfamily {o : Ordinal} (f : ∀, ∀ b < o, ∀, Ordinal → Ordinal) (a) : a ≤ nfpBfamily o f a :=
  le_sup _ []

theorem lt_nfp_bfamily {a b} : a < nfpBfamily o f b ↔ ∃ l, a < List.foldr (familyOfBfamily o f) b l :=
  lt_sup

theorem nfp_bfamily_le_iff {o : Ordinal} {f : ∀, ∀ b < o, ∀, Ordinal → Ordinal} {a b} :
    nfpBfamily o f a ≤ b ↔ ∀ l, List.foldr (familyOfBfamily o f) a l ≤ b :=
  sup_le_iff

theorem nfp_bfamily_le {o : Ordinal} {f : ∀, ∀ b < o, ∀, Ordinal → Ordinal} {a b} :
    (∀ l, List.foldr (familyOfBfamily o f) a l ≤ b) → nfpBfamily o f a ≤ b :=
  sup_le

theorem nfp_bfamily_monotone (hf : ∀ i hi, Monotone (f i hi)) : Monotone (nfpBfamily o f) :=
  nfp_family_monotone fun i => hf _ _

theorem apply_lt_nfp_bfamily (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∀ i hi, f i hi b < nfpBfamily o f a) ↔ b < nfpBfamily o f a := by
  unfold nfp_bfamily
  rw [← @apply_lt_nfp_family_iff _ (family_of_bfamily o f) (out_nonempty_iff_ne_zero.2 ho) fun i => H _ _]
  refine' ⟨fun h i => h _ (typein_lt_self i), fun h i hio => _⟩
  rw [← family_of_bfamily_enum o f]
  apply h

theorem nfp_bfamily_le_apply (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∃ i hi, nfpBfamily o f a ≤ f i hi b) ↔ nfpBfamily o f a ≤ b := by
  rw [← not_iff_not]
  push_neg
  convert apply_lt_nfp_bfamily ho H
  simp only [← not_leₓ]

theorem nfp_bfamily_le_fp (H : ∀ i hi, Monotone (f i hi)) {a b} (ab : a ≤ b) (h : ∀ i hi, f i hi b ≤ b) :
    nfpBfamily o f a ≤ b :=
  nfp_family_le_fp (fun _ => H _ _) ab fun i => h _ _

theorem nfp_bfamily_fp {i hi} (H : IsNormal (f i hi)) (a) : f i hi (nfpBfamily o f a) = nfpBfamily o f a := by
  rw [← family_of_bfamily_enum o f]
  apply nfp_family_fp
  rw [family_of_bfamily_enum]
  exact H

theorem apply_le_nfp_bfamily (ho : o ≠ 0) (H : ∀ i hi, IsNormal (f i hi)) {a b} :
    (∀ i hi, f i hi b ≤ nfpBfamily o f a) ↔ b ≤ nfpBfamily o f a := by
  refine' ⟨fun h => _, fun h i hi => _⟩
  · have ho' : 0 < o := Ordinal.pos_iff_ne_zero.2 ho
    exact ((H 0 ho').self_le b).trans (h 0 ho')
    
  rw [← nfp_bfamily_fp (H i hi)]
  exact (H i hi).Monotone h

theorem nfp_bfamily_eq_self {a} (h : ∀ i hi, f i hi a = a) : nfpBfamily o f a = a :=
  nfp_family_eq_self fun _ => h _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i hi)
/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
theorem fp_bfamily_unbounded (H : ∀ i hi, IsNormal (f i hi)) :
    (⋂ (i) (hi), Function.FixedPoints (f i hi)).Unbounded (· < ·) := fun a =>
  ⟨_, by
    rw [Set.mem_Inter₂]
    exact fun i hi => nfp_bfamily_fp (H i hi) _, (le_nfp_bfamily f a).not_lt⟩

/-- The derivative of a family of normal functions is the sequence of their common fixed points. -/
def derivBfamily (o : Ordinal) (f : ∀, ∀ b < o, ∀, Ordinal → Ordinal) : Ordinal → Ordinal :=
  derivFamily (familyOfBfamily o f)

theorem deriv_bfamily_eq_deriv_family {o : Ordinal} (f : ∀, ∀ b < o, ∀, Ordinal → Ordinal) :
    derivBfamily o f = derivFamily (familyOfBfamily o f) :=
  rfl

theorem deriv_bfamily_is_normal {o : Ordinal} (f : ∀, ∀ b < o, ∀, Ordinal → Ordinal) : IsNormal (derivBfamily o f) :=
  deriv_family_is_normal _

theorem deriv_bfamily_fp {i hi} (H : IsNormal (f i hi)) (a : Ordinal) :
    f i hi (derivBfamily o f a) = derivBfamily o f a := by
  rw [← family_of_bfamily_enum o f]
  apply deriv_family_fp
  rw [family_of_bfamily_enum]
  exact H

theorem le_iff_deriv_bfamily (H : ∀ i hi, IsNormal (f i hi)) {a} :
    (∀ i hi, f i hi a ≤ a) ↔ ∃ b, derivBfamily o f b = a := by
  unfold deriv_bfamily
  rw [← le_iff_deriv_family]
  · refine' ⟨fun h i => h _ _, fun h i hi => _⟩
    rw [← family_of_bfamily_enum o f]
    apply h
    
  exact fun _ => H _ _

theorem fp_iff_deriv_bfamily (H : ∀ i hi, IsNormal (f i hi)) {a} :
    (∀ i hi, f i hi a = a) ↔ ∃ b, derivBfamily o f b = a := by
  rw [← le_iff_deriv_bfamily H]
  refine' ⟨fun h i hi => le_of_eqₓ (h i hi), fun h i hi => _⟩
  rw [← (H i hi).le_iff_eq]
  exact h i hi

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i hi)
theorem deriv_bfamily_eq_enum_ord (H : ∀ i hi, IsNormal (f i hi)) :
    derivBfamily o f = enumOrd (⋂ (i) (hi), Function.FixedPoints (f i hi)) := by
  rw [← eq_enum_ord _ (fp_bfamily_unbounded H)]
  use (deriv_bfamily_is_normal f).StrictMono
  rw [Set.range_eq_iff]
  refine' ⟨fun a => Set.mem_Inter₂.2 fun i hi => deriv_bfamily_fp (H i hi) a, fun a ha => _⟩
  rw [Set.mem_Inter₂] at ha
  rwa [← fp_iff_deriv_bfamily H]

end

/-! ### Fixed points of a single function -/


section

variable {f : Ordinal.{u} → Ordinal.{u}}

/-- The next fixed point function, the least fixed point of the normal function `f`, at least `a`.
-/
def nfp (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily fun _ : Unit => f

theorem nfp_eq_nfp_family (f : Ordinal → Ordinal) : nfp f = nfpFamily fun _ : Unit => f :=
  rfl

@[simp]
theorem sup_iterate_eq_nfp (f : Ordinal.{u} → Ordinal.{u}) : (fun a => sup fun n : ℕ => (f^[n]) a) = nfp f := by
  refine' funext fun a => le_antisymmₓ _ (sup_le fun l => _)
  · rw [sup_le_iff]
    intro n
    rw [← List.length_repeat Unit.star n, ← List.foldr_const f a]
    apply le_sup
    
  · rw [List.foldr_const f a l]
    exact le_sup _ _
    

theorem iterate_le_nfp (f a n) : (f^[n]) a ≤ nfp f a := by
  rw [← sup_iterate_eq_nfp]
  exact le_sup _ n

theorem le_nfp (f a) : a ≤ nfp f a :=
  iterate_le_nfp f a 0

theorem lt_nfp {a b} : a < nfp f b ↔ ∃ n, a < (f^[n]) b := by
  rw [← sup_iterate_eq_nfp]
  exact lt_sup

theorem nfp_le_iff {a b} : nfp f a ≤ b ↔ ∀ n, (f^[n]) a ≤ b := by
  rw [← sup_iterate_eq_nfp]
  exact sup_le_iff

theorem nfp_le {a b} : (∀ n, (f^[n]) a ≤ b) → nfp f a ≤ b :=
  nfp_le_iff.2

@[simp]
theorem nfp_id : nfp id = id :=
  funext fun a => by
    simp_rw [← sup_iterate_eq_nfp, iterate_id]
    exact sup_const a

theorem nfp_monotone (hf : Monotone f) : Monotone (nfp f) :=
  nfp_family_monotone fun i => hf

theorem IsNormal.apply_lt_nfp {f} (H : IsNormal f) {a b} : f b < nfp f a ↔ b < nfp f a := by
  unfold nfp
  rw [← @apply_lt_nfp_family_iff Unit (fun _ => f) _ (fun _ => H) a b]
  exact ⟨fun h _ => h, fun h => h Unit.star⟩

theorem IsNormal.nfp_le_apply {f} (H : IsNormal f) {a b} : nfp f a ≤ f b ↔ nfp f a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 H.apply_lt_nfp

theorem nfp_le_fp {f} (H : Monotone f) {a b} (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
  nfp_family_le_fp (fun _ => H) ab fun _ => h

theorem IsNormal.nfp_fp {f} (H : IsNormal f) : ∀ a, f (nfp f a) = nfp f a :=
  @nfp_family_fp Unit (fun _ => f) Unit.star H

theorem IsNormal.apply_le_nfp {f} (H : IsNormal f) {a b} : f b ≤ nfp f a ↔ b ≤ nfp f a :=
  ⟨le_transₓ (H.self_le _), fun h => by
    simpa only [← H.nfp_fp] using H.le_iff.2 h⟩

theorem nfp_eq_self {f : Ordinal → Ordinal} {a} (h : f a = a) : nfp f a = a :=
  nfp_family_eq_self fun _ => h

/-- The fixed point lemma for normal functions: any normal function has an unbounded set of
fixed points. -/
theorem fp_unbounded (H : IsNormal f) : (Function.FixedPoints f).Unbounded (· < ·) := by
  convert fp_family_unbounded fun _ : Unit => H
  exact (Set.Inter_const _).symm

/-- The derivative of a normal function `f` is the sequence of fixed points of `f`. -/
def deriv (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  derivFamily fun _ : Unit => f

theorem deriv_eq_deriv_family (f : Ordinal → Ordinal) : deriv f = derivFamily fun _ : Unit => f :=
  rfl

@[simp]
theorem deriv_zero (f) : deriv f 0 = nfp f 0 :=
  deriv_family_zero _

@[simp]
theorem deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
  deriv_family_succ _ _

theorem deriv_limit (f) {o} : IsLimit o → deriv f o = bsup.{u, 0} o fun a _ => deriv f a :=
  deriv_family_limit _

theorem deriv_is_normal (f) : IsNormal (deriv f) :=
  deriv_family_is_normal _

theorem deriv_id_of_nfp_id {f : Ordinal → Ordinal} (h : nfp f = id) : deriv f = id :=
  ((deriv_is_normal _).eq_iff_zero_and_succ IsNormal.refl).2
    (by
      simp [← h])

theorem IsNormal.deriv_fp {f} (H : IsNormal f) : ∀ o, f (deriv f o) = deriv f o :=
  @deriv_family_fp Unit (fun _ => f) Unit.star H

theorem IsNormal.le_iff_deriv {f} (H : IsNormal f) {a} : f a ≤ a ↔ ∃ o, deriv f o = a := by
  unfold deriv
  rw [← le_iff_deriv_family fun _ : Unit => H]
  exact ⟨fun h _ => h, fun h => h Unit.star⟩

theorem IsNormal.fp_iff_deriv {f} (H : IsNormal f) {a} : f a = a ↔ ∃ o, deriv f o = a := by
  rw [← H.le_iff_eq, H.le_iff_deriv]

theorem deriv_eq_enum_ord (H : IsNormal f) : deriv f = enumOrd (Function.FixedPoints f) := by
  convert deriv_family_eq_enum_ord fun _ : Unit => H
  exact (Set.Inter_const _).symm

theorem deriv_eq_id_of_nfp_eq_id {f : Ordinal → Ordinal} (h : nfp f = id) : deriv f = id :=
  (IsNormal.eq_iff_zero_and_succ (deriv_is_normal _) IsNormal.refl).2
    (by
      simp [← h])

end

/-! ### Fixed points of addition -/


@[simp]
theorem nfp_add_zero (a) : nfp ((· + ·) a) 0 = a * omega := by
  simp_rw [← sup_iterate_eq_nfp, ← sup_mul_nat]
  congr
  funext
  induction' n with n hn
  · rw [Nat.cast_zeroₓ, mul_zero, iterate_zero_apply]
    
  · nth_rw 1[Nat.succ_eq_one_add]
    rw [Nat.cast_addₓ, Nat.cast_oneₓ, mul_one_add, iterate_succ_apply', hn]
    

theorem nfp_add_eq_mul_omega {a b} (hba : b ≤ a * omega) : nfp ((· + ·) a) b = a * omega := by
  apply le_antisymmₓ (nfp_le_fp (add_is_normal a).Monotone hba _)
  · rw [← nfp_add_zero]
    exact nfp_monotone (add_is_normal a).Monotone (Ordinal.zero_le b)
    
  · rw [← mul_one_add, one_add_omega]
    

theorem add_eq_right_iff_mul_omega_le {a b : Ordinal} : a + b = b ↔ a * omega ≤ b := by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [← nfp_add_zero a, ← deriv_zero]
    cases' (add_is_normal a).fp_iff_deriv.1 h with c hc
    rw [← hc]
    exact (deriv_is_normal _).Monotone (Ordinal.zero_le _)
    
  · have := Ordinal.add_sub_cancel_of_le h
    nth_rw 0[← this]
    rwa [← add_assocₓ, ← mul_one_add, one_add_omega]
    

theorem add_le_right_iff_mul_omega_le {a b : Ordinal} : a + b ≤ b ↔ a * omega ≤ b := by
  rw [← add_eq_right_iff_mul_omega_le]
  exact (add_is_normal a).le_iff_eq

theorem deriv_add_eq_mul_omega_add (a b : Ordinal.{u}) : deriv ((· + ·) a) b = a * omega + b := by
  revert b
  rw [← funext_iff, is_normal.eq_iff_zero_and_succ (deriv_is_normal _) (add_is_normal _)]
  refine' ⟨_, fun a h => _⟩
  · rw [deriv_zero, add_zeroₓ]
    exact nfp_add_zero a
    
  · rw [deriv_succ, h, add_succ]
    exact nfp_eq_self (add_eq_right_iff_mul_omega_le.2 ((le_add_right _ _).trans (le_succ _)))
    

/-! ### Fixed points of multiplication -/


-- mathport name: «expr ^ »
local infixr:0 "^" => @pow Ordinal Ordinal Ordinal.hasPow

@[simp]
theorem nfp_mul_one {a : Ordinal} (ha : 0 < a) : nfp ((· * ·) a) 1 = (a^omega) := by
  rw [← sup_iterate_eq_nfp, ← sup_opow_nat]
  · dsimp'
    congr
    funext
    induction' n with n hn
    · rw [Nat.cast_zeroₓ, opow_zero, iterate_zero_apply]
      
    nth_rw 1[Nat.succ_eq_one_add]
    rw [Nat.cast_addₓ, Nat.cast_oneₓ, opow_add, opow_one, iterate_succ_apply', hn]
    
  · exact ha
    

@[simp]
theorem nfp_mul_zero (a : Ordinal) : nfp ((· * ·) a) 0 = 0 := by
  rw [← Ordinal.le_zero, nfp_le_iff]
  intro n
  induction' n with n hn
  · rfl
    
  rwa [iterate_succ_apply, mul_zero]

@[simp]
theorem nfp_zero_mul : nfp ((· * ·) 0) = id := by
  rw [← sup_iterate_eq_nfp]
  refine' funext fun a => (sup_le fun n => _).antisymm (le_sup (fun n => ((· * ·) 0^[n]) a) 0)
  induction' n with n hn
  · rfl
    
  rw [Function.iterate_succ']
  change 0 * _ ≤ a
  rw [zero_mul]
  exact Ordinal.zero_le a

@[simp]
theorem deriv_mul_zero : deriv ((· * ·) 0) = id :=
  deriv_eq_id_of_nfp_eq_id nfp_zero_mul

theorem nfp_mul_eq_opow_omega {a b : Ordinal} (hb : 0 < b) (hba : b ≤ (a^omega)) : nfp ((· * ·) a) b = (a^omega.{u}) :=
  by
  cases' eq_zero_or_pos a with ha ha
  · rw [ha, zero_opow omega_ne_zero] at *
    rw [Ordinal.le_zero.1 hba, nfp_zero_mul]
    rfl
    
  apply le_antisymmₓ
  · apply nfp_le_fp (mul_is_normal ha).Monotone hba
    rw [← opow_one_add, one_add_omega]
    
  rw [← nfp_mul_one ha]
  exact nfp_monotone (mul_is_normal ha).Monotone (one_le_iff_pos.2 hb)

theorem eq_zero_or_opow_omega_le_of_mul_eq_right {a b : Ordinal} (hab : a * b = b) : b = 0 ∨ (a^omega.{u}) ≤ b := by
  cases' eq_zero_or_pos a with ha ha
  · rw [ha, zero_opow omega_ne_zero]
    exact Or.inr (Ordinal.zero_le b)
    
  rw [or_iff_not_imp_left]
  intro hb
  change b ≠ 0 at hb
  rw [← nfp_mul_one ha]
  rw [← one_le_iff_ne_zero] at hb
  exact nfp_le_fp (mul_is_normal ha).Monotone hb (le_of_eqₓ hab)

theorem mul_eq_right_iff_opow_omega_dvd {a b : Ordinal} : a * b = b ↔ (a^omega) ∣ b := by
  cases' eq_zero_or_pos a with ha ha
  · rw [ha, zero_mul, zero_opow omega_ne_zero, zero_dvd_iff]
    exact eq_comm
    
  refine' ⟨fun hab => _, fun h => _⟩
  · rw [dvd_iff_mod_eq_zero]
    rw [← div_add_mod b (a^omega), mul_addₓ, ← mul_assoc, ← opow_one_add, one_add_omega, add_left_cancelₓ] at hab
    cases' eq_zero_or_opow_omega_le_of_mul_eq_right hab with hab hab
    · exact hab
      
    refine' (not_lt_of_le hab (mod_lt b (opow_ne_zero omega _))).elim
    rwa [← Ordinal.pos_iff_ne_zero]
    
  cases' h with c hc
  rw [hc, ← mul_assoc, ← opow_one_add, one_add_omega]

theorem mul_le_right_iff_opow_omega_dvd {a b : Ordinal} (ha : 0 < a) : a * b ≤ b ↔ (a^omega) ∣ b := by
  rw [← mul_eq_right_iff_opow_omega_dvd]
  exact (mul_is_normal ha).le_iff_eq

theorem nfp_mul_opow_omega_add {a c : Ordinal} (b) (ha : 0 < a) (hc : 0 < c) (hca : c ≤ (a^omega)) :
    nfp ((· * ·) a) ((a^omega) * b + c) = (a^omega.{u}) * succ b := by
  apply le_antisymmₓ
  · apply nfp_le_fp (mul_is_normal ha).Monotone
    · rw [mul_succ]
      apply add_le_add_left hca
      
    · rw [← mul_assoc, ← opow_one_add, one_add_omega]
      
    
  · cases' mul_eq_right_iff_opow_omega_dvd.1 ((mul_is_normal ha).nfp_fp ((a^omega) * b + c)) with d hd
    rw [hd]
    apply mul_le_mul_left'
    have := le_nfp (Mul.mul a) ((a^omega) * b + c)
    rw [hd] at this
    have := (add_lt_add_left hc ((a^omega) * b)).trans_le this
    rw [add_zeroₓ, mul_lt_mul_iff_left (opow_pos omega ha)] at this
    rwa [succ_le_iff]
    

theorem deriv_mul_eq_opow_omega_mul {a : Ordinal.{u}} (ha : 0 < a) (b) : deriv ((· * ·) a) b = (a^omega) * b := by
  revert b
  rw [← funext_iff, is_normal.eq_iff_zero_and_succ (deriv_is_normal _) (mul_is_normal (opow_pos omega ha))]
  refine' ⟨_, fun c h => _⟩
  · rw [deriv_zero, nfp_mul_zero, mul_zero]
    
  · rw [deriv_succ, h]
    exact nfp_mul_opow_omega_add c ha zero_lt_one (one_le_iff_pos.2 (opow_pos _ ha))
    

end Ordinal


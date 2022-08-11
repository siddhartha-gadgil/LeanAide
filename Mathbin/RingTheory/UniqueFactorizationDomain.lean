/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
import Mathbin.Algebra.BigOperators.Associated
import Mathbin.Algebra.GcdMonoid.Basic
import Mathbin.Data.Finsupp.Multiset
import Mathbin.RingTheory.Noetherian
import Mathbin.RingTheory.Multiplicity

/-!

# Unique factorization

## Main Definitions
* `wf_dvd_monoid` holds for `monoid`s for which a strict divisibility relation is
  well-founded.
* `unique_factorization_monoid` holds for `wf_dvd_monoid`s where
  `irreducible` is equivalent to `prime`

## To do
* set up the complete lattice structure on `factor_set`.

-/


variable {α : Type _}

-- mathport name: «expr ~ᵤ »
local infixl:50 " ~ᵤ " => Associated

/-- Well-foundedness of the strict version of |, which is equivalent to the descending chain
condition on divisibility and to the ascending chain condition on
principal ideals in an integral domain.
  -/
class WfDvdMonoid (α : Type _) [CommMonoidWithZero α] : Prop where
  well_founded_dvd_not_unit : WellFounded (@DvdNotUnit α _)

export WfDvdMonoid (well_founded_dvd_not_unit)

-- see Note [lower instance priority]
instance (priority := 100) IsNoetherianRing.wf_dvd_monoid [CommRingₓ α] [IsDomain α] [IsNoetherianRing α] :
    WfDvdMonoid α :=
  ⟨by
    convert InvImage.wfₓ (fun a => Ideal.span ({a} : Set α)) (well_founded_submodule_gt _ _)
    ext
    exact ideal.span_singleton_lt_span_singleton.symm⟩

namespace WfDvdMonoid

variable [CommMonoidWithZero α]

open Associates Nat

theorem of_wf_dvd_monoid_associates (h : WfDvdMonoid (Associates α)) : WfDvdMonoid α :=
  ⟨by
    have := h
    refine' (Surjective.well_founded_iff mk_surjective _).2 well_founded_dvd_not_unit
    intros
    rw [mk_dvd_not_unit_mk_iff]⟩

variable [WfDvdMonoid α]

instance wf_dvd_monoid_associates : WfDvdMonoid (Associates α) :=
  ⟨by
    refine' (Surjective.well_founded_iff mk_surjective _).1 well_founded_dvd_not_unit
    intros
    rw [mk_dvd_not_unit_mk_iff]⟩

theorem well_founded_associates : WellFounded ((· < ·) : Associates α → Associates α → Prop) :=
  Subrelation.wfₓ (fun x y => dvd_not_unit_of_lt) well_founded_dvd_not_unit

attribute [local elab_as_eliminator] WellFounded.fix

theorem exists_irreducible_factor {a : α} (ha : ¬IsUnit a) (ha0 : a ≠ 0) : ∃ i, Irreducible i ∧ i ∣ a :=
  let ⟨b, hs, hr⟩ := well_founded_dvd_not_unit.has_min { b | b ∣ a ∧ ¬IsUnit b } ⟨a, dvd_rfl, ha⟩
  ⟨b,
    ⟨hs.2, fun c d he =>
      let h := dvd_trans ⟨d, he⟩ hs.1
      or_iff_not_imp_left.2 fun hc => of_not_not fun hd => hr c ⟨h, hc⟩ ⟨ne_zero_of_dvd_ne_zero ha0 h, d, hd, he⟩⟩,
    hs.1⟩

@[elab_as_eliminator]
theorem induction_on_irreducible {P : α → Prop} (a : α) (h0 : P 0) (hu : ∀ u : α, IsUnit u → P u)
    (hi : ∀ a i : α, a ≠ 0 → Irreducible i → P a → P (i * a)) : P a :=
  have := Classical.dec
  well_founded_dvd_not_unit.fix
    (fun a ih =>
      if ha0 : a = 0 then ha0.substr h0
      else
        if hau : IsUnit a then hu a hau
        else
          let ⟨i, hii, b, hb⟩ := exists_irreducible_factor hau ha0
          let hb0 : b ≠ 0 := ne_zero_of_dvd_ne_zero ha0 ⟨i, mul_comm i b ▸ hb⟩
          hb.symm ▸ hi b i hb0 hii <| ih b ⟨hb0, i, hii.1, mul_comm i b ▸ hb⟩)
    a

theorem exists_factors (a : α) : a ≠ 0 → ∃ f : Multiset α, (∀, ∀ b ∈ f, ∀, Irreducible b) ∧ Associated f.Prod a :=
  induction_on_irreducible a (fun h => (h rfl).elim) (fun u hu _ => ⟨0, fun _ h => h.elim, hu.Unit, one_mulₓ _⟩)
    fun a i ha0 hi ih _ =>
    let ⟨s, hs⟩ := ih ha0
    ⟨i ::ₘ s, fun b H => (Multiset.mem_cons.1 H).elim (fun h => h.symm ▸ hi) (hs.1 b), by
      rw [s.prod_cons i]
      exact hs.2.mul_left i⟩

theorem not_unit_iff_exists_factors_eq (a : α) (hn0 : a ≠ 0) :
    ¬IsUnit a ↔ ∃ f : Multiset α, (∀, ∀ b ∈ f, ∀, Irreducible b) ∧ f.Prod = a ∧ f ≠ ∅ :=
  ⟨fun hnu => by
    obtain ⟨f, hi, u, rfl⟩ := exists_factors a hn0
    obtain ⟨b, h⟩ :=
      Multiset.exists_mem_of_ne_zero fun h : f = 0 =>
        hnu <| by
          simp [← h]
    classical
    refine' ⟨(f.erase b).cons (b * u), fun a ha => _, _, Multiset.cons_ne_zero⟩
    · obtain rfl | ha := Multiset.mem_cons.1 ha
      exacts[Associated.irreducible ⟨u, rfl⟩ (hi b h), hi a (Multiset.mem_of_mem_erase ha)]
      
    · rw [Multiset.prod_cons, mul_comm b, mul_assoc, Multiset.prod_erase h, mul_comm]
      ,
    fun ⟨f, hi, he, hne⟩ =>
    let ⟨b, h⟩ := Multiset.exists_mem_of_ne_zero hne
    not_is_unit_of_not_is_unit_dvd (hi b h).not_unit <| he ▸ Multiset.dvd_prod h⟩

end WfDvdMonoid

theorem WfDvdMonoid.of_well_founded_associates [CancelCommMonoidWithZero α]
    (h : WellFounded ((· < ·) : Associates α → Associates α → Prop)) : WfDvdMonoid α :=
  WfDvdMonoid.of_wf_dvd_monoid_associates
    ⟨by
      convert h
      ext
      exact Associates.dvd_not_unit_iff_lt⟩

theorem WfDvdMonoid.iff_well_founded_associates [CancelCommMonoidWithZero α] :
    WfDvdMonoid α ↔ WellFounded ((· < ·) : Associates α → Associates α → Prop) :=
  ⟨by
    apply WfDvdMonoid.well_founded_associates, WfDvdMonoid.of_well_founded_associates⟩

section Prio

-- ./././Mathport/Syntax/Translate/Basic.lean:304:40: warning: unsupported option default_priority
set_option default_priority 100

/-- unique factorization monoids.

These are defined as `cancel_comm_monoid_with_zero`s with well-founded strict divisibility
relations, but this is equivalent to more familiar definitions:

Each element (except zero) is uniquely represented as a multiset of irreducible factors.
Uniqueness is only up to associated elements.

Each element (except zero) is non-uniquely represented as a multiset
of prime factors.

To define a UFD using the definition in terms of multisets
of irreducible factors, use the definition `of_exists_unique_irreducible_factors`

To define a UFD using the definition in terms of multisets
of prime factors, use the definition `of_exists_prime_factors`

-/
-- see Note [default priority]
class UniqueFactorizationMonoid (α : Type _) [CancelCommMonoidWithZero α] extends WfDvdMonoid α : Prop where
  irreducible_iff_prime : ∀ {a : α}, Irreducible a ↔ Prime a

/-- Can't be an instance because it would cause a loop `ufm → wf_dvd_monoid → ufm → ...`. -/
@[reducible]
theorem ufm_of_gcd_of_wf_dvd_monoid [CancelCommMonoidWithZero α] [WfDvdMonoid α] [GcdMonoid α] :
    UniqueFactorizationMonoid α :=
  { ‹WfDvdMonoid α› with irreducible_iff_prime := fun _ => GcdMonoid.irreducible_iff_prime }

instance Associates.ufm [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α] :
    UniqueFactorizationMonoid (Associates α) :=
  { (WfDvdMonoid.wf_dvd_monoid_associates : WfDvdMonoid (Associates α)) with
    irreducible_iff_prime := by
      rw [← Associates.irreducible_iff_prime_iff]
      apply UniqueFactorizationMonoid.irreducible_iff_prime }

end Prio

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]

theorem exists_prime_factors (a : α) : a ≠ 0 → ∃ f : Multiset α, (∀, ∀ b ∈ f, ∀, Prime b) ∧ f.Prod ~ᵤ a := by
  simp_rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  apply WfDvdMonoid.exists_factors a

@[elab_as_eliminator]
theorem induction_on_prime {P : α → Prop} (a : α) (h₁ : P 0) (h₂ : ∀ x : α, IsUnit x → P x)
    (h₃ : ∀ a p : α, a ≠ 0 → Prime p → P a → P (p * a)) : P a := by
  simp_rw [← UniqueFactorizationMonoid.irreducible_iff_prime] at h₃
  exact WfDvdMonoid.induction_on_irreducible a h₁ h₂ h₃

end UniqueFactorizationMonoid

theorem prime_factors_unique [CancelCommMonoidWithZero α] :
    ∀ {f g : Multiset α},
      (∀, ∀ x ∈ f, ∀, Prime x) → (∀, ∀ x ∈ g, ∀, Prime x) → f.Prod ~ᵤ g.Prod → Multiset.Rel Associated f g :=
  have := Classical.decEq α
  fun f =>
  Multiset.induction_on f
    (fun g _ hg h =>
      Multiset.rel_zero_left.2 <|
        Multiset.eq_zero_of_forall_not_mem fun x hx =>
          have : IsUnit g.Prod := by
            simpa [← associated_one_iff_is_unit] using h.symm
          (hg x hx).not_unit <| is_unit_iff_dvd_one.2 <| (Multiset.dvd_prod hx).trans (is_unit_iff_dvd_one.1 this))
    fun p f ih g hf hg hfg => by
    let ⟨b, hbg, hb⟩ :=
      (exists_associated_mem_of_dvd_prod
          (hf p
            (by
              simp ))
          fun q hq => hg _ hq) <|
        hfg.dvd_iff_dvd_right.1
          (show p ∣ (p ::ₘ f).Prod by
            simp )
    rw [← Multiset.cons_erase hbg]
    exact
      Multiset.Rel.cons hb
        (ih
          (fun q hq =>
            hf _
              (by
                simp [← hq]))
          (fun q (hq : q ∈ g.erase b) => hg q (Multiset.mem_of_mem_erase hq))
          (Associated.of_mul_left
            (by
              rwa [← Multiset.prod_cons, ← Multiset.prod_cons, Multiset.cons_erase hbg])
            hb
            (hf p
                (by
                  simp )).ne_zero))

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]

theorem factors_unique {f g : Multiset α} (hf : ∀, ∀ x ∈ f, ∀, Irreducible x) (hg : ∀, ∀ x ∈ g, ∀, Irreducible x)
    (h : f.Prod ~ᵤ g.Prod) : Multiset.Rel Associated f g :=
  prime_factors_unique (fun x hx => irreducible_iff_prime.mp (hf x hx)) (fun x hx => irreducible_iff_prime.mp (hg x hx))
    h

end UniqueFactorizationMonoid

/-- If an irreducible has a prime factorization,
  then it is an associate of one of its prime factors. -/
theorem prime_factors_irreducible [CancelCommMonoidWithZero α] {a : α} {f : Multiset α} (ha : Irreducible a)
    (pfa : (∀, ∀ b ∈ f, ∀, Prime b) ∧ f.Prod ~ᵤ a) : ∃ p, a ~ᵤ p ∧ f = {p} := by
  have := Classical.decEq α
  refine'
    Multiset.induction_on f (fun h => (ha.not_unit (associated_one_iff_is_unit.1 (Associated.symm h))).elim) _ pfa.2
      pfa.1
  rintro p s _ ⟨u, hu⟩ hs
  use p
  have hs0 : s = 0 := by
    by_contra hs0
    obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero hs0
    apply
      (hs q
            (by
              simp [← hq])).2.1
    refine' (ha.is_unit_or_is_unit (_ : _ = p * ↑u * (s.erase q).Prod * _)).resolve_left _
    · rw [mul_right_commₓ _ _ q, mul_assoc, ← Multiset.prod_cons, Multiset.cons_erase hq, ← hu, mul_comm, mul_comm p _,
        mul_assoc]
      simp
      
    apply mt is_unit_of_mul_is_unit_left (mt is_unit_of_mul_is_unit_left _)
    apply (hs p (Multiset.mem_cons_self _ _)).2.1
  simp only [← mul_oneₓ, ← Multiset.prod_cons, ← Multiset.prod_zero, ← hs0] at *
  exact ⟨Associated.symm ⟨u, hu⟩, rfl⟩

section ExistsPrimeFactors

variable [CancelCommMonoidWithZero α]

variable (pf : ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀, ∀ b ∈ f, ∀, Prime b) ∧ f.Prod ~ᵤ a)

include pf

theorem WfDvdMonoid.of_exists_prime_factors : WfDvdMonoid α :=
  ⟨by
    classical
    refine'
      RelHomClass.well_founded (RelHom.mk _ _ : (DvdNotUnit : α → α → Prop) →r ((· < ·) : WithTop ℕ → WithTop ℕ → Prop))
        (WithTop.well_founded_lt Nat.lt_wf)
    · intro a
      by_cases' h : a = 0
      · exact ⊤
        
      exact (Classical.some (pf a h)).card
      
    rintro a b ⟨ane0, ⟨c, hc, b_eq⟩⟩
    rw [dif_neg ane0]
    by_cases' h : b = 0
    · simp [← h, ← lt_top_iff_ne_top]
      
    rw [dif_neg h, WithTop.coe_lt_coe]
    have cne0 : c ≠ 0 := by
      refine' mt (fun con => _) h
      rw [b_eq, Con, mul_zero]
    calc Multiset.card (Classical.some (pf a ane0)) < _ + Multiset.card (Classical.some (pf c cne0)) :=
        lt_add_of_pos_right _
          (multiset.card_pos.mpr fun con =>
            hc
              (associated_one_iff_is_unit.mp
                _))_ = Multiset.card (Classical.some (pf a ane0) + Classical.some (pf c cne0)) :=
        (Multiset.card_add _ _).symm _ = Multiset.card (Classical.some (pf b h)) :=
        Multiset.card_eq_card_of_rel (prime_factors_unique _ (Classical.some_spec (pf _ h)).1 _)
    · convert (Classical.some_spec (pf c cne0)).2.symm
      rw [Con, Multiset.prod_zero]
      
    · intro x hadd
      rw [Multiset.mem_add] at hadd
      cases hadd <;> apply (Classical.some_spec (pf _ _)).1 _ hadd
      
    · rw [Multiset.prod_add]
      trans a * c
      · apply Associated.mul_mul <;> apply (Classical.some_spec (pf _ _)).2
        
      · rw [← b_eq]
        apply (Classical.some_spec (pf _ _)).2.symm
        
      ⟩

theorem irreducible_iff_prime_of_exists_prime_factors {p : α} : Irreducible p ↔ Prime p := by
  by_cases' hp0 : p = 0
  · simp [← hp0]
    
  refine' ⟨fun h => _, Prime.irreducible⟩
  obtain ⟨f, hf⟩ := pf p hp0
  obtain ⟨q, hq, rfl⟩ := prime_factors_irreducible h hf
  rw [hq.prime_iff]
  exact hf.1 q (Multiset.mem_singleton_self _)

theorem UniqueFactorizationMonoid.of_exists_prime_factors : UniqueFactorizationMonoid α :=
  { WfDvdMonoid.of_exists_prime_factors pf with
    irreducible_iff_prime := fun _ => irreducible_iff_prime_of_exists_prime_factors pf }

end ExistsPrimeFactors

theorem UniqueFactorizationMonoid.iff_exists_prime_factors [CancelCommMonoidWithZero α] :
    UniqueFactorizationMonoid α ↔ ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀, ∀ b ∈ f, ∀, Prime b) ∧ f.Prod ~ᵤ a :=
  ⟨fun h => @UniqueFactorizationMonoid.exists_prime_factors _ _ h, UniqueFactorizationMonoid.of_exists_prime_factors⟩

section

variable {β : Type _} [CancelCommMonoidWithZero α] [CancelCommMonoidWithZero β]

theorem MulEquiv.unique_factorization_monoid (e : α ≃* β) (hα : UniqueFactorizationMonoid α) :
    UniqueFactorizationMonoid β := by
  rw [UniqueFactorizationMonoid.iff_exists_prime_factors] at hα⊢
  intro a ha
  obtain ⟨w, hp, u, h⟩ :=
    hα (e.symm a) fun h =>
      ha <| by
        convert ← map_zero e
        simp [h]
  exact
    ⟨w.map e, fun b hb =>
      let ⟨c, hc, he⟩ := Multiset.mem_map.1 hb
      he ▸ e.prime_iff.1 (hp c hc),
      Units.map e.to_monoid_hom u, by
      erw [Multiset.prod_hom, ← e.map_mul, h]
      simp ⟩

theorem MulEquiv.unique_factorization_monoid_iff (e : α ≃* β) :
    UniqueFactorizationMonoid α ↔ UniqueFactorizationMonoid β :=
  ⟨e.UniqueFactorizationMonoid, e.symm.UniqueFactorizationMonoid⟩

end

theorem irreducible_iff_prime_of_exists_unique_irreducible_factors [CancelCommMonoidWithZero α]
    (eif : ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀, ∀ b ∈ f, ∀, Irreducible b) ∧ f.Prod ~ᵤ a)
    (uif :
      ∀ f g : Multiset α,
        (∀, ∀ x ∈ f, ∀, Irreducible x) →
          (∀, ∀ x ∈ g, ∀, Irreducible x) → f.Prod ~ᵤ g.Prod → Multiset.Rel Associated f g)
    (p : α) : Irreducible p ↔ Prime p :=
  ⟨by
    let this := Classical.decEq α <;>
      exact fun hpi =>
        ⟨hpi.ne_zero, hpi.1, fun a b ⟨x, hx⟩ =>
          if hab0 : a * b = 0 then
            (eq_zero_or_eq_zero_of_mul_eq_zero hab0).elim
              (fun ha0 => by
                simp [← ha0])
              fun hb0 => by
              simp [← hb0]
          else by
            have hx0 : x ≠ 0 := fun hx0 => by
              simp_all
            have ha0 : a ≠ 0 := left_ne_zero_of_mul hab0
            have hb0 : b ≠ 0 := right_ne_zero_of_mul hab0
            cases' eif x hx0 with fx hfx
            cases' eif a ha0 with fa hfa
            cases' eif b hb0 with fb hfb
            have h : Multiset.Rel Associated (p ::ₘ fx) (fa + fb) := by
              apply uif
              · exact fun i hi => (Multiset.mem_cons.1 hi).elim (fun hip => hip.symm ▸ hpi) (hfx.1 _)
                
              · exact fun i hi => (Multiset.mem_add.1 hi).elim (hfa.1 _) (hfb.1 _)
                
              calc Multiset.prod (p ::ₘ fx) ~ᵤ a * b := by
                  rw [hx, Multiset.prod_cons] <;> exact hfx.2.mul_left _ _ ~ᵤ fa.Prod * fb.Prod :=
                  hfa.2.symm.mul_mul hfb.2.symm _ = _ := by
                  rw [Multiset.prod_add]
            exact
              let ⟨q, hqf, hq⟩ := Multiset.exists_mem_of_rel_of_mem h (Multiset.mem_cons_self p _)
              (Multiset.mem_add.1 hqf).elim
                (fun hqa => Or.inl <| hq.dvd_iff_dvd_left.2 <| hfa.2.dvd_iff_dvd_right.1 (Multiset.dvd_prod hqa))
                fun hqb => Or.inr <| hq.dvd_iff_dvd_left.2 <| hfb.2.dvd_iff_dvd_right.1 (Multiset.dvd_prod hqb)⟩,
    Prime.irreducible⟩

theorem UniqueFactorizationMonoid.of_exists_unique_irreducible_factors [CancelCommMonoidWithZero α]
    (eif : ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀, ∀ b ∈ f, ∀, Irreducible b) ∧ f.Prod ~ᵤ a)
    (uif :
      ∀ f g : Multiset α,
        (∀, ∀ x ∈ f, ∀, Irreducible x) →
          (∀, ∀ x ∈ g, ∀, Irreducible x) → f.Prod ~ᵤ g.Prod → Multiset.Rel Associated f g) :
    UniqueFactorizationMonoid α :=
  UniqueFactorizationMonoid.of_exists_prime_factors
    (by
      convert eif
      simp_rw [irreducible_iff_prime_of_exists_unique_irreducible_factors eif uif])

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [DecidableEq α]

variable [UniqueFactorizationMonoid α]

/-- Noncomputably determines the multiset of prime factors. -/
noncomputable def factors (a : α) : Multiset α :=
  if h : a = 0 then 0 else Classical.some (UniqueFactorizationMonoid.exists_prime_factors a h)

theorem factors_prod {a : α} (ane0 : a ≠ 0) : Associated (factors a).Prod a := by
  rw [factors, dif_neg ane0]
  exact (Classical.some_spec (exists_prime_factors a ane0)).2

theorem ne_zero_of_mem_factors {p a : α} (h : p ∈ factors a) : a ≠ 0 := by
  intro ha
  rw [factors, dif_pos ha] at h
  exact Multiset.not_mem_zero _ h

theorem dvd_of_mem_factors {p a : α} (h : p ∈ factors a) : p ∣ a :=
  dvd_trans (Multiset.dvd_prod h) (Associated.dvd (factors_prod (ne_zero_of_mem_factors h)))

theorem prime_of_factor {a : α} (x : α) (hx : x ∈ factors a) : Prime x := by
  have ane0 := ne_zero_of_mem_factors hx
  rw [factors, dif_neg ane0] at hx
  exact (Classical.some_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 x hx

theorem irreducible_of_factor {a : α} : ∀ x : α, x ∈ factors a → Irreducible x := fun x h =>
  (prime_of_factor x h).Irreducible

@[simp]
theorem factors_zero : factors (0 : α) = 0 := by
  simp [← factors]

@[simp]
theorem factors_one : factors (1 : α) = 0 := by
  nontriviality α using ← factors
  rw [← Multiset.rel_zero_right]
  refine' factors_unique irreducible_of_factor (fun x hx => (Multiset.not_mem_zero x hx).elim) _
  rw [Multiset.prod_zero]
  exact factors_prod one_ne_zero

theorem exists_mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) : p ∣ a → ∃ q ∈ factors a, p ~ᵤ q :=
  fun ⟨b, hb⟩ =>
  have hb0 : b ≠ 0 := fun hb0 => by
    simp_all
  have : Multiset.Rel Associated (p ::ₘ factors b) (factors a) :=
    factors_unique (fun x hx => (Multiset.mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_factor _))
      irreducible_of_factor
      (Associated.symm <|
        calc
          Multiset.prod (factors a) ~ᵤ a := factors_prod ha0
          _ = p * b := hb
          _ ~ᵤ Multiset.prod (p ::ₘ factors b) := by
            rw [Multiset.prod_cons] <;> exact (factors_prod hb0).symm.mul_left _
          )
  Multiset.exists_mem_of_rel_of_mem this
    (by
      simp )

theorem factors_mul {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    Multiset.Rel Associated (factors (x * y)) (factors x + factors y) := by
  refine'
    factors_unique irreducible_of_factor
      (fun a ha => (multiset.mem_add.mp ha).byCases (irreducible_of_factor _) (irreducible_of_factor _))
      ((factors_prod (mul_ne_zero hx hy)).trans _)
  rw [Multiset.prod_add]
  exact (Associated.mul_mul (factors_prod hx) (factors_prod hy)).symm

theorem factors_pow {x : α} (n : ℕ) : Multiset.Rel Associated (factors (x ^ n)) (n • factors x) := by
  induction' n with n ih
  · simp
    
  by_cases' h0 : x = 0
  · simp [← h0, ← zero_pow n.succ_pos, ← smul_zero]
    
  rw [pow_succₓ, succ_nsmul]
  refine' Multiset.Rel.trans _ (factors_mul h0 (pow_ne_zero n h0)) _
  refine' Multiset.Rel.add _ ih
  exact Multiset.rel_refl_of_refl_on fun y hy => Associated.refl _

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [DecidableEq α] [NormalizationMonoid α]

variable [UniqueFactorizationMonoid α]

/-- Noncomputably determines the multiset of prime factors. -/
noncomputable def normalizedFactors (a : α) : Multiset α :=
  Multiset.map normalize <| factors a

/-- An arbitrary choice of factors of `x : M` is exactly the (unique) normalized set of factors,
if `M` has a trivial group of units. -/
@[simp]
theorem factors_eq_normalized_factors {M : Type _} [CancelCommMonoidWithZero M] [DecidableEq M]
    [UniqueFactorizationMonoid M] [Unique Mˣ] (x : M) : factors x = normalizedFactors x := by
  unfold normalized_factors
  convert (Multiset.map_id (factors x)).symm
  ext p
  exact normalize_eq p

theorem normalized_factors_prod {a : α} (ane0 : a ≠ 0) : Associated (normalizedFactors a).Prod a := by
  rw [normalized_factors, factors, dif_neg ane0]
  refine' Associated.trans _ (Classical.some_spec (exists_prime_factors a ane0)).2
  rw [← Associates.mk_eq_mk_iff_associated, ← Associates.prod_mk, ← Associates.prod_mk, Multiset.map_map]
  congr 2
  ext
  rw [Function.comp_applyₓ, Associates.mk_normalize]

theorem prime_of_normalized_factor {a : α} : ∀ x : α, x ∈ normalizedFactors a → Prime x := by
  rw [normalized_factors, factors]
  split_ifs with ane0
  · simp
    
  intro x hx
  rcases Multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩
  rw [(normalize_associated _).prime_iff]
  exact (Classical.some_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 y hy

theorem irreducible_of_normalized_factor {a : α} : ∀ x : α, x ∈ normalizedFactors a → Irreducible x := fun x h =>
  (prime_of_normalized_factor x h).Irreducible

theorem normalize_normalized_factor {a : α} : ∀ x : α, x ∈ normalizedFactors a → normalize x = x := by
  rw [normalized_factors, factors]
  split_ifs with h
  · simp
    
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
  apply normalize_idem

theorem normalized_factors_irreducible {a : α} (ha : Irreducible a) : normalizedFactors a = {normalize a} := by
  obtain ⟨p, a_assoc, hp⟩ :=
    prime_factors_irreducible ha ⟨prime_of_normalized_factor, normalized_factors_prod ha.ne_zero⟩
  have p_mem : p ∈ normalized_factors a := by
    rw [hp]
    exact Multiset.mem_singleton_self _
  convert hp
  rwa [← normalize_normalized_factor p p_mem, normalize_eq_normalize_iff, dvd_dvd_iff_associated]

theorem exists_mem_normalized_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    p ∣ a → ∃ q ∈ normalizedFactors a, p ~ᵤ q := fun ⟨b, hb⟩ =>
  have hb0 : b ≠ 0 := fun hb0 => by
    simp_all
  have : Multiset.Rel Associated (p ::ₘ normalizedFactors b) (normalizedFactors a) :=
    factors_unique
      (fun x hx => (Multiset.mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_normalized_factor _))
      irreducible_of_normalized_factor
      (Associated.symm <|
        calc
          Multiset.prod (normalizedFactors a) ~ᵤ a := normalized_factors_prod ha0
          _ = p * b := hb
          _ ~ᵤ Multiset.prod (p ::ₘ normalizedFactors b) := by
            rw [Multiset.prod_cons] <;> exact (normalized_factors_prod hb0).symm.mul_left _
          )
  Multiset.exists_mem_of_rel_of_mem this
    (by
      simp )

@[simp]
theorem normalized_factors_zero : normalizedFactors (0 : α) = 0 := by
  simp [← normalized_factors, ← factors]

@[simp]
theorem normalized_factors_one : normalizedFactors (1 : α) = 0 := by
  nontriviality α using ← normalized_factors, ← factors
  rw [← Multiset.rel_zero_right]
  apply factors_unique irreducible_of_normalized_factor
  · intro x hx
    exfalso
    apply Multiset.not_mem_zero x hx
    
  · simp [← normalized_factors_prod (@one_ne_zero α _ _)]
    
  infer_instance

@[simp]
theorem normalized_factors_mul {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    normalizedFactors (x * y) = normalizedFactors x + normalizedFactors y := by
  have h : (normalize : α → α) = Associates.out ∘ Associates.mk := by
    ext
    rw [Function.comp_applyₓ, Associates.out_mk]
  rw [← Multiset.map_id' (normalized_factors (x * y)), ← Multiset.map_id' (normalized_factors x), ←
    Multiset.map_id' (normalized_factors y), ← Multiset.map_congr rfl normalize_normalized_factor, ←
    Multiset.map_congr rfl normalize_normalized_factor, ← Multiset.map_congr rfl normalize_normalized_factor, ←
    Multiset.map_add, h, ← Multiset.map_map Associates.out, eq_comm, ← Multiset.map_map Associates.out]
  refine' congr rfl _
  apply Multiset.map_mk_eq_map_mk_of_rel
  apply factors_unique
  · intro x hx
    rcases Multiset.mem_add.1 hx with (hx | hx) <;> exact irreducible_of_normalized_factor x hx
    
  · exact irreducible_of_normalized_factor
    
  · rw [Multiset.prod_add]
    exact
      ((normalized_factors_prod hx).mul_mul (normalized_factors_prod hy)).trans
        (normalized_factors_prod (mul_ne_zero hx hy)).symm
    

@[simp]
theorem normalized_factors_pow {x : α} (n : ℕ) : normalizedFactors (x ^ n) = n • normalizedFactors x := by
  induction' n with n ih
  · simp
    
  by_cases' h0 : x = 0
  · simp [← h0, ← zero_pow n.succ_pos, ← smul_zero]
    
  rw [pow_succₓ, succ_nsmul, normalized_factors_mul h0 (pow_ne_zero _ h0), ih]

theorem _root_.irreducible.normalized_factors_pow {p : α} (hp : Irreducible p) (k : ℕ) :
    normalizedFactors (p ^ k) = Multiset.repeat (normalize p) k := by
  rw [normalized_factors_pow, normalized_factors_irreducible hp, Multiset.nsmul_singleton]

theorem dvd_iff_normalized_factors_le_normalized_factors {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ∣ y ↔ normalizedFactors x ≤ normalizedFactors y := by
  constructor
  · rintro ⟨c, rfl⟩
    simp [← hx, ← right_ne_zero_of_mul hy]
    
  · rw [← (normalized_factors_prod hx).dvd_iff_dvd_left, ← (normalized_factors_prod hy).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
    

theorem normalized_factors_of_irreducible_pow {p : α} (hp : Irreducible p) (k : ℕ) :
    normalizedFactors (p ^ k) = Multiset.repeat (normalize p) k := by
  rw [normalized_factors_pow, normalized_factors_irreducible hp, Multiset.nsmul_singleton]

theorem zero_not_mem_normalized_factors (x : α) : (0 : α) ∉ normalizedFactors x := fun h =>
  Prime.ne_zero (prime_of_normalized_factor _ h) rfl

theorem dvd_of_mem_normalized_factors {a p : α} (H : p ∈ normalizedFactors a) : p ∣ a := by
  by_cases' hcases : a = 0
  · rw [hcases]
    exact dvd_zero p
    
  · exact dvd_trans (Multiset.dvd_prod H) (Associated.dvd (normalized_factors_prod hcases))
    

theorem exists_associated_prime_pow_of_unique_normalized_factor {p r : α} (h : ∀ {m}, m ∈ normalizedFactors r → m = p)
    (hr : r ≠ 0) : ∃ i : ℕ, Associated (p ^ i) r := by
  use (normalized_factors r).card
  have := UniqueFactorizationMonoid.normalized_factors_prod hr
  rwa [Multiset.eq_repeat_of_mem fun b => h, Multiset.prod_repeat] at this

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

open Classical

open Multiset Associates

noncomputable section

variable [CancelCommMonoidWithZero α] [Nontrivial α] [UniqueFactorizationMonoid α]

/-- Noncomputably defines a `normalization_monoid` structure on a `unique_factorization_monoid`. -/
protected def normalizationMonoid : NormalizationMonoid α :=
  normalizationMonoidOfMonoidHomRightInverse
    { toFun := fun a : Associates α =>
        if a = 0 then 0
        else ((normalizedFactors a).map (Classical.some mk_surjective.HasRightInverse : Associates α → α)).Prod,
      map_one' := by
        simp ,
      map_mul' := fun x y => by
        by_cases' hx : x = 0
        · simp [← hx]
          
        by_cases' hy : y = 0
        · simp [← hy]
          
        simp [← hx, ← hy] }
    (by
      intro x
      dsimp'
      by_cases' hx : x = 0
      · simp [← hx]
        
      have h :
        Associates.mkMonoidHom ∘ Classical.some mk_surjective.has_right_inverse = (id : Associates α → Associates α) :=
        by
        ext x
        rw [Function.comp_applyₓ, mk_monoid_hom_apply, Classical.some_spec mk_surjective.has_right_inverse x]
        rfl
      rw [if_neg hx, ← mk_monoid_hom_apply, MonoidHom.map_multiset_prod, map_map, h, map_id, ← associated_iff_eq]
      apply normalized_factors_prod hx)

instance : Inhabited (NormalizationMonoid α) :=
  ⟨UniqueFactorizationMonoid.normalizationMonoid⟩

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

variable {R : Type _} [CancelCommMonoidWithZero R] [UniqueFactorizationMonoid R]

theorem no_factors_of_no_prime_factors {a b : R} (ha : a ≠ 0) (h : ∀ {d}, d ∣ a → d ∣ b → ¬Prime d) :
    ∀ {d}, d ∣ a → d ∣ b → IsUnit d := fun d =>
  induction_on_prime d
    (by
      simp only [← zero_dvd_iff]
      intros
      contradiction)
    (fun x hx _ _ => hx) fun d q hp hq ih dvd_a dvd_b =>
    absurd hq (h (dvd_of_mul_right_dvd dvd_a) (dvd_of_mul_right_dvd dvd_b))

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
Compare `is_coprime.dvd_of_dvd_mul_left`. -/
theorem dvd_of_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a ≠ 0) :
    (∀ {d}, d ∣ a → d ∣ c → ¬Prime d) → a ∣ b * c → a ∣ b := by
  refine' induction_on_prime c _ _ _
  · intro no_factors
    simp only [← dvd_zero, ← mul_zero, ← forall_prop_of_true]
    have := Classical.propDecidable
    exact is_unit_iff_forall_dvd.mp (no_factors_of_no_prime_factors ha (@no_factors) (dvd_refl a) (dvd_zero a)) _
    
  · rintro _ ⟨x, rfl⟩ _ a_dvd_bx
    apply units.dvd_mul_right.mp a_dvd_bx
    
  · intro c p hc hp ih no_factors a_dvd_bpc
    apply ih fun q dvd_a dvd_c hq => no_factors dvd_a (dvd_c.mul_left _) hq
    rw [mul_left_commₓ] at a_dvd_bpc
    refine' Or.resolve_left (hp.left_dvd_or_dvd_right_of_dvd_mul a_dvd_bpc) fun h => _
    exact no_factors h (dvd_mul_right p c) hp
    

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
Compare `is_coprime.dvd_of_dvd_mul_right`. -/
theorem dvd_of_dvd_mul_right_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
    (no_factors : ∀ {d}, d ∣ a → d ∣ b → ¬Prime d) : a ∣ b * c → a ∣ c := by
  simpa [← mul_comm b c] using dvd_of_dvd_mul_left_of_no_prime_factors ha @no_factors

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a «expr ≠ » (0 : R))
/-- If `a ≠ 0, b` are elements of a unique factorization domain, then dividing
out their common factor `c'` gives `a'` and `b'` with no factors in common. -/
theorem exists_reduced_factors :
    ∀ (a) (_ : a ≠ (0 : R)) (b), ∃ a' b' c', (∀ {d}, d ∣ a' → d ∣ b' → IsUnit d) ∧ c' * a' = a ∧ c' * b' = b := by
  have := Classical.propDecidable
  intro a
  refine' induction_on_prime a _ _ _
  · intros
    contradiction
    
  · intro a a_unit a_ne_zero b
    use a, b, 1
    constructor
    · intro p p_dvd_a _
      exact is_unit_of_dvd_unit p_dvd_a a_unit
      
    · simp
      
    
  · intro a p a_ne_zero p_prime ih_a pa_ne_zero b
    by_cases' p ∣ b
    · rcases h with ⟨b, rfl⟩
      obtain ⟨a', b', c', no_factor, ha', hb'⟩ := ih_a a_ne_zero b
      refine' ⟨a', b', p * c', @no_factor, _, _⟩
      · rw [mul_assoc, ha']
        
      · rw [mul_assoc, hb']
        
      
    · obtain ⟨a', b', c', coprime, rfl, rfl⟩ := ih_a a_ne_zero b
      refine' ⟨p * a', b', c', _, mul_left_commₓ _ _ _, rfl⟩
      intro q q_dvd_pa' q_dvd_b'
      cases' p_prime.left_dvd_or_dvd_right_of_dvd_mul q_dvd_pa' with p_dvd_q q_dvd_a'
      · have : p ∣ c' * b' := dvd_mul_of_dvd_right (p_dvd_q.trans q_dvd_b') _
        contradiction
        
      exact coprime q_dvd_a' q_dvd_b'
      
    

theorem exists_reduced_factors' (a b : R) (hb : b ≠ 0) :
    ∃ a' b' c', (∀ {d}, d ∣ a' → d ∣ b' → IsUnit d) ∧ c' * a' = a ∧ c' * b' = b :=
  let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
  ⟨a', b', c', fun _ hpb hpa => no_factor hpa hpb, ha, hb⟩

section multiplicity

variable [Nontrivial R] [NormalizationMonoid R] [DecidableEq R]

variable [dec_dvd : DecidableRel (Dvd.Dvd : R → R → Prop)]

open multiplicity Multiset

include dec_dvd

theorem le_multiplicity_iff_repeat_le_normalized_factors {a b : R} {n : ℕ} (ha : Irreducible a) (hb : b ≠ 0) :
    ↑n ≤ multiplicity a b ↔ repeat (normalize a) n ≤ normalizedFactors b := by
  rw [← pow_dvd_iff_le_multiplicity]
  revert b
  induction' n with n ih
  · simp
    
  intro b hb
  constructor
  · rintro ⟨c, rfl⟩
    rw [Ne.def, pow_succₓ, mul_assoc, mul_eq_zero, Decidable.not_or_iff_and_not] at hb
    rw [pow_succₓ, mul_assoc, normalized_factors_mul hb.1 hb.2, repeat_succ, normalized_factors_irreducible ha,
      singleton_add, cons_le_cons_iff, ← ih hb.2]
    apply Dvd.intro _ rfl
    
  · rw [Multiset.le_iff_exists_add]
    rintro ⟨u, hu⟩
    rw [← (normalized_factors_prod hb).dvd_iff_dvd_right, hu, prod_add, prod_repeat]
    exact (Associated.pow_pow <| associated_normalize a).Dvd.trans (Dvd.intro u.prod rfl)
    

/-- The multiplicity of an irreducible factor of a nonzero element is exactly the number of times
the normalized factor occurs in the `normalized_factors`.

See also `count_normalized_factors_eq` which expands the definition of `multiplicity`
to produce a specification for `count (normalized_factors _) _`..
-/
theorem multiplicity_eq_count_normalized_factors {a b : R} (ha : Irreducible a) (hb : b ≠ 0) :
    multiplicity a b = (normalizedFactors b).count (normalize a) := by
  apply le_antisymmₓ
  · apply PartEnat.le_of_lt_add_one
    rw [← Nat.cast_oneₓ, ← Nat.cast_addₓ, lt_iff_not_geₓ, ge_iff_le,
      le_multiplicity_iff_repeat_le_normalized_factors ha hb, ← le_count_iff_repeat_le]
    simp
    
  rw [le_multiplicity_iff_repeat_le_normalized_factors ha hb, ← le_count_iff_repeat_le]

omit dec_dvd

/-- The number of times an irreducible factor `p` appears in `normalized_factors x` is defined by
the number of times it divides `x`.

See also `multiplicity_eq_count_normalized_factors` if `n` is given by `multiplicity p x`.
-/
theorem count_normalized_factors_eq {p x : R} (hp : Irreducible p) (hnorm : normalize p = p) {n : ℕ} (hle : p ^ n ∣ x)
    (hlt : ¬p ^ (n + 1) ∣ x) : (normalizedFactors x).count p = n := by
  let this : DecidableRel ((· ∣ ·) : R → R → Prop) := fun _ _ => Classical.propDecidable _
  by_cases' hx0 : x = 0
  · simp [← hx0] at hlt
    contradiction
    
  rw [← PartEnat.coe_inj]
  convert (multiplicity_eq_count_normalized_factors hp hx0).symm
  · exact hnorm.symm
    
  exact (multiplicity.eq_coe_iff.mpr ⟨hle, hlt⟩).symm

/-- The number of times an irreducible factor `p` appears in `normalized_factors x` is defined by
the number of times it divides `x`. This is a slightly more general version of
`unique_factorization_monoid.count_normalized_factors_eq` that allows `p = 0`.

See also `multiplicity_eq_count_normalized_factors` if `n` is given by `multiplicity p x`.
-/
theorem count_normalized_factors_eq' {p x : R} (hp : p = 0 ∨ Irreducible p) (hnorm : normalize p = p) {n : ℕ}
    (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) : (normalizedFactors x).count p = n := by
  rcases hp with (rfl | hp)
  · cases n
    · exact count_eq_zero.2 (zero_not_mem_normalized_factors _)
      
    · rw [zero_pow (Nat.succ_posₓ _)] at hle hlt
      exact absurd hle hlt
      
    
  · exact count_normalized_factors_eq hp hnorm hle hlt
    

end multiplicity

end UniqueFactorizationMonoid

namespace Associates

open UniqueFactorizationMonoid Associated Multiset

variable [CancelCommMonoidWithZero α]

/-- `factor_set α` representation elements of unique factorization domain as multisets.
`multiset α` produced by `normalized_factors` are only unique up to associated elements, while the
multisets in `factor_set α` are unique by equality and restricted to irreducible elements. This
gives us a representation of each element as a unique multisets (or the added ⊤ for 0), which has a
complete lattice struture. Infimum is the greatest common divisor and supremum is the least common
multiple.
-/
@[reducible]
def FactorSet.{u} (α : Type u) [CancelCommMonoidWithZero α] : Type u :=
  WithTop (Multiset { a : Associates α // Irreducible a })

attribute [local instance] Associated.setoid

theorem FactorSet.coe_add {a b : Multiset { a : Associates α // Irreducible a }} : (↑(a + b) : FactorSet α) = a + b :=
  by
  norm_cast

theorem FactorSet.sup_add_inf_eq_add [DecidableEq (Associates α)] : ∀ a b : FactorSet α, a⊔b + a⊓b = a + b
  | none, b =>
    show ⊤⊔b + ⊤⊓b = ⊤ + b by
      simp
  | a, none =>
    show a⊔⊤ + a⊓⊤ = a + ⊤ by
      simp
  | some a, some b =>
    show (a : FactorSet α)⊔b + a⊓b = a + b by
      rw [← WithTop.coe_sup, ← WithTop.coe_inf, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_eq_coe]
      exact Multiset.union_add_inter _ _

/-- Evaluates the product of a `factor_set` to be the product of the corresponding multiset,
  or `0` if there is none. -/
def FactorSet.prod : FactorSet α → Associates α
  | none => 0
  | some s => (s.map coe).Prod

@[simp]
theorem prod_top : (⊤ : FactorSet α).Prod = 0 :=
  rfl

@[simp]
theorem prod_coe {s : Multiset { a : Associates α // Irreducible a }} : (s : FactorSet α).Prod = (s.map coe).Prod :=
  rfl

@[simp]
theorem prod_add : ∀ a b : FactorSet α, (a + b).Prod = a.Prod * b.Prod
  | none, b =>
    show (⊤ + b).Prod = (⊤ : FactorSet α).Prod * b.Prod by
      simp
  | a, none =>
    show (a + ⊤).Prod = a.Prod * (⊤ : FactorSet α).Prod by
      simp
  | some a, some b =>
    show (↑a + ↑b : FactorSet α).Prod = (↑a : FactorSet α).Prod * (↑b : FactorSet α).Prod by
      rw [← factor_set.coe_add, prod_coe, prod_coe, prod_coe, Multiset.map_add, Multiset.prod_add]

theorem prod_mono : ∀ {a b : FactorSet α}, a ≤ b → a.Prod ≤ b.Prod
  | none, b, h => by
    have : b = ⊤ := top_unique h
    rw [this, prod_top] <;> exact le_rfl
  | a, none, h =>
    show a.Prod ≤ (⊤ : FactorSet α).Prod by
      simp <;> exact le_top
  | some a, some b, h => prod_le_prod <| Multiset.map_le_map <| WithTop.coe_le_coe.1 <| h

theorem FactorSet.prod_eq_zero_iff [Nontrivial α] (p : FactorSet α) : p.Prod = 0 ↔ p = ⊤ := by
  induction p using WithTop.recTopCoe
  · simp only [← iff_selfₓ, ← eq_self_iff_true, ← Associates.prod_top]
    
  simp only [← prod_coe, ← WithTop.coe_ne_top, ← iff_falseₓ, ← prod_eq_zero_iff, ← Multiset.mem_map]
  rintro ⟨⟨a, ha⟩, -, eq⟩
  rw [Subtype.coe_mk] at eq
  exact ha.ne_zero Eq

/-- `bcount p s` is the multiplicity of `p` in the factor_set `s` (with bundled `p`)-/
def bcount [DecidableEq (Associates α)] (p : { a : Associates α // Irreducible a }) : FactorSet α → ℕ
  | none => 0
  | some s => s.count p

variable [dec_irr : ∀ p : Associates α, Decidable (Irreducible p)]

include dec_irr

/-- `count p s` is the multiplicity of the irreducible `p` in the factor_set `s`.

If `p` is not irreducible, `count p s` is defined to be `0`. -/
def count [DecidableEq (Associates α)] (p : Associates α) : FactorSet α → ℕ :=
  if hp : Irreducible p then bcount ⟨p, hp⟩ else 0

@[simp]
theorem count_some [DecidableEq (Associates α)] {p : Associates α} (hp : Irreducible p) (s : Multiset _) :
    count p (some s) = s.count ⟨p, hp⟩ := by
  dunfold count
  split_ifs
  rfl

@[simp]
theorem count_zero [DecidableEq (Associates α)] {p : Associates α} (hp : Irreducible p) :
    count p (0 : FactorSet α) = 0 := by
  dunfold count
  split_ifs
  rfl

theorem count_reducible [DecidableEq (Associates α)] {p : Associates α} (hp : ¬Irreducible p) : count p = 0 :=
  dif_neg hp

omit dec_irr

/-- membership in a factor_set (bundled version) -/
def BfactorSetMem : { a : Associates α // Irreducible a } → FactorSet α → Prop
  | _, ⊤ => True
  | p, some l => p ∈ l

include dec_irr

/-- `factor_set_mem p s` is the predicate that the irreducible `p` is a member of
`s : factor_set α`.

If `p` is not irreducible, `p` is not a member of any `factor_set`. -/
def FactorSetMem (p : Associates α) (s : FactorSet α) : Prop :=
  if hp : Irreducible p then BfactorSetMem ⟨p, hp⟩ s else False

instance : HasMem (Associates α) (FactorSet α) :=
  ⟨FactorSetMem⟩

@[simp]
theorem factor_set_mem_eq_mem (p : Associates α) (s : FactorSet α) : FactorSetMem p s = (p ∈ s) :=
  rfl

theorem mem_factor_set_top {p : Associates α} {hp : Irreducible p} : p ∈ (⊤ : FactorSet α) := by
  dunfold HasMem.Mem
  dunfold factor_set_mem
  split_ifs
  exact trivialₓ

theorem mem_factor_set_some {p : Associates α} {hp : Irreducible p}
    {l : Multiset { a : Associates α // Irreducible a }} : p ∈ (l : FactorSet α) ↔ Subtype.mk p hp ∈ l := by
  dunfold HasMem.Mem
  dunfold factor_set_mem
  split_ifs
  rfl

theorem reducible_not_mem_factor_set {p : Associates α} (hp : ¬Irreducible p) (s : FactorSet α) : ¬p ∈ s :=
  fun h : if hp : Irreducible p then BfactorSetMem ⟨p, hp⟩ s else False => by
  rwa [dif_neg hp] at h

omit dec_irr

variable [UniqueFactorizationMonoid α]

theorem unique' {p q : Multiset (Associates α)} :
    (∀, ∀ a ∈ p, ∀, Irreducible a) → (∀, ∀ a ∈ q, ∀, Irreducible a) → p.Prod = q.Prod → p = q := by
  apply Multiset.induction_on_multiset_quot p
  apply Multiset.induction_on_multiset_quot q
  intro s t hs ht eq
  refine' Multiset.map_mk_eq_map_mk_of_rel (UniqueFactorizationMonoid.factors_unique _ _ _)
  · exact fun a ha => (irreducible_mk _).1 <| hs _ <| Multiset.mem_map_of_mem _ ha
    
  · exact fun a ha => (irreducible_mk _).1 <| ht _ <| Multiset.mem_map_of_mem _ ha
    
  simpa [← quot_mk_eq_mk, ← prod_mk, ← mk_eq_mk_iff_associated] using Eq

theorem FactorSet.unique [Nontrivial α] {p q : FactorSet α} (h : p.Prod = q.Prod) : p = q := by
  induction p using WithTop.recTopCoe <;> induction q using WithTop.recTopCoe
  · rfl
    
  · rw [eq_comm, ← factor_set.prod_eq_zero_iff, ← h, Associates.prod_top]
    
  · rw [← factor_set.prod_eq_zero_iff, h, Associates.prod_top]
    
  · congr 1
    rw [← Multiset.map_eq_map Subtype.coe_injective]
    apply unique' _ _ h <;>
      · intro a ha
        obtain ⟨⟨a', irred⟩, -, rfl⟩ := multiset.mem_map.mp ha
        rwa [Subtype.coe_mk]
        
    

theorem prod_le_prod_iff_le [Nontrivial α] {p q : Multiset (Associates α)} (hp : ∀, ∀ a ∈ p, ∀, Irreducible a)
    (hq : ∀, ∀ a ∈ q, ∀, Irreducible a) : p.Prod ≤ q.Prod ↔ p ≤ q :=
  Iff.intro
    (by
      classical
      rintro ⟨c, eqc⟩
      refine' Multiset.le_iff_exists_add.2 ⟨factors c, unique' hq (fun x hx => _) _⟩
      · obtain h | h := Multiset.mem_add.1 hx
        · exact hp x h
          
        · exact irreducible_of_factor _ h
          
        
      · rw [eqc, Multiset.prod_add]
        congr
        refine' associated_iff_eq.mp (factors_prod fun hc => _).symm
        refine' not_irreducible_zero (hq _ _)
        rw [← prod_eq_zero_iff, eqc, hc, mul_zero]
        )
    prod_le_prod

variable [dec : DecidableEq α] [dec' : DecidableEq (Associates α)]

include dec

/-- This returns the multiset of irreducible factors as a `factor_set`,
  a multiset of irreducible associates `with_top`. -/
noncomputable def factors' (a : α) : Multiset { a : Associates α // Irreducible a } :=
  (factors a).pmap (fun a ha => ⟨Associates.mk a, (irreducible_mk _).2 ha⟩) irreducible_of_factor

@[simp]
theorem map_subtype_coe_factors' {a : α} : (factors' a).map coe = (factors a).map Associates.mk := by
  simp [← factors', ← Multiset.map_pmap, ← Multiset.pmap_eq_map]

theorem factors'_cong {a b : α} (h : a ~ᵤ b) : factors' a = factors' b := by
  obtain rfl | hb := eq_or_ne b 0
  · rw [associated_zero_iff_eq_zero] at h
    rw [h]
    
  have ha : a ≠ 0 := by
    contrapose! hb with ha
    rw [← associated_zero_iff_eq_zero, ← ha]
    exact h.symm
  rw [← Multiset.map_eq_map Subtype.coe_injective, map_subtype_coe_factors', map_subtype_coe_factors', ←
    rel_associated_iff_map_eq_map]
  exact
    factors_unique irreducible_of_factor irreducible_of_factor
      ((factors_prod ha).trans <| h.trans <| (factors_prod hb).symm)

include dec'

/-- This returns the multiset of irreducible factors of an associate as a `factor_set`,
  a multiset of irreducible associates `with_top`. -/
noncomputable def factors (a : Associates α) : FactorSet α := by
  refine' if h : a = 0 then ⊤ else Quotientₓ.hrecOn a (fun x h => some <| factors' x) _ h
  intro a b hab
  apply Function.hfunext
  · have : a ~ᵤ 0 ↔ b ~ᵤ 0 := Iff.intro (fun ha0 => hab.symm.trans ha0) fun hb0 => hab.trans hb0
    simp only [← associated_zero_iff_eq_zero] at this
    simp only [← quotient_mk_eq_mk, ← this, ← mk_eq_zero]
    
  exact fun ha hb eq => heq_of_eq <| congr_arg some <| factors'_cong hab

@[simp]
theorem factors_0 : (0 : Associates α).factors = ⊤ :=
  dif_pos rfl

@[simp]
theorem factors_mk (a : α) (h : a ≠ 0) : (Associates.mk a).factors = factors' a := by
  classical
  apply dif_neg
  apply mt mk_eq_zero.1 h

@[simp]
theorem factors_prod (a : Associates α) : a.factors.Prod = a :=
  (Quotientₓ.induction_on a) fun a =>
    Decidable.byCases
      (fun this : Associates.mk a = 0 => by
        simp [← quotient_mk_eq_mk, ← this])
      fun this : Associates.mk a ≠ 0 => by
      have : a ≠ 0 := by
        simp_all
      simp [← this, ← quotient_mk_eq_mk, ← prod_mk, ← mk_eq_mk_iff_associated.2 (factors_prod this)]

theorem prod_factors [Nontrivial α] (s : FactorSet α) : s.Prod.factors = s :=
  factor_set.unique <| factors_prod _

@[nontriviality]
theorem factors_subsingleton [Subsingleton α] {a : Associates α} : a.factors = Option.none := by
  convert factors_0 <;> infer_instance

theorem factors_eq_none_iff_zero {a : Associates α} : a.factors = Option.none ↔ a = 0 := by
  nontriviality α
  exact
    ⟨fun h => by
      rwa [← factors_prod a, factor_set.prod_eq_zero_iff], fun h => h.symm ▸ factors_0⟩

theorem factors_eq_some_iff_ne_zero {a : Associates α} :
    (∃ s : Multiset { p : Associates α // Irreducible p }, a.factors = some s) ↔ a ≠ 0 := by
  rw [← Option.is_some_iff_exists, ← Option.ne_none_iff_is_some, Ne.def, Ne.def, factors_eq_none_iff_zero]

theorem eq_of_factors_eq_factors {a b : Associates α} (h : a.factors = b.factors) : a = b := by
  have : a.factors.Prod = b.factors.Prod := by
    rw [h]
  rwa [factors_prod, factors_prod] at this

omit dec dec'

theorem eq_of_prod_eq_prod [Nontrivial α] {a b : FactorSet α} (h : a.Prod = b.Prod) : a = b := by
  classical
  have : a.prod.factors = b.prod.factors := by
    rw [h]
  rwa [prod_factors, prod_factors] at this

include dec dec' dec_irr

theorem eq_factors_of_eq_counts {a b : Associates α} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ (p : Associates α) (hp : Irreducible p), p.count a.factors = p.count b.factors) : a.factors = b.factors := by
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb
  rw [h_sa, h_sb] at h⊢
  rw [Option.some_inj]
  have h_count : ∀ (p : Associates α) (hp : Irreducible p), sa.count ⟨p, hp⟩ = sb.count ⟨p, hp⟩ := by
    intro p hp
    rw [← count_some, ← count_some, h p hp]
  apply multiset.to_finsupp.injective
  ext ⟨p, hp⟩
  rw [Multiset.to_finsupp_apply, Multiset.to_finsupp_apply, h_count p hp]

theorem eq_of_eq_counts {a b : Associates α} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : Associates α, Irreducible p → p.count a.factors = p.count b.factors) : a = b :=
  eq_of_factors_eq_factors (eq_factors_of_eq_counts ha hb h)

theorem count_le_count_of_factors_le {a b p : Associates α} (hb : b ≠ 0) (hp : Irreducible p)
    (h : a.factors ≤ b.factors) : p.count a.factors ≤ p.count b.factors := by
  by_cases' ha : a = 0
  · simp_all
    
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb
  rw [h_sa, h_sb] at h⊢
  rw [count_some hp, count_some hp]
  rw [WithTop.some_le_some] at h
  exact Multiset.count_le_of_le _ h

omit dec_irr

@[simp]
theorem factors_mul (a b : Associates α) : (a * b).factors = a.factors + b.factors := by
  cases subsingleton_or_nontrivial α
  · simp [← Subsingleton.elimₓ a 0]
    
  refine' eq_of_prod_eq_prod (eq_of_factors_eq_factors _)
  rw [prod_add, factors_prod, factors_prod, factors_prod]

theorem factors_mono : ∀ {a b : Associates α}, a ≤ b → a.factors ≤ b.factors
  | s, t, ⟨d, rfl⟩ => by
    rw [factors_mul] <;> exact le_add_of_nonneg_right bot_le

theorem factors_le {a b : Associates α} : a.factors ≤ b.factors ↔ a ≤ b :=
  Iff.intro
    (fun h => by
      have : a.factors.Prod ≤ b.factors.Prod := prod_mono h
      rwa [factors_prod, factors_prod] at this)
    factors_mono

include dec_irr

theorem count_le_count_of_le {a b p : Associates α} (hb : b ≠ 0) (hp : Irreducible p) (h : a ≤ b) :
    p.count a.factors ≤ p.count b.factors :=
  count_le_count_of_factors_le hb hp <| factors_mono h

omit dec dec' dec_irr

theorem prod_le [Nontrivial α] {a b : FactorSet α} : a.Prod ≤ b.Prod ↔ a ≤ b := by
  classical
  exact
    Iff.intro
      (fun h => by
        have : a.prod.factors ≤ b.prod.factors := factors_mono h
        rwa [prod_factors, prod_factors] at this)
      prod_mono

include dec dec'

noncomputable instance : HasSup (Associates α) :=
  ⟨fun a b => (a.factors⊔b.factors).Prod⟩

noncomputable instance : HasInf (Associates α) :=
  ⟨fun a b => (a.factors⊓b.factors).Prod⟩

noncomputable instance : Lattice (Associates α) :=
  { Associates.partialOrder with sup := (·⊔·), inf := (·⊓·),
    sup_le := fun a b c hac hbc => factors_prod c ▸ prod_mono (sup_le (factors_mono hac) (factors_mono hbc)),
    le_sup_left := fun a b => le_transₓ (le_of_eqₓ (factors_prod a).symm) <| prod_mono <| le_sup_left,
    le_sup_right := fun a b => le_transₓ (le_of_eqₓ (factors_prod b).symm) <| prod_mono <| le_sup_right,
    le_inf := fun a b c hac hbc => factors_prod a ▸ prod_mono (le_inf (factors_mono hac) (factors_mono hbc)),
    inf_le_left := fun a b => le_transₓ (prod_mono inf_le_left) (le_of_eqₓ (factors_prod a)),
    inf_le_right := fun a b => le_transₓ (prod_mono inf_le_right) (le_of_eqₓ (factors_prod b)) }

theorem sup_mul_inf (a b : Associates α) : (a⊔b) * (a⊓b) = a * b :=
  show (a.factors⊔b.factors).Prod * (a.factors⊓b.factors).Prod = a * b by
    nontriviality α
    refine' eq_of_factors_eq_factors _
    rw [← prod_add, prod_factors, factors_mul, factor_set.sup_add_inf_eq_add]

include dec_irr

theorem dvd_of_mem_factors {a p : Associates α} {hp : Irreducible p} (hm : p ∈ factors a) : p ∣ a := by
  by_cases' ha0 : a = 0
  · rw [ha0]
    exact dvd_zero p
    
  obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha0
  rw [← Associates.factors_prod a]
  rw [← ha', factors_mk a0 nza] at hm⊢
  erw [prod_coe]
  apply Multiset.dvd_prod
  apply multiset.mem_map.mpr
  exact ⟨⟨p, hp⟩, mem_factor_set_some.mp hm, rfl⟩

omit dec'

theorem dvd_of_mem_factors' {a : α} {p : Associates α} {hp : Irreducible p} {hz : a ≠ 0}
    (h_mem : Subtype.mk p hp ∈ factors' a) : p ∣ Associates.mk a := by
  have := Classical.decEq (Associates α)
  apply @dvd_of_mem_factors _ _ _ _ _ _ _ _ hp
  rw [factors_mk _ hz]
  apply mem_factor_set_some.2 h_mem

omit dec_irr

theorem mem_factors'_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) (hd : p ∣ a) :
    Subtype.mk (Associates.mk p) ((irreducible_mk _).2 hp) ∈ factors' a := by
  obtain ⟨q, hq, hpq⟩ := exists_mem_factors_of_dvd ha0 hp hd
  apply multiset.mem_pmap.mpr
  use q
  use hq
  exact Subtype.eq (Eq.symm (mk_eq_mk_iff_associated.mpr hpq))

include dec_irr

theorem mem_factors'_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    Subtype.mk (Associates.mk p) ((irreducible_mk _).2 hp) ∈ factors' a ↔ p ∣ a := by
  constructor
  · rw [← mk_dvd_mk]
    apply dvd_of_mem_factors'
    apply ha0
    
  · apply mem_factors'_of_dvd ha0
    

include dec'

theorem mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) (hd : p ∣ a) :
    Associates.mk p ∈ factors (Associates.mk a) := by
  rw [factors_mk _ ha0]
  exact mem_factor_set_some.mpr (mem_factors'_of_dvd ha0 hp hd)

theorem mem_factors_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    Associates.mk p ∈ factors (Associates.mk a) ↔ p ∣ a := by
  constructor
  · rw [← mk_dvd_mk]
    apply dvd_of_mem_factors
    exact (irreducible_mk p).mpr hp
    
  · apply mem_factors_of_dvd ha0 hp
    

theorem exists_prime_dvd_of_not_inf_one {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) (h : Associates.mk a⊓Associates.mk b ≠ 1) :
    ∃ p : α, Prime p ∧ p ∣ a ∧ p ∣ b := by
  have hz : factors (Associates.mk a)⊓factors (Associates.mk b) ≠ 0 := by
    contrapose! h with hf
    change (factors (Associates.mk a)⊓factors (Associates.mk b)).Prod = 1
    rw [hf]
    exact Multiset.prod_zero
  rw [factors_mk a ha, factors_mk b hb, ← WithTop.coe_inf] at hz
  obtain ⟨⟨p0, p0_irr⟩, p0_mem⟩ := Multiset.exists_mem_of_ne_zero ((mt with_top.coe_eq_coe.mpr) hz)
  rw [Multiset.inf_eq_inter] at p0_mem
  obtain ⟨p, rfl⟩ : ∃ p, Associates.mk p = p0 := Quot.exists_rep p0
  refine' ⟨p, _, _, _⟩
  · rw [← irreducible_iff_prime, ← irreducible_mk]
    exact p0_irr
    
  · apply dvd_of_mk_le_mk
    apply dvd_of_mem_factors' (multiset.mem_inter.mp p0_mem).left
    apply ha
    
  · apply dvd_of_mk_le_mk
    apply dvd_of_mem_factors' (multiset.mem_inter.mp p0_mem).right
    apply hb
    

theorem coprime_iff_inf_one {a b : α} (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    Associates.mk a⊓Associates.mk b = 1 ↔ ∀ {d : α}, d ∣ a → d ∣ b → ¬Prime d := by
  constructor
  · intro hg p ha hb hp
    refine' ((Associates.prime_mk _).mpr hp).not_unit (is_unit_of_dvd_one _ _)
    rw [← hg]
    exact le_inf (mk_le_mk_of_dvd ha) (mk_le_mk_of_dvd hb)
    
  · contrapose
    intro hg hc
    obtain ⟨p, hp, hpa, hpb⟩ := exists_prime_dvd_of_not_inf_one ha0 hb0 hg
    exact hc hpa hpb hp
    

omit dec_irr

theorem factors_self [Nontrivial α] {p : Associates α} (hp : Irreducible p) : p.factors = some {⟨p, hp⟩} :=
  eq_of_prod_eq_prod
    (by
      rw [factors_prod, factor_set.prod, map_singleton, prod_singleton, Subtype.coe_mk])

theorem factors_prime_pow [Nontrivial α] {p : Associates α} (hp : Irreducible p) (k : ℕ) :
    factors (p ^ k) = some (Multiset.repeat ⟨p, hp⟩ k) :=
  eq_of_prod_eq_prod
    (by
      rw [Associates.factors_prod, factor_set.prod, Multiset.map_repeat, Multiset.prod_repeat, Subtype.coe_mk])

include dec_irr

theorem prime_pow_dvd_iff_le [Nontrivial α] {m p : Associates α} (h₁ : m ≠ 0) (h₂ : Irreducible p) {k : ℕ} :
    p ^ k ≤ m ↔ k ≤ count p m.factors := by
  obtain ⟨a, nz, rfl⟩ := Associates.exists_non_zero_rep h₁
  rw [factors_mk _ nz, ← WithTop.some_eq_coe, count_some, Multiset.le_count_iff_repeat_le, ← factors_le,
    factors_prime_pow h₂, factors_mk _ nz]
  exact WithTop.coe_le_coe

theorem le_of_count_ne_zero {m p : Associates α} (h0 : m ≠ 0) (hp : Irreducible p) : count p m.factors ≠ 0 → p ≤ m := by
  nontriviality α
  rw [← pos_iff_ne_zero]
  intro h
  rw [← pow_oneₓ p]
  apply (prime_pow_dvd_iff_le h0 hp).2
  simpa only

theorem count_ne_zero_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : Irreducible p) :
    (Associates.mk p).count (Associates.mk a).factors ≠ 0 ↔ p ∣ a := by
  nontriviality α
  rw [← Associates.mk_le_mk_iff_dvd_iff]
  refine'
    ⟨fun h => Associates.le_of_count_ne_zero (associates.mk_ne_zero.mpr ha0) ((Associates.irreducible_mk p).mpr hp) h,
      fun h => _⟩
  · rw [← pow_oneₓ (Associates.mk p),
      Associates.prime_pow_dvd_iff_le (associates.mk_ne_zero.mpr ha0) ((Associates.irreducible_mk p).mpr hp)] at h
    exact (zero_lt_one.trans_le h).ne'
    

theorem count_self [Nontrivial α] {p : Associates α} (hp : Irreducible p) : p.count p.factors = 1 := by
  simp [← factors_self hp, ← Associates.count_some hp]

theorem count_eq_zero_of_ne {p q : Associates α} (hp : Irreducible p) (hq : Irreducible q) (h : p ≠ q) :
    p.count q.factors = 0 :=
  not_ne_iff.mp fun h' =>
    h <|
      associated_iff_eq.mp <|
        hp.associated_of_dvd hq <| by
          nontriviality α
          exact le_of_count_ne_zero hq.ne_zero hp h'

theorem count_mul {a : Associates α} (ha : a ≠ 0) {b : Associates α} (hb : b ≠ 0) {p : Associates α}
    (hp : Irreducible p) : count p (factors (a * b)) = count p a.factors + count p b.factors := by
  obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha
  obtain ⟨b0, nzb, hb'⟩ := exists_non_zero_rep hb
  rw [factors_mul, ← ha', ← hb', factors_mk a0 nza, factors_mk b0 nzb, ← factor_set.coe_add, ← WithTop.some_eq_coe, ←
    WithTop.some_eq_coe, ← WithTop.some_eq_coe, count_some hp, Multiset.count_add, count_some hp, count_some hp]

theorem count_of_coprime {a : Associates α} (ha : a ≠ 0) {b : Associates α} (hb : b ≠ 0)
    (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {p : Associates α} (hp : Irreducible p) :
    count p a.factors = 0 ∨ count p b.factors = 0 := by
  rw [or_iff_not_imp_left, ← Ne.def]
  intro hca
  contrapose! hab with hcb
  exact ⟨p, le_of_count_ne_zero ha hp hca, le_of_count_ne_zero hb hp hcb, irreducible_iff_prime.mp hp⟩

theorem count_mul_of_coprime {a : Associates α} {b : Associates α} (hb : b ≠ 0) {p : Associates α} (hp : Irreducible p)
    (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) : count p a.factors = 0 ∨ count p a.factors = count p (a * b).factors := by
  by_cases' ha : a = 0
  · simp [← ha]
    
  cases' count_of_coprime ha hb hab hp with hz hb0
  · tauto
    
  apply Or.intro_rightₓ
  rw [count_mul ha hb hp, hb0, add_zeroₓ]

theorem count_mul_of_coprime' {a b : Associates α} {p : Associates α} (hp : Irreducible p)
    (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) :
    count p (a * b).factors = count p a.factors ∨ count p (a * b).factors = count p b.factors := by
  by_cases' ha : a = 0
  · simp [← ha]
    
  by_cases' hb : b = 0
  · simp [← hb]
    
  rw [count_mul ha hb hp]
  cases' count_of_coprime ha hb hab hp with ha0 hb0
  · apply Or.intro_rightₓ
    rw [ha0, zero_addₓ]
    
  · apply Or.intro_left
    rw [hb0, add_zeroₓ]
    

theorem dvd_count_of_dvd_count_mul {a b : Associates α} (hb : b ≠ 0) {p : Associates α} (hp : Irreducible p)
    (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {k : ℕ} (habk : k ∣ count p (a * b).factors) : k ∣ count p a.factors := by
  by_cases' ha : a = 0
  · simpa [*] using habk
    
  cases' count_of_coprime ha hb hab hp with hz h
  · rw [hz]
    exact dvd_zero k
    
  · rw [count_mul ha hb hp, h] at habk
    exact habk
    

omit dec_irr

@[simp]
theorem factors_one [Nontrivial α] : factors (1 : Associates α) = 0 := by
  apply eq_of_prod_eq_prod
  rw [Associates.factors_prod]
  exact Multiset.prod_zero

@[simp]
theorem pow_factors [Nontrivial α] {a : Associates α} {k : ℕ} : (a ^ k).factors = k • a.factors := by
  induction' k with n h
  · rw [zero_nsmul, pow_zeroₓ]
    exact factors_one
    
  · rw [pow_succₓ, succ_nsmul, factors_mul, h]
    

include dec_irr

theorem count_pow [Nontrivial α] {a : Associates α} (ha : a ≠ 0) {p : Associates α} (hp : Irreducible p) (k : ℕ) :
    count p (a ^ k).factors = k * count p a.factors := by
  induction' k with n h
  · rw [pow_zeroₓ, factors_one, zero_mul, count_zero hp]
    
  · rw [pow_succₓ, count_mul ha (pow_ne_zero _ ha) hp, h, Nat.succ_eq_add_one]
    ring
    

theorem dvd_count_pow [Nontrivial α] {a : Associates α} (ha : a ≠ 0) {p : Associates α} (hp : Irreducible p) (k : ℕ) :
    k ∣ count p (a ^ k).factors := by
  rw [count_pow ha hp]
  apply dvd_mul_right

theorem is_pow_of_dvd_count [Nontrivial α] {a : Associates α} (ha : a ≠ 0) {k : ℕ}
    (hk : ∀ (p : Associates α) (hp : Irreducible p), k ∣ count p a.factors) : ∃ b : Associates α, a = b ^ k := by
  obtain ⟨a0, hz, rfl⟩ := exists_non_zero_rep ha
  rw [factors_mk a0 hz] at hk
  have hk' : ∀ p, p ∈ factors' a0 → k ∣ (factors' a0).count p := by
    rintro p -
    have pp : p = ⟨p.val, p.2⟩ := by
      simp only [← Subtype.coe_eta, ← Subtype.val_eq_coe]
    rw [pp, ← count_some p.2]
    exact hk p.val p.2
  obtain ⟨u, hu⟩ := Multiset.exists_smul_of_dvd_count _ hk'
  use (u : factor_set α).Prod
  apply eq_of_factors_eq_factors
  rw [pow_factors, prod_factors, factors_mk a0 hz, ← WithTop.some_eq_coe, hu]
  exact WithBot.coe_nsmul u k

/-- The only divisors of prime powers are prime powers. See `eq_pow_find_of_dvd_irreducible_pow`
for an explicit expression as a p-power (without using `count`). -/
theorem eq_pow_count_factors_of_dvd_pow {p a : Associates α} (hp : Irreducible p) {n : ℕ} (h : a ∣ p ^ n) :
    a = p ^ p.count a.factors := by
  nontriviality α
  have hph := pow_ne_zero n hp.ne_zero
  have ha := ne_zero_of_dvd_ne_zero hph h
  apply eq_of_eq_counts ha (pow_ne_zero _ hp.ne_zero)
  have eq_zero_of_ne : ∀ q : Associates α, Irreducible q → q ≠ p → _ = 0 := fun q hq h' =>
    Nat.eq_zero_of_le_zeroₓ <| by
      convert count_le_count_of_le hph hq h
      symm
      rw [count_pow hp.ne_zero hq, count_eq_zero_of_ne hq hp h', mul_zero]
  intro q hq
  rw [count_pow hp.ne_zero hq]
  by_cases' h : q = p
  · rw [h, count_self hp, mul_oneₓ]
    
  · rw [count_eq_zero_of_ne hq hp h, mul_zero, eq_zero_of_ne q hq h]
    

theorem count_factors_eq_find_of_dvd_pow {a p : Associates α} (hp : Irreducible p) [∀ n : ℕ, Decidable (a ∣ p ^ n)]
    {n : ℕ} (h : a ∣ p ^ n) : Nat.findₓ ⟨n, h⟩ = p.count a.factors := by
  apply le_antisymmₓ
  · refine' Nat.find_le ⟨1, _⟩
    rw [mul_oneₓ]
    symm
    exact eq_pow_count_factors_of_dvd_pow hp h
    
  · have hph := pow_ne_zero (Nat.findₓ ⟨n, h⟩) hp.ne_zero
    cases' subsingleton_or_nontrivial α with hα hα
    · simpa using hph
      
    convert count_le_count_of_le hph hp (Nat.find_specₓ ⟨n, h⟩)
    rw [count_pow hp.ne_zero hp, count_self hp, mul_oneₓ]
    

omit dec

omit dec_irr

omit dec'

theorem eq_pow_of_mul_eq_pow [Nontrivial α] {a b c : Associates α} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) {k : ℕ} (h : a * b = c ^ k) : ∃ d : Associates α, a = d ^ k := by
  classical
  by_cases' hk0 : k = 0
  · use 1
    rw [hk0, pow_zeroₓ] at h⊢
    apply (mul_eq_one_iff.1 h).1
    
  · refine' is_pow_of_dvd_count ha _
    intro p hp
    apply dvd_count_of_dvd_count_mul hb hp hab
    rw [h]
    apply dvd_count_pow _ hp
    rintro rfl
    rw [zero_pow' _ hk0] at h
    cases mul_eq_zero.mp h <;> contradiction
    

/-- The only divisors of prime powers are prime powers. -/
theorem eq_pow_find_of_dvd_irreducible_pow {a p : Associates α} (hp : Irreducible p) [∀ n : ℕ, Decidable (a ∣ p ^ n)]
    {n : ℕ} (h : a ∣ p ^ n) : a = p ^ Nat.findₓ ⟨n, h⟩ := by
  classical
  rw [count_factors_eq_find_of_dvd_pow hp, ← eq_pow_count_factors_of_dvd_pow hp h]

end Associates

section

open Associates UniqueFactorizationMonoid

theorem Associates.quot_out {α : Type _} [CommMonoidₓ α] (a : Associates α) : Associates.mk (Quot.out a) = a := by
  rw [← quot_mk_eq_mk, Quot.out_eq]

/-- `to_gcd_monoid` constructs a GCD monoid out of a unique factorization domain. -/
noncomputable def UniqueFactorizationMonoid.toGcdMonoid (α : Type _) [CancelCommMonoidWithZero α]
    [UniqueFactorizationMonoid α] [DecidableEq (Associates α)] [DecidableEq α] : GcdMonoid α where
  gcd := fun a b => Quot.out (Associates.mk a⊓Associates.mk b : Associates α)
  lcm := fun a b => Quot.out (Associates.mk a⊔Associates.mk b : Associates α)
  gcd_dvd_left := fun a b => by
    rw [← mk_dvd_mk, (Associates.mk a⊓Associates.mk b).quot_out, dvd_eq_le]
    exact inf_le_left
  gcd_dvd_right := fun a b => by
    rw [← mk_dvd_mk, (Associates.mk a⊓Associates.mk b).quot_out, dvd_eq_le]
    exact inf_le_right
  dvd_gcd := fun a b c hac hab => by
    rw [← mk_dvd_mk, (Associates.mk c⊓Associates.mk b).quot_out, dvd_eq_le, le_inf_iff, mk_le_mk_iff_dvd_iff,
      mk_le_mk_iff_dvd_iff]
    exact ⟨hac, hab⟩
  lcm_zero_left := fun a => by
    have : Associates.mk (0 : α) = ⊤ := rfl
    rw [this, top_sup_eq, ← this, ← associated_zero_iff_eq_zero, ← mk_eq_mk_iff_associated, ← associated_iff_eq,
      Associates.quot_out]
  lcm_zero_right := fun a => by
    have : Associates.mk (0 : α) = ⊤ := rfl
    rw [this, sup_top_eq, ← this, ← associated_zero_iff_eq_zero, ← mk_eq_mk_iff_associated, ← associated_iff_eq,
      Associates.quot_out]
  gcd_mul_lcm := fun a b => by
    rw [← mk_eq_mk_iff_associated, ← Associates.mk_mul_mk, ← associated_iff_eq, Associates.quot_out,
      Associates.quot_out, mul_comm, sup_mul_inf, Associates.mk_mul_mk]

/-- `to_normalized_gcd_monoid` constructs a GCD monoid out of a normalization on a
  unique factorization domain. -/
noncomputable def UniqueFactorizationMonoid.toNormalizedGcdMonoid (α : Type _) [CancelCommMonoidWithZero α]
    [UniqueFactorizationMonoid α] [NormalizationMonoid α] [DecidableEq (Associates α)] [DecidableEq α] :
    NormalizedGcdMonoid α :=
  { ‹NormalizationMonoid α› with gcd := fun a b => (Associates.mk a⊓Associates.mk b).out,
    lcm := fun a b => (Associates.mk a⊔Associates.mk b).out,
    gcd_dvd_left := fun a b => (out_dvd_iff a (Associates.mk a⊓Associates.mk b)).2 <| inf_le_left,
    gcd_dvd_right := fun a b => (out_dvd_iff b (Associates.mk a⊓Associates.mk b)).2 <| inf_le_right,
    dvd_gcd := fun a b c hac hab =>
      show a ∣ (Associates.mk c⊓Associates.mk b).out by
        rw [dvd_out_iff, le_inf_iff, mk_le_mk_iff_dvd_iff, mk_le_mk_iff_dvd_iff] <;> exact ⟨hac, hab⟩,
    lcm_zero_left := fun a =>
      show (⊤⊔Associates.mk a).out = 0 by
        simp ,
    lcm_zero_right := fun a =>
      show (Associates.mk a⊔⊤).out = 0 by
        simp ,
    gcd_mul_lcm := fun a b => by
      rw [← out_mul, mul_comm, sup_mul_inf, mk_mul_mk, out_mk]
      exact normalize_associated (a * b),
    normalize_gcd := fun a b => by
      convert normalize_out _,
    normalize_lcm := fun a b => by
      convert normalize_out _ }

end

namespace UniqueFactorizationMonoid

/-- If `y` is a nonzero element of a unique factorization monoid with finitely
many units (e.g. `ℤ`, `ideal (ring_of_integers K)`), it has finitely many divisors. -/
noncomputable def fintypeSubtypeDvd {M : Type _} [CancelCommMonoidWithZero M] [UniqueFactorizationMonoid M] [Fintype Mˣ]
    (y : M) (hy : y ≠ 0) : Fintype { x // x ∣ y } := by
  have : Nontrivial M := ⟨⟨y, 0, hy⟩⟩
  have : NormalizationMonoid M := UniqueFactorizationMonoid.normalizationMonoid
  have := Classical.decEq M
  have := Classical.decEq (Associates M)
  -- We'll show `λ (u : Mˣ) (f ⊆ factors y) → u * Π f` is injective
  -- and has image exactly the divisors of `y`.
  refine'
    Fintype.ofFinset
      (((normalized_factors y).Powerset.toFinset.product (Finset.univ : Finset Mˣ)).Image fun s =>
        (s.snd : M) * s.fst.prod)
      fun x => _
  simp only [← exists_prop, ← Finset.mem_image, ← Finset.mem_product, ← Finset.mem_univ, ← and_trueₓ, ←
    Multiset.mem_to_finset, ← Multiset.mem_powerset, ← exists_eq_right, ← Multiset.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have prod_s_ne : s.fst.prod ≠ 0 := by
      intro hz
      apply hy (eq_zero_of_zero_dvd _)
      have hz := (@Multiset.prod_eq_zero_iff M _ _ _ s.fst).mp hz
      rw [← (normalized_factors_prod hy).dvd_iff_dvd_right]
      exact Multiset.dvd_prod (Multiset.mem_of_le hs hz)
    show (s.snd : M) * s.fst.prod ∣ y
    rw [(unit_associated_one.mul_right s.fst.prod).dvd_iff_dvd_left, one_mulₓ, ←
      (normalized_factors_prod hy).dvd_iff_dvd_right]
    exact Multiset.prod_dvd_prod_of_le hs
    
  · rintro (h : x ∣ y)
    have hx : x ≠ 0 := by
      refine' mt (fun hx => _) hy
      rwa [hx, zero_dvd_iff] at h
    obtain ⟨u, hu⟩ := normalized_factors_prod hx
    refine' ⟨⟨normalized_factors x, u⟩, _, (mul_comm _ _).trans hu⟩
    exact (dvd_iff_normalized_factors_le_normalized_factors hx hy).mp h
    

end UniqueFactorizationMonoid

section Finsupp

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]

variable [NormalizationMonoid α] [DecidableEq α]

open UniqueFactorizationMonoid

/-- This returns the multiset of irreducible factors as a `finsupp` -/
noncomputable def factorization (n : α) : α →₀ ℕ :=
  (normalizedFactors n).toFinsupp

theorem factorization_eq_count {n p : α} : factorization n p = Multiset.count p (normalizedFactors n) := by
  simp [← factorization]

@[simp]
theorem factorization_zero : factorization (0 : α) = 0 := by
  simp [← factorization]

@[simp]
theorem factorization_one : factorization (1 : α) = 0 := by
  simp [← factorization]

/-- The support of `factorization n` is exactly the finset of normalized factors -/
@[simp]
theorem support_factorization {n : α} : (factorization n).Support = (normalizedFactors n).toFinset := by
  simp [← factorization, ← Multiset.to_finsupp_support]

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp]
theorem factorization_mul {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
    factorization (a * b) = factorization a + factorization b := by
  simp [← factorization, ← normalized_factors_mul ha hb]

/-- For any `p`, the power of `p` in `x^n` is `n` times the power in `x` -/
theorem factorization_pow {x : α} {n : ℕ} : factorization (x ^ n) = n • factorization x := by
  ext
  simp [← factorization]

theorem associated_of_factorization_eq (a b : α) (ha : a ≠ 0) (hb : b ≠ 0) (h : factorization a = factorization b) :
    Associated a b := by
  simp only [← factorization, ← AddEquiv.apply_eq_iff_eq] at h
  have ha' := normalized_factors_prod ha
  rw [h] at ha'
  exact Associated.trans ha'.symm (normalized_factors_prod hb)

end Finsupp


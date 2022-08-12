/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.RingTheory.AdjoinRoot

/-!
# Splitting fields

This file introduces the notion of a splitting field of a polynomial and provides an embedding from
a splitting field to any field that splits the polynomial. A polynomial `f : polynomial K` splits
over a field extension `L` of `K` if it is zero or all of its irreducible factors over `L` have
degree `1`. A field extension of `K` of a polynomial `f : polynomial K` is called a splitting field
if it is the smallest field extension of `K` such that `f` splits.

## Main definitions

* `polynomial.splits i f`: A predicate on a field homomorphism `i : K → L` and a polynomial `f`
  saying that `f` is zero or all of its irreducible factors over `L` have degree `1`.
* `polynomial.splitting_field f`: A fixed splitting field of the polynomial `f`.
* `polynomial.is_splitting_field`: A predicate on a field to be a splitting field of a polynomial
  `f`.

## Main statements

* `polynomial.C_leading_coeff_mul_prod_multiset_X_sub_C`: If a polynomial has as many roots as its
  degree, it can be written as the product of its leading coefficient with `∏ (X - a)` where `a`
  ranges through its roots.
* `lift_of_splits`: If `K` and `L` are field extensions of a field `F` and for some finite subset
  `S` of `K`, the minimal polynomial of every `x ∈ K` splits as a polynomial with coefficients in
  `L`, then `algebra.adjoin F S` embeds into `L`.
* `polynomial.is_splitting_field.lift`: An embedding of a splitting field of the polynomial `f` into
  another field such that `f` splits.
* `polynomial.is_splitting_field.alg_equiv`: Every splitting field of a polynomial `f` is isomorphic
  to `splitting_field f` and thus, being a splitting field is unique up to isomorphism.

-/


noncomputable section

open Classical BigOperators Polynomial

universe u v w

variable {F : Type u} {K : Type v} {L : Type w}

namespace Polynomial

variable [Field K] [Field L] [Field F]

open Polynomial

section Splits

variable (i : K →+* L)

/-- A polynomial `splits` iff it is zero or all of its irreducible factors have `degree` 1. -/
def Splits (f : K[X]) : Prop :=
  f = 0 ∨ ∀ {g : L[X]}, Irreducible g → g ∣ f.map i → degree g = 1

@[simp]
theorem splits_zero : Splits i (0 : K[X]) :=
  Or.inl rfl

@[simp]
theorem splits_C (a : K) : Splits i (c a) :=
  if ha : a = 0 then ha.symm ▸ (@C_0 K _).symm ▸ splits_zero i
  else
    have hia : i a ≠ 0 := mt ((injective_iff_map_eq_zero i).1 i.Injective _) ha
    Or.inr fun g hg ⟨p, hp⟩ =>
      absurd hg.1
        (not_not.2
          (is_unit_iff_degree_eq_zero.2 <| by
            have := congr_arg degree hp <;>
              simp [← degree_C hia, ← @eq_comm (WithBot ℕ) 0, ← Nat.WithBot.add_eq_zero_iff] at this <;>
                clear _fun_match <;> tauto))

theorem splits_of_degree_eq_one {f : K[X]} (hf : degree f = 1) : Splits i f :=
  Or.inr fun g hg ⟨p, hp⟩ => by
    have := congr_arg degree hp <;>
      simp [← Nat.WithBot.add_eq_one_iff, ← hf, ← @eq_comm (WithBot ℕ) 1, ← mt is_unit_iff_degree_eq_zero.2 hg.1] at
          this <;>
        clear _fun_match <;> tauto

theorem splits_of_degree_le_one {f : K[X]} (hf : degree f ≤ 1) : Splits i f := by
  cases' h : degree f with n
  · rw [degree_eq_bot.1 h] <;> exact splits_zero i
    
  · cases' n with n
    · rw [eq_C_of_degree_le_zero (trans_rel_right (· ≤ ·) h le_rfl)] <;> exact splits_C _ _
      
    · have hn : n = 0 := by
        rw [h] at hf
        cases n
        · rfl
          
        · exact
            absurd hf
              (by
                decide)
          
      exact
        splits_of_degree_eq_one _
          (by
            rw [h, hn] <;> rfl)
      
    

theorem splits_of_nat_degree_le_one {f : K[X]} (hf : natDegree f ≤ 1) : Splits i f :=
  splits_of_degree_le_one i (degree_le_of_nat_degree_le hf)

theorem splits_of_nat_degree_eq_one {f : K[X]} (hf : natDegree f = 1) : Splits i f :=
  splits_of_nat_degree_le_one i (le_of_eqₓ hf)

theorem splits_mul {f g : K[X]} (hf : Splits i f) (hg : Splits i g) : Splits i (f * g) :=
  if h : f * g = 0 then by
    simp [← h]
  else
    Or.inr fun p hp hpf =>
      ((PrincipalIdealRing.irreducible_iff_prime.1 hp).2.2 _ _
            (show p ∣ map i f * map i g by
              convert hpf <;> rw [Polynomial.map_mul])).elim
        (hf.resolve_left
          (fun hf => by
            simpa [← hf] using h)
          hp)
        (hg.resolve_left
          (fun hg => by
            simpa [← hg] using h)
          hp)

theorem splits_of_splits_mul {f g : K[X]} (hfg : f * g ≠ 0) (h : Splits i (f * g)) : Splits i f ∧ Splits i g :=
  ⟨Or.inr fun g hgi hg =>
      Or.resolve_left h hfg hgi
        (by
          rw [Polynomial.map_mul] <;> exact hg.trans (dvd_mul_right _ _)),
    Or.inr fun g hgi hg =>
      Or.resolve_left h hfg hgi
        (by
          rw [Polynomial.map_mul] <;> exact hg.trans (dvd_mul_left _ _))⟩

theorem splits_of_splits_of_dvd {f g : K[X]} (hf0 : f ≠ 0) (hf : Splits i f) (hgf : g ∣ f) : Splits i g := by
  obtain ⟨f, rfl⟩ := hgf
  exact (splits_of_splits_mul i hf0 hf).1

theorem splits_of_splits_gcd_left {f g : K[X]} (hf0 : f ≠ 0) (hf : Splits i f) : Splits i (EuclideanDomain.gcd f g) :=
  Polynomial.splits_of_splits_of_dvd i hf0 hf (EuclideanDomain.gcd_dvd_left f g)

theorem splits_of_splits_gcd_right {f g : K[X]} (hg0 : g ≠ 0) (hg : Splits i g) : Splits i (EuclideanDomain.gcd f g) :=
  Polynomial.splits_of_splits_of_dvd i hg0 hg (EuclideanDomain.gcd_dvd_right f g)

theorem splits_map_iff (j : L →+* F) {f : K[X]} : Splits j (f.map i) ↔ Splits (j.comp i) f := by
  simp [← splits, ← Polynomial.map_map]

theorem splits_one : Splits i 1 :=
  splits_C i 1

theorem splits_of_is_unit {u : K[X]} (hu : IsUnit u) : u.Splits i :=
  splits_of_splits_of_dvd i one_ne_zero (splits_one _) <| is_unit_iff_dvd_one.1 hu

theorem splits_X_sub_C {x : K} : (X - c x).Splits i :=
  splits_of_degree_eq_one _ <| degree_X_sub_C x

theorem splits_X : x.Splits i :=
  splits_of_degree_eq_one _ <| degree_X

theorem splits_id_iff_splits {f : K[X]} : (f.map i).Splits (RingHom.id L) ↔ f.Splits i := by
  rw [splits_map_iff, RingHom.id_comp]

theorem splits_mul_iff {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) : (f * g).Splits i ↔ f.Splits i ∧ g.Splits i :=
  ⟨splits_of_splits_mul i (mul_ne_zero hf hg), fun ⟨hfs, hgs⟩ => splits_mul i hfs hgs⟩

theorem splits_prod {ι : Type u} {s : ι → K[X]} {t : Finset ι} :
    (∀, ∀ j ∈ t, ∀, (s j).Splits i) → (∏ x in t, s x).Splits i := by
  refine' Finset.induction_on t (fun _ => splits_one i) fun a t hat ih ht => _
  rw [Finset.forall_mem_insert] at ht
  rw [Finset.prod_insert hat]
  exact splits_mul i ht.1 (ih ht.2)

theorem splits_pow {f : K[X]} (hf : f.Splits i) (n : ℕ) : (f ^ n).Splits i := by
  rw [← Finset.card_range n, ← Finset.prod_const]
  exact splits_prod i fun j hj => hf

theorem splits_X_pow (n : ℕ) : (X ^ n).Splits i :=
  splits_pow i (splits_X i) n

theorem splits_prod_iff {ι : Type u} {s : ι → K[X]} {t : Finset ι} :
    (∀, ∀ j ∈ t, ∀, s j ≠ 0) → ((∏ x in t, s x).Splits i ↔ ∀, ∀ j ∈ t, ∀, (s j).Splits i) := by
  refine' Finset.induction_on t (fun _ => ⟨fun _ _ h => h.elim, fun _ => splits_one i⟩) fun a t hat ih ht => _
  rw [Finset.forall_mem_insert] at ht⊢
  rw [Finset.prod_insert hat, splits_mul_iff i ht.1 (Finset.prod_ne_zero_iff.2 ht.2), ih ht.2]

theorem degree_eq_one_of_irreducible_of_splits {p : L[X]} (hp : Irreducible p) (hp_splits : Splits (RingHom.id L) p) :
    p.degree = 1 := by
  by_cases' h_nz : p = 0
  · exfalso
    simp_all
    
  rcases hp_splits with ⟨⟩
  · contradiction
    
  · apply hp_splits hp
    simp
    

theorem exists_root_of_splits {f : K[X]} (hs : Splits i f) (hf0 : degree f ≠ 0) : ∃ x, eval₂ i x f = 0 :=
  if hf0 : f = 0 then by
    simp [← hf0]
  else
    let ⟨g, hg⟩ :=
      WfDvdMonoid.exists_irreducible_factor
        (show ¬IsUnit (f.map i) from
          mt is_unit_iff_degree_eq_zero.1
            (by
              rwa [degree_map]))
        (map_ne_zero hf0)
    let ⟨x, hx⟩ := exists_root_of_degree_eq_one (hs.resolve_left hf0 hg.1 hg.2)
    let ⟨i, hi⟩ := hg.2
    ⟨x, by
      rw [← eval_map, hi, eval_mul, show _ = _ from hx, zero_mul]⟩

theorem roots_ne_zero_of_splits {f : K[X]} (hs : Splits i f) (hf0 : natDegree f ≠ 0) : (f.map i).roots ≠ 0 :=
  let ⟨x, hx⟩ := exists_root_of_splits i hs fun h => hf0 <| nat_degree_eq_of_degree_eq_some h
  fun h => by
  rw [← eval_map] at hx
  cases h.subst ((mem_roots _).2 hx)
  exact map_ne_zero fun h => (h.subst hf0) rfl

/-- Pick a root of a polynomial that splits. -/
def rootOfSplits {f : K[X]} (hf : f.Splits i) (hfd : f.degree ≠ 0) : L :=
  Classical.some <| exists_root_of_splits i hf hfd

theorem map_root_of_splits {f : K[X]} (hf : f.Splits i) (hfd) : f.eval₂ i (rootOfSplits i hf hfd) = 0 :=
  Classical.some_spec <| exists_root_of_splits i hf hfd

theorem nat_degree_eq_card_roots {p : K[X]} {i : K →+* L} (hsplit : Splits i p) : p.natDegree = (p.map i).roots.card :=
  by
  by_cases' hp : p = 0
  · rw [hp, nat_degree_zero, Polynomial.map_zero, roots_zero, Multiset.card_zero]
    
  obtain ⟨q, he, hd, hr⟩ := exists_prod_multiset_X_sub_C_mul (p.map i)
  rw [← splits_id_iff_splits, ← he] at hsplit
  have hpm : p.map i ≠ 0 := map_ne_zero hp
  rw [← he] at hpm
  have hq : q ≠ 0 := fun h =>
    hpm
      (by
        rw [h, mul_zero])
  rw [← nat_degree_map i, ← hd, add_right_eq_selfₓ]
  by_contra
  have := roots_ne_zero_of_splits (RingHom.id L) (splits_of_splits_mul _ _ hsplit).2 h
  · rw [map_id] at this
    exact this hr
    
  · exact mul_ne_zero monic_prod_multiset_X_sub_C.ne_zero hq
    

theorem degree_eq_card_roots {p : K[X]} {i : K →+* L} (p_ne_zero : p ≠ 0) (hsplit : Splits i p) :
    p.degree = (p.map i).roots.card := by
  rw [degree_eq_nat_degree p_ne_zero, nat_degree_eq_card_roots hsplit]

theorem roots_map {f : K[X]} (hf : f.Splits <| RingHom.id K) : (f.map i).roots = f.roots.map i :=
  (roots_map_of_injective_card_eq_total_degree i.Injective <| by
      convert (nat_degree_eq_card_roots hf).symm
      rw [map_id]).symm

theorem eq_prod_roots_of_splits {p : K[X]} {i : K →+* L} (hsplit : Splits i p) :
    p.map i = c (i p.leadingCoeff) * ((p.map i).roots.map fun a => X - c a).Prod := by
  rw [← leading_coeff_map]
  symm
  apply C_leading_coeff_mul_prod_multiset_X_sub_C
  rw [nat_degree_map]
  exact (nat_degree_eq_card_roots hsplit).symm

theorem eq_prod_roots_of_splits_id {p : K[X]} (hsplit : Splits (RingHom.id K) p) :
    p = c p.leadingCoeff * (p.roots.map fun a => X - c a).Prod := by
  simpa using eq_prod_roots_of_splits hsplit

theorem eq_prod_roots_of_monic_of_splits_id {p : K[X]} (m : Monic p) (hsplit : Splits (RingHom.id K) p) :
    p = (p.roots.map fun a => X - c a).Prod := by
  convert eq_prod_roots_of_splits_id hsplit
  simp [← m]

theorem eq_X_sub_C_of_splits_of_single_root {x : K} {h : K[X]} (h_splits : Splits i h)
    (h_roots : (h.map i).roots = {i x}) : h = c h.leadingCoeff * (X - c x) := by
  apply Polynomial.map_injective _ i.injective
  rw [eq_prod_roots_of_splits h_splits, h_roots]
  simp

section UFD

attribute [local instance] PrincipalIdealRing.to_unique_factorization_monoid

-- mathport name: «expr ~ᵤ »
local infixl:50 " ~ᵤ " => Associated

open UniqueFactorizationMonoid Associates

theorem splits_of_exists_multiset {f : K[X]} {s : Multiset L}
    (hs : f.map i = c (i f.leadingCoeff) * (s.map fun a : L => X - c a).Prod) : Splits i f :=
  if hf0 : f = 0 then Or.inl hf0
  else
    Or.inr fun p hp hdp => by
      rw [irreducible_iff_prime] at hp
      rw [hs, ← Multiset.prod_to_list] at hdp
      obtain hd | hd := hp.2.2 _ _ hdp
      · refine' (hp.2.1 <| is_unit_of_dvd_unit hd _).elim
        exact is_unit_C.2 ((leading_coeff_ne_zero.2 hf0).IsUnit.map i)
        
      · obtain ⟨q, hq, hd⟩ := hp.dvd_prod_iff.1 hd
        obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 ((Multiset.mem_to_list _ _).1 hq)
        rw [degree_eq_degree_of_associated ((hp.dvd_prime_iff_associated <| prime_X_sub_C a).1 hd)]
        exact degree_X_sub_C a
        

theorem splits_of_splits_id {f : K[X]} : Splits (RingHom.id _) f → Splits i f :=
  UniqueFactorizationMonoid.induction_on_prime f (fun _ => splits_zero _)
    (fun _ hu _ =>
      splits_of_degree_le_one _
        ((is_unit_iff_degree_eq_zero.1 hu).symm ▸ by
          decide))
    fun a p ha0 hp ih hfi =>
    splits_mul _
      (splits_of_degree_eq_one _
        ((splits_of_splits_mul _ (mul_ne_zero hp.1 ha0) hfi).1.resolve_left hp.1 hp.Irreducible
          (by
            rw [map_id])))
      (ih (splits_of_splits_mul _ (mul_ne_zero hp.1 ha0) hfi).2)

end UFD

theorem splits_iff_exists_multiset {f : K[X]} :
    Splits i f ↔ ∃ s : Multiset L, f.map i = c (i f.leadingCoeff) * (s.map fun a : L => X - c a).Prod :=
  ⟨fun hf => ⟨(f.map i).roots, eq_prod_roots_of_splits hf⟩, fun ⟨s, hs⟩ => splits_of_exists_multiset i hs⟩

theorem splits_comp_of_splits (j : L →+* F) {f : K[X]} (h : Splits i f) : Splits (j.comp i) f := by
  change i with (RingHom.id _).comp i at h
  rw [← splits_map_iff]
  rw [← splits_map_iff i] at h
  exact splits_of_splits_id _ h

/-- A polynomial splits if and only if it has as many roots as its degree. -/
theorem splits_iff_card_roots {p : K[X]} : Splits (RingHom.id K) p ↔ p.roots.card = p.natDegree := by
  constructor
  · intro H
    rw [nat_degree_eq_card_roots H, map_id]
    
  · intro hroots
    rw [splits_iff_exists_multiset (RingHom.id K)]
    use p.roots
    simp only [← RingHom.id_apply, ← map_id]
    exact (C_leading_coeff_mul_prod_multiset_X_sub_C hroots).symm
    

theorem aeval_root_derivative_of_splits [Algebra K L] {P : K[X]} (hmo : P.Monic) (hP : P.Splits (algebraMap K L))
    {r : L} (hr : r ∈ (P.map (algebraMap K L)).roots) :
    aeval r P.derivative = (((P.map <| algebraMap K L).roots.erase r).map fun a => r - a).Prod := by
  replace hmo := hmo.map (algebraMap K L)
  replace hP := (splits_id_iff_splits (algebraMap K L)).2 hP
  rw [aeval_def, ← eval_map, ← derivative_map]
  nth_rw 0[eq_prod_roots_of_monic_of_splits_id hmo hP]
  rw [eval_multiset_prod_X_sub_C_derivative hr]

/-- If `P` is a monic polynomial that splits, then `coeff P 0` equals the product of the roots. -/
theorem prod_roots_eq_coeff_zero_of_monic_of_split {P : K[X]} (hmo : P.Monic) (hP : P.Splits (RingHom.id K)) :
    coeff P 0 = -1 ^ P.natDegree * P.roots.Prod := by
  nth_rw 0[eq_prod_roots_of_monic_of_splits_id hmo hP]
  rw [coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map]
  simp_rw [Function.comp_app, eval_sub, eval_X, zero_sub, eval_C]
  conv_lhs => congr congr ext rw [neg_eq_neg_one_mul]
  rw [Multiset.prod_map_mul, Multiset.map_const, Multiset.prod_repeat, Multiset.map_id', splits_iff_card_roots.1 hP]

/-- If `P` is a monic polynomial that splits, then `P.next_coeff` equals the sum of the roots. -/
theorem sum_roots_eq_next_coeff_of_monic_of_split {P : K[X]} (hmo : P.Monic) (hP : P.Splits (RingHom.id K)) :
    P.nextCoeff = -P.roots.Sum := by
  nth_rw 0[eq_prod_roots_of_monic_of_splits_id hmo hP]
  rw [monic.next_coeff_multiset_prod _ _ fun a ha => _]
  · simp_rw [next_coeff_X_sub_C, Multiset.sum_map_neg']
    
  · exact monic_X_sub_C a
    

end Splits

end Polynomial

section Embeddings

variable (F) [Field F]

/-- If `p` is the minimal polynomial of `a` over `F` then `F[a] ≃ₐ[F] F[x]/(p)` -/
def AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly {R : Type _} [CommRingₓ R] [Algebra F R] (x : R) :
    Algebra.adjoin F ({x} : Set R) ≃ₐ[F] AdjoinRoot (minpoly F x) :=
  AlgEquiv.symm <|
    AlgEquiv.ofBijective
      (AlgHom.codRestrict (AdjoinRoot.liftHom _ x <| minpoly.aeval F x) _ fun p =>
        (AdjoinRoot.induction_on _ p) fun p =>
          (Algebra.adjoin_singleton_eq_range_aeval F x).symm ▸ (Polynomial.aeval _).mem_range.mpr ⟨p, rfl⟩)
      ⟨(AlgHom.injective_cod_restrict _ _ _).2 <|
          (injective_iff_map_eq_zero _).2 fun p =>
            (AdjoinRoot.induction_on _ p) fun p hp =>
              Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.mem_span_singleton.2 <| minpoly.dvd F x hp,
        fun y =>
        let ⟨p, hp⟩ := (SetLike.ext_iff.1 (Algebra.adjoin_singleton_eq_range_aeval F x) (y : R)).1 y.2
        ⟨AdjoinRoot.mk _ p, Subtype.eq hp⟩⟩

open Finset

/-- If a `subalgebra` is finite_dimensional as a submodule then it is `finite_dimensional`. -/
theorem FiniteDimensional.of_subalgebra_to_submodule {K V : Type _} [Field K] [Ringₓ V] [Algebra K V]
    {s : Subalgebra K V} (h : FiniteDimensional K s.toSubmodule) : FiniteDimensional K s :=
  h

/-- If `K` and `L` are field extensions of `F` and we have `s : finset K` such that
the minimal polynomial of each `x ∈ s` splits in `L` then `algebra.adjoin F s` embeds in `L`. -/
theorem lift_of_splits {F K L : Type _} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] (s : Finset K) :
    (∀, ∀ x ∈ s, ∀, IsIntegral F x ∧ Polynomial.Splits (algebraMap F L) (minpoly F x)) →
      Nonempty (Algebra.adjoin F (↑s : Set K) →ₐ[F] L) :=
  by
  refine' Finset.induction_on s (fun H => _) fun a s has ih H => _
  · rw [coe_empty, Algebra.adjoin_empty]
    exact ⟨(Algebra.ofId F L).comp (Algebra.botEquiv F K)⟩
    
  rw [forall_mem_insert] at H
  rcases H with ⟨⟨H1, H2⟩, H3⟩
  cases' ih H3 with f
  choose H3 H4 using H3
  rw [coe_insert, Set.insert_eq, Set.union_comm, Algebra.adjoin_union_eq_adjoin_adjoin]
  let this := (f : Algebra.adjoin F (↑s : Set K) →+* L).toAlgebra
  have : FiniteDimensional F (Algebra.adjoin F (↑s : Set K)) :=
    ((Submodule.fg_iff_finite_dimensional _).1 (fg_adjoin_of_finite s.finite_to_set H3)).of_subalgebra_to_submodule
  let this := fieldOfFiniteDimensional F (Algebra.adjoin F (↑s : Set K))
  have H5 : IsIntegral (Algebra.adjoin F (↑s : Set K)) a := is_integral_of_is_scalar_tower a H1
  have H6 : (minpoly (Algebra.adjoin F (↑s : Set K)) a).Splits (algebraMap (Algebra.adjoin F (↑s : Set K)) L) := by
    refine'
      Polynomial.splits_of_splits_of_dvd _
        (Polynomial.map_ne_zero <| minpoly.ne_zero H1 : Polynomial.map (algebraMap _ _) _ ≠ 0)
        ((Polynomial.splits_map_iff _ _).2 _) (minpoly.dvd _ _ _)
    · rw [← IsScalarTower.algebra_map_eq]
      exact H2
      
    · rw [← IsScalarTower.aeval_apply, minpoly.aeval]
      
  obtain ⟨y, hy⟩ := Polynomial.exists_root_of_splits _ H6 (ne_of_ltₓ (minpoly.degree_pos H5)).symm
  refine' ⟨Subalgebra.ofRestrictScalars _ _ _⟩
  refine' (AdjoinRoot.liftHom (minpoly (Algebra.adjoin F (↑s : Set K)) a) y hy).comp _
  exact AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly (Algebra.adjoin F (↑s : Set K)) a

end Embeddings

namespace Polynomial

variable [Field K] [Field L] [Field F]

open Polynomial

section SplittingField

/-- Non-computably choose an irreducible factor from a polynomial. -/
def factor (f : K[X]) : K[X] :=
  if H : ∃ g, Irreducible g ∧ g ∣ f then Classical.some H else x

theorem irreducible_factor (f : K[X]) : Irreducible (factor f) := by
  rw [factor]
  split_ifs with H
  · exact (Classical.some_spec H).1
    
  · exact irreducible_X
    

/-- See note [fact non-instances]. -/
theorem fact_irreducible_factor (f : K[X]) : Fact (Irreducible (factor f)) :=
  ⟨irreducible_factor f⟩

attribute [local instance] fact_irreducible_factor

theorem factor_dvd_of_not_is_unit {f : K[X]} (hf1 : ¬IsUnit f) : factor f ∣ f := by
  by_cases' hf2 : f = 0
  · rw [hf2]
    exact dvd_zero _
    
  rw [factor, dif_pos (WfDvdMonoid.exists_irreducible_factor hf1 hf2)]
  exact (Classical.some_spec <| WfDvdMonoid.exists_irreducible_factor hf1 hf2).2

theorem factor_dvd_of_degree_ne_zero {f : K[X]} (hf : f.degree ≠ 0) : factor f ∣ f :=
  factor_dvd_of_not_is_unit (mt degree_eq_zero_of_is_unit hf)

theorem factor_dvd_of_nat_degree_ne_zero {f : K[X]} (hf : f.natDegree ≠ 0) : factor f ∣ f :=
  factor_dvd_of_degree_ne_zero (mt nat_degree_eq_of_degree_eq_some hf)

/-- Divide a polynomial f by X - C r where r is a root of f in a bigger field extension. -/
def removeFactor (f : K[X]) : Polynomial (AdjoinRoot <| factor f) :=
  map (AdjoinRoot.of f.factor) f /ₘ (X - c (AdjoinRoot.root f.factor))

theorem X_sub_C_mul_remove_factor (f : K[X]) (hf : f.natDegree ≠ 0) :
    (X - c (AdjoinRoot.root f.factor)) * f.removeFactor = map (AdjoinRoot.of f.factor) f :=
  let ⟨g, hg⟩ := factor_dvd_of_nat_degree_ne_zero hf
  mul_div_by_monic_eq_iff_is_root.2 <| by
    rw [is_root.def, eval_map, hg, eval₂_mul, ← hg, AdjoinRoot.eval₂_root, zero_mul]

theorem nat_degree_remove_factor (f : K[X]) : f.removeFactor.natDegree = f.natDegree - 1 := by
  rw [remove_factor, nat_degree_div_by_monic _ (monic_X_sub_C _), nat_degree_map, nat_degree_X_sub_C]

theorem nat_degree_remove_factor' {f : K[X]} {n : ℕ} (hfn : f.natDegree = n + 1) : f.removeFactor.natDegree = n := by
  rw [nat_degree_remove_factor, hfn, n.add_sub_cancel]

/-- Auxiliary construction to a splitting field of a polynomial. Uses induction on the degree. -/
def SplittingFieldAux (n : ℕ) : ∀ {K : Type u} [Field K], ∀ f : K[X], f.natDegree = n → Type u :=
  (Nat.recOn n fun K _ _ _ => K) fun n ih K _ f hf => ih f.remove_factor (nat_degree_remove_factor' hf)

namespace SplittingFieldAux

theorem succ (n : ℕ) (f : K[X]) (hfn : f.natDegree = n + 1) :
    SplittingFieldAux (n + 1) f hfn = SplittingFieldAux n f.removeFactor (nat_degree_remove_factor' hfn) :=
  rfl

instance field (n : ℕ) :
    ∀ {K : Type u} [Field K], ∀ {f : K[X]} (hfn : f.natDegree = n), Field (splitting_field_aux n f hfn) :=
  (Nat.recOn n fun K _ _ _ => ‹Field K›) fun n ih K _ f hf => ih _

instance inhabited {n : ℕ} {f : K[X]} (hfn : f.natDegree = n) : Inhabited (SplittingFieldAux n f hfn) :=
  ⟨37⟩

/-
Note that the recursive nature of this definition and `splitting_field_aux.field` creates
non-definitionally-equal diamonds in the `ℕ`- and `ℤ`- actions.
```lean
example (n : ℕ) {K : Type u} [field K] {f : K[X]} (hfn : f.nat_degree = n) :
    (add_comm_monoid.nat_module : module ℕ (splitting_field_aux n f hfn)) =
  @algebra.to_module _ _ _ _ (splitting_field_aux.algebra n _ hfn) :=
rfl  -- fails
```
It's not immediately clear whether this _can_ be fixed; the failure is much the same as the reason
that the following fails:
```lean
def cases_twice {α} (a₀ aₙ : α) : ℕ → α × α
| 0 := (a₀, a₀)
| (n + 1) := (aₙ, aₙ)

example (x : ℕ) {α} (a₀ aₙ : α) : (cases_twice a₀ aₙ x).1 = (cases_twice a₀ aₙ x).2 := rfl  -- fails
```
We don't really care at this point because this is an implementation detail (which is why this is
not a docstring), but we do in `splitting_field.algebra'` below. -/
instance algebra (n : ℕ) :
    ∀ (R : Type _) {K : Type u} [CommSemiringₓ R] [Field K],
      ∀ [Algebra R K] {f : K[X]} (hfn : f.natDegree = n), Algebra R (splitting_field_aux n f hfn) :=
  (Nat.recOn n fun R K _ _ _ _ _ => ‹Algebra R K›) fun n ih R K _ _ _ f hfn => ih R (nat_degree_remove_factor' hfn)

instance is_scalar_tower (n : ℕ) :
    ∀ (R₁ R₂ : Type _) {K : Type u} [CommSemiringₓ R₁] [CommSemiringₓ R₂] [HasSmul R₁ R₂] [Field K],
      ∀ [Algebra R₁ K] [Algebra R₂ K],
        ∀ [IsScalarTower R₁ R₂ K] {f : K[X]} (hfn : f.natDegree = n),
          IsScalarTower R₁ R₂ (splitting_field_aux n f hfn) :=
  (Nat.recOn n fun R₁ R₂ K _ _ _ _ _ _ _ _ _ => ‹IsScalarTower R₁ R₂ K›) fun n ih R₁ R₂ K _ _ _ _ _ _ _ f hfn =>
    ih R₁ R₂ (nat_degree_remove_factor' hfn)

instance algebra''' {n : ℕ} {f : K[X]} (hfn : f.natDegree = n + 1) :
    Algebra (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor (nat_degree_remove_factor' hfn)) :=
  SplittingFieldAux.algebra n _ _

instance algebra' {n : ℕ} {f : K[X]} (hfn : f.natDegree = n + 1) :
    Algebra (AdjoinRoot f.factor) (SplittingFieldAux n.succ f hfn) :=
  SplittingFieldAux.algebra''' _

instance algebra'' {n : ℕ} {f : K[X]} (hfn : f.natDegree = n + 1) :
    Algebra K (SplittingFieldAux n f.removeFactor (nat_degree_remove_factor' hfn)) :=
  SplittingFieldAux.algebra n K _

instance scalar_tower' {n : ℕ} {f : K[X]} (hfn : f.natDegree = n + 1) :
    IsScalarTower K (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor (nat_degree_remove_factor' hfn)) := by
  -- finding this instance ourselves makes things faster
  have : IsScalarTower K (AdjoinRoot f.factor) (AdjoinRoot f.factor) := IsScalarTower.right
  exact splitting_field_aux.is_scalar_tower n K (AdjoinRoot f.factor) (nat_degree_remove_factor' hfn)

instance scalar_tower {n : ℕ} {f : K[X]} (hfn : f.natDegree = n + 1) :
    IsScalarTower K (AdjoinRoot f.factor) (SplittingFieldAux _ f hfn) :=
  SplittingFieldAux.scalar_tower' _

theorem algebra_map_succ (n : ℕ) (f : K[X]) (hfn : f.natDegree = n + 1) :
    algebraMap K (splitting_field_aux _ _ hfn) =
      (algebraMap (AdjoinRoot f.factor) (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn))).comp
        (AdjoinRoot.of f.factor) :=
  IsScalarTower.algebra_map_eq _ _ _

protected theorem splits (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n), splits (algebraMap K <| splitting_field_aux n f hfn) f :=
  (Nat.recOn n fun K _ _ hf =>
      splits_of_degree_le_one _ (le_transₓ degree_le_nat_degree <| hf.symm ▸ WithBot.coe_le_coe.2 zero_le_one))
    fun n ih K _ f hf => by
    skip
    rw [← splits_id_iff_splits, algebra_map_succ, ← map_map, splits_id_iff_splits, ←
      X_sub_C_mul_remove_factor f fun h => by
        rw [h] at hf
        cases hf]
    exact splits_mul _ (splits_X_sub_C _) (ih _ _)

theorem exists_lift (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n) {L : Type _} [Field L],
        ∀ (j : K →+* L) (hf : splits j f), ∃ k : splitting_field_aux n f hfn →+* L, k.comp (algebraMap _ _) = j :=
  (Nat.recOn n fun K _ _ _ L _ j _ => ⟨j, j.comp_id⟩) fun n ih K _ f hf L _ j hj =>
    have hndf : f.nat_degree ≠ 0 := by
      intro h
      rw [h] at hf
      cases hf
    have hfn0 : f ≠ 0 := by
      intro h
      rw [h] at hndf
      exact hndf rfl
    let ⟨r, hr⟩ :=
      exists_root_of_splits _ (splits_of_splits_of_dvd j hfn0 hj (factor_dvd_of_nat_degree_ne_zero hndf))
        (mt is_unit_iff_degree_eq_zero.2 f.irreducible_factor.1)
    have hmf0 : map (AdjoinRoot.of f.factor) f ≠ 0 := map_ne_zero hfn0
    have hsf : splits (AdjoinRoot.lift j r hr) f.remove_factor := by
      rw [← X_sub_C_mul_remove_factor _ hndf] at hmf0
      refine' (splits_of_splits_mul _ hmf0 _).2
      rwa [X_sub_C_mul_remove_factor _ hndf, ← splits_id_iff_splits, map_map, AdjoinRoot.lift_comp_of,
        splits_id_iff_splits]
    let ⟨k, hk⟩ := ih f.remove_factor (nat_degree_remove_factor' hf) (AdjoinRoot.lift j r hr) hsf
    ⟨k, by
      rw [algebra_map_succ, ← RingHom.comp_assoc, hk, AdjoinRoot.lift_comp_of]⟩

theorem adjoin_roots (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n),
        Algebra.adjoin K
            (↑(f.map <| algebraMap K <| splitting_field_aux n f hfn).roots.toFinset :
              Set (splitting_field_aux n f hfn)) =
          ⊤ :=
  (Nat.recOn n fun K _ f hf => Algebra.eq_top_iff.2 fun x => Subalgebra.range_le _ ⟨x, rfl⟩) fun n ih K _ f hfn => by
    have hndf : f.nat_degree ≠ 0 := by
      intro h
      rw [h] at hfn
      cases hfn
    have hfn0 : f ≠ 0 := by
      intro h
      rw [h] at hndf
      exact hndf rfl
    have hmf0 : map (algebraMap K (splitting_field_aux n.succ f hfn)) f ≠ 0 := map_ne_zero hfn0
    rw [algebra_map_succ, ← map_map, ← X_sub_C_mul_remove_factor _ hndf, Polynomial.map_mul] at hmf0⊢
    rw [roots_mul hmf0, Polynomial.map_sub, map_X, map_C, roots_X_sub_C, Multiset.to_finset_add, Finset.coe_union,
      Multiset.to_finset_singleton, Finset.coe_singleton, Algebra.adjoin_union_eq_adjoin_adjoin, ← Set.image_singleton,
      Algebra.adjoin_algebra_map K (AdjoinRoot f.factor)
        (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)),
      AdjoinRoot.adjoin_root_eq_top, Algebra.map_top,
      IsScalarTower.adjoin_range_to_alg_hom K (AdjoinRoot f.factor)
        (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)),
      ih, Subalgebra.restrict_scalars_top]

end SplittingFieldAux

/-- A splitting field of a polynomial. -/
def SplittingField (f : K[X]) :=
  SplittingFieldAux _ f rfl

namespace SplittingField

variable (f : K[X])

instance : Field (SplittingField f) :=
  SplittingFieldAux.field _ _

instance inhabited : Inhabited (SplittingField f) :=
  ⟨37⟩

/-- This should be an instance globally, but it creates diamonds with the `ℕ` and `ℤ` actions:

```lean
example :
  (add_comm_monoid.nat_module : module ℕ (splitting_field f)) =
    @algebra.to_module _ _ _ _ (splitting_field.algebra' f) :=
rfl  -- fails

example :
  (add_comm_group.int_module _ : module ℤ (splitting_field f)) =
    @algebra.to_module _ _ _ _ (splitting_field.algebra' f) :=
rfl  -- fails
```

Until we resolve these diamonds, it's more convenient to only turn this instance on with
`local attribute [instance]` in places where the benefit of having the instance outweighs the cost.

In the meantime, the `splitting_field.algebra` instance below is immune to these particular diamonds
since `K = ℕ` and `K = ℤ` are not possible due to the `field K` assumption. Diamonds in
`algebra ℚ (splitting_field f)` instances are still possible, but this is a problem throughout the
library and not unique to this `algebra` instance.
-/
instance algebra' {R} [CommSemiringₓ R] [Algebra R K] : Algebra R (SplittingField f) :=
  SplittingFieldAux.algebra _ _ _

instance : Algebra K (SplittingField f) :=
  SplittingFieldAux.algebra _ _ _

protected theorem splits : Splits (algebraMap K (SplittingField f)) f :=
  SplittingFieldAux.splits _ _ _

variable [Algebra K L] (hb : Splits (algebraMap K L) f)

/-- Embeds the splitting field into any other field that splits the polynomial. -/
def lift : SplittingField f →ₐ[K] L :=
  { Classical.some (SplittingFieldAux.exists_lift _ _ _ _ hb) with
    commutes' := fun r => by
      have := Classical.some_spec (splitting_field_aux.exists_lift _ _ _ _ hb)
      exact RingHom.ext_iff.1 this r }

theorem adjoin_roots :
    Algebra.adjoin K (↑(f.map (algebraMap K <| SplittingField f)).roots.toFinset : Set (SplittingField f)) = ⊤ :=
  SplittingFieldAux.adjoin_roots _ _ _

theorem adjoin_root_set : Algebra.adjoin K (f.RootSet f.SplittingField) = ⊤ :=
  adjoin_roots f

end SplittingField

variable (K L) [Algebra K L]

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`Splits] []
-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`adjoin_roots] []
/-- Typeclass characterising splitting fields. -/
class IsSplittingField (f : K[X]) : Prop where
  Splits : Splits (algebraMap K L) f
  adjoin_roots : Algebra.adjoin K (↑(f.map (algebraMap K L)).roots.toFinset : Set L) = ⊤

namespace IsSplittingField

variable {K}

instance splitting_field (f : K[X]) : IsSplittingField K (SplittingField f) f :=
  ⟨SplittingField.splits f, SplittingField.adjoin_roots f⟩

section ScalarTower

variable {K L F} [Algebra F K] [Algebra F L] [IsScalarTower F K L]

variable {K}

instance map (f : F[X]) [IsSplittingField F L f] : IsSplittingField K L (f.map <| algebraMap F K) :=
  ⟨by
    rw [splits_map_iff, ← IsScalarTower.algebra_map_eq]
    exact splits L f,
    Subalgebra.restrict_scalars_injective F <| by
      rw [map_map, ← IsScalarTower.algebra_map_eq, Subalgebra.restrict_scalars_top, eq_top_iff, ← adjoin_roots L f,
        Algebra.adjoin_le_iff]
      exact fun x hx => @Algebra.subset_adjoin K _ _ _ _ _ _ hx⟩

variable {K} (L)

theorem splits_iff (f : K[X]) [IsSplittingField K L f] :
    Polynomial.Splits (RingHom.id K) f ↔ (⊤ : Subalgebra K L) = ⊥ :=
  ⟨fun h =>
    eq_bot_iff.2 <|
      adjoin_roots L f ▸
        (roots_map (algebraMap K L) h).symm ▸
          Algebra.adjoin_le_iff.2 fun y hy =>
            let ⟨x, hxs, hxy⟩ :=
              Finset.mem_image.1
                (by
                  rwa [Multiset.to_finset_map] at hy)
            hxy ▸ SetLike.mem_coe.2 <| Subalgebra.algebra_map_mem _ _,
    fun h =>
    @RingEquiv.to_ring_hom_refl K _ ▸
      RingEquiv.self_trans_symm (RingEquiv.ofBijective _ <| Algebra.bijective_algebra_map_iff.2 h) ▸ by
        rw [RingEquiv.to_ring_hom_trans]
        exact splits_comp_of_splits _ _ (splits L f)⟩

theorem mul (f g : F[X]) (hf : f ≠ 0) (hg : g ≠ 0) [IsSplittingField F K f]
    [IsSplittingField K L (g.map <| algebraMap F K)] : IsSplittingField F L (f * g) :=
  ⟨(IsScalarTower.algebra_map_eq F K L).symm ▸
      splits_mul _ (splits_comp_of_splits _ _ (splits K f))
        ((splits_map_iff _ _).1 (splits L <| g.map <| algebraMap F K)),
    by
    rw [Polynomial.map_mul, roots_mul (mul_ne_zero (map_ne_zero hf : f.map (algebraMap F L) ≠ 0) (map_ne_zero hg)),
      Multiset.to_finset_add, Finset.coe_union, Algebra.adjoin_union_eq_adjoin_adjoin,
      IsScalarTower.algebra_map_eq F K L, ← map_map,
      roots_map (algebraMap K L) ((splits_id_iff_splits <| algebraMap F K).2 <| splits K f), Multiset.to_finset_map,
      Finset.coe_image, Algebra.adjoin_algebra_map, adjoin_roots, Algebra.map_top,
      IsScalarTower.adjoin_range_to_alg_hom, ← map_map, adjoin_roots, Subalgebra.restrict_scalars_top]⟩

end ScalarTower

/-- Splitting field of `f` embeds into any field that splits `f`. -/
def lift [Algebra K F] (f : K[X]) [IsSplittingField K L f] (hf : Polynomial.Splits (algebraMap K F) f) : L →ₐ[K] F :=
  if hf0 : f = 0 then
    (Algebra.ofId K F).comp <|
      (Algebra.botEquiv K L : (⊥ : Subalgebra K L) →ₐ[K] K).comp <| by
        rw [← (splits_iff L f).1 (show f.splits (RingHom.id K) from hf0.symm ▸ splits_zero _)]
        exact Algebra.toTop
  else
    AlgHom.comp
      (by
        rw [← adjoin_roots L f]
        exact
          Classical.choice
            ((lift_of_splits _) fun y hy =>
              have : aeval y f = 0 :=
                (eval₂_eq_eval_map _).trans <| (mem_roots <| map_ne_zero hf0).1 (multiset.mem_to_finset.mp hy)
              ⟨is_algebraic_iff_is_integral.1 ⟨f, hf0, this⟩,
                splits_of_splits_of_dvd _ hf0 hf <| minpoly.dvd _ _ this⟩))
      Algebra.toTop

theorem finite_dimensional (f : K[X]) [IsSplittingField K L f] : FiniteDimensional K L :=
  ⟨@Algebra.top_to_submodule K L _ _ _ ▸
      adjoin_roots L f ▸
        fg_adjoin_of_finite (Finset.finite_to_set _) fun y hy =>
          if hf : f = 0 then by
            rw [hf, Polynomial.map_zero, roots_zero] at hy
            cases hy
          else
            is_algebraic_iff_is_integral.1
              ⟨f, hf, (eval₂_eq_eval_map _).trans <| (mem_roots <| map_ne_zero hf).1 (Multiset.mem_to_finset.mp hy)⟩⟩

instance (f : K[X]) : FiniteDimensional K f.SplittingField :=
  finite_dimensional f.SplittingField f

/-- Any splitting field is isomorphic to `splitting_field f`. -/
def algEquiv (f : K[X]) [IsSplittingField K L f] : L ≃ₐ[K] SplittingField f := by
  refine'
    AlgEquiv.ofBijective (lift L f <| splits (splitting_field f) f)
      ⟨RingHom.injective (lift L f <| splits (splitting_field f) f).toRingHom, _⟩
  have := FiniteDimensional (splitting_field f) f
  have := FiniteDimensional L f
  have : FiniteDimensional.finrank K L = FiniteDimensional.finrank K (splitting_field f) :=
    le_antisymmₓ
      (LinearMap.finrank_le_finrank_of_injective
        (show Function.Injective (lift L f <| splits (splitting_field f) f).toLinearMap from
          RingHom.injective (lift L f <| splits (splitting_field f) f : L →+* f.splitting_field)))
      (LinearMap.finrank_le_finrank_of_injective
        (show Function.Injective (lift (splitting_field f) f <| splits L f).toLinearMap from
          RingHom.injective (lift (splitting_field f) f <| splits L f : f.splitting_field →+* L)))
  change Function.Surjective (lift L f <| splits (splitting_field f) f).toLinearMap
  refine' (LinearMap.injective_iff_surjective_of_finrank_eq_finrank this).1 _
  exact RingHom.injective (lift L f <| splits (splitting_field f) f : L →+* f.splitting_field)

end IsSplittingField

end SplittingField

end Polynomial


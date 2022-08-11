/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.PunitInstances
import Mathbin.LinearAlgebra.Finsupp
import Mathbin.RingTheory.Nilpotent
import Mathbin.RingTheory.Localization.Away
import Mathbin.RingTheory.Ideal.Prod
import Mathbin.RingTheory.Ideal.Over
import Mathbin.Topology.Sets.Opens
import Mathbin.Topology.Sober

/-!
# Prime spectrum of a commutative ring

The prime spectrum of a commutative ring is the type of all prime ideals.
It is naturally endowed with a topology: the Zariski topology.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `algebraic_geometry.structure_sheaf`.)

## Main definitions

* `prime_spectrum R`: The prime spectrum of a commutative ring `R`,
  i.e., the set of all prime ideals of `R`.
* `zero_locus s`: The zero locus of a subset `s` of `R`
  is the subset of `prime_spectrum R` consisting of all prime ideals that contain `s`.
* `vanishing_ideal t`: The vanishing ideal of a subset `t` of `prime_spectrum R`
  is the intersection of points in `t` (viewed as prime ideals).

## Conventions

We denote subsets of rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from
<https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

-/


noncomputable section

open Classical

universe u v

variable (R : Type u) [CommRingₓ R]

/-- The prime spectrum of a commutative ring `R`
is the type of all prime ideals of `R`.

It is naturally endowed with a topology (the Zariski topology),
and a sheaf of commutative rings (see `algebraic_geometry.structure_sheaf`).
It is a fundamental building block in algebraic geometry. -/
@[nolint has_inhabited_instance]
def PrimeSpectrum :=
  { I : Ideal R // I.IsPrime }

variable {R}

namespace PrimeSpectrum

/-- A method to view a point in the prime spectrum of a commutative ring
as an ideal of that ring. -/
abbrev asIdeal (x : PrimeSpectrum R) : Ideal R :=
  x.val

instance is_prime (x : PrimeSpectrum R) : x.asIdeal.IsPrime :=
  x.2

/-- The prime spectrum of the zero ring is empty.
-/
theorem punit (x : PrimeSpectrum PUnit) : False :=
  x.1.ne_top_iff_one.1 x.2.1 <| Subsingleton.elimₓ (0 : PUnit) 1 ▸ x.1.zero_mem

section

variable (R) (S : Type v) [CommRingₓ S]

/-- The prime spectrum of `R × S` is in bijection with the disjoint unions of the prime spectrum of
    `R` and the prime spectrum of `S`. -/
noncomputable def primeSpectrumProd : PrimeSpectrum (R × S) ≃ Sum (PrimeSpectrum R) (PrimeSpectrum S) :=
  Ideal.primeIdealsEquiv R S

variable {R S}

@[simp]
theorem prime_spectrum_prod_symm_inl_as_ideal (x : PrimeSpectrum R) :
    ((primeSpectrumProd R S).symm (Sum.inl x)).asIdeal = Ideal.prod x.asIdeal ⊤ := by
  cases x
  rfl

@[simp]
theorem prime_spectrum_prod_symm_inr_as_ideal (x : PrimeSpectrum S) :
    ((primeSpectrumProd R S).symm (Sum.inr x)).asIdeal = Ideal.prod ⊤ x.asIdeal := by
  cases x
  rfl

end

@[ext]
theorem ext {x y : PrimeSpectrum R} : x = y ↔ x.asIdeal = y.asIdeal :=
  Subtype.ext_iff_val

/-- The zero locus of a set `s` of elements of a commutative ring `R`
is the set of all prime ideals of the ring that contain the set `s`.

An element `f` of `R` can be thought of as a dependent function
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `zero_locus s` is exactly the subset of `prime_spectrum R`
where all "functions" in `s` vanish simultaneously.
-/
def ZeroLocus (s : Set R) : Set (PrimeSpectrum R) :=
  { x | s ⊆ x.asIdeal }

@[simp]
theorem mem_zero_locus (x : PrimeSpectrum R) (s : Set R) : x ∈ ZeroLocus s ↔ s ⊆ x.asIdeal :=
  Iff.rfl

@[simp]
theorem zero_locus_span (s : Set R) : ZeroLocus (Ideal.span s : Set R) = ZeroLocus s := by
  ext x
  exact (Submodule.gi R R).gc s x.as_ideal

/-- The vanishing ideal of a set `t` of points
of the prime spectrum of a commutative ring `R`
is the intersection of all the prime ideals in the set `t`.

An element `f` of `R` can be thought of as a dependent function
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `vanishing_ideal t` is exactly the ideal of `R`
consisting of all "functions" that vanish on all of `t`.
-/
def vanishingIdeal (t : Set (PrimeSpectrum R)) : Ideal R :=
  ⨅ (x : PrimeSpectrum R) (h : x ∈ t), x.asIdeal

theorem coe_vanishing_ideal (t : Set (PrimeSpectrum R)) :
    (vanishingIdeal t : Set R) = { f : R | ∀ x : PrimeSpectrum R, x ∈ t → f ∈ x.asIdeal } := by
  ext f
  rw [vanishing_ideal, SetLike.mem_coe, Submodule.mem_infi]
  apply forall_congrₓ
  intro x
  rw [Submodule.mem_infi]

theorem mem_vanishing_ideal (t : Set (PrimeSpectrum R)) (f : R) :
    f ∈ vanishingIdeal t ↔ ∀ x : PrimeSpectrum R, x ∈ t → f ∈ x.asIdeal := by
  rw [← SetLike.mem_coe, coe_vanishing_ideal, Set.mem_set_of_eq]

@[simp]
theorem vanishing_ideal_singleton (x : PrimeSpectrum R) : vanishingIdeal ({x} : Set (PrimeSpectrum R)) = x.asIdeal := by
  simp [← vanishing_ideal]

theorem subset_zero_locus_iff_le_vanishing_ideal (t : Set (PrimeSpectrum R)) (I : Ideal R) :
    t ⊆ ZeroLocus I ↔ I ≤ vanishingIdeal t :=
  ⟨fun h f k => (mem_vanishing_ideal _ _).mpr fun x j => (mem_zero_locus _ _).mpr (h j) k, fun h => fun x j =>
    (mem_zero_locus _ _).mpr (le_transₓ h fun f h => ((mem_vanishing_ideal _ _).mp h) x j)⟩

section Gc

variable (R)

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
theorem gc :
    @GaloisConnection (Ideal R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun I => ZeroLocus I) fun t => vanishingIdeal t :=
  fun I t => subset_zero_locus_iff_le_vanishing_ideal t I

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
theorem gc_set :
    @GaloisConnection (Set R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun s => ZeroLocus s) fun t => vanishingIdeal t := by
  have ideal_gc : GaloisConnection Ideal.span coe := (Submodule.gi R R).gc
  simpa [← zero_locus_span, ← Function.comp] using ideal_gc.compose (gc R)

theorem subset_zero_locus_iff_subset_vanishing_ideal (t : Set (PrimeSpectrum R)) (s : Set R) :
    t ⊆ ZeroLocus s ↔ s ⊆ vanishingIdeal t :=
  (gc_set R) s t

end Gc

theorem subset_vanishing_ideal_zero_locus (s : Set R) : s ⊆ vanishingIdeal (ZeroLocus s) :=
  (gc_set R).le_u_l s

theorem le_vanishing_ideal_zero_locus (I : Ideal R) : I ≤ vanishingIdeal (ZeroLocus I) :=
  (gc R).le_u_l I

@[simp]
theorem vanishing_ideal_zero_locus_eq_radical (I : Ideal R) : vanishingIdeal (ZeroLocus (I : Set R)) = I.radical :=
  Ideal.ext fun f => by
    rw [mem_vanishing_ideal, Ideal.radical_eq_Inf, Submodule.mem_Inf]
    exact ⟨fun h x hx => h ⟨x, hx.2⟩ hx.1, fun h x hx => h x.1 ⟨hx, x.2⟩⟩

@[simp]
theorem zero_locus_radical (I : Ideal R) : ZeroLocus (I.radical : Set R) = ZeroLocus I :=
  vanishing_ideal_zero_locus_eq_radical I ▸ (gc R).l_u_l_eq_l I

theorem subset_zero_locus_vanishing_ideal (t : Set (PrimeSpectrum R)) : t ⊆ ZeroLocus (vanishingIdeal t) :=
  (gc R).l_u_le t

theorem zero_locus_anti_mono {s t : Set R} (h : s ⊆ t) : ZeroLocus t ⊆ ZeroLocus s :=
  (gc_set R).monotone_l h

theorem zero_locus_anti_mono_ideal {s t : Ideal R} (h : s ≤ t) : ZeroLocus (t : Set R) ⊆ ZeroLocus (s : Set R) :=
  (gc R).monotone_l h

theorem vanishing_ideal_anti_mono {s t : Set (PrimeSpectrum R)} (h : s ⊆ t) : vanishingIdeal t ≤ vanishingIdeal s :=
  (gc R).monotone_u h

theorem zero_locus_subset_zero_locus_iff (I J : Ideal R) :
    ZeroLocus (I : Set R) ⊆ ZeroLocus (J : Set R) ↔ J ≤ I.radical :=
  ⟨fun h =>
    Ideal.radical_le_radical_iff.mp
      (vanishing_ideal_zero_locus_eq_radical I ▸ vanishing_ideal_zero_locus_eq_radical J ▸ vanishing_ideal_anti_mono h),
    fun h => zero_locus_radical I ▸ zero_locus_anti_mono_ideal h⟩

theorem zero_locus_subset_zero_locus_singleton_iff (f g : R) :
    ZeroLocus ({f} : Set R) ⊆ ZeroLocus {g} ↔ g ∈ (Ideal.span ({f} : Set R)).radical := by
  rw [← zero_locus_span {f}, ← zero_locus_span {g}, zero_locus_subset_zero_locus_iff, Ideal.span_le,
    Set.singleton_subset_iff, SetLike.mem_coe]

theorem zero_locus_bot : ZeroLocus ((⊥ : Ideal R) : Set R) = Set.Univ :=
  (gc R).l_bot

@[simp]
theorem zero_locus_singleton_zero : ZeroLocus ({0} : Set R) = Set.Univ :=
  zero_locus_bot

@[simp]
theorem zero_locus_empty : ZeroLocus (∅ : Set R) = Set.Univ :=
  (gc_set R).l_bot

@[simp]
theorem vanishing_ideal_univ : vanishingIdeal (∅ : Set (PrimeSpectrum R)) = ⊤ := by
  simpa using (gc R).u_top

theorem zero_locus_empty_of_one_mem {s : Set R} (h : (1 : R) ∈ s) : ZeroLocus s = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro x hx
  rw [mem_zero_locus] at hx
  have x_prime : x.as_ideal.is_prime := by
    infer_instance
  have eq_top : x.as_ideal = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact hx h
  apply x_prime.ne_top eq_top

@[simp]
theorem zero_locus_singleton_one : ZeroLocus ({1} : Set R) = ∅ :=
  zero_locus_empty_of_one_mem (Set.mem_singleton (1 : R))

theorem zero_locus_empty_iff_eq_top {I : Ideal R} : ZeroLocus (I : Set R) = ∅ ↔ I = ⊤ := by
  constructor
  · contrapose!
    intro h
    apply set.ne_empty_iff_nonempty.mpr
    rcases Ideal.exists_le_maximal I h with ⟨M, hM, hIM⟩
    exact ⟨⟨M, hM.is_prime⟩, hIM⟩
    
  · rintro rfl
    apply zero_locus_empty_of_one_mem
    trivial
    

@[simp]
theorem zero_locus_univ : ZeroLocus (Set.Univ : Set R) = ∅ :=
  zero_locus_empty_of_one_mem (Set.mem_univ 1)

theorem zero_locus_sup (I J : Ideal R) : ZeroLocus ((I⊔J : Ideal R) : Set R) = ZeroLocus I ∩ ZeroLocus J :=
  (gc R).l_sup

theorem zero_locus_union (s s' : Set R) : ZeroLocus (s ∪ s') = ZeroLocus s ∩ ZeroLocus s' :=
  (gc_set R).l_sup

theorem vanishing_ideal_union (t t' : Set (PrimeSpectrum R)) :
    vanishingIdeal (t ∪ t') = vanishingIdeal t⊓vanishingIdeal t' :=
  (gc R).u_inf

theorem zero_locus_supr {ι : Sort _} (I : ι → Ideal R) :
    ZeroLocus ((⨆ i, I i : Ideal R) : Set R) = ⋂ i, ZeroLocus (I i) :=
  (gc R).l_supr

theorem zero_locus_Union {ι : Sort _} (s : ι → Set R) : ZeroLocus (⋃ i, s i) = ⋂ i, ZeroLocus (s i) :=
  (gc_set R).l_supr

theorem zero_locus_bUnion (s : Set (Set R)) : ZeroLocus (⋃ s' ∈ s, s' : Set R) = ⋂ s' ∈ s, ZeroLocus s' := by
  simp only [← zero_locus_Union]

theorem vanishing_ideal_Union {ι : Sort _} (t : ι → Set (PrimeSpectrum R)) :
    vanishingIdeal (⋃ i, t i) = ⨅ i, vanishingIdeal (t i) :=
  (gc R).u_infi

theorem zero_locus_inf (I J : Ideal R) : ZeroLocus ((I⊓J : Ideal R) : Set R) = ZeroLocus I ∪ ZeroLocus J :=
  Set.ext fun x => by
    simpa using x.2.inf_le

theorem union_zero_locus (s s' : Set R) :
    ZeroLocus s ∪ ZeroLocus s' = ZeroLocus (Ideal.span s⊓Ideal.span s' : Ideal R) := by
  rw [zero_locus_inf]
  simp

theorem zero_locus_mul (I J : Ideal R) : ZeroLocus ((I * J : Ideal R) : Set R) = ZeroLocus I ∪ ZeroLocus J :=
  Set.ext fun x => by
    simpa using x.2.mul_le

theorem zero_locus_singleton_mul (f g : R) : ZeroLocus ({f * g} : Set R) = ZeroLocus {f} ∪ ZeroLocus {g} :=
  Set.ext fun x => by
    simpa using x.2.mul_mem_iff_mem_or_mem

@[simp]
theorem zero_locus_pow (I : Ideal R) {n : ℕ} (hn : 0 < n) : ZeroLocus ((I ^ n : Ideal R) : Set R) = ZeroLocus I :=
  zero_locus_radical (I ^ n) ▸ (I.radical_pow n hn).symm ▸ zero_locus_radical I

@[simp]
theorem zero_locus_singleton_pow (f : R) (n : ℕ) (hn : 0 < n) : ZeroLocus ({f ^ n} : Set R) = ZeroLocus {f} :=
  Set.ext fun x => by
    simpa using x.2.pow_mem_iff_mem n hn

theorem sup_vanishing_ideal_le (t t' : Set (PrimeSpectrum R)) :
    vanishingIdeal t⊔vanishingIdeal t' ≤ vanishingIdeal (t ∩ t') := by
  intro r
  rw [Submodule.mem_sup, mem_vanishing_ideal]
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  rw [mem_vanishing_ideal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim

theorem mem_compl_zero_locus_iff_not_mem {f : R} {I : PrimeSpectrum R} :
    I ∈ (ZeroLocus {f} : Set (PrimeSpectrum R))ᶜ ↔ f ∉ I.asIdeal := by
  rw [Set.mem_compl_eq, mem_zero_locus, Set.singleton_subset_iff] <;> rfl

/-- The Zariski topology on the prime spectrum of a commutative ring
is defined via the closed sets of the topology:
they are exactly those sets that are the zero locus of a subset of the ring. -/
instance zariskiTopology : TopologicalSpace (PrimeSpectrum R) :=
  TopologicalSpace.ofClosed (Set.Range PrimeSpectrum.ZeroLocus)
    ⟨Set.Univ, by
      simp ⟩
    (by
      intro Zs h
      rw [Set.sInter_eq_Inter]
      let f : Zs → Set R := fun i => Classical.some (h i.2)
      have hf : ∀ i : Zs, ↑i = zero_locus (f i) := fun i => (Classical.some_spec (h i.2)).symm
      simp only [← hf]
      exact ⟨_, zero_locus_Union _⟩)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact ⟨_, (union_zero_locus s t).symm⟩)

theorem is_open_iff (U : Set (PrimeSpectrum R)) : IsOpen U ↔ ∃ s, Uᶜ = ZeroLocus s := by
  simp only [← @eq_comm _ (Uᶜ)] <;> rfl

theorem is_closed_iff_zero_locus (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ ∃ s, Z = ZeroLocus s := by
  rw [← is_open_compl_iff, is_open_iff, compl_compl]

theorem is_closed_iff_zero_locus_ideal (Z : Set (PrimeSpectrum R)) : IsClosed Z ↔ ∃ s : Ideal R, Z = ZeroLocus s :=
  (is_closed_iff_zero_locus _).trans
    ⟨fun x => ⟨_, x.some_spec.trans (zero_locus_span _).symm⟩, fun x => ⟨_, x.some_spec⟩⟩

theorem is_closed_iff_zero_locus_radical_ideal (Z : Set (PrimeSpectrum R)) :
    IsClosed Z ↔ ∃ s : Ideal R, s.radical = s ∧ Z = ZeroLocus s :=
  (is_closed_iff_zero_locus_ideal _).trans
    ⟨fun x => ⟨_, Ideal.radical_idem _, x.some_spec.trans (zero_locus_radical _).symm⟩, fun x => ⟨_, x.some_spec.2⟩⟩

theorem is_closed_zero_locus (s : Set R) : IsClosed (ZeroLocus s) := by
  rw [is_closed_iff_zero_locus]
  exact ⟨s, rfl⟩

theorem is_closed_singleton_iff_is_maximal (x : PrimeSpectrum R) :
    IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x.asIdeal.IsMaximal := by
  refine' (is_closed_iff_zero_locus _).trans ⟨fun h => _, fun h => _⟩
  · obtain ⟨s, hs⟩ := h
    rw [eq_comm, Set.eq_singleton_iff_unique_mem] at hs
    refine'
      ⟨⟨x.2.1, fun I hI =>
          not_not.1 (mt (Ideal.exists_le_maximal I) <| not_exists.2 fun J => not_and.2 fun hJ hIJ => _)⟩⟩
    exact
      ne_of_ltₓ (lt_of_lt_of_leₓ hI hIJ)
        (symm <| congr_arg PrimeSpectrum.asIdeal (hs.2 ⟨J, hJ.is_prime⟩ fun r hr => hIJ (le_of_ltₓ hI <| hs.1 hr)))
    
  · refine' ⟨x.as_ideal.1, _⟩
    rw [eq_comm, Set.eq_singleton_iff_unique_mem]
    refine' ⟨fun _ h => h, fun y hy => PrimeSpectrum.ext.2 (h.eq_of_le y.2.ne_top hy).symm⟩
    

theorem zero_locus_vanishing_ideal_eq_closure (t : Set (PrimeSpectrum R)) :
    ZeroLocus (vanishingIdeal t : Set R) = Closure t := by
  apply Set.Subset.antisymm
  · rintro x hx t' ⟨ht', ht⟩
    obtain ⟨fs, rfl⟩ : ∃ s, t' = zero_locus s := by
      rwa [is_closed_iff_zero_locus] at ht'
    rw [subset_zero_locus_iff_subset_vanishing_ideal] at ht
    exact Set.Subset.trans ht hx
    
  · rw [(is_closed_zero_locus _).closure_subset_iff]
    exact subset_zero_locus_vanishing_ideal t
    

theorem vanishing_ideal_closure (t : Set (PrimeSpectrum R)) : vanishingIdeal (Closure t) = vanishingIdeal t :=
  zero_locus_vanishing_ideal_eq_closure t ▸ (gc R).u_l_u_eq_u t

theorem t1_space_iff_is_field [IsDomain R] : T1Space (PrimeSpectrum R) ↔ IsField R := by
  refine' ⟨_, fun h => _⟩
  · intro h
    have hbot : Ideal.IsPrime (⊥ : Ideal R) := Ideal.bot_prime
    exact
      not_not.1
        (mt
          (Ringₓ.ne_bot_of_is_maximal_of_not_is_field <|
            (is_closed_singleton_iff_is_maximal _).1 (T1Space.t1 ⟨⊥, hbot⟩))
          (not_not.2 rfl))
    
  · refine' ⟨fun x => (is_closed_singleton_iff_is_maximal x).2 _⟩
    by_cases' hx : x.as_ideal = ⊥
    · exact hx.symm ▸ @Ideal.bot_is_maximal R (@Field.toDivisionRing _ h.to_field)
      
    · exact absurd h (Ringₓ.not_is_field_iff_exists_prime.2 ⟨x.as_ideal, ⟨hx, x.2⟩⟩)
      
    

-- mathport name: «exprZ( )»
local notation "Z(" a ")" => ZeroLocus (a : Set R)

theorem is_irreducible_zero_locus_iff_of_radical (I : Ideal R) (hI : I.radical = I) :
    IsIrreducible (ZeroLocus (I : Set R)) ↔ I.IsPrime := by
  rw [Ideal.is_prime_iff, IsIrreducible]
  apply and_congr
  · rw [← Set.ne_empty_iff_nonempty, Ne.def, zero_locus_empty_iff_eq_top]
    
  · trans ∀ x y : Ideal R, Z(I) ⊆ Z(x) ∪ Z(y) → Z(I) ⊆ Z(x) ∨ Z(I) ⊆ Z(y)
    · simp_rw [is_preirreducible_iff_closed_union_closed, is_closed_iff_zero_locus_ideal]
      constructor
      · rintro h x y
        exact h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        
      · rintro h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact h x y
        
      
    · simp_rw [← zero_locus_inf, subset_zero_locus_iff_le_vanishing_ideal, vanishing_ideal_zero_locus_eq_radical, hI]
      constructor
      · intro h x y h'
        simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Ideal.span_le]
        apply h
        rw [← hI, ← Ideal.radical_le_radical_iff, Ideal.radical_inf, ← Ideal.radical_mul, Ideal.radical_le_radical_iff,
          hI, Ideal.span_mul_span]
        simpa [← Ideal.span_le] using h'
        
      · simp_rw [or_iff_not_imp_left, SetLike.not_le_iff_exists]
        rintro h s t h' ⟨x, hx, hx'⟩ y hy
        exact h (h' ⟨Ideal.mul_mem_right _ _ hx, Ideal.mul_mem_left _ _ hy⟩) hx'
        
      
    

theorem is_irreducible_zero_locus_iff (I : Ideal R) : IsIrreducible (ZeroLocus (I : Set R)) ↔ I.radical.IsPrime :=
  zero_locus_radical I ▸ is_irreducible_zero_locus_iff_of_radical _ I.radical_idem

instance [IsDomain R] : IrreducibleSpace (PrimeSpectrum R) := by
  rw [irreducible_space_def, Set.top_eq_univ, ← zero_locus_bot, is_irreducible_zero_locus_iff]
  simpa using Ideal.bot_prime

instance : QuasiSober (PrimeSpectrum R) := by
  constructor
  intro S h₁ h₂
  rw [← h₂.closure_eq, ← zero_locus_vanishing_ideal_eq_closure, is_irreducible_zero_locus_iff] at h₁
  use ⟨_, h₁⟩
  obtain ⟨s, hs, rfl⟩ := (is_closed_iff_zero_locus_radical_ideal _).mp h₂
  rw [is_generic_point_iff_forall_closed h₂]
  intro Z hZ hxZ
  obtain ⟨t, rfl⟩ := (is_closed_iff_zero_locus_ideal _).mp hZ
  exact
    zero_locus_anti_mono
      (by
        simpa [← hs] using hxZ)
  simp [← hs]

section Comap

variable {S : Type v} [CommRingₓ S] {S' : Type _} [CommRingₓ S']

theorem preimage_comap_zero_locus_aux (f : R →+* S) (s : Set R) :
    (fun y => ⟨Ideal.comap f y.asIdeal, inferInstance⟩ : PrimeSpectrum S → PrimeSpectrum R) ⁻¹' ZeroLocus s =
      ZeroLocus (f '' s) :=
  by
  ext x
  simp only [← mem_zero_locus, ← Set.image_subset_iff]
  rfl

/-- The function between prime spectra of commutative rings induced by a ring homomorphism.
This function is continuous. -/
def comap (f : R →+* S) : C(PrimeSpectrum S, PrimeSpectrum R) where
  toFun := fun y => ⟨Ideal.comap f y.asIdeal, inferInstance⟩
  continuous_to_fun := by
    simp only [← continuous_iff_is_closed, ← is_closed_iff_zero_locus]
    rintro _ ⟨s, rfl⟩
    exact ⟨_, preimage_comap_zero_locus_aux f s⟩

variable (f : R →+* S)

@[simp]
theorem comap_as_ideal (y : PrimeSpectrum S) : (comap f y).asIdeal = Ideal.comap f y.asIdeal :=
  rfl

@[simp]
theorem comap_id : comap (RingHom.id R) = ContinuousMap.id _ := by
  ext
  rfl

@[simp]
theorem comap_comp (f : R →+* S) (g : S →+* S') : comap (g.comp f) = (comap f).comp (comap g) :=
  rfl

theorem comap_comp_apply (f : R →+* S) (g : S →+* S') (x : PrimeSpectrum S') :
    PrimeSpectrum.comap (g.comp f) x = (PrimeSpectrum.comap f) (PrimeSpectrum.comap g x) :=
  rfl

@[simp]
theorem preimage_comap_zero_locus (s : Set R) : comap f ⁻¹' ZeroLocus s = ZeroLocus (f '' s) :=
  preimage_comap_zero_locus_aux f s

theorem comap_injective_of_surjective (f : R →+* S) (hf : Function.Surjective f) : Function.Injective (comap f) :=
  fun x y h =>
  PrimeSpectrum.ext.2
    (Ideal.comap_injective_of_surjective f hf
      (congr_arg PrimeSpectrum.asIdeal h : (comap f x).asIdeal = (comap f y).asIdeal))

theorem comap_singleton_is_closed_of_surjective (f : R →+* S) (hf : Function.Surjective f) (x : PrimeSpectrum S)
    (hx : IsClosed ({x} : Set (PrimeSpectrum S))) : IsClosed ({comap f x} : Set (PrimeSpectrum R)) := by
  have : x.as_ideal.is_maximal := (is_closed_singleton_iff_is_maximal x).1 hx
  exact (is_closed_singleton_iff_is_maximal _).2 (Ideal.comap_is_maximal_of_surjective f hf)

theorem comap_singleton_is_closed_of_is_integral (f : R →+* S) (hf : f.IsIntegral) (x : PrimeSpectrum S)
    (hx : IsClosed ({x} : Set (PrimeSpectrum S))) : IsClosed ({comap f x} : Set (PrimeSpectrum R)) :=
  (is_closed_singleton_iff_is_maximal _).2
    (Ideal.is_maximal_comap_of_is_integral_of_is_maximal' f hf x.asIdeal <| (is_closed_singleton_iff_is_maximal x).1 hx)

variable (S)

theorem localization_comap_inducing [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Inducing (comap (algebraMap R S)) := by
  constructor
  rw [topological_space_eq_iff]
  intro U
  simp_rw [← is_closed_compl_iff]
  generalize Uᶜ = Z
  simp_rw [is_closed_induced_iff, is_closed_iff_zero_locus]
  constructor
  · rintro ⟨s, rfl⟩
    refine' ⟨_, ⟨algebraMap R S ⁻¹' Ideal.span s, rfl⟩, _⟩
    rw [preimage_comap_zero_locus, ← zero_locus_span, ← zero_locus_span s]
    congr 1
    exact congr_arg Submodule.Carrier (IsLocalization.map_comap M S (Ideal.span s))
    
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    simp
    

theorem localization_comap_injective [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Function.Injective (comap (algebraMap R S)) := by
  intro p q h
  replace h := congr_arg (fun x : PrimeSpectrum R => Ideal.map (algebraMap R S) x.asIdeal) h
  dsimp' only  at h
  erw [IsLocalization.map_comap M S, IsLocalization.map_comap M S] at h
  ext1
  exact h

theorem localization_comap_embedding [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Embedding (comap (algebraMap R S)) :=
  ⟨localization_comap_inducing S M, localization_comap_injective S M⟩

theorem localization_comap_range [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    Set.Range (comap (algebraMap R S)) = { p | Disjoint (M : Set R) p.asIdeal } := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩ x ⟨hx₁, hx₂⟩
    exact (p.2.1 : ¬_) (p.as_ideal.eq_top_of_is_unit_mem hx₂ (IsLocalization.map_units S ⟨x, hx₁⟩))
    
  · intro h
    use ⟨x.as_ideal.map (algebraMap R S), IsLocalization.is_prime_of_is_prime_disjoint M S _ x.2 h⟩
    ext1
    exact IsLocalization.comap_map_of_is_prime_disjoint M S _ x.2 h
    

end Comap

section BasicOpen

/-- `basic_open r` is the open subset containing all prime ideals not containing `r`. -/
def basicOpen (r : R) : TopologicalSpace.Opens (PrimeSpectrum R) where
  val := { x | r ∉ x.asIdeal }
  property := ⟨{r}, Set.ext fun x => Set.singleton_subset_iff.trans <| not_not.symm⟩

@[simp]
theorem mem_basic_open (f : R) (x : PrimeSpectrum R) : x ∈ basicOpen f ↔ f ∉ x.asIdeal :=
  Iff.rfl

theorem is_open_basic_open {a : R} : IsOpen (basicOpen a : Set (PrimeSpectrum R)) :=
  (basicOpen a).property

@[simp]
theorem basic_open_eq_zero_locus_compl (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = ZeroLocus {r}ᶜ :=
  Set.ext fun x => by
    simpa only [← Set.mem_compl_eq, ← mem_zero_locus, ← Set.singleton_subset_iff]

@[simp]
theorem basic_open_one : basicOpen (1 : R) = ⊤ :=
  TopologicalSpace.Opens.ext <| by
    simp

@[simp]
theorem basic_open_zero : basicOpen (0 : R) = ⊥ :=
  TopologicalSpace.Opens.ext <| by
    simp

theorem basic_open_le_basic_open_iff (f g : R) : basicOpen f ≤ basicOpen g ↔ f ∈ (Ideal.span ({g} : Set R)).radical :=
  by
  rw [TopologicalSpace.Opens.le_def, basic_open_eq_zero_locus_compl, basic_open_eq_zero_locus_compl, Set.le_eq_subset,
    Set.compl_subset_compl, zero_locus_subset_zero_locus_singleton_iff]

theorem basic_open_mul (f g : R) : basicOpen (f * g) = basicOpen f⊓basicOpen g :=
  TopologicalSpace.Opens.ext <| by
    simp [← zero_locus_singleton_mul]

theorem basic_open_mul_le_left (f g : R) : basicOpen (f * g) ≤ basicOpen f := by
  rw [basic_open_mul f g]
  exact inf_le_left

theorem basic_open_mul_le_right (f g : R) : basicOpen (f * g) ≤ basicOpen g := by
  rw [basic_open_mul f g]
  exact inf_le_right

@[simp]
theorem basic_open_pow (f : R) (n : ℕ) (hn : 0 < n) : basicOpen (f ^ n) = basicOpen f :=
  TopologicalSpace.Opens.ext <| by
    simpa using zero_locus_singleton_pow f n hn

theorem is_topological_basis_basic_opens :
    TopologicalSpace.IsTopologicalBasis (Set.Range fun r : R => (basicOpen r : Set (PrimeSpectrum R))) := by
  apply TopologicalSpace.is_topological_basis_of_open_of_nhds
  · rintro _ ⟨r, rfl⟩
    exact is_open_basic_open
    
  · rintro p U hp ⟨s, hs⟩
    rw [← compl_compl U, Set.mem_compl_eq, ← hs, mem_zero_locus, Set.not_subset] at hp
    obtain ⟨f, hfs, hfp⟩ := hp
    refine' ⟨basic_open f, ⟨f, rfl⟩, hfp, _⟩
    rw [← Set.compl_subset_compl, ← hs, basic_open_eq_zero_locus_compl, compl_compl]
    exact zero_locus_anti_mono (set.singleton_subset_iff.mpr hfs)
    

theorem is_basis_basic_opens : TopologicalSpace.Opens.IsBasis (Set.Range (@basicOpen R _)) := by
  unfold TopologicalSpace.Opens.IsBasis
  convert is_topological_basis_basic_opens
  rw [← Set.range_comp]

theorem is_compact_basic_open (f : R) : IsCompact (basicOpen f : Set (PrimeSpectrum R)) :=
  is_compact_of_finite_subfamily_closed fun ι Z hZc hZ => by
    let I : ι → Ideal R := fun i => vanishing_ideal (Z i)
    have hI : ∀ i, Z i = zero_locus (I i) := fun i => by
      simpa only [← zero_locus_vanishing_ideal_eq_closure] using (hZc i).closure_eq.symm
    rw [basic_open_eq_zero_locus_compl f, Set.inter_comm, ← Set.diff_eq, Set.diff_eq_empty, funext hI, ←
      zero_locus_supr] at hZ
    obtain ⟨n, hn⟩ : f ∈ (⨆ i : ι, I i).radical := by
      rw [← vanishing_ideal_zero_locus_eq_radical]
      apply vanishing_ideal_anti_mono hZ
      exact subset_vanishing_ideal_zero_locus {f} (Set.mem_singleton f)
    rcases Submodule.exists_finset_of_mem_supr I hn with ⟨s, hs⟩
    use s
    -- Using simp_rw here, because `hI` and `zero_locus_supr` need to be applied underneath binders
    simp_rw [basic_open_eq_zero_locus_compl f, Set.inter_comm, ← Set.diff_eq, Set.diff_eq_empty, hI, ← zero_locus_supr]
    rw [← zero_locus_radical]
    -- this one can't be in `simp_rw` because it would loop
    apply zero_locus_anti_mono
    rw [Set.singleton_subset_iff]
    exact ⟨n, hs⟩

@[simp]
theorem basic_open_eq_bot_iff (f : R) : basicOpen f = ⊥ ↔ IsNilpotent f := by
  rw [← subtype.coe_injective.eq_iff, basic_open_eq_zero_locus_compl]
  simp only [← Set.eq_univ_iff_forall, ← TopologicalSpace.Opens.empty_eq, ← Set.singleton_subset_iff, ←
    TopologicalSpace.Opens.coe_bot, ← nilpotent_iff_mem_prime, ← Set.compl_empty_iff, ← mem_zero_locus, ←
    SetLike.mem_coe]
  exact Subtype.forall

theorem localization_away_comap_range (S : Type v) [CommRingₓ S] [Algebra R S] (r : R) [IsLocalization.Away r S] :
    Set.Range (comap (algebraMap R S)) = basicOpen r := by
  rw [localization_comap_range S (Submonoid.powers r)]
  ext
  simp only [← mem_zero_locus, ← basic_open_eq_zero_locus_compl, ← SetLike.mem_coe, ← Set.mem_set_of_eq, ←
    Set.singleton_subset_iff, ← Set.mem_compl_eq]
  constructor
  · intro h₁ h₂
    exact h₁ ⟨Submonoid.mem_powers r, h₂⟩
    
  · rintro h₁ _ ⟨⟨n, rfl⟩, h₃⟩
    exact h₁ (x.2.mem_of_pow_mem _ h₃)
    

theorem localization_away_open_embedding (S : Type v) [CommRingₓ S] [Algebra R S] (r : R) [IsLocalization.Away r S] :
    OpenEmbedding (comap (algebraMap R S)) :=
  { toEmbedding := localization_comap_embedding S (Submonoid.powers r),
    open_range := by
      rw [localization_away_comap_range S r]
      exact is_open_basic_open }

end BasicOpen

/-- The prime spectrum of a commutative ring is a compact topological space. -/
instance :
    CompactSpace (PrimeSpectrum R) where compact_univ := by
    convert is_compact_basic_open (1 : R)
    rw [basic_open_one]
    rfl

section Order

/-!
## The specialization order

We endow `prime_spectrum R` with a partial order,
where `x ≤ y` if and only if `y ∈ closure {x}`.
-/


instance : PartialOrderₓ (PrimeSpectrum R) :=
  Subtype.partialOrder _

@[simp]
theorem as_ideal_le_as_ideal (x y : PrimeSpectrum R) : x.asIdeal ≤ y.asIdeal ↔ x ≤ y :=
  Subtype.coe_le_coe

@[simp]
theorem as_ideal_lt_as_ideal (x y : PrimeSpectrum R) : x.asIdeal < y.asIdeal ↔ x < y :=
  Subtype.coe_lt_coe

theorem le_iff_mem_closure (x y : PrimeSpectrum R) : x ≤ y ↔ y ∈ Closure ({x} : Set (PrimeSpectrum R)) := by
  rw [← as_ideal_le_as_ideal, ← zero_locus_vanishing_ideal_eq_closure, mem_zero_locus, vanishing_ideal_singleton,
    SetLike.coe_subset_coe]

theorem le_iff_specializes (x y : PrimeSpectrum R) : x ≤ y ↔ x ⤳ y :=
  (le_iff_mem_closure x y).trans specializes_iff_mem_closure.symm

/-- `nhds` as an order embedding. -/
@[simps (config := { fullyApplied := true })]
def nhdsOrderEmbedding : PrimeSpectrum R ↪o Filter (PrimeSpectrum R) :=
  (OrderEmbedding.ofMapLeIff nhds) fun a b => (le_iff_specializes a b).symm

instance : T0Space (PrimeSpectrum R) :=
  ⟨nhdsOrderEmbedding.Injective⟩

end Order

/-- If `x` specializes to `y`, then there is a natural map from the localization of `y` to
the localization of `x`. -/
def localizationMapOfSpecializes {x y : PrimeSpectrum R} (h : x ⤳ y) :
    Localization.AtPrime y.asIdeal →+* Localization.AtPrime x.asIdeal :=
  @IsLocalization.lift _ _ _ _ _ _ _ _ Localization.is_localization (algebraMap R (Localization.AtPrime x.asIdeal))
    (by
      rintro ⟨a, ha⟩
      rw [← PrimeSpectrum.le_iff_specializes, ← as_ideal_le_as_ideal, ← SetLike.coe_subset_coe, ←
        Set.compl_subset_compl] at h
      exact (IsLocalization.map_units _ ⟨a, show a ∈ x.as_ideal.prime_compl from h ha⟩ : _))

end PrimeSpectrum

namespace LocalRing

variable (R) [LocalRing R]

/-- The closed point in the prime spectrum of a local ring.
-/
def closedPoint : PrimeSpectrum R :=
  ⟨maximalIdeal R, (maximalIdeal.is_maximal R).IsPrime⟩

variable {R}

theorem is_local_ring_hom_iff_comap_closed_point {S : Type v} [CommRingₓ S] [LocalRing S] (f : R →+* S) :
    IsLocalRingHom f ↔ PrimeSpectrum.comap f (closedPoint S) = closedPoint R := by
  rw [(local_hom_tfae f).out 0 4, Subtype.ext_iff]
  rfl

@[simp]
theorem comap_closed_point {S : Type v} [CommRingₓ S] [LocalRing S] (f : R →+* S) [IsLocalRingHom f] :
    PrimeSpectrum.comap f (closedPoint S) = closedPoint R :=
  (is_local_ring_hom_iff_comap_closed_point f).mp inferInstance

end LocalRing


/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Johan Commelin
-/
import Mathbin.Topology.Category.Top.Default
import Mathbin.RingTheory.GradedAlgebra.HomogeneousIdeal

/-!
# Projective spectrum of a graded ring

The projective spectrum of a graded commutative ring is the subtype of all homogenous ideals that
are prime and do not contain the irrelevant ideal.
It is naturally endowed with a topology: the Zariski topology.

## Notation
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `𝒜 : ℕ → submodule R A` is the grading of `A`;

## Main definitions

* `projective_spectrum 𝒜`: The projective spectrum of a graded ring `A`, or equivalently, the set of
  all homogeneous ideals of `A` that is both prime and relevant i.e. not containing irrelevant
  ideal. Henceforth, we call elements of projective spectrum *relevant homogeneous prime ideals*.
* `projective_spectrum.zero_locus 𝒜 s`: The zero locus of a subset `s` of `A`
  is the subset of `projective_spectrum 𝒜` consisting of all relevant homogeneous prime ideals that
  contain `s`.
* `projective_spectrum.vanishing_ideal t`: The vanishing ideal of a subset `t` of
  `projective_spectrum 𝒜` is the intersection of points in `t` (viewed as relevant homogeneous prime
  ideals).
* `projective_spectrum.Top`: the topological space of `projective_spectrum 𝒜` endowed with the
  Zariski topology

-/


noncomputable section

open DirectSum BigOperators Pointwise

open DirectSum SetLike Top TopologicalSpace CategoryTheory Opposite

variable {R A : Type _}

variable [CommSemiringₓ R] [CommRingₓ A] [Algebra R A]

variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The projective spectrum of a graded commutative ring is the subtype of all homogenous ideals that
are prime and do not contain the irrelevant ideal.
-/
@[nolint has_inhabited_instance]
def ProjectiveSpectrum :=
  { I : HomogeneousIdeal 𝒜 // I.toIdeal.IsPrime ∧ ¬HomogeneousIdeal.irrelevant 𝒜 ≤ I }

namespace ProjectiveSpectrum

variable {𝒜}

/-- A method to view a point in the projective spectrum of a graded ring
as a homogeneous ideal of that ring. -/
abbrev asHomogeneousIdeal (x : ProjectiveSpectrum 𝒜) : HomogeneousIdeal 𝒜 :=
  x.1

theorem as_homogeneous_ideal_def (x : ProjectiveSpectrum 𝒜) : x.asHomogeneousIdeal = x.1 :=
  rfl

instance is_prime (x : ProjectiveSpectrum 𝒜) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.2.1

@[ext]
theorem ext {x y : ProjectiveSpectrum 𝒜} : x = y ↔ x.asHomogeneousIdeal = y.asHomogeneousIdeal :=
  Subtype.ext_iff_val

variable (𝒜)

/-- The zero locus of a set `s` of elements of a commutative ring `A`
is the set of all relevant homogeneous prime ideals of the ring that contain the set `s`.

An element `f` of `A` can be thought of as a dependent function on the projective spectrum of `𝒜`.
At a point `x` (a homogeneous prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `A` modulo the prime ideal `x`.
In this manner, `zero_locus s` is exactly the subset of `projective_spectrum 𝒜`
where all "functions" in `s` vanish simultaneously. -/
def ZeroLocus (s : Set A) : Set (ProjectiveSpectrum 𝒜) :=
  { x | s ⊆ x.asHomogeneousIdeal }

@[simp]
theorem mem_zero_locus (x : ProjectiveSpectrum 𝒜) (s : Set A) : x ∈ ZeroLocus 𝒜 s ↔ s ⊆ x.asHomogeneousIdeal :=
  Iff.rfl

@[simp]
theorem zero_locus_span (s : Set A) : ZeroLocus 𝒜 (Ideal.span s) = ZeroLocus 𝒜 s := by
  ext x
  exact (Submodule.gi _ _).gc s x.as_homogeneous_ideal.to_ideal

variable {𝒜}

/-- The vanishing ideal of a set `t` of points
of the prime spectrum of a commutative ring `R`
is the intersection of all the prime ideals in the set `t`.

An element `f` of `A` can be thought of as a dependent function on the projective spectrum of `𝒜`.
At a point `x` (a homogeneous prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `A` modulo the prime ideal `x`.
In this manner, `vanishing_ideal t` is exactly the ideal of `A`
consisting of all "functions" that vanish on all of `t`. -/
def vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) : HomogeneousIdeal 𝒜 :=
  ⨅ (x : ProjectiveSpectrum 𝒜) (h : x ∈ t), x.asHomogeneousIdeal

theorem coe_vanishing_ideal (t : Set (ProjectiveSpectrum 𝒜)) :
    (vanishingIdeal t : Set A) = { f | ∀ x : ProjectiveSpectrum 𝒜, x ∈ t → f ∈ x.asHomogeneousIdeal } := by
  ext f
  rw [vanishing_ideal, SetLike.mem_coe, ← HomogeneousIdeal.mem_iff, HomogeneousIdeal.to_ideal_infi, Submodule.mem_infi]
  apply forall_congrₓ fun x => _
  rw [HomogeneousIdeal.to_ideal_infi, Submodule.mem_infi, HomogeneousIdeal.mem_iff]

theorem mem_vanishing_ideal (t : Set (ProjectiveSpectrum 𝒜)) (f : A) :
    f ∈ vanishingIdeal t ↔ ∀ x : ProjectiveSpectrum 𝒜, x ∈ t → f ∈ x.asHomogeneousIdeal := by
  rw [← SetLike.mem_coe, coe_vanishing_ideal, Set.mem_set_of_eq]

@[simp]
theorem vanishing_ideal_singleton (x : ProjectiveSpectrum 𝒜) :
    vanishingIdeal ({x} : Set (ProjectiveSpectrum 𝒜)) = x.asHomogeneousIdeal := by
  simp [← vanishing_ideal]

theorem subset_zero_locus_iff_le_vanishing_ideal (t : Set (ProjectiveSpectrum 𝒜)) (I : Ideal A) :
    t ⊆ ZeroLocus 𝒜 I ↔ I ≤ (vanishingIdeal t).toIdeal :=
  ⟨fun h f k => (mem_vanishing_ideal _ _).mpr fun x j => (mem_zero_locus _ _ _).mpr (h j) k, fun h => fun x j =>
    (mem_zero_locus _ _ _).mpr (le_transₓ h fun f h => ((mem_vanishing_ideal _ _).mp h) x j)⟩

variable (𝒜)

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
theorem gc_ideal :
    @GaloisConnection (Ideal A) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => ZeroLocus 𝒜 I) fun t =>
      (vanishingIdeal t).toIdeal :=
  fun I t => subset_zero_locus_iff_le_vanishing_ideal t I

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
theorem gc_set :
    @GaloisConnection (Set A) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun s => ZeroLocus 𝒜 s) fun t => vanishingIdeal t :=
  by
  have ideal_gc : GaloisConnection Ideal.span coe := (Submodule.gi A _).gc
  simpa [← zero_locus_span, ← Function.comp] using GaloisConnection.compose ideal_gc (gc_ideal 𝒜)

theorem gc_homogeneous_ideal :
    @GaloisConnection (HomogeneousIdeal 𝒜) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _ (fun I => ZeroLocus 𝒜 I) fun t =>
      vanishingIdeal t :=
  fun I t => by
  simpa [← show I.to_ideal ≤ (vanishing_ideal t).toIdeal ↔ I ≤ vanishing_ideal t from Iff.rfl] using
    subset_zero_locus_iff_le_vanishing_ideal t I.to_ideal

theorem subset_zero_locus_iff_subset_vanishing_ideal (t : Set (ProjectiveSpectrum 𝒜)) (s : Set A) :
    t ⊆ ZeroLocus 𝒜 s ↔ s ⊆ vanishingIdeal t :=
  (gc_set _) s t

theorem subset_vanishing_ideal_zero_locus (s : Set A) : s ⊆ vanishingIdeal (ZeroLocus 𝒜 s) :=
  (gc_set _).le_u_l s

theorem ideal_le_vanishing_ideal_zero_locus (I : Ideal A) : I ≤ (vanishingIdeal (ZeroLocus 𝒜 I)).toIdeal :=
  (gc_ideal _).le_u_l I

theorem homogeneous_ideal_le_vanishing_ideal_zero_locus (I : HomogeneousIdeal 𝒜) : I ≤ vanishingIdeal (ZeroLocus 𝒜 I) :=
  (gc_homogeneous_ideal _).le_u_l I

theorem subset_zero_locus_vanishing_ideal (t : Set (ProjectiveSpectrum 𝒜)) : t ⊆ ZeroLocus 𝒜 (vanishingIdeal t) :=
  (gc_ideal _).l_u_le t

theorem zero_locus_anti_mono {s t : Set A} (h : s ⊆ t) : ZeroLocus 𝒜 t ⊆ ZeroLocus 𝒜 s :=
  (gc_set _).monotone_l h

theorem zero_locus_anti_mono_ideal {s t : Ideal A} (h : s ≤ t) : ZeroLocus 𝒜 (t : Set A) ⊆ ZeroLocus 𝒜 (s : Set A) :=
  (gc_ideal _).monotone_l h

theorem zero_locus_anti_mono_homogeneous_ideal {s t : HomogeneousIdeal 𝒜} (h : s ≤ t) :
    ZeroLocus 𝒜 (t : Set A) ⊆ ZeroLocus 𝒜 (s : Set A) :=
  (gc_homogeneous_ideal _).monotone_l h

theorem vanishing_ideal_anti_mono {s t : Set (ProjectiveSpectrum 𝒜)} (h : s ⊆ t) :
    vanishingIdeal t ≤ vanishingIdeal s :=
  (gc_ideal _).monotone_u h

theorem zero_locus_bot : ZeroLocus 𝒜 ((⊥ : Ideal A) : Set A) = Set.Univ :=
  (gc_ideal 𝒜).l_bot

@[simp]
theorem zero_locus_singleton_zero : ZeroLocus 𝒜 ({0} : Set A) = Set.Univ :=
  zero_locus_bot _

@[simp]
theorem zero_locus_empty : ZeroLocus 𝒜 (∅ : Set A) = Set.Univ :=
  (gc_set 𝒜).l_bot

@[simp]
theorem vanishing_ideal_univ : vanishingIdeal (∅ : Set (ProjectiveSpectrum 𝒜)) = ⊤ := by
  simpa using (gc_ideal _).u_top

theorem zero_locus_empty_of_one_mem {s : Set A} (h : (1 : A) ∈ s) : ZeroLocus 𝒜 s = ∅ :=
  Set.eq_empty_iff_forall_not_mem.mpr fun x hx =>
    (inferInstance : x.asHomogeneousIdeal.toIdeal.IsPrime).ne_top <|
      x.asHomogeneousIdeal.toIdeal.eq_top_iff_one.mpr <| hx h

@[simp]
theorem zero_locus_singleton_one : ZeroLocus 𝒜 ({1} : Set A) = ∅ :=
  zero_locus_empty_of_one_mem 𝒜 (Set.mem_singleton (1 : A))

@[simp]
theorem zero_locus_univ : ZeroLocus 𝒜 (Set.Univ : Set A) = ∅ :=
  zero_locus_empty_of_one_mem _ (Set.mem_univ 1)

theorem zero_locus_sup_ideal (I J : Ideal A) : ZeroLocus 𝒜 ((I⊔J : Ideal A) : Set A) = ZeroLocus _ I ∩ ZeroLocus _ J :=
  (gc_ideal 𝒜).l_sup

theorem zero_locus_sup_homogeneous_ideal (I J : HomogeneousIdeal 𝒜) :
    ZeroLocus 𝒜 ((I⊔J : HomogeneousIdeal 𝒜) : Set A) = ZeroLocus _ I ∩ ZeroLocus _ J :=
  (gc_homogeneous_ideal 𝒜).l_sup

theorem zero_locus_union (s s' : Set A) : ZeroLocus 𝒜 (s ∪ s') = ZeroLocus _ s ∩ ZeroLocus _ s' :=
  (gc_set 𝒜).l_sup

theorem vanishing_ideal_union (t t' : Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal (t ∪ t') = vanishingIdeal t⊓vanishingIdeal t' := by
  ext1 <;> convert (gc_ideal 𝒜).u_inf

theorem zero_locus_supr_ideal {γ : Sort _} (I : γ → Ideal A) :
    ZeroLocus _ ((⨆ i, I i : Ideal A) : Set A) = ⋂ i, ZeroLocus 𝒜 (I i) :=
  (gc_ideal 𝒜).l_supr

theorem zero_locus_supr_homogeneous_ideal {γ : Sort _} (I : γ → HomogeneousIdeal 𝒜) :
    ZeroLocus _ ((⨆ i, I i : HomogeneousIdeal 𝒜) : Set A) = ⋂ i, ZeroLocus 𝒜 (I i) :=
  (gc_homogeneous_ideal 𝒜).l_supr

theorem zero_locus_Union {γ : Sort _} (s : γ → Set A) : ZeroLocus 𝒜 (⋃ i, s i) = ⋂ i, ZeroLocus 𝒜 (s i) :=
  (gc_set 𝒜).l_supr

theorem zero_locus_bUnion (s : Set (Set A)) : ZeroLocus 𝒜 (⋃ s' ∈ s, s' : Set A) = ⋂ s' ∈ s, ZeroLocus 𝒜 s' := by
  simp only [← zero_locus_Union]

theorem vanishing_ideal_Union {γ : Sort _} (t : γ → Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal (⋃ i, t i) = ⨅ i, vanishingIdeal (t i) :=
  HomogeneousIdeal.to_ideal_injective <| by
    convert (gc_ideal 𝒜).u_infi <;> exact HomogeneousIdeal.to_ideal_infi _

theorem zero_locus_inf (I J : Ideal A) : ZeroLocus 𝒜 ((I⊓J : Ideal A) : Set A) = ZeroLocus 𝒜 I ∪ ZeroLocus 𝒜 J :=
  Set.ext fun x => by
    simpa using x.2.1.inf_le

theorem union_zero_locus (s s' : Set A) :
    ZeroLocus 𝒜 s ∪ ZeroLocus 𝒜 s' = ZeroLocus 𝒜 (Ideal.span s⊓Ideal.span s' : Ideal A) := by
  rw [zero_locus_inf]
  simp

theorem zero_locus_mul_ideal (I J : Ideal A) :
    ZeroLocus 𝒜 ((I * J : Ideal A) : Set A) = ZeroLocus 𝒜 I ∪ ZeroLocus 𝒜 J :=
  Set.ext fun x => by
    simpa using x.2.1.mul_le

theorem zero_locus_mul_homogeneous_ideal (I J : HomogeneousIdeal 𝒜) :
    ZeroLocus 𝒜 ((I * J : HomogeneousIdeal 𝒜) : Set A) = ZeroLocus 𝒜 I ∪ ZeroLocus 𝒜 J :=
  Set.ext fun x => by
    simpa using x.2.1.mul_le

theorem zero_locus_singleton_mul (f g : A) : ZeroLocus 𝒜 ({f * g} : Set A) = ZeroLocus 𝒜 {f} ∪ ZeroLocus 𝒜 {g} :=
  Set.ext fun x => by
    simpa using x.2.1.mul_mem_iff_mem_or_mem

@[simp]
theorem zero_locus_singleton_pow (f : A) (n : ℕ) (hn : 0 < n) : ZeroLocus 𝒜 ({f ^ n} : Set A) = ZeroLocus 𝒜 {f} :=
  Set.ext fun x => by
    simpa using x.2.1.pow_mem_iff_mem n hn

theorem sup_vanishing_ideal_le (t t' : Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal t⊔vanishingIdeal t' ≤ vanishingIdeal (t ∩ t') := by
  intro r
  rw [← HomogeneousIdeal.mem_iff, HomogeneousIdeal.to_ideal_sup, mem_vanishing_ideal, Submodule.mem_sup]
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  erw [mem_vanishing_ideal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim

theorem mem_compl_zero_locus_iff_not_mem {f : A} {I : ProjectiveSpectrum 𝒜} :
    I ∈ (ZeroLocus 𝒜 {f} : Set (ProjectiveSpectrum 𝒜))ᶜ ↔ f ∉ I.asHomogeneousIdeal := by
  rw [Set.mem_compl_eq, mem_zero_locus, Set.singleton_subset_iff] <;> rfl

/-- The Zariski topology on the prime spectrum of a commutative ring
is defined via the closed sets of the topology:
they are exactly those sets that are the zero locus of a subset of the ring. -/
instance zariskiTopology : TopologicalSpace (ProjectiveSpectrum 𝒜) :=
  TopologicalSpace.ofClosed (Set.Range (ProjectiveSpectrum.ZeroLocus 𝒜))
    ⟨Set.Univ, by
      simp ⟩
    (by
      intro Zs h
      rw [Set.sInter_eq_Inter]
      let f : Zs → Set _ := fun i => Classical.some (h i.2)
      have hf : ∀ i : Zs, ↑i = zero_locus 𝒜 (f i) := fun i => (Classical.some_spec (h i.2)).symm
      simp only [← hf]
      exact ⟨_, zero_locus_Union 𝒜 _⟩)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact ⟨_, (union_zero_locus 𝒜 s t).symm⟩)

/-- The underlying topology of `Proj` is the projective spectrum of graded ring `A`.
-/
def top : Top :=
  Top.of (ProjectiveSpectrum 𝒜)

theorem is_open_iff (U : Set (ProjectiveSpectrum 𝒜)) : IsOpen U ↔ ∃ s, Uᶜ = ZeroLocus 𝒜 s := by
  simp only [← @eq_comm _ (Uᶜ)] <;> rfl

theorem is_closed_iff_zero_locus (Z : Set (ProjectiveSpectrum 𝒜)) : IsClosed Z ↔ ∃ s, Z = ZeroLocus 𝒜 s := by
  rw [← is_open_compl_iff, is_open_iff, compl_compl]

theorem is_closed_zero_locus (s : Set A) : IsClosed (ZeroLocus 𝒜 s) := by
  rw [is_closed_iff_zero_locus]
  exact ⟨s, rfl⟩

theorem zero_locus_vanishing_ideal_eq_closure (t : Set (ProjectiveSpectrum 𝒜)) :
    ZeroLocus 𝒜 (vanishingIdeal t : Set A) = Closure t := by
  apply Set.Subset.antisymm
  · rintro x hx t' ⟨ht', ht⟩
    obtain ⟨fs, rfl⟩ : ∃ s, t' = zero_locus 𝒜 s := by
      rwa [is_closed_iff_zero_locus] at ht'
    rw [subset_zero_locus_iff_subset_vanishing_ideal] at ht
    exact Set.Subset.trans ht hx
    
  · rw [(is_closed_zero_locus _ _).closure_subset_iff]
    exact subset_zero_locus_vanishing_ideal 𝒜 t
    

theorem vanishing_ideal_closure (t : Set (ProjectiveSpectrum 𝒜)) : vanishingIdeal (Closure t) = vanishingIdeal t := by
  have := (gc_ideal 𝒜).u_l_u_eq_u t
  dsimp' only  at this
  ext1
  erw [zero_locus_vanishing_ideal_eq_closure 𝒜 t] at this
  exact this

section BasicOpen

/-- `basic_open r` is the open subset containing all prime ideals not containing `r`. -/
def basicOpen (r : A) : TopologicalSpace.Opens (ProjectiveSpectrum 𝒜) where
  val := { x | r ∉ x.asHomogeneousIdeal }
  property := ⟨{r}, Set.ext fun x => Set.singleton_subset_iff.trans <| not_not.symm⟩

@[simp]
theorem mem_basic_open (f : A) (x : ProjectiveSpectrum 𝒜) : x ∈ basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal :=
  Iff.rfl

theorem mem_coe_basic_open (f : A) (x : ProjectiveSpectrum 𝒜) :
    x ∈ (↑(basicOpen 𝒜 f) : Set (ProjectiveSpectrum 𝒜)) ↔ f ∉ x.asHomogeneousIdeal :=
  Iff.rfl

theorem is_open_basic_open {a : A} : IsOpen (basicOpen 𝒜 a : Set (ProjectiveSpectrum 𝒜)) :=
  (basicOpen 𝒜 a).property

@[simp]
theorem basic_open_eq_zero_locus_compl (r : A) : (basicOpen 𝒜 r : Set (ProjectiveSpectrum 𝒜)) = ZeroLocus 𝒜 {r}ᶜ :=
  Set.ext fun x => by
    simpa only [← Set.mem_compl_eq, ← mem_zero_locus, ← Set.singleton_subset_iff]

@[simp]
theorem basic_open_one : basicOpen 𝒜 (1 : A) = ⊤ :=
  TopologicalSpace.Opens.ext <| by
    simp

@[simp]
theorem basic_open_zero : basicOpen 𝒜 (0 : A) = ⊥ :=
  TopologicalSpace.Opens.ext <| by
    simp

theorem basic_open_mul (f g : A) : basicOpen 𝒜 (f * g) = basicOpen 𝒜 f⊓basicOpen 𝒜 g :=
  TopologicalSpace.Opens.ext <| by
    simp [← zero_locus_singleton_mul]

theorem basic_open_mul_le_left (f g : A) : basicOpen 𝒜 (f * g) ≤ basicOpen 𝒜 f := by
  rw [basic_open_mul 𝒜 f g]
  exact inf_le_left

theorem basic_open_mul_le_right (f g : A) : basicOpen 𝒜 (f * g) ≤ basicOpen 𝒜 g := by
  rw [basic_open_mul 𝒜 f g]
  exact inf_le_right

@[simp]
theorem basic_open_pow (f : A) (n : ℕ) (hn : 0 < n) : basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f :=
  TopologicalSpace.Opens.ext <| by
    simpa using zero_locus_singleton_pow 𝒜 f n hn

theorem basic_open_eq_union_of_projection (f : A) : basicOpen 𝒜 f = ⨆ i : ℕ, basicOpen 𝒜 (GradedAlgebra.proj 𝒜 i f) :=
  TopologicalSpace.Opens.ext <|
    Set.ext fun z => by
      erw [mem_coe_basic_open, TopologicalSpace.Opens.mem_Sup]
      constructor <;> intro hz
      · rcases show ∃ i, GradedAlgebra.proj 𝒜 i f ∉ z.as_homogeneous_ideal by
            contrapose! hz with H
            classical
            rw [← DirectSum.sum_support_decompose 𝒜 f]
            apply Ideal.sum_mem _ fun i hi => H i with
          ⟨i, hi⟩
        exact
          ⟨basic_open 𝒜 (GradedAlgebra.proj 𝒜 i f), ⟨i, rfl⟩, by
            rwa [mem_basic_open]⟩
        
      · obtain ⟨_, ⟨i, rfl⟩, hz⟩ := hz
        exact fun rid => hz (z.1.2 i rid)
        

theorem is_topological_basis_basic_opens :
    TopologicalSpace.IsTopologicalBasis (Set.Range fun r : A => (basicOpen 𝒜 r : Set (ProjectiveSpectrum 𝒜))) := by
  apply TopologicalSpace.is_topological_basis_of_open_of_nhds
  · rintro _ ⟨r, rfl⟩
    exact is_open_basic_open 𝒜
    
  · rintro p U hp ⟨s, hs⟩
    rw [← compl_compl U, Set.mem_compl_eq, ← hs, mem_zero_locus, Set.not_subset] at hp
    obtain ⟨f, hfs, hfp⟩ := hp
    refine' ⟨basic_open 𝒜 f, ⟨f, rfl⟩, hfp, _⟩
    rw [← Set.compl_subset_compl, ← hs, basic_open_eq_zero_locus_compl, compl_compl]
    exact zero_locus_anti_mono 𝒜 (set.singleton_subset_iff.mpr hfs)
    

end BasicOpen

section Order

/-!
## The specialization order

We endow `projective_spectrum 𝒜` with a partial order,
where `x ≤ y` if and only if `y ∈ closure {x}`.
-/


instance : PartialOrderₓ (ProjectiveSpectrum 𝒜) :=
  Subtype.partialOrder _

@[simp]
theorem as_ideal_le_as_ideal (x y : ProjectiveSpectrum 𝒜) : x.asHomogeneousIdeal ≤ y.asHomogeneousIdeal ↔ x ≤ y :=
  Subtype.coe_le_coe

@[simp]
theorem as_ideal_lt_as_ideal (x y : ProjectiveSpectrum 𝒜) : x.asHomogeneousIdeal < y.asHomogeneousIdeal ↔ x < y :=
  Subtype.coe_lt_coe

theorem le_iff_mem_closure (x y : ProjectiveSpectrum 𝒜) : x ≤ y ↔ y ∈ Closure ({x} : Set (ProjectiveSpectrum 𝒜)) := by
  rw [← as_ideal_le_as_ideal, ← zero_locus_vanishing_ideal_eq_closure, mem_zero_locus, vanishing_ideal_singleton]
  simp only [← coe_subset_coe, ← Subtype.coe_le_coe, ← coe_coe]

end Order

end ProjectiveSpectrum


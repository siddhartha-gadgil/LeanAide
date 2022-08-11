/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.ModelTheory.FinitelyGenerated
import Mathbin.ModelTheory.DirectLimit
import Mathbin.ModelTheory.Bundled

/-!
# Fraïssé Classes and Fraïssé Limits

This file pertains to the ages of countable first-order structures. The age of a structure is the
class of all finitely-generated structures that embed into it.

Of particular interest are Fraïssé classes, which are exactly the ages of countable
ultrahomogeneous structures. To each is associated a unique (up to nonunique isomorphism)
Fraïssé limit - the countable ultrahomogeneous structure with that age.

## Main Definitions
* `first_order.language.age` is the class of finitely-generated structures that embed into a
particular structure.
* A class `K` has the `first_order.language.hereditary` when all finitely-generated
structures that embed into structures in `K` are also in `K`.
* A class `K` has the `first_order.language.joint_embedding` when for every `M`, `N` in
`K`, there is another structure in `K` into which both `M` and `N` embed.
* A class `K` has the `first_order.language.amalgamation` when for any pair of embeddings
of a structure `M` in `K` into other structures in `K`, those two structures can be embedded into a
fourth structure in `K` such that the resulting square of embeddings commutes.
* `first_order.language.is_fraisse` indicates that a class is nonempty, isomorphism-invariant,
essentially countable, and satisfies the hereditary, joint embedding, and amalgamation properties.
* `first_order.language.is_fraisse_limit` indicates that a structure is a Fraïssé limit for a given
class.

## Main Results
* We show that the age of any structure is isomorphism-invariant and satisfies the hereditary and
joint-embedding properties.
* `first_order.language.age.countable_quotient` shows that the age of any countable structure is
essentially countable.
* `first_order.language.exists_countable_is_age_of_iff` gives necessary and sufficient conditions
for a class to be the age of a countable structure in a language with countably many functions.

## Implementation Notes
* Classes of structures are formalized with `set (bundled L.Structure)`.
* Some results pertain to countable limit structures, others to countably-generated limit
structures. In the case of a language with countably many function symbols, these are equivalent.

## References
- [W. Hodges, *A Shorter Model Theory*][Hodges97]
- [K. Tent, M. Ziegler, *A Course in Model Theory*][Tent_Ziegler]

## TODO
* Show existence and uniqueness of Fraïssé limits

-/


universe u v w w'

open FirstOrder

open Set CategoryTheory

namespace FirstOrder

namespace Language

open Structure Substructure

variable (L : Language.{u, v})

/-! ### The Age of a Structure and Fraïssé Classes-/


/-- The age of a structure `M` is the class of finitely-generated structures that embed into it. -/
def Age (M : Type w) [L.Structure M] : Set (Bundled.{w} L.Structure) :=
  { N | Structure.Fg L N ∧ Nonempty (N ↪[L] M) }

variable {L} (K : Set (Bundled.{w} L.Structure))

/-- A class `K` has the hereditary property when all finitely-generated structures that embed into
  structures in `K` are also in `K`.  -/
def Hereditary : Prop :=
  ∀ M : Bundled.{w} L.Structure, M ∈ K → L.Age M ⊆ K

/-- A class `K` has the joint embedding property when for every `M`, `N` in `K`, there is another
  structure in `K` into which both `M` and `N` embed. -/
def JointEmbedding : Prop :=
  DirectedOn (fun M N : Bundled.{w} L.Structure => Nonempty (M ↪[L] N)) K

/-- A class `K` has the amalgamation property when for any pair of embeddings of a structure `M` in
  `K` into other structures in `K`, those two structures can be embedded into a fourth structure in
  `K` such that the resulting square of embeddings commutes. -/
def Amalgamation : Prop :=
  ∀ (M N P : Bundled.{w} L.Structure) (MN : M ↪[L] N) (MP : M ↪[L] P),
    M ∈ K →
      N ∈ K → P ∈ K → ∃ (Q : Bundled.{w} L.Structure)(NQ : N ↪[L] Q)(PQ : P ↪[L] Q), Q ∈ K ∧ NQ.comp MN = PQ.comp MP

/-- A Fraïssé class is a nonempty, isomorphism-invariant, essentially countable class of structures
satisfying the hereditary, joint embedding, and amalgamation properties. -/
class IsFraisse : Prop where
  is_nonempty : K.Nonempty
  Fg : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.Fg L M
  is_equiv_invariant : ∀ M N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K)
  is_essentially_countable : (Quotientₓ.mk '' K).Countable
  Hereditary : Hereditary K
  JointEmbedding : JointEmbedding K
  Amalgamation : Amalgamation K

variable {K} (L) (M : Type w) [L.Structure M]

theorem Age.is_equiv_invariant (N P : Bundled.{w} L.Structure) (h : Nonempty (N ≃[L] P)) : N ∈ L.Age M ↔ P ∈ L.Age M :=
  and_congr h.some.fg_iff
    ⟨Nonempty.map fun x => Embedding.comp x h.some.symm.toEmbedding,
      Nonempty.map fun x => Embedding.comp x h.some.toEmbedding⟩

variable {L} {M} {N : Type w} [L.Structure N]

theorem Embedding.age_subset_age (MN : M ↪[L] N) : L.Age M ⊆ L.Age N := fun _ => And.imp_right (Nonempty.map MN.comp)

theorem Equiv.age_eq_age (MN : M ≃[L] N) : L.Age M = L.Age N :=
  le_antisymmₓ MN.toEmbedding.age_subset_age MN.symm.toEmbedding.age_subset_age

theorem Structure.Fg.mem_age_of_equiv {M N : Bundled L.Structure} (h : Structure.Fg L M) (MN : Nonempty (M ≃[L] N)) :
    N ∈ L.Age M :=
  ⟨MN.some.fg_iff.1 h, ⟨MN.some.symm.toEmbedding⟩⟩

theorem Hereditary.is_equiv_invariant_of_fg (h : Hereditary K)
    (fg : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.Fg L M) (M N : Bundled.{w} L.Structure)
    (hn : Nonempty (M ≃[L] N)) : M ∈ K ↔ N ∈ K :=
  ⟨fun MK => h M MK ((fg M MK).mem_age_of_equiv hn), fun NK => h N NK ((fg N NK).mem_age_of_equiv ⟨hn.some.symm⟩)⟩

variable (M)

theorem Age.nonempty : (L.Age M).Nonempty :=
  ⟨Bundled.of (Substructure.closure L (∅ : Set M)), (fg_iff_Structure_fg _).1 (fg_closure Set.finite_empty),
    ⟨Substructure.subtype _⟩⟩

theorem Age.hereditary : Hereditary (L.Age M) := fun N hN P hP => hN.2.some.age_subset_age hP

theorem Age.joint_embedding : JointEmbedding (L.Age M) := fun N hN P hP =>
  ⟨Bundled.of ↥(hN.2.some.toHom.range⊔hP.2.some.toHom.range),
    ⟨(fg_iff_Structure_fg _).1 ((hN.1.range hN.2.some.toHom).sup (hP.1.range hP.2.some.toHom)), ⟨Subtype _⟩⟩,
    ⟨Embedding.comp (inclusion le_sup_left) hN.2.some.equivRange.toEmbedding⟩,
    ⟨Embedding.comp (inclusion le_sup_right) hP.2.some.equivRange.toEmbedding⟩⟩

/-- The age of a countable structure is essentially countable (has countably many isomorphism
classes). -/
theorem Age.countable_quotient (h : (Univ : Set M).Countable) : (Quotientₓ.mk '' L.Age M).Countable := by
  refine'
    Eq.mp (congr rfl (Set.ext _)) ((countable_set_of_finite_subset h).Image fun s => ⟦⟨closure L s, inferInstance⟩⟧)
  rw [forall_quotient_iff]
  intro N
  simp only [← subset_univ, ← and_trueₓ, ← mem_image, ← mem_set_of_eq, ← Quotientₓ.eq]
  constructor
  · rintro ⟨s, hs1, hs2⟩
    use bundled.of ↥(closure L s)
    exact ⟨⟨(fg_iff_Structure_fg _).1 (fg_closure hs1), ⟨Subtype _⟩⟩, hs2⟩
    
  · rintro ⟨P, ⟨⟨s, hs⟩, ⟨PM⟩⟩, hP2⟩
    refine' ⟨PM '' s, Set.Finite.image PM s.finite_to_set, Setoidₓ.trans _ hP2⟩
    rw [← embedding.coe_to_hom, closure_image PM.to_hom, hs, ← hom.range_eq_map]
    exact ⟨PM.equiv_range.symm⟩
    

/-- The age of a direct limit of structures is the union of the ages of the structures. -/
@[simp]
theorem age_direct_limit {ι : Type w} [Preorderₓ ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (G : ι → Type max w w')
    [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j) [DirectedSystem G fun i j h => f i j h] :
    L.Age (DirectLimit G f) = ⋃ i : ι, L.Age (G i) := by
  classical
  ext M
  simp only [← mem_Union]
  constructor
  · rintro ⟨Mfg, ⟨e⟩⟩
    obtain ⟨s, hs⟩ := Mfg.range e.to_hom
    let out := @Quotientₓ.out _ (direct_limit.setoid G f)
    obtain ⟨i, hi⟩ := Finset.exists_le (s.image (Sigma.fst ∘ out))
    have e' := (direct_limit.of L ι G f i).equivRange.symm.toEmbedding
    refine' ⟨i, Mfg, ⟨e'.comp ((substructure.inclusion _).comp e.equiv_range.to_embedding)⟩⟩
    rw [← hs, closure_le]
    intro x hx
    refine' ⟨f (out x).1 i (hi (out x).1 (Finset.mem_image_of_mem _ hx)) (out x).2, _⟩
    rw [embedding.coe_to_hom, direct_limit.of_apply, Quotientₓ.mk_eq_iff_out,
      direct_limit.equiv_iff G f _ (hi (out x).1 (Finset.mem_image_of_mem _ hx)), DirectedSystem.map_self]
    rfl
    
  · rintro ⟨i, Mfg, ⟨e⟩⟩
    exact ⟨Mfg, ⟨embedding.comp (direct_limit.of L ι G f i) e⟩⟩
    

/-- Sufficient conditions for a class to be the age of a countably-generated structure. -/
theorem exists_cg_is_age_of (hn : K.Nonempty)
    (h : ∀ M N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K)) (hc : (Quotientₓ.mk '' K).Countable)
    (fg : ∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.Fg L M) (hp : Hereditary K) (jep : JointEmbedding K) :
    ∃ M : Bundled.{w} L.Structure, Structure.Cg L M ∧ L.Age M = K := by
  obtain ⟨F, hF⟩ := hc.exists_surjective (hn.image _)
  simp only [← Set.ext_iff, ← forall_quotient_iff, ← mem_image, ← mem_range, ← Quotientₓ.eq] at hF
  simp_rw [Quotientₓ.eq_mk_iff_out] at hF
  have hF' : ∀ n : ℕ, (F n).out ∈ K := by
    intro n
    obtain ⟨P, hP1, hP2⟩ := (hF (F n).out).2 ⟨n, Setoidₓ.refl _⟩
    exact (h _ _ hP2).1 hP1
  choose P hPK hP hFP using fun (N : K) (n : ℕ) => jep N N.2 (F (n + 1)).out (hF' _)
  let G : ℕ → K := @Nat.rec (fun _ => K) ⟨(F 0).out, hF' 0⟩ fun n N => ⟨P N n, hPK N n⟩
  let f : ∀ i j, i ≤ j → G i ↪[L] G j := directed_system.nat_le_rec fun n => (hP _ n).some
  refine'
    ⟨bundled.of (direct_limit (fun n => G n) f), direct_limit.cg _ fun n => (fg _ (G n).2).Cg,
      (age_direct_limit _ _).trans (subset_antisymm (Union_subset fun n N hN => hp (G n) (G n).2 hN) fun N KN => _)⟩
  obtain ⟨n, ⟨e⟩⟩ := (hF N).1 ⟨N, KN, Setoidₓ.refl _⟩
  refine' mem_Union_of_mem n ⟨fg _ KN, ⟨embedding.comp _ e.symm.to_embedding⟩⟩
  cases n
  · exact embedding.refl _ _
    
  · exact (hFP _ n).some
    

theorem exists_countable_is_age_of_iff [L.CountableFunctions] :
    (∃ M : Bundled.{w} L.Structure, (Univ : Set M).Countable ∧ L.Age M = K) ↔
      K.Nonempty ∧
        (∀ M N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K)) ∧
          (Quotientₓ.mk '' K).Countable ∧
            (∀ M : Bundled.{w} L.Structure, M ∈ K → Structure.Fg L M) ∧ Hereditary K ∧ JointEmbedding K :=
  by
  constructor
  · rintro ⟨M, h1, h2, rfl⟩
    skip
    refine'
      ⟨age.nonempty M, age.is_equiv_invariant L M, age.countable_quotient M h1, fun N hN => hN.1, age.hereditary M,
        age.joint_embedding M⟩
    
  · rintro ⟨Kn, eqinv, cq, hfg, hp, jep⟩
    obtain ⟨M, hM, rfl⟩ := exists_cg_is_age_of Kn eqinv cq hfg hp jep
    have := (Structure.cg_iff_countable.1 hM).some
    refine' ⟨M, countable_encodable _, rfl⟩
    

variable {K} (L) (M)

/-- A structure `M` is ultrahomogeneous if every embedding of a finitely generated substructure
into `M` extends to an automorphism of `M`. -/
def IsUltrahomogeneous : Prop :=
  ∀ (S : L.Substructure M) (hs : S.Fg) (f : S ↪[L] M), ∃ g : M ≃[L] M, f = g.toEmbedding.comp S.Subtype

variable {L} (K)

/-- A structure `M` is a Fraïssé limit for a class `K` if it is countably generated,
ultrahomogeneous, and has age `K`. -/
structure IsFraisseLimit [CountableFunctions L] : Prop where
  ultrahomogeneous : IsUltrahomogeneous L M
  Countable : (Univ : Set M).Countable
  Age : L.Age M = K

variable {L} {M}

theorem IsUltrahomogeneous.amalgamation_age (h : L.IsUltrahomogeneous M) : Amalgamation (L.Age M) := by
  rintro N P Q NP NQ ⟨Nfg, ⟨NM⟩⟩ ⟨Pfg, ⟨PM⟩⟩ ⟨Qfg, ⟨QM⟩⟩
  obtain ⟨g, hg⟩ :=
    h (PM.comp NP).toHom.range (Nfg.range _) ((QM.comp NQ).comp (PM.comp NP).equivRange.symm.toEmbedding)
  let s := (g.to_hom.comp PM.to_hom).range⊔QM.to_hom.range
  refine'
    ⟨bundled.of s, embedding.comp (substructure.inclusion le_sup_left) (g.to_embedding.comp PM).equivRange.toEmbedding,
      embedding.comp (substructure.inclusion le_sup_right) QM.equiv_range.to_embedding,
      ⟨(fg_iff_Structure_fg _).1 (fg.sup (Pfg.range _) (Qfg.range _)), ⟨substructure.subtype _⟩⟩, _⟩
  ext n
  have hgn := (embedding.ext_iff.1 hg) ((PM.comp NP).equivRange n)
  simp only [← embedding.comp_apply, ← equiv.coe_to_embedding, ← Equivₓ.symm_apply_apply, ← substructure.coe_subtype, ←
    embedding.equiv_range_apply] at hgn
  simp only [← embedding.comp_apply, ← equiv.coe_to_embedding, ← substructure.coe_inclusion, ← Set.coe_inclusion, ←
    embedding.equiv_range_apply, ← hgn]

theorem IsUltrahomogeneous.age_is_fraisse (hc : (Univ : Set M).Countable) (h : L.IsUltrahomogeneous M) :
    IsFraisse (L.Age M) :=
  ⟨Age.nonempty M, fun _ hN => hN.1, Age.is_equiv_invariant L M, Age.countable_quotient M hc, Age.hereditary M,
    Age.joint_embedding M, h.amalgamation_age⟩

namespace IsFraisseLimit

/-- If a class has a Fraïssé limit, it must be Fraïssé. -/
theorem is_fraisse [CountableFunctions L] (h : IsFraisseLimit K M) : IsFraisse K :=
  (congr rfl h.Age).mp (h.ultrahomogeneous.age_is_fraisse h.Countable)

end IsFraisseLimit

end Language

end FirstOrder


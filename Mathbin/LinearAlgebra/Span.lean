/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathbin.LinearAlgebra.Basic
import Mathbin.Order.OmegaCompletePartialOrder

/-!
# The span of a set of vectors, as a submodule

* `submodule.span s` is defined to be the smallest submodule containing the set `s`.

## Notations

* We introduce the notation `R ∙ v` for the span of a singleton, `submodule.span R {v}`.  This is
  `\.`, not the same as the scalar multiplication `•`/`\bub`.

-/


variable {R R₂ K M M₂ V S : Type _}

namespace Submodule

open Function Set

open Pointwise

section AddCommMonoidₓ

variable [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

variable {x : M} (p p' : Submodule R M)

variable [Semiringₓ R₂] {σ₁₂ : R →+* R₂}

variable [AddCommMonoidₓ M₂] [Module R₂ M₂]

section

variable (R)

/-- The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. -/
def span (s : Set M) : Submodule R M :=
  inf { p | s ⊆ p }

end

variable {s t : Set M}

theorem mem_span : x ∈ span R s ↔ ∀ p : Submodule R M, s ⊆ p → x ∈ p :=
  mem_Inter₂

theorem subset_span : s ⊆ span R s := fun x h => mem_span.2 fun p hp => hp h

theorem span_le {p} : span R s ≤ p ↔ s ⊆ p :=
  ⟨Subset.trans subset_span, fun ss x h => mem_span.1 h _ ss⟩

theorem span_mono (h : s ⊆ t) : span R s ≤ span R t :=
  span_le.2 <| Subset.trans h subset_span

theorem span_eq_of_le (h₁ : s ⊆ p) (h₂ : p ≤ span R s) : span R s = p :=
  le_antisymmₓ (span_le.2 h₁) h₂

theorem span_eq : span R (p : Set M) = p :=
  span_eq_of_le _ (Subset.refl _) subset_span

theorem span_eq_span (hs : s ⊆ span R t) (ht : t ⊆ span R s) : span R s = span R t :=
  le_antisymmₓ (span_le.2 hs) (span_le.2 ht)

/-- A version of `submodule.span_eq` for when the span is by a smaller ring. -/
@[simp]
theorem span_coe_eq_restrict_scalars [Semiringₓ S] [HasSmul S R] [Module S M] [IsScalarTower S R M] :
    span S (p : Set M) = p.restrictScalars S :=
  span_eq (p.restrictScalars S)

theorem map_span [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (s : Set M) : (span R s).map f = span R₂ (f '' s) :=
  Eq.symm <|
    span_eq_of_le _ (Set.image_subset f subset_span) <|
      map_le_iff_le_comap.2 <| span_le.2 fun x hx => subset_span ⟨x, hx, rfl⟩

alias Submodule.map_span ← _root_.linear_map.map_span

theorem map_span_le [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (s : Set M) (N : Submodule R₂ M₂) :
    map f (span R s) ≤ N ↔ ∀, ∀ m ∈ s, ∀, f m ∈ N := by
  rw [f.map_span, span_le, Set.image_subset_iff]
  exact Iff.rfl

alias Submodule.map_span_le ← _root_.linear_map.map_span_le

@[simp]
theorem span_insert_zero : span R (insert (0 : M) s) = span R s := by
  refine' le_antisymmₓ _ (Submodule.span_mono (Set.subset_insert 0 s))
  rw [span_le, Set.insert_subset]
  exact
    ⟨by
      simp only [← SetLike.mem_coe, ← Submodule.zero_mem], Submodule.subset_span⟩

-- See also `span_preimage_eq` below.
theorem span_preimage_le (f : M →ₛₗ[σ₁₂] M₂) (s : Set M₂) : span R (f ⁻¹' s) ≤ (span R₂ s).comap f := by
  rw [span_le, comap_coe]
  exact preimage_mono subset_span

alias Submodule.span_preimage_le ← _root_.linear_map.span_preimage_le

theorem closure_subset_span {s : Set M} : (AddSubmonoid.closure s : Set M) ⊆ span R s :=
  (@AddSubmonoid.closure_le _ _ _ (span R s).toAddSubmonoid).mpr subset_span

theorem closure_le_to_add_submonoid_span {s : Set M} : AddSubmonoid.closure s ≤ (span R s).toAddSubmonoid :=
  closure_subset_span

@[simp]
theorem span_closure {s : Set M} : span R (AddSubmonoid.closure s : Set M) = span R s :=
  le_antisymmₓ (span_le.mpr closure_subset_span) (span_mono AddSubmonoid.subset_closure)

/-- An induction principle for span membership. If `p` holds for 0 and all elements of `s`, and is
preserved under addition and scalar multiplication, then `p` holds for all elements of the span of
`s`. -/
@[elab_as_eliminator]
theorem span_induction {p : M → Prop} (h : x ∈ span R s) (Hs : ∀, ∀ x ∈ s, ∀, p x) (H0 : p 0)
    (H1 : ∀ x y, p x → p y → p (x + y)) (H2 : ∀ (a : R) (x), p x → p (a • x)) : p x :=
  (@span_le _ _ _ _ _ _ ⟨p, H1, H0, H2⟩).2 Hs h

/-- A dependent version of `submodule.span_induction`. -/
theorem span_induction' {p : ∀ x, x ∈ span R s → Prop} (Hs : ∀ (x) (h : x ∈ s), p x (subset_span h))
    (H0 : p 0 (Submodule.zero_mem _)) (H1 : ∀ x hx y hy, p x hx → p y hy → p (x + y) (Submodule.add_mem _ ‹_› ‹_›))
    (H2 : ∀ (a : R) (x hx), p x hx → p (a • x) (Submodule.smul_mem _ _ ‹_›)) {x} (hx : x ∈ span R s) : p x hx := by
  refine' Exists.elim _ fun (hx : x ∈ span R s) (hc : p x hx) => hc
  refine'
    span_induction hx (fun m hm => ⟨subset_span hm, Hs m hm⟩) ⟨zero_mem _, H0⟩
      (fun x y hx hy =>
        (Exists.elim hx) fun hx' hx => (Exists.elim hy) fun hy' hy => ⟨add_mem hx' hy', H1 _ _ _ _ hx hy⟩)
      fun r x hx => (Exists.elim hx) fun hx' hx => ⟨smul_mem _ _ hx', H2 r _ _ hx⟩

@[simp]
theorem span_span_coe_preimage : span R ((coe : span R s → M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x =>
    (Subtype.recOn x) fun x hx _ => by
      refine' span_induction' (fun x hx => _) _ (fun x y _ _ => _) (fun r x _ => _) hx
      · exact subset_span hx
        
      · exact zero_mem _
        
      · exact add_mem
        
      · exact smul_mem _ _
        

theorem span_nat_eq_add_submonoid_closure (s : Set M) : (span ℕ s).toAddSubmonoid = AddSubmonoid.closure s := by
  refine' Eq.symm (AddSubmonoid.closure_eq_of_le subset_span _)
  apply add_submonoid.to_nat_submodule.symm.to_galois_connection.l_le _
  rw [span_le]
  exact AddSubmonoid.subset_closure

@[simp]
theorem span_nat_eq (s : AddSubmonoid M) : (span ℕ (s : Set M)).toAddSubmonoid = s := by
  rw [span_nat_eq_add_submonoid_closure, s.closure_eq]

theorem span_int_eq_add_subgroup_closure {M : Type _} [AddCommGroupₓ M] (s : Set M) :
    (span ℤ s).toAddSubgroup = AddSubgroup.closure s :=
  Eq.symm <|
    (AddSubgroup.closure_eq_of_le _ subset_span) fun x hx =>
      span_induction hx (fun x hx => AddSubgroup.subset_closure hx) (AddSubgroup.zero_mem _)
        (fun _ _ => AddSubgroup.add_mem _) fun _ _ _ => AddSubgroup.zsmul_mem _ ‹_› _

@[simp]
theorem span_int_eq {M : Type _} [AddCommGroupₓ M] (s : AddSubgroup M) : (span ℤ (s : Set M)).toAddSubgroup = s := by
  rw [span_int_eq_add_subgroup_closure, s.closure_eq]

section

variable (R M)

/-- `span` forms a Galois insertion with the coercion from submodule to set. -/
protected def gi : GaloisInsertion (@span R M _ _ _) coe where
  choice := fun s _ => span R s
  gc := fun s t => span_le
  le_l_u := fun s => subset_span
  choice_eq := fun s h => rfl

end

@[simp]
theorem span_empty : span R (∅ : Set M) = ⊥ :=
  (Submodule.gi R M).gc.l_bot

@[simp]
theorem span_univ : span R (Univ : Set M) = ⊤ :=
  eq_top_iff.2 <| SetLike.le_def.2 <| subset_span

theorem span_union (s t : Set M) : span R (s ∪ t) = span R s⊔span R t :=
  (Submodule.gi R M).gc.l_sup

theorem span_Union {ι} (s : ι → Set M) : span R (⋃ i, s i) = ⨆ i, span R (s i) :=
  (Submodule.gi R M).gc.l_supr

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem span_Union₂ {ι} {κ : ι → Sort _} (s : ∀ i, κ i → Set M) :
    span R (⋃ (i) (j), s i j) = ⨆ (i) (j), span R (s i j) :=
  (Submodule.gi R M).gc.l_supr₂

theorem span_attach_bUnion [DecidableEq M] {α : Type _} (s : Finset α) (f : s → Finset M) :
    span R (s.attach.bUnion f : Set M) = ⨆ x, span R (f x) := by
  simpa [← span_Union]

theorem sup_span : p⊔span R s = span R (p ∪ s) := by
  rw [Submodule.span_union, p.span_eq]

theorem span_sup : span R s⊔p = span R (s ∪ p) := by
  rw [Submodule.span_union, p.span_eq]

-- mathport name: «expr ∙ »
notation:1000 R "∙"
  x =>/- Note that the character `∙` U+2219 used below is different from the scalar multiplication
    character `•` U+2022 and the matrix multiplication character `⬝` U+2B1D. -/
    span
    R (@singleton _ _ Set.hasSingleton x)

theorem span_eq_supr_of_singleton_spans (s : Set M) : span R s = ⨆ x ∈ s, R∙x := by
  simp only [span_Union, ← Set.bUnion_of_singleton s]

theorem span_range_eq_supr {ι : Type _} {v : ι → M} : span R (Range v) = ⨆ i, R∙v i := by
  rw [span_eq_supr_of_singleton_spans, supr_range]

theorem span_smul_le (s : Set M) (r : R) : span R (r • s) ≤ span R s := by
  rw [span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact smul_mem (span R s) r (subset_span hx)

theorem subset_span_trans {U V W : Set M} (hUV : U ⊆ Submodule.span R V) (hVW : V ⊆ Submodule.span R W) :
    U ⊆ Submodule.span R W :=
  (Submodule.gi R M).gc.le_u_l_trans hUV hVW

/-- See `submodule.span_smul_eq` (in `ring_theory.ideal.operations`) for
`span R (r • s) = r • span R s` that holds for arbitrary `r` in a `comm_semiring`. -/
theorem span_smul_eq_of_is_unit (s : Set M) (r : R) (hr : IsUnit r) : span R (r • s) = span R s := by
  apply le_antisymmₓ
  · apply span_smul_le
    
  · convert span_smul_le (r • s) ((hr.unit⁻¹ : _) : R)
    rw [smul_smul]
    erw [hr.unit.inv_val]
    rw [one_smul]
    

@[simp]
theorem coe_supr_of_directed {ι} [hι : Nonempty ι] (S : ι → Submodule R M) (H : Directed (· ≤ ·) S) :
    ((supr S : Submodule R M) : Set M) = ⋃ i, S i := by
  refine' subset.antisymm _ (Union_subset <| le_supr S)
  suffices (span R (⋃ i, (S i : Set M)) : Set M) ⊆ ⋃ i : ι, ↑(S i) by
    simpa only [← span_Union, ← span_eq] using this
  refine' fun x hx => span_induction hx (fun _ => id) _ _ _ <;> simp only [← mem_Union, ← exists_imp_distrib]
  · exact hι.elim fun i => ⟨i, (S i).zero_mem⟩
    
  · intro x y i hi j hj
    rcases H i j with ⟨k, ik, jk⟩
    exact ⟨k, add_mem (ik hi) (jk hj)⟩
    
  · exact fun a x i hi => ⟨i, smul_mem _ a hi⟩
    

@[simp]
theorem mem_supr_of_directed {ι} [Nonempty ι] (S : ι → Submodule R M) (H : Directed (· ≤ ·) S) {x} :
    x ∈ supr S ↔ ∃ i, x ∈ S i := by
  rw [← SetLike.mem_coe, coe_supr_of_directed S H, mem_Union]
  rfl

theorem mem_Sup_of_directed {s : Set (Submodule R M)} {z} (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) :
    z ∈ sup s ↔ ∃ y ∈ s, z ∈ y := by
  have : Nonempty s := hs.to_subtype
  simp only [← Sup_eq_supr', ← mem_supr_of_directed _ hdir.directed_coe, ← SetCoe.exists, ← Subtype.coe_mk]

@[norm_cast, simp]
theorem coe_supr_of_chain (a : ℕ →o Submodule R M) : (↑(⨆ k, a k) : Set M) = ⋃ k, (a k : Set M) :=
  coe_supr_of_directed a a.Monotone.directed_le

/-- We can regard `coe_supr_of_chain` as the statement that `coe : (submodule R M) → set M` is
Scott continuous for the ω-complete partial order induced by the complete lattice structures. -/
theorem coe_scott_continuous : OmegaCompletePartialOrder.Continuous' (coe : Submodule R M → Set M) :=
  ⟨SetLike.coe_mono, coe_supr_of_chain⟩

@[simp]
theorem mem_supr_of_chain (a : ℕ →o Submodule R M) (m : M) : (m ∈ ⨆ k, a k) ↔ ∃ k, m ∈ a k :=
  mem_supr_of_directed a a.Monotone.directed_le

section

variable {p p'}

theorem mem_sup : x ∈ p⊔p' ↔ ∃ y ∈ p, ∃ z ∈ p', y + z = x :=
  ⟨fun h => by
    rw [← span_eq p, ← span_eq p', ← span_union] at h
    apply span_induction h
    · rintro y (h | h)
      · exact
          ⟨y, h, 0, by
            simp , by
            simp ⟩
        
      · exact
          ⟨0, by
            simp , y, h, by
            simp ⟩
        
      
    · exact
        ⟨0, by
          simp , 0, by
          simp ⟩
      
    · rintro _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      exact
        ⟨_, add_mem hy₁ hy₂, _, add_mem hz₁ hz₂, by
          simp [← add_assocₓ] <;> cc⟩
      
    · rintro a _ ⟨y, hy, z, hz, rfl⟩
      exact
        ⟨_, smul_mem _ a hy, _, smul_mem _ a hz, by
          simp [← smul_add]⟩
      ,
    by
    rintro ⟨y, hy, z, hz, rfl⟩ <;> exact add_mem ((le_sup_left : p ≤ p⊔p') hy) ((le_sup_right : p' ≤ p⊔p') hz)⟩

theorem mem_sup' : x ∈ p⊔p' ↔ ∃ (y : p)(z : p'), (y : M) + z = x :=
  mem_sup.trans <| by
    simp only [← SetLike.exists, ← coe_mk]

variable (p p')

theorem coe_sup : ↑(p⊔p') = (p + p' : Set M) := by
  ext
  rw [SetLike.mem_coe, mem_sup, Set.mem_add]
  simp

theorem sup_to_add_submonoid : (p⊔p').toAddSubmonoid = p.toAddSubmonoid⊔p'.toAddSubmonoid := by
  ext x
  rw [mem_to_add_submonoid, mem_sup, AddSubmonoid.mem_sup]
  rfl

theorem sup_to_add_subgroup {R M : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M] (p p' : Submodule R M) :
    (p⊔p').toAddSubgroup = p.toAddSubgroup⊔p'.toAddSubgroup := by
  ext x
  rw [mem_to_add_subgroup, mem_sup, AddSubgroup.mem_sup]
  rfl

end

theorem mem_span_singleton_self (x : M) : x ∈ R∙x :=
  subset_span rfl

theorem nontrivial_span_singleton {x : M} (h : x ≠ 0) : Nontrivial (R∙x) :=
  ⟨by
    use 0, x, Submodule.mem_span_singleton_self x
    intro H
    rw [eq_comm, Submodule.mk_eq_zero] at H
    exact h H⟩

theorem mem_span_singleton {y : M} : (x ∈ R∙y) ↔ ∃ a : R, a • y = x :=
  ⟨fun h => by
    apply span_induction h
    · rintro y (rfl | ⟨⟨⟩⟩)
      exact
        ⟨1, by
          simp ⟩
      
    · exact
        ⟨0, by
          simp ⟩
      
    · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact
        ⟨a + b, by
          simp [← add_smul]⟩
      
    · rintro a _ ⟨b, rfl⟩
      exact
        ⟨a * b, by
          simp [← smul_smul]⟩
      ,
    by
    rintro ⟨a, y, rfl⟩ <;>
      exact
        smul_mem _ _
          (subset_span <| by
            simp )⟩

theorem le_span_singleton_iff {s : Submodule R M} {v₀ : M} : (s ≤ R∙v₀) ↔ ∀, ∀ v ∈ s, ∀, ∃ r : R, r • v₀ = v := by
  simp_rw [SetLike.le_def, mem_span_singleton]

variable (R)

theorem span_singleton_eq_top_iff (x : M) : (R∙x) = ⊤ ↔ ∀ v, ∃ r : R, r • x = v := by
  rw [eq_top_iff, le_span_singleton_iff]
  tauto

@[simp]
theorem span_zero_singleton : (R∙(0 : M)) = ⊥ := by
  ext
  simp [← mem_span_singleton, ← eq_comm]

theorem span_singleton_eq_range (y : M) : ↑(R∙y) = Range ((· • y) : R → M) :=
  Set.ext fun x => mem_span_singleton

theorem span_singleton_smul_le {S} [Monoidₓ S] [HasSmul S R] [MulAction S M] [IsScalarTower S R M] (r : S) (x : M) :
    (R∙r • x) ≤ R∙x := by
  rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  exact smul_of_tower_mem _ _ (mem_span_singleton_self _)

theorem span_singleton_group_smul_eq {G} [Groupₓ G] [HasSmul G R] [MulAction G M] [IsScalarTower G R M] (g : G)
    (x : M) : (R∙g • x) = R∙x := by
  refine' le_antisymmₓ (span_singleton_smul_le R g x) _
  convert span_singleton_smul_le R g⁻¹ (g • x)
  exact (inv_smul_smul g x).symm

variable {R}

theorem span_singleton_smul_eq {r : R} (hr : IsUnit r) (x : M) : (R∙r • x) = R∙x := by
  lift r to Rˣ using hr
  rw [← Units.smul_def]
  exact span_singleton_group_smul_eq R r x

theorem disjoint_span_singleton {K E : Type _} [DivisionRing K] [AddCommGroupₓ E] [Module K E] {s : Submodule K E}
    {x : E} : Disjoint s (K∙x) ↔ x ∈ s → x = 0 := by
  refine' disjoint_def.trans ⟨fun H hx => H x hx <| subset_span <| mem_singleton x, _⟩
  intro H y hy hyx
  obtain ⟨c, rfl⟩ := mem_span_singleton.1 hyx
  by_cases' hc : c = 0
  · rw [hc, zero_smul]
    
  · rw [s.smul_mem_iff hc] at hy
    rw [H hy, smul_zero]
    

theorem disjoint_span_singleton' {K E : Type _} [DivisionRing K] [AddCommGroupₓ E] [Module K E] {p : Submodule K E}
    {x : E} (x0 : x ≠ 0) : Disjoint p (K∙x) ↔ x ∉ p :=
  disjoint_span_singleton.trans ⟨fun h₁ h₂ => x0 (h₁ h₂), fun h₁ h₂ => (h₁ h₂).elim⟩

theorem mem_span_singleton_trans {x y z : M} (hxy : x ∈ R∙y) (hyz : y ∈ R∙z) : x ∈ R∙z := by
  rw [← SetLike.mem_coe, ← singleton_subset_iff] at *
  exact Submodule.subset_span_trans hxy hyz

theorem mem_span_insert {y} : x ∈ span R (insert y s) ↔ ∃ a : R, ∃ z ∈ span R s, x = a • y + z := by
  simp only [union_singleton, ← span_union, ← mem_sup, ← mem_span_singleton, ← exists_prop, ← exists_exists_eq_and]
  rw [exists_comm]
  simp only [← eq_comm, ← add_commₓ, ← exists_and_distrib_left]

theorem span_insert (x) (s : Set M) : span R (insert x s) = span R ({x} : Set M)⊔span R s := by
  rw [insert_eq, span_union]

theorem span_insert_eq_span (h : x ∈ span R s) : span R (insert x s) = span R s :=
  span_eq_of_le _ (Set.insert_subset.mpr ⟨h, subset_span⟩) (span_mono <| subset_insert _ _)

theorem span_span : span R (span R s : Set M) = span R s :=
  span_eq _

variable (R S s)

/-- If `R` is "smaller" ring than `S` then the span by `R` is smaller than the span by `S`. -/
theorem span_le_restrict_scalars [Semiringₓ S] [HasSmul R S] [Module S M] [IsScalarTower R S M] :
    span R s ≤ (span S s).restrictScalars R :=
  Submodule.span_le.2 Submodule.subset_span

/-- A version of `submodule.span_le_restrict_scalars` with coercions. -/
@[simp]
theorem span_subset_span [Semiringₓ S] [HasSmul R S] [Module S M] [IsScalarTower R S M] :
    ↑(span R s) ⊆ (span S s : Set M) :=
  span_le_restrict_scalars R S s

/-- Taking the span by a large ring of the span by the small ring is the same as taking the span
by just the large ring. -/
theorem span_span_of_tower [Semiringₓ S] [HasSmul R S] [Module S M] [IsScalarTower R S M] :
    span S (span R s : Set M) = span S s :=
  le_antisymmₓ (span_le.2 <| span_subset_span R S s) (span_mono subset_span)

variable {R S s}

theorem span_eq_bot : span R (s : Set M) = ⊥ ↔ ∀, ∀ x ∈ s, ∀, (x : M) = 0 :=
  eq_bot_iff.trans
    ⟨fun H x h => (mem_bot R).1 <| H <| subset_span h, fun H => span_le.2 fun x h => (mem_bot R).2 <| H x h⟩

@[simp]
theorem span_singleton_eq_bot : (R∙x) = ⊥ ↔ x = 0 :=
  span_eq_bot.trans <| by
    simp

@[simp]
theorem span_zero : span R (0 : Set M) = ⊥ := by
  rw [← singleton_zero, span_singleton_eq_bot]

theorem span_singleton_eq_span_singleton {R M : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M]
    [NoZeroSmulDivisors R M] {x y : M} : ((R∙x) = R∙y) ↔ ∃ z : Rˣ, z • x = y := by
  by_cases' hx : x = 0
  · rw [hx, span_zero_singleton, eq_comm, span_singleton_eq_bot]
    exact
      ⟨fun hy =>
        ⟨1, by
          rw [hy, smul_zero]⟩,
        fun ⟨_, hz⟩ => by
        rw [← hz, smul_zero]⟩
    
  by_cases' hy : y = 0
  · rw [hy, span_zero_singleton, span_singleton_eq_bot]
    exact
      ⟨fun hx =>
        ⟨1, by
          rw [hx, smul_zero]⟩,
        fun ⟨z, hz⟩ => (smul_eq_zero_iff_eq z).mp hz⟩
    
  constructor
  · intro hxy
    cases'
      mem_span_singleton.mp
        (by
          rw [hxy]
          apply mem_span_singleton_self) with
      v hv
    cases'
      mem_span_singleton.mp
        (by
          rw [← hxy]
          apply mem_span_singleton_self) with
      i hi
    have vi : v * i = 1 := by
      rw [← one_smul R y, ← hi, smul_smul] at hv
      exact smul_left_injective R hy hv
    have iv : i * v = 1 := by
      rw [← one_smul R x, ← hv, smul_smul] at hi
      exact smul_left_injective R hx hi
    exact ⟨⟨v, i, vi, iv⟩, hv⟩
    
  · rintro ⟨v, rfl⟩
    rw [span_singleton_group_smul_eq]
    

@[simp]
theorem span_image [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) : span R₂ (f '' s) = map f (span R s) :=
  (map_span f s).symm

theorem apply_mem_span_image_of_mem_span [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) {x : M} {s : Set M}
    (h : x ∈ Submodule.span R s) : f x ∈ Submodule.span R₂ (f '' s) := by
  rw [Submodule.span_image]
  exact Submodule.mem_map_of_mem h

@[simp]
theorem map_subtype_span_singleton {p : Submodule R M} (x : p) : map p.Subtype (R∙x) = R∙(x : M) := by
  simp [span_image]

/-- `f` is an explicit argument so we can `apply` this theorem and obtain `h` as a new goal. -/
theorem not_mem_span_of_apply_not_mem_span_image [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) {x : M} {s : Set M}
    (h : f x ∉ Submodule.span R₂ (f '' s)) : x ∉ Submodule.span R s :=
  h.imp (apply_mem_span_image_of_mem_span f)

theorem supr_eq_span {ι : Sort _} (p : ι → Submodule R M) : (⨆ i : ι, p i) = Submodule.span R (⋃ i : ι, ↑(p i)) :=
  le_antisymmₓ (supr_le fun i => Subset.trans (fun m hm => Set.mem_Union.mpr ⟨i, hm⟩) subset_span)
    (span_le.mpr <| Union_subset_iff.mpr fun i m hm => mem_supr_of_mem i hm)

theorem supr_to_add_submonoid {ι : Sort _} (p : ι → Submodule R M) :
    (⨆ i, p i).toAddSubmonoid = ⨆ i, (p i).toAddSubmonoid := by
  refine' le_antisymmₓ (fun x => _) (supr_le fun i => to_add_submonoid_mono <| le_supr _ i)
  simp_rw [supr_eq_span, AddSubmonoid.supr_eq_closure, mem_to_add_submonoid, coe_to_add_submonoid]
  intro hx
  refine' Submodule.span_induction hx (fun x hx => _) _ (fun x y hx hy => _) fun r x hx => _
  · exact AddSubmonoid.subset_closure hx
    
  · exact AddSubmonoid.zero_mem _
    
  · exact AddSubmonoid.add_mem _ hx hy
    
  · apply AddSubmonoid.closure_induction hx
    · rintro x ⟨_, ⟨i, rfl⟩, hix : x ∈ p i⟩
      apply AddSubmonoid.subset_closure (set.mem_Union.mpr ⟨i, _⟩)
      exact smul_mem _ r hix
      
    · rw [smul_zero]
      exact AddSubmonoid.zero_mem _
      
    · intro x y hx hy
      rw [smul_add]
      exact AddSubmonoid.add_mem _ hx hy
      
    

/-- An induction principle for elements of `⨆ i, p i`.
If `C` holds for `0` and all elements of `p i` for all `i`, and is preserved under addition,
then it holds for all elements of the supremum of `p`. -/
@[elab_as_eliminator]
theorem supr_induction {ι : Sort _} (p : ι → Submodule R M) {C : M → Prop} {x : M} (hx : x ∈ ⨆ i, p i)
    (hp : ∀ (i), ∀ x ∈ p i, ∀, C x) (h0 : C 0) (hadd : ∀ x y, C x → C y → C (x + y)) : C x := by
  rw [← mem_to_add_submonoid, supr_to_add_submonoid] at hx
  exact AddSubmonoid.supr_induction _ hx hp h0 hadd

/-- A dependent version of `submodule.supr_induction`. -/
@[elab_as_eliminator]
theorem supr_induction' {ι : Sort _} (p : ι → Submodule R M) {C : ∀ x, (x ∈ ⨆ i, p i) → Prop}
    (hp : ∀ (i), ∀ x ∈ p i, ∀, C x (mem_supr_of_mem i ‹_›)) (h0 : C 0 (zero_mem _))
    (hadd : ∀ x y hx hy, C x hx → C y hy → C (x + y) (add_mem ‹_› ‹_›)) {x : M} (hx : x ∈ ⨆ i, p i) : C x hx := by
  refine' Exists.elim _ fun (hx : x ∈ ⨆ i, p i) (hc : C x hx) => hc
  refine' supr_induction p hx (fun i x hx => _) _ fun x y => _
  · exact ⟨_, hp _ _ hx⟩
    
  · exact ⟨_, h0⟩
    
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    refine' ⟨_, hadd _ _ _ _ Cx Cy⟩
    

@[simp]
theorem span_singleton_le_iff_mem (m : M) (p : Submodule R M) : (R∙m) ≤ p ↔ m ∈ p := by
  rw [span_le, singleton_subset_iff, SetLike.mem_coe]

theorem singleton_span_is_compact_element (x : M) : CompleteLattice.IsCompactElement (span R {x} : Submodule R M) := by
  rw [CompleteLattice.is_compact_element_iff_le_of_directed_Sup_le]
  intro d hemp hdir hsup
  have : x ∈ Sup d := (set_like.le_def.mp hsup) (mem_span_singleton_self x)
  obtain ⟨y, ⟨hyd, hxy⟩⟩ := (mem_Sup_of_directed hemp hdir).mp this
  exact
    ⟨y,
      ⟨hyd, by
        simpa only [← span_le, ← singleton_subset_iff] ⟩⟩

/-- The span of a finite subset is compact in the lattice of submodules. -/
theorem finset_span_is_compact_element (S : Finset M) : CompleteLattice.IsCompactElement (span R S : Submodule R M) :=
  by
  rw [span_eq_supr_of_singleton_spans]
  simp only [← Finset.mem_coe]
  rw [← Finset.sup_eq_supr]
  exact CompleteLattice.finset_sup_compact_of_compact S fun x _ => singleton_span_is_compact_element x

/-- The span of a finite subset is compact in the lattice of submodules. -/
theorem finite_span_is_compact_element (S : Set M) (h : S.Finite) :
    CompleteLattice.IsCompactElement (span R S : Submodule R M) :=
  Finite.coe_to_finset h ▸ finset_span_is_compact_element h.toFinset

instance : IsCompactlyGenerated (Submodule R M) :=
  ⟨fun s =>
    ⟨(fun x => span R {x}) '' s,
      ⟨fun t ht => by
        rcases(Set.mem_image _ _ _).1 ht with ⟨x, hx, rfl⟩
        apply singleton_span_is_compact_element, by
        rw [Sup_eq_supr, supr_image, ← span_eq_supr_of_singleton_spans, span_eq]⟩⟩⟩

theorem lt_sup_iff_not_mem {I : Submodule R M} {a : M} : (I < I⊔R∙a) ↔ a ∉ I := by
  constructor
  · intro h
    by_contra akey
    have h1 : (I⊔R∙a) ≤ I := by
      simp only [← sup_le_iff]
      constructor
      · exact le_reflₓ I
        
      · exact (span_singleton_le_iff_mem a I).mpr akey
        
    have h2 := gt_of_ge_of_gtₓ h1 h
    exact lt_irreflₓ I h2
    
  · intro h
    apply set_like.lt_iff_le_and_exists.mpr
    constructor
    simp only [← le_sup_left]
    use a
    constructor
    swap
    · assumption
      
    · have : (R∙a) ≤ I⊔R∙a := le_sup_right
      exact this (mem_span_singleton_self a)
      
    

theorem mem_supr {ι : Sort _} (p : ι → Submodule R M) {m : M} : (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  rw [← span_singleton_le_iff_mem, le_supr_iff]
  simp only [← span_singleton_le_iff_mem]

section

open Classical

/-- For every element in the span of a set, there exists a finite subset of the set
such that the element is contained in the span of the subset. -/
theorem mem_span_finite_of_mem_span {S : Set M} {x : M} (hx : x ∈ span R S) :
    ∃ T : Finset M, ↑T ⊆ S ∧ x ∈ span R (T : Set M) := by
  refine' span_induction hx (fun x hx => _) _ _ _
  · refine' ⟨{x}, _, _⟩
    · rwa [Finset.coe_singleton, Set.singleton_subset_iff]
      
    · rw [Finset.coe_singleton]
      exact Submodule.mem_span_singleton_self x
      
    
  · use ∅
    simp
    
  · rintro x y ⟨X, hX, hxX⟩ ⟨Y, hY, hyY⟩
    refine' ⟨X ∪ Y, _, _⟩
    · rw [Finset.coe_union]
      exact Set.union_subset hX hY
      
    rw [Finset.coe_union, span_union, mem_sup]
    exact ⟨x, hxX, y, hyY, rfl⟩
    
  · rintro a x ⟨T, hT, h2⟩
    exact ⟨T, hT, smul_mem _ _ h2⟩
    

end

variable {M' : Type _} [AddCommMonoidₓ M'] [Module R M'] (q₁ q₁' : Submodule R M')

/-- The product of two submodules is a submodule. -/
def prod : Submodule R (M × M') :=
  { p.toAddSubmonoid.Prod q₁.toAddSubmonoid with Carrier := (p : Set M) ×ˢ (q₁ : Set M'),
    smul_mem' := by
      rintro a ⟨x, y⟩ ⟨hx, hy⟩ <;> exact ⟨smul_mem _ a hx, smul_mem _ a hy⟩ }

@[simp]
theorem prod_coe : (prod p q₁ : Set (M × M')) = (p : Set M) ×ˢ (q₁ : Set M') :=
  rfl

@[simp]
theorem mem_prod {p : Submodule R M} {q : Submodule R M'} {x : M × M'} : x ∈ prod p q ↔ x.1 ∈ p ∧ x.2 ∈ q :=
  Set.mem_prod

theorem span_prod_le (s : Set M) (t : Set M') : span R (s ×ˢ t) ≤ prod (span R s) (span R t) :=
  span_le.2 <| Set.prod_mono subset_span subset_span

@[simp]
theorem prod_top : (prod ⊤ ⊤ : Submodule R (M × M')) = ⊤ := by
  ext <;> simp

@[simp]
theorem prod_bot : (prod ⊥ ⊥ : Submodule R (M × M')) = ⊥ := by
  ext ⟨x, y⟩ <;> simp [← Prod.zero_eq_mk]

theorem prod_mono {p p' : Submodule R M} {q q' : Submodule R M'} : p ≤ p' → q ≤ q' → prod p q ≤ prod p' q' :=
  prod_mono

@[simp]
theorem prod_inf_prod : prod p q₁⊓prod p' q₁' = prod (p⊓p') (q₁⊓q₁') :=
  SetLike.coe_injective Set.prod_inter_prod

@[simp]
theorem prod_sup_prod : prod p q₁⊔prod p' q₁' = prod (p⊔p') (q₁⊔q₁') := by
  refine' le_antisymmₓ (sup_le (prod_mono le_sup_left le_sup_left) (prod_mono le_sup_right le_sup_right)) _
  simp [← SetLike.le_def]
  intro xx yy hxx hyy
  rcases mem_sup.1 hxx with ⟨x, hx, x', hx', rfl⟩
  rcases mem_sup.1 hyy with ⟨y, hy, y', hy', rfl⟩
  refine' mem_sup.2 ⟨(x, y), ⟨hx, hy⟩, (x', y'), ⟨hx', hy'⟩, rfl⟩

end AddCommMonoidₓ

section AddCommGroupₓ

variable [Ringₓ R] [AddCommGroupₓ M] [Module R M]

@[simp]
theorem span_neg (s : Set M) : span R (-s) = span R s :=
  calc
    span R (-s) = span R ((-LinearMap.id : M →ₗ[R] M) '' s) := by
      simp
    _ = map (-LinearMap.id) (span R s) := ((-LinearMap.id).map_span _).symm
    _ = span R s := by
      simp
    

theorem mem_span_insert' {x y} {s : Set M} : x ∈ span R (insert y s) ↔ ∃ a : R, x + a • y ∈ span R s := by
  rw [mem_span_insert]
  constructor
  · rintro ⟨a, z, hz, rfl⟩
    exact
      ⟨-a, by
        simp [← hz, ← add_assocₓ]⟩
    
  · rintro ⟨a, h⟩
    exact
      ⟨-a, _, h, by
        simp [← add_commₓ, ← add_left_commₓ]⟩
    

instance : IsModularLattice (Submodule R M) :=
  ⟨fun x y z xz a ha => by
    rw [mem_inf, mem_sup] at ha
    rcases ha with ⟨⟨b, hb, c, hc, rfl⟩, haz⟩
    rw [mem_sup]
    refine' ⟨b, hb, c, mem_inf.2 ⟨hc, _⟩, rfl⟩
    rw [← add_sub_cancel c b, add_commₓ]
    apply z.sub_mem haz (xz hb)⟩

end AddCommGroupₓ

section AddCommGroupₓ

variable [Semiringₓ R] [Semiringₓ R₂]

variable [AddCommGroupₓ M] [Module R M] [AddCommGroupₓ M₂] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]

theorem comap_map_eq (f : M →ₛₗ[τ₁₂] M₂) (p : Submodule R M) : comap f (map f p) = p⊔f.ker := by
  refine' le_antisymmₓ _ (sup_le (le_comap_map _ _) (comap_mono bot_le))
  rintro x ⟨y, hy, e⟩
  exact
    mem_sup.2
      ⟨y, hy, x - y, by
        simpa using sub_eq_zero.2 e.symm, by
        simp ⟩

theorem comap_map_eq_self {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M} (h : f.ker ≤ p) : comap f (map f p) = p := by
  rw [Submodule.comap_map_eq, sup_of_le_left h]

end AddCommGroupₓ

end Submodule

namespace LinearMap

open Submodule Function

section AddCommGroupₓ

variable [Semiringₓ R] [Semiringₓ R₂]

variable [AddCommGroupₓ M] [AddCommGroupₓ M₂]

variable [Module R M] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]

include R

protected theorem map_le_map_iff (f : M →ₛₗ[τ₁₂] M₂) {p p'} : map f p ≤ map f p' ↔ p ≤ p'⊔ker f := by
  rw [map_le_iff_le_comap, Submodule.comap_map_eq]

theorem map_le_map_iff' {f : M →ₛₗ[τ₁₂] M₂} (hf : ker f = ⊥) {p p'} : map f p ≤ map f p' ↔ p ≤ p' := by
  rw [LinearMap.map_le_map_iff, hf, sup_bot_eq]

theorem map_injective {f : M →ₛₗ[τ₁₂] M₂} (hf : ker f = ⊥) : Injective (map f) := fun p p' h =>
  le_antisymmₓ ((map_le_map_iff' hf).1 (le_of_eqₓ h)) ((map_le_map_iff' hf).1 (ge_of_eq h))

theorem map_eq_top_iff {f : M →ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) {p : Submodule R M} : p.map f = ⊤ ↔ p⊔f.ker = ⊤ := by
  simp_rw [← top_le_iff, ← hf, range_eq_map, LinearMap.map_le_map_iff]

end AddCommGroupₓ

section

variable (R) (M) [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

/-- Given an element `x` of a module `M` over `R`, the natural map from
    `R` to scalar multiples of `x`.-/
@[simps]
def toSpanSingleton (x : M) : R →ₗ[R] M :=
  LinearMap.id.smul_right x

/-- The range of `to_span_singleton x` is the span of `x`.-/
theorem span_singleton_eq_range (x : M) : (R∙x) = (toSpanSingleton R M x).range :=
  Submodule.ext fun y => by
    refine' Iff.trans _ linear_map.mem_range.symm
    exact mem_span_singleton

@[simp]
theorem to_span_singleton_one (x : M) : toSpanSingleton R M x 1 = x :=
  one_smul _ _

@[simp]
theorem to_span_singleton_zero : toSpanSingleton R M 0 = 0 := by
  ext
  simp

end

section AddCommMonoidₓ

variable [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

variable [Semiringₓ R₂] [AddCommMonoidₓ M₂] [Module R₂ M₂]

variable {σ₁₂ : R →+* R₂}

/-- If two linear maps are equal on a set `s`, then they are equal on `submodule.span s`.

See also `linear_map.eq_on_span'` for a version using `set.eq_on`. -/
theorem eq_on_span {s : Set M} {f g : M →ₛₗ[σ₁₂] M₂} (H : Set.EqOn f g s) ⦃x⦄ (h : x ∈ span R s) : f x = g x := by
  apply span_induction h H <;> simp (config := { contextual := true })

/-- If two linear maps are equal on a set `s`, then they are equal on `submodule.span s`.

This version uses `set.eq_on`, and the hidden argument will expand to `h : x ∈ (span R s : set M)`.
See `linear_map.eq_on_span` for a version that takes `h : x ∈ span R s` as an argument. -/
theorem eq_on_span' {s : Set M} {f g : M →ₛₗ[σ₁₂] M₂} (H : Set.EqOn f g s) : Set.EqOn f g (span R s : Set M) :=
  eq_on_span H

/-- If `s` generates the whole module and linear maps `f`, `g` are equal on `s`, then they are
equal. -/
theorem ext_on {s : Set M} {f g : M →ₛₗ[σ₁₂] M₂} (hv : span R s = ⊤) (h : Set.EqOn f g s) : f = g :=
  LinearMap.ext fun x => eq_on_span h (eq_top_iff'.1 hv _)

/-- If the range of `v : ι → M` generates the whole module and linear maps `f`, `g` are equal at
each `v i`, then they are equal. -/
theorem ext_on_range {ι : Type _} {v : ι → M} {f g : M →ₛₗ[σ₁₂] M₂} (hv : span R (Set.Range v) = ⊤)
    (h : ∀ i, f (v i) = g (v i)) : f = g :=
  ext_on hv (Set.forall_range_iff.2 h)

end AddCommMonoidₓ

section Field

variable {K V} [Field K] [AddCommGroupₓ V] [Module K V]

noncomputable section

open Classical

theorem span_singleton_sup_ker_eq_top (f : V →ₗ[K] K) {x : V} (hx : f x ≠ 0) : (K∙x)⊔f.ker = ⊤ :=
  eq_top_iff.2 fun y hy =>
    Submodule.mem_sup.2
      ⟨(f y * (f x)⁻¹) • x, Submodule.mem_span_singleton.2 ⟨f y * (f x)⁻¹, rfl⟩,
        ⟨y - (f y * (f x)⁻¹) • x, by
          rw [LinearMap.mem_ker, f.map_sub, f.map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel hx, mul_oneₓ, sub_self],
          by
          simp only [← add_sub_cancel'_right]⟩⟩

variable (K V)

theorem ker_to_span_singleton {x : V} (h : x ≠ 0) : (toSpanSingleton K V x).ker = ⊥ := by
  ext c
  constructor
  · intro hc
    rw [Submodule.mem_bot]
    rw [mem_ker] at hc
    by_contra hc'
    have : x = 0
    calc x = c⁻¹ • c • x := by
        rw [← mul_smul, inv_mul_cancel hc', one_smul]_ = c⁻¹ • (to_span_singleton K V x) c := rfl _ = 0 := by
        rw [hc, smul_zero]
    tauto
    
  · rw [mem_ker, Submodule.mem_bot]
    intro h
    rw [h]
    simp
    

end Field

end LinearMap

open LinearMap

namespace LinearEquiv

section Field

variable (K V) [Field K] [AddCommGroupₓ V] [Module K V]

/-- Given a nonzero element `x` of a vector space `V` over a field `K`, the natural
    map from `K` to the span of `x`, with invertibility check to consider it as an
    isomorphism.-/
def toSpanNonzeroSingleton (x : V) (h : x ≠ 0) : K ≃ₗ[K] K∙x :=
  LinearEquiv.trans
    (LinearEquiv.ofInjective (LinearMap.toSpanSingleton K V x) (ker_eq_bot.1 <| LinearMap.ker_to_span_singleton K V h))
    (LinearEquiv.ofEq (toSpanSingleton K V x).range (K∙x) (span_singleton_eq_range K V x).symm)

theorem to_span_nonzero_singleton_one (x : V) (h : x ≠ 0) :
    LinearEquiv.toSpanNonzeroSingleton K V x h 1 = (⟨x, Submodule.mem_span_singleton_self x⟩ : K∙x) := by
  apply set_like.coe_eq_coe.mp
  have : ↑(to_span_nonzero_singleton K V x h 1) = to_span_singleton K V x 1 := rfl
  rw [this, to_span_singleton_one, Submodule.coe_mk]

/-- Given a nonzero element `x` of a vector space `V` over a field `K`, the natural map
    from the span of `x` to `K`.-/
abbrev coord (x : V) (h : x ≠ 0) : (K∙x) ≃ₗ[K] K :=
  (toSpanNonzeroSingleton K V x h).symm

theorem coord_self (x : V) (h : x ≠ 0) : (coord K V x h) (⟨x, Submodule.mem_span_singleton_self x⟩ : K∙x) = 1 := by
  rw [← to_span_nonzero_singleton_one K V x h, LinearEquiv.symm_apply_apply]

end Field

end LinearEquiv


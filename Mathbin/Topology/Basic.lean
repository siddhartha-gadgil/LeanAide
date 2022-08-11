/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
import Mathbin.Order.Filter.Ultrafilter
import Mathbin.Order.Filter.Partial
import Mathbin.Order.Filter.SmallSets
import Mathbin.Algebra.Support

/-!
# Basic theory of topological spaces.

The main definition is the type class `topological space α` which endows a type `α` with a topology.
Then `set α` gets predicates `is_open`, `is_closed` and functions `interior`, `closure` and
`frontier`. Each point `x` of `α` gets a neighborhood filter `𝓝 x`. A filter `F` on `α` has
`x` as a cluster point if `cluster_pt x F : 𝓝 x ⊓ F ≠ ⊥`. A map `f : ι → α` clusters at `x`
along `F : filter ι` if `map_cluster_pt x F f : cluster_pt x (map f F)`. In particular
the notion of cluster point of a sequence `u` is `map_cluster_pt x at_top u`.

This file also defines locally finite families of subsets of `α`.

For topological spaces `α` and `β`, a function `f : α → β` and a point `a : α`,
`continuous_at f a` means `f` is continuous at `a`, and global continuity is
`continuous f`. There is also a version of continuity `pcontinuous` for
partially defined functions.

## Notation

* `𝓝 x`: the filter `nhds x` of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhds_within x s` of neighborhoods of a point `x` within a set `s`;
* `𝓝[≤] x`: the filter `nhds_within x (set.Iic x)` of left-neighborhoods of `x`;
* `𝓝[≥] x`: the filter `nhds_within x (set.Ici x)` of right-neighborhoods of `x`;
* `𝓝[<] x`: the filter `nhds_within x (set.Iio x)` of punctured left-neighborhoods of `x`;
* `𝓝[>] x`: the filter `nhds_within x (set.Ioi x)` of punctured right-neighborhoods of `x`;
* `𝓝[≠] x`: the filter `nhds_within x {x}ᶜ` of punctured neighborhoods of `x`.

## Implementation notes

Topology in mathlib heavily uses filters (even more than in Bourbaki). See explanations in
<https://leanprover-community.github.io/theories/topology.html>.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]
*  [I. M. James, *Topologies and Uniformities*][james1999]

## Tags

topological space, interior, closure, frontier, neighborhood, continuity, continuous function
-/


noncomputable section

open Set Filter Classical

open Classical Filter

universe u v w

/-!
### Topological spaces
-/


/-- A topology on `α`. -/
@[protect_proj]
structure TopologicalSpace (α : Type u) where
  IsOpen : Set α → Prop
  is_open_univ : IsOpen Univ
  is_open_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  is_open_sUnion : ∀ s, (∀, ∀ t ∈ s, ∀, IsOpen t) → IsOpen (⋃₀s)

attribute [class] TopologicalSpace

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (A «expr ⊆ » T)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (A B «expr ∈ » T)
/-- A constructor for topologies by specifying the closed sets,
and showing that they satisfy the appropriate conditions. -/
def TopologicalSpace.ofClosed {α : Type u} (T : Set (Set α)) (empty_mem : ∅ ∈ T)
    (sInter_mem : ∀ (A) (_ : A ⊆ T), ⋂₀ A ∈ T) (union_mem : ∀ (A B) (_ : A ∈ T) (_ : B ∈ T), A ∪ B ∈ T) :
    TopologicalSpace α where
  IsOpen := fun X => Xᶜ ∈ T
  is_open_univ := by
    simp [← empty_mem]
  is_open_inter := fun s t hs ht => by
    simpa only [← compl_inter] using union_mem (sᶜ) hs (tᶜ) ht
  is_open_sUnion := fun s hs => by
    rw [Set.compl_sUnion] <;>
      exact
        sInter_mem (compl '' s) fun z ⟨y, hy, hz⟩ => by
          simpa [← hz.symm] using hs y hy

section TopologicalSpace

variable {α : Type u} {β : Type v} {ι : Sort w} {a : α} {s s₁ s₂ t : Set α} {p p₁ p₂ : α → Prop}

@[ext]
theorem topological_space_eq : ∀ {f g : TopologicalSpace α}, f.IsOpen = g.IsOpen → f = g
  | ⟨a, _, _, _⟩, ⟨b, _, _, _⟩, rfl => rfl

section

variable [TopologicalSpace α]

/-- `is_open s` means that `s` is open in the ambient topological space on `α` -/
def IsOpen (s : Set α) : Prop :=
  TopologicalSpace.IsOpen ‹_› s

@[simp]
theorem is_open_univ : IsOpen (Univ : Set α) :=
  TopologicalSpace.is_open_univ _

theorem IsOpen.inter (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s₁ ∩ s₂) :=
  TopologicalSpace.is_open_inter _ s₁ s₂ h₁ h₂

theorem is_open_sUnion {s : Set (Set α)} (h : ∀, ∀ t ∈ s, ∀, IsOpen t) : IsOpen (⋃₀s) :=
  TopologicalSpace.is_open_sUnion _ s h

end

theorem topological_space_eq_iff {t t' : TopologicalSpace α} : t = t' ↔ ∀ s, @IsOpen α t s ↔ @IsOpen α t' s :=
  ⟨fun h s => h ▸ Iff.rfl, fun h => by
    ext
    exact h _⟩

theorem is_open_fold {s : Set α} {t : TopologicalSpace α} : t.IsOpen s = @IsOpen α t s :=
  rfl

variable [TopologicalSpace α]

theorem is_open_Union {f : ι → Set α} (h : ∀ i, IsOpen (f i)) : IsOpen (⋃ i, f i) :=
  is_open_sUnion <| by
    rintro _ ⟨i, rfl⟩ <;> exact h i

theorem is_open_bUnion {s : Set β} {f : β → Set α} (h : ∀, ∀ i ∈ s, ∀, IsOpen (f i)) : IsOpen (⋃ i ∈ s, f i) :=
  is_open_Union fun i => is_open_Union fun hi => h i hi

theorem IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s₁ ∪ s₂) := by
  rw [union_eq_Union] <;> exact is_open_Union (Bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp]
theorem is_open_empty : IsOpen (∅ : Set α) := by
  rw [← sUnion_empty] <;> exact is_open_sUnion fun a => False.elim

theorem is_open_sInter {s : Set (Set α)} (hs : s.Finite) : (∀, ∀ t ∈ s, ∀, IsOpen t) → IsOpen (⋂₀ s) :=
  (Finite.induction_on hs fun _ => by
      rw [sInter_empty] <;> exact is_open_univ)
    fun a s has hs ih h => by
    rw [sInter_insert] <;> exact IsOpen.inter (h _ <| mem_insert _ _) (ih fun t => h t ∘ mem_insert_of_mem _)

theorem is_open_bInter {s : Set β} {f : β → Set α} (hs : s.Finite) :
    (∀, ∀ i ∈ s, ∀, IsOpen (f i)) → IsOpen (⋂ i ∈ s, f i) :=
  Finite.induction_on hs
    (fun _ => by
      rw [bInter_empty] <;> exact is_open_univ)
    fun a s has hs ih h => by
    rw [bInter_insert] <;> exact IsOpen.inter (h a (mem_insert _ _)) (ih fun i hi => h i (mem_insert_of_mem _ hi))

theorem is_open_Inter [Fintype β] {s : β → Set α} (h : ∀ i, IsOpen (s i)) : IsOpen (⋂ i, s i) :=
  suffices IsOpen (⋂ (i : β) (hi : i ∈ @Univ β), s i) by
    simpa
  is_open_bInter finite_univ fun i _ => h i

theorem is_open_Inter_prop {p : Prop} {s : p → Set α} (h : ∀ h : p, IsOpen (s h)) : IsOpen (Inter s) := by
  by_cases' p <;> simp [*]

theorem is_open_const {p : Prop} : IsOpen { a : α | p } :=
  by_cases
    (fun this : p => by
      simp only [← this] <;> exact is_open_univ)
    fun this : ¬p => by
    simp only [← this] <;> exact is_open_empty

theorem IsOpen.and : IsOpen { a | p₁ a } → IsOpen { a | p₂ a } → IsOpen { a | p₁ a ∧ p₂ a } :=
  IsOpen.inter

/-- A set is closed if its complement is open -/
class IsClosed (s : Set α) : Prop where
  is_open_compl : IsOpen (sᶜ)

@[simp]
theorem is_open_compl_iff {s : Set α} : IsOpen (sᶜ) ↔ IsClosed s :=
  ⟨fun h => ⟨h⟩, fun h => h.is_open_compl⟩

@[simp]
theorem is_closed_empty : IsClosed (∅ : Set α) := by
  rw [← is_open_compl_iff, compl_empty]
  exact is_open_univ

@[simp]
theorem is_closed_univ : IsClosed (Univ : Set α) := by
  rw [← is_open_compl_iff, compl_univ]
  exact is_open_empty

theorem IsClosed.union : IsClosed s₁ → IsClosed s₂ → IsClosed (s₁ ∪ s₂) := fun h₁ h₂ => by
  rw [← is_open_compl_iff] at *
  rw [compl_union]
  exact IsOpen.inter h₁ h₂

theorem is_closed_sInter {s : Set (Set α)} : (∀, ∀ t ∈ s, ∀, IsClosed t) → IsClosed (⋂₀ s) := by
  simpa only [is_open_compl_iff, ← compl_sInter, ← sUnion_image] using is_open_bUnion

theorem is_closed_Inter {f : ι → Set α} (h : ∀ i, IsClosed (f i)) : IsClosed (⋂ i, f i) :=
  is_closed_sInter fun t ⟨i, (HEq : f i = t)⟩ => HEq ▸ h i

theorem is_closed_bInter {s : Set β} {f : β → Set α} (h : ∀, ∀ i ∈ s, ∀, IsClosed (f i)) : IsClosed (⋂ i ∈ s, f i) :=
  is_closed_Inter fun i => is_closed_Inter <| h i

@[simp]
theorem is_closed_compl_iff {s : Set α} : IsClosed (sᶜ) ↔ IsOpen s := by
  rw [← is_open_compl_iff, compl_compl]

theorem IsOpen.is_closed_compl {s : Set α} (hs : IsOpen s) : IsClosed (sᶜ) :=
  is_closed_compl_iff.2 hs

theorem IsOpen.sdiff {s t : Set α} (h₁ : IsOpen s) (h₂ : IsClosed t) : IsOpen (s \ t) :=
  IsOpen.inter h₁ <| is_open_compl_iff.mpr h₂

theorem IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : IsClosed (s₁ ∩ s₂) := by
  rw [← is_open_compl_iff] at *
  rw [compl_inter]
  exact IsOpen.union h₁ h₂

theorem IsClosed.sdiff {s t : Set α} (h₁ : IsClosed s) (h₂ : IsOpen t) : IsClosed (s \ t) :=
  IsClosed.inter h₁ (is_closed_compl_iff.mpr h₂)

theorem is_closed_bUnion {s : Set β} {f : β → Set α} (hs : s.Finite) :
    (∀, ∀ i ∈ s, ∀, IsClosed (f i)) → IsClosed (⋃ i ∈ s, f i) :=
  Finite.induction_on hs
    (fun _ => by
      rw [bUnion_empty] <;> exact is_closed_empty)
    fun a s has hs ih h => by
    rw [bUnion_insert] <;> exact IsClosed.union (h a (mem_insert _ _)) (ih fun i hi => h i (mem_insert_of_mem _ hi))

theorem is_closed_Union [Fintype β] {s : β → Set α} (h : ∀ i, IsClosed (s i)) : IsClosed (Union s) :=
  suffices IsClosed (⋃ (i : β) (hi : i ∈ @Univ β), s i) by
    convert this <;> simp [← Set.ext_iff]
  is_closed_bUnion finite_univ fun i _ => h i

theorem is_closed_Union_prop {p : Prop} {s : p → Set α} (h : ∀ h : p, IsClosed (s h)) : IsClosed (Union s) := by
  by_cases' p <;> simp [*]

theorem is_closed_imp {p q : α → Prop} (hp : IsOpen { x | p x }) (hq : IsClosed { x | q x }) :
    IsClosed { x | p x → q x } := by
  have : { x | p x → q x } = { x | p x }ᶜ ∪ { x | q x } := Set.ext fun x => imp_iff_not_or
  rw [this] <;> exact IsClosed.union (is_closed_compl_iff.mpr hp) hq

theorem IsClosed.not : IsClosed { a | p a } → IsOpen { a | ¬p a } :=
  is_open_compl_iff.mpr

/-!
### Interior of a set
-/


/-- The interior of a set `s` is the largest open subset of `s`. -/
def Interior (s : Set α) : Set α :=
  ⋃₀{ t | IsOpen t ∧ t ⊆ s }

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem mem_interior {s : Set α} {x : α} : x ∈ Interior s ↔ ∃ (t : _)(_ : t ⊆ s), IsOpen t ∧ x ∈ t := by
  simp only [← Interior, ← mem_sUnion, ← mem_set_of_eq, ← exists_prop, ← and_assoc, ← And.left_comm]

@[simp]
theorem is_open_interior {s : Set α} : IsOpen (Interior s) :=
  is_open_sUnion fun t ⟨h₁, h₂⟩ => h₁

theorem interior_subset {s : Set α} : Interior s ⊆ s :=
  sUnion_subset fun t ⟨h₁, h₂⟩ => h₂

theorem interior_maximal {s t : Set α} (h₁ : t ⊆ s) (h₂ : IsOpen t) : t ⊆ Interior s :=
  subset_sUnion_of_mem ⟨h₂, h₁⟩

theorem IsOpen.interior_eq {s : Set α} (h : IsOpen s) : Interior s = s :=
  Subset.antisymm interior_subset (interior_maximal (Subset.refl s) h)

theorem interior_eq_iff_open {s : Set α} : Interior s = s ↔ IsOpen s :=
  ⟨fun h => h ▸ is_open_interior, IsOpen.interior_eq⟩

theorem subset_interior_iff_open {s : Set α} : s ⊆ Interior s ↔ IsOpen s := by
  simp only [← interior_eq_iff_open.symm, ← subset.antisymm_iff, ← interior_subset, ← true_andₓ]

theorem subset_interior_iff_subset_of_open {s t : Set α} (h₁ : IsOpen s) : s ⊆ Interior t ↔ s ⊆ t :=
  ⟨fun h => Subset.trans h interior_subset, fun h₂ => interior_maximal h₂ h₁⟩

theorem subset_interior_iff {s t : Set α} : t ⊆ Interior s ↔ ∃ U, IsOpen U ∧ t ⊆ U ∧ U ⊆ s :=
  ⟨fun h => ⟨Interior s, is_open_interior, h, interior_subset⟩, fun ⟨U, hU, htU, hUs⟩ =>
    htU.trans (interior_maximal hUs hU)⟩

@[mono]
theorem interior_mono {s t : Set α} (h : s ⊆ t) : Interior s ⊆ Interior t :=
  interior_maximal (Subset.trans interior_subset h) is_open_interior

@[simp]
theorem interior_empty : Interior (∅ : Set α) = ∅ :=
  is_open_empty.interior_eq

@[simp]
theorem interior_univ : Interior (Univ : Set α) = univ :=
  is_open_univ.interior_eq

@[simp]
theorem interior_eq_univ {s : Set α} : Interior s = univ ↔ s = univ :=
  ⟨fun h => univ_subset_iff.mp <| h.symm.trans_le interior_subset, fun h => h.symm ▸ interior_univ⟩

@[simp]
theorem interior_interior {s : Set α} : Interior (Interior s) = Interior s :=
  is_open_interior.interior_eq

@[simp]
theorem interior_inter {s t : Set α} : Interior (s ∩ t) = Interior s ∩ Interior t :=
  Subset.antisymm (subset_inter (interior_mono <| inter_subset_left s t) (interior_mono <| inter_subset_right s t))
    (interior_maximal (inter_subset_inter interior_subset interior_subset) <|
      IsOpen.inter is_open_interior is_open_interior)

@[simp]
theorem Finset.interior_Inter {ι : Type _} (s : Finset ι) (f : ι → Set α) :
    Interior (⋂ i ∈ s, f i) = ⋂ i ∈ s, Interior (f i) := by
  classical
  refine'
    s.induction_on
      (by
        simp )
      _
  intro i s h₁ h₂
  simp [← h₂]

@[simp]
theorem interior_Inter_of_fintype {ι : Type _} [Fintype ι] (f : ι → Set α) :
    Interior (⋂ i, f i) = ⋂ i, Interior (f i) := by
  convert finset.univ.interior_Inter f <;> simp

theorem interior_union_is_closed_of_interior_empty {s t : Set α} (h₁ : IsClosed s) (h₂ : Interior t = ∅) :
    Interior (s ∪ t) = Interior s :=
  have : Interior (s ∪ t) ⊆ s := fun x ⟨u, ⟨(hu₁ : IsOpen u), (hu₂ : u ⊆ s ∪ t)⟩, (hx₁ : x ∈ u)⟩ =>
    Classical.by_contradiction fun hx₂ : x ∉ s =>
      have : u \ s ⊆ t := fun x ⟨h₁, h₂⟩ => Or.resolve_left (hu₂ h₁) h₂
      have : u \ s ⊆ Interior t := by
        rwa [subset_interior_iff_subset_of_open (IsOpen.sdiff hu₁ h₁)]
      have : u \ s ⊆ ∅ := by
        rwa [h₂] at this
      this ⟨hx₁, hx₂⟩
  Subset.antisymm (interior_maximal this is_open_interior) (interior_mono <| subset_union_left _ _)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem is_open_iff_forall_mem_open : IsOpen s ↔ ∀, ∀ x ∈ s, ∀, ∃ (t : _)(_ : t ⊆ s), IsOpen t ∧ x ∈ t := by
  rw [← subset_interior_iff_open] <;> simp only [← subset_def, ← mem_interior]

theorem interior_Inter_subset (s : ι → Set α) : Interior (⋂ i, s i) ⊆ ⋂ i, Interior (s i) :=
  subset_Inter fun i => interior_mono <| Inter_subset _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem interior_Inter₂_subset (p : ι → Sort _) (s : ∀ i, p i → Set α) :
    Interior (⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), Interior (s i j) :=
  (interior_Inter_subset _).trans <| Inter_mono fun i => interior_Inter_subset _

theorem interior_sInter_subset (S : Set (Set α)) : Interior (⋂₀ S) ⊆ ⋂ s ∈ S, Interior s :=
  calc
    Interior (⋂₀ S) = Interior (⋂ s ∈ S, s) := by
      rw [sInter_eq_bInter]
    _ ⊆ ⋂ s ∈ S, Interior s := interior_Inter₂_subset _ _
    

/-!
### Closure of a set
-/


/-- The closure of `s` is the smallest closed set containing `s`. -/
def Closure (s : Set α) : Set α :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }

@[simp]
theorem is_closed_closure {s : Set α} : IsClosed (Closure s) :=
  is_closed_sInter fun t ⟨h₁, h₂⟩ => h₁

theorem subset_closure {s : Set α} : s ⊆ Closure s :=
  subset_sInter fun t ⟨h₁, h₂⟩ => h₂

theorem not_mem_of_not_mem_closure {s : Set α} {P : α} (hP : P ∉ Closure s) : P ∉ s := fun h => hP (subset_closure h)

theorem closure_minimal {s t : Set α} (h₁ : s ⊆ t) (h₂ : IsClosed t) : Closure s ⊆ t :=
  sInter_subset_of_mem ⟨h₂, h₁⟩

theorem Disjoint.closure_left {s t : Set α} (hd : Disjoint s t) (ht : IsOpen t) : Disjoint (Closure s) t :=
  disjoint_compl_left.mono_left <| closure_minimal hd.subset_compl_right ht.is_closed_compl

theorem Disjoint.closure_right {s t : Set α} (hd : Disjoint s t) (hs : IsOpen s) : Disjoint s (Closure t) :=
  (hd.symm.closure_left hs).symm

theorem IsClosed.closure_eq {s : Set α} (h : IsClosed s) : Closure s = s :=
  Subset.antisymm (closure_minimal (Subset.refl s) h) subset_closure

theorem IsClosed.closure_subset {s : Set α} (hs : IsClosed s) : Closure s ⊆ s :=
  closure_minimal (Subset.refl _) hs

theorem IsClosed.closure_subset_iff {s t : Set α} (h₁ : IsClosed t) : Closure s ⊆ t ↔ s ⊆ t :=
  ⟨Subset.trans subset_closure, fun h => closure_minimal h h₁⟩

theorem IsClosed.mem_iff_closure_subset {α : Type _} [TopologicalSpace α] {U : Set α} (hU : IsClosed U) {x : α} :
    x ∈ U ↔ Closure ({x} : Set α) ⊆ U :=
  (hU.closure_subset_iff.trans Set.singleton_subset_iff).symm

@[mono]
theorem closure_mono {s t : Set α} (h : s ⊆ t) : Closure s ⊆ Closure t :=
  closure_minimal (Subset.trans h subset_closure) is_closed_closure

theorem monotone_closure (α : Type _) [TopologicalSpace α] : Monotone (@Closure α _) := fun _ _ => closure_mono

theorem diff_subset_closure_iff {s t : Set α} : s \ t ⊆ Closure t ↔ s ⊆ Closure t := by
  rw [diff_subset_iff, union_eq_self_of_subset_left subset_closure]

theorem closure_inter_subset_inter_closure (s t : Set α) : Closure (s ∩ t) ⊆ Closure s ∩ Closure t :=
  (monotone_closure α).map_inf_le s t

theorem is_closed_of_closure_subset {s : Set α} (h : Closure s ⊆ s) : IsClosed s := by
  rw [subset.antisymm subset_closure h] <;> exact is_closed_closure

theorem closure_eq_iff_is_closed {s : Set α} : Closure s = s ↔ IsClosed s :=
  ⟨fun h => h ▸ is_closed_closure, IsClosed.closure_eq⟩

theorem closure_subset_iff_is_closed {s : Set α} : Closure s ⊆ s ↔ IsClosed s :=
  ⟨is_closed_of_closure_subset, IsClosed.closure_subset⟩

@[simp]
theorem closure_empty : Closure (∅ : Set α) = ∅ :=
  is_closed_empty.closure_eq

@[simp]
theorem closure_empty_iff (s : Set α) : Closure s = ∅ ↔ s = ∅ :=
  ⟨subset_eq_empty subset_closure, fun h => h.symm ▸ closure_empty⟩

@[simp]
theorem closure_nonempty_iff {s : Set α} : (Closure s).Nonempty ↔ s.Nonempty := by
  simp only [ne_empty_iff_nonempty, ← Ne.def, ← closure_empty_iff]

alias closure_nonempty_iff ↔ Set.Nonempty.of_closure Set.Nonempty.closure

@[simp]
theorem closure_univ : Closure (Univ : Set α) = univ :=
  is_closed_univ.closure_eq

@[simp]
theorem closure_closure {s : Set α} : Closure (Closure s) = Closure s :=
  is_closed_closure.closure_eq

@[simp]
theorem closure_union {s t : Set α} : Closure (s ∪ t) = Closure s ∪ Closure t :=
  Subset.antisymm
    (closure_minimal (union_subset_union subset_closure subset_closure) <|
      IsClosed.union is_closed_closure is_closed_closure)
    ((monotone_closure α).le_map_sup s t)

@[simp]
theorem Finset.closure_bUnion {ι : Type _} (s : Finset ι) (f : ι → Set α) :
    Closure (⋃ i ∈ s, f i) = ⋃ i ∈ s, Closure (f i) := by
  classical
  refine'
    s.induction_on
      (by
        simp )
      _
  intro i s h₁ h₂
  simp [← h₂]

@[simp]
theorem closure_Union_of_fintype {ι : Type _} [Fintype ι] (f : ι → Set α) : Closure (⋃ i, f i) = ⋃ i, Closure (f i) :=
  by
  convert finset.univ.closure_bUnion f <;> simp

theorem interior_subset_closure {s : Set α} : Interior s ⊆ Closure s :=
  Subset.trans interior_subset subset_closure

theorem closure_eq_compl_interior_compl {s : Set α} : Closure s = Interior (sᶜ)ᶜ := by
  rw [Interior, Closure, compl_sUnion, compl_image_set_of]
  simp only [← compl_subset_compl, ← is_open_compl_iff]

@[simp]
theorem interior_compl {s : Set α} : Interior (sᶜ) = Closure sᶜ := by
  simp [← closure_eq_compl_interior_compl]

@[simp]
theorem closure_compl {s : Set α} : Closure (sᶜ) = Interior sᶜ := by
  simp [← closure_eq_compl_interior_compl]

theorem mem_closure_iff {s : Set α} {a : α} : a ∈ Closure s ↔ ∀ o, IsOpen o → a ∈ o → (o ∩ s).Nonempty :=
  ⟨fun h o oo ao =>
    Classical.by_contradiction fun os =>
      have : s ⊆ oᶜ := fun x xs xo => os ⟨x, xo, xs⟩
      closure_minimal this (is_closed_compl_iff.2 oo) h ao,
    fun H c ⟨h₁, h₂⟩ =>
    Classical.by_contradiction fun nc =>
      let ⟨x, hc, hs⟩ := H _ h₁.is_open_compl nc
      hc (h₂ hs)⟩

/-- A set is dense in a topological space if every point belongs to its closure. -/
def Dense (s : Set α) : Prop :=
  ∀ x, x ∈ Closure s

theorem dense_iff_closure_eq {s : Set α} : Dense s ↔ Closure s = univ :=
  eq_univ_iff_forall.symm

theorem Dense.closure_eq {s : Set α} (h : Dense s) : Closure s = univ :=
  dense_iff_closure_eq.mp h

theorem interior_eq_empty_iff_dense_compl {s : Set α} : Interior s = ∅ ↔ Dense (sᶜ) := by
  rw [dense_iff_closure_eq, closure_compl, compl_univ_iff]

theorem Dense.interior_compl {s : Set α} (h : Dense s) : Interior (sᶜ) = ∅ :=
  interior_eq_empty_iff_dense_compl.2 <| by
    rwa [compl_compl]

/-- The closure of a set `s` is dense if and only if `s` is dense. -/
@[simp]
theorem dense_closure {s : Set α} : Dense (Closure s) ↔ Dense s := by
  rw [Dense, Dense, closure_closure]

alias dense_closure ↔ Dense.of_closure Dense.closure

@[simp]
theorem dense_univ : Dense (Univ : Set α) := fun x => subset_closure trivialₓ

/-- A set is dense if and only if it has a nonempty intersection with each nonempty open set. -/
theorem dense_iff_inter_open {s : Set α} : Dense s ↔ ∀ U, IsOpen U → U.Nonempty → (U ∩ s).Nonempty := by
  constructor <;> intro h
  · rintro U U_op ⟨x, x_in⟩
    exact
      mem_closure_iff.1
        (by
          simp only [← h.closure_eq])
        U U_op x_in
    
  · intro x
    rw [mem_closure_iff]
    intro U U_op x_in
    exact h U U_op ⟨_, x_in⟩
    

alias dense_iff_inter_open ↔ Dense.inter_open_nonempty _

theorem Dense.exists_mem_open {s : Set α} (hs : Dense s) {U : Set α} (ho : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ s, x ∈ U :=
  let ⟨x, hx⟩ := hs.inter_open_nonempty U ho hne
  ⟨x, hx.2, hx.1⟩

theorem Dense.nonempty_iff {s : Set α} (hs : Dense s) : s.Nonempty ↔ Nonempty α :=
  ⟨fun ⟨x, hx⟩ => ⟨x⟩, fun ⟨x⟩ =>
    let ⟨y, hy⟩ := hs.inter_open_nonempty _ is_open_univ ⟨x, trivialₓ⟩
    ⟨y, hy.2⟩⟩

theorem Dense.nonempty [h : Nonempty α] {s : Set α} (hs : Dense s) : s.Nonempty :=
  hs.nonempty_iff.2 h

@[mono]
theorem Dense.mono {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) (hd : Dense s₁) : Dense s₂ := fun x => closure_mono h (hd x)

/-- Complement to a singleton is dense if and only if the singleton is not an open set. -/
theorem dense_compl_singleton_iff_not_open {x : α} : Dense ({x}ᶜ : Set α) ↔ ¬IsOpen ({x} : Set α) := by
  fconstructor
  · intro hd ho
    exact (hd.inter_open_nonempty _ ho (singleton_nonempty _)).ne_empty (inter_compl_self _)
    
  · refine' fun ho => dense_iff_inter_open.2 fun U hU hne => inter_compl_nonempty_iff.2 fun hUx => _
    obtain rfl : U = {x}
    exact eq_singleton_iff_nonempty_unique_mem.2 ⟨hne, hUx⟩
    exact ho hU
    

/-!
### Frontier of a set
-/


/-- The frontier of a set is the set of points between the closure and interior. -/
def Frontier (s : Set α) : Set α :=
  Closure s \ Interior s

@[simp]
theorem closure_diff_interior (s : Set α) : Closure s \ Interior s = Frontier s :=
  rfl

@[simp]
theorem closure_diff_frontier (s : Set α) : Closure s \ Frontier s = Interior s := by
  rw [Frontier, diff_diff_right_self, inter_eq_self_of_subset_right interior_subset_closure]

@[simp]
theorem self_diff_frontier (s : Set α) : s \ Frontier s = Interior s := by
  rw [Frontier, diff_diff_right, diff_eq_empty.2 subset_closure, inter_eq_self_of_subset_right interior_subset,
    empty_union]

theorem frontier_eq_closure_inter_closure {s : Set α} : Frontier s = Closure s ∩ Closure (sᶜ) := by
  rw [closure_compl, Frontier, diff_eq]

theorem frontier_subset_closure {s : Set α} : Frontier s ⊆ Closure s :=
  diff_subset _ _

theorem IsClosed.frontier_subset (hs : IsClosed s) : Frontier s ⊆ s :=
  frontier_subset_closure.trans hs.closure_eq.Subset

theorem frontier_closure_subset {s : Set α} : Frontier (Closure s) ⊆ Frontier s :=
  diff_subset_diff closure_closure.Subset <| interior_mono subset_closure

theorem frontier_interior_subset {s : Set α} : Frontier (Interior s) ⊆ Frontier s :=
  diff_subset_diff (closure_mono interior_subset) interior_interior.symm.Subset

/-- The complement of a set has the same frontier as the original set. -/
@[simp]
theorem frontier_compl (s : Set α) : Frontier (sᶜ) = Frontier s := by
  simp only [← frontier_eq_closure_inter_closure, ← compl_compl, ← inter_comm]

@[simp]
theorem frontier_univ : Frontier (Univ : Set α) = ∅ := by
  simp [← Frontier]

@[simp]
theorem frontier_empty : Frontier (∅ : Set α) = ∅ := by
  simp [← Frontier]

theorem frontier_inter_subset (s t : Set α) : Frontier (s ∩ t) ⊆ Frontier s ∩ Closure t ∪ Closure s ∩ Frontier t := by
  simp only [← frontier_eq_closure_inter_closure, ← compl_inter, ← closure_union]
  convert inter_subset_inter_left _ (closure_inter_subset_inter_closure s t)
  simp only [← inter_distrib_left, ← inter_distrib_right, ← inter_assoc]
  congr 2
  apply inter_comm

theorem frontier_union_subset (s t : Set α) :
    Frontier (s ∪ t) ⊆ Frontier s ∩ Closure (tᶜ) ∪ Closure (sᶜ) ∩ Frontier t := by
  simpa only [← frontier_compl, compl_union] using frontier_inter_subset (sᶜ) (tᶜ)

theorem IsClosed.frontier_eq {s : Set α} (hs : IsClosed s) : Frontier s = s \ Interior s := by
  rw [Frontier, hs.closure_eq]

theorem IsOpen.frontier_eq {s : Set α} (hs : IsOpen s) : Frontier s = Closure s \ s := by
  rw [Frontier, hs.interior_eq]

theorem IsOpen.inter_frontier_eq {s : Set α} (hs : IsOpen s) : s ∩ Frontier s = ∅ := by
  rw [hs.frontier_eq, inter_diff_self]

/-- The frontier of a set is closed. -/
theorem is_closed_frontier {s : Set α} : IsClosed (Frontier s) := by
  rw [frontier_eq_closure_inter_closure] <;> exact IsClosed.inter is_closed_closure is_closed_closure

/-- The frontier of a closed set has no interior point. -/
theorem interior_frontier {s : Set α} (h : IsClosed s) : Interior (Frontier s) = ∅ := by
  have A : Frontier s = s \ Interior s := h.frontier_eq
  have B : Interior (Frontier s) ⊆ Interior s := by
    rw [A] <;> exact interior_mono (diff_subset _ _)
  have C : Interior (Frontier s) ⊆ Frontier s := interior_subset
  have : Interior (Frontier s) ⊆ Interior s ∩ (s \ Interior s) :=
    subset_inter B
      (by
        simpa [← A] using C)
  rwa [inter_diff_self, subset_empty_iff] at this

theorem closure_eq_interior_union_frontier (s : Set α) : Closure s = Interior s ∪ Frontier s :=
  (union_diff_cancel interior_subset_closure).symm

theorem closure_eq_self_union_frontier (s : Set α) : Closure s = s ∪ Frontier s :=
  (union_diff_cancel' interior_subset subset_closure).symm

theorem Disjoint.frontier_left (ht : IsOpen t) (hd : Disjoint s t) : Disjoint (Frontier s) t :=
  subset_compl_iff_disjoint_right.1 <|
    frontier_subset_closure.trans <| closure_minimal (disjoint_left.1 hd) <| is_closed_compl_iff.2 ht

theorem Disjoint.frontier_right (hs : IsOpen s) (hd : Disjoint s t) : Disjoint s (Frontier t) :=
  (hd.symm.frontier_left hs).symm

theorem frontier_eq_inter_compl_interior {s : Set α} : Frontier s = Interior sᶜ ∩ Interior (sᶜ)ᶜ := by
  rw [← frontier_compl, ← closure_compl]
  rfl

theorem compl_frontier_eq_union_interior {s : Set α} : Frontier sᶜ = Interior s ∪ Interior (sᶜ) := by
  rw [frontier_eq_inter_compl_interior]
  simp only [← compl_inter, ← compl_compl]

/-!
### Neighborhoods
-/


/-- A set is called a neighborhood of `a` if it contains an open set around `a`. The set of all
neighborhoods of `a` forms a filter, the neighborhood filter at `a`, is here defined as the
infimum over the principal filters of all open sets containing `a`. -/
irreducible_def nhds (a : α) : Filter α :=
  ⨅ s ∈ { s : Set α | a ∈ s ∧ IsOpen s }, 𝓟 s

-- mathport name: «expr𝓝»
localized [TopologicalSpace] notation "𝓝" => nhds

/-- The "neighborhood within" filter. Elements of `𝓝[s] a` are sets containing the
intersection of `s` and a neighborhood of `a`. -/
def nhdsWithin (a : α) (s : Set α) : Filter α :=
  𝓝 a⊓𝓟 s

-- mathport name: «expr𝓝[ ] »
localized [TopologicalSpace] notation "𝓝[" s "] " x:100 => nhdsWithin x s

-- mathport name: «expr𝓝[≠] »
localized [TopologicalSpace] notation "𝓝[≠] " x:100 => nhdsWithin x ({x}ᶜ)

-- mathport name: «expr𝓝[≥] »
localized [TopologicalSpace] notation "𝓝[≥] " x:100 => nhdsWithin x (Set.Ici x)

-- mathport name: «expr𝓝[≤] »
localized [TopologicalSpace] notation "𝓝[≤] " x:100 => nhdsWithin x (Set.Iic x)

-- mathport name: «expr𝓝[>] »
localized [TopologicalSpace] notation "𝓝[>] " x:100 => nhdsWithin x (Set.Ioi x)

-- mathport name: «expr𝓝[<] »
localized [TopologicalSpace] notation "𝓝[<] " x:100 => nhdsWithin x (Set.Iio x)

theorem nhds_def (a : α) : 𝓝 a = ⨅ s ∈ { s : Set α | a ∈ s ∧ IsOpen s }, 𝓟 s := by
  rw [nhds]

theorem nhds_def' (a : α) : 𝓝 a = ⨅ (s : Set α) (hs : IsOpen s) (ha : a ∈ s), 𝓟 s := by
  simp only [← nhds_def, ← mem_set_of_eq, ← and_comm (a ∈ _), ← infi_and]

/-- The open sets containing `a` are a basis for the neighborhood filter. See `nhds_basis_opens'`
for a variant using open neighborhoods instead. -/
theorem nhds_basis_opens (a : α) : (𝓝 a).HasBasis (fun s : Set α => a ∈ s ∧ IsOpen s) fun s => s := by
  rw [nhds_def]
  exact
    has_basis_binfi_principal
      (fun s ⟨has, hs⟩ t ⟨hat, ht⟩ =>
        ⟨s ∩ t, ⟨⟨has, hat⟩, IsOpen.inter hs ht⟩, ⟨inter_subset_left _ _, inter_subset_right _ _⟩⟩)
      ⟨univ, ⟨mem_univ a, is_open_univ⟩⟩

theorem nhds_basis_closeds (a : α) : (𝓝 a).HasBasis (fun s : Set α => a ∉ s ∧ IsClosed s) compl :=
  ⟨fun t =>
    (nhds_basis_opens a).mem_iff.trans <|
      compl_surjective.exists.trans <| by
        simp only [← is_open_compl_iff, ← mem_compl_iff]⟩

/-- A filter lies below the neighborhood filter at `a` iff it contains every open set around `a`. -/
theorem le_nhds_iff {f a} : f ≤ 𝓝 a ↔ ∀ s : Set α, a ∈ s → IsOpen s → s ∈ f := by
  simp [← nhds_def]

/-- To show a filter is above the neighborhood filter at `a`, it suffices to show that it is above
the principal filter of some open set `s` containing `a`. -/
theorem nhds_le_of_le {f a} {s : Set α} (h : a ∈ s) (o : IsOpen s) (sf : 𝓟 s ≤ f) : 𝓝 a ≤ f := by
  rw [nhds_def] <;> exact infi_le_of_le s (infi_le_of_le ⟨h, o⟩ sf)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem mem_nhds_iff {a : α} {s : Set α} : s ∈ 𝓝 a ↔ ∃ (t : _)(_ : t ⊆ s), IsOpen t ∧ a ∈ t :=
  (nhds_basis_opens a).mem_iff.trans
    ⟨fun ⟨t, ⟨hat, ht⟩, hts⟩ => ⟨t, hts, ht, hat⟩, fun ⟨t, hts, ht, hat⟩ => ⟨t, ⟨hat, ht⟩, hts⟩⟩

/-- A predicate is true in a neighborhood of `a` iff it is true for all the points in an open set
containing `a`. -/
theorem eventually_nhds_iff {a : α} {p : α → Prop} :
    (∀ᶠ x in 𝓝 a, p x) ↔ ∃ t : Set α, (∀, ∀ x ∈ t, ∀, p x) ∧ IsOpen t ∧ a ∈ t :=
  mem_nhds_iff.trans <| by
    simp only [← subset_def, ← exists_prop, ← mem_set_of_eq]

theorem map_nhds {a : α} {f : α → β} : map f (𝓝 a) = ⨅ s ∈ { s : Set α | a ∈ s ∧ IsOpen s }, 𝓟 (Image f s) :=
  ((nhds_basis_opens a).map f).eq_binfi

theorem mem_of_mem_nhds {a : α} {s : Set α} : s ∈ 𝓝 a → a ∈ s := fun H =>
  let ⟨t, ht, _, hs⟩ := mem_nhds_iff.1 H
  ht hs

/-- If a predicate is true in a neighborhood of `a`, then it is true for `a`. -/
theorem Filter.Eventually.self_of_nhds {p : α → Prop} {a : α} (h : ∀ᶠ y in 𝓝 a, p y) : p a :=
  mem_of_mem_nhds h

theorem IsOpen.mem_nhds {a : α} {s : Set α} (hs : IsOpen s) (ha : a ∈ s) : s ∈ 𝓝 a :=
  mem_nhds_iff.2 ⟨s, Subset.refl _, hs, ha⟩

theorem IsOpen.mem_nhds_iff {a : α} {s : Set α} (hs : IsOpen s) : s ∈ 𝓝 a ↔ a ∈ s :=
  ⟨mem_of_mem_nhds, fun ha => mem_nhds_iff.2 ⟨s, Subset.refl _, hs, ha⟩⟩

theorem IsClosed.compl_mem_nhds {a : α} {s : Set α} (hs : IsClosed s) (ha : a ∉ s) : sᶜ ∈ 𝓝 a :=
  hs.is_open_compl.mem_nhds (mem_compl ha)

theorem IsOpen.eventually_mem {a : α} {s : Set α} (hs : IsOpen s) (ha : a ∈ s) : ∀ᶠ x in 𝓝 a, x ∈ s :=
  IsOpen.mem_nhds hs ha

/-- The open neighborhoods of `a` are a basis for the neighborhood filter. See `nhds_basis_opens`
for a variant using open sets around `a` instead. -/
theorem nhds_basis_opens' (a : α) : (𝓝 a).HasBasis (fun s : Set α => s ∈ 𝓝 a ∧ IsOpen s) fun x => x := by
  convert nhds_basis_opens a
  ext s
  exact And.congr_left_iff.2 IsOpen.mem_nhds_iff

/-- If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of `s`:
it contains an open set containing `s`. -/
theorem exists_open_set_nhds {s U : Set α} (h : ∀, ∀ x ∈ s, ∀, U ∈ 𝓝 x) : ∃ V : Set α, s ⊆ V ∧ IsOpen V ∧ V ⊆ U := by
  have := fun x hx => (nhds_basis_opens x).mem_iff.1 (h x hx)
  choose! Z hZ hZU using this
  choose hZmem hZo using hZ
  exact ⟨⋃ x ∈ s, Z x, fun x hx => mem_bUnion hx (hZmem x hx), is_open_bUnion hZo, Union₂_subset hZU⟩

/-- If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of s:
it contains an open set containing `s`. -/
theorem exists_open_set_nhds' {s U : Set α} (h : U ∈ ⨆ x ∈ s, 𝓝 x) : ∃ V : Set α, s ⊆ V ∧ IsOpen V ∧ V ⊆ U :=
  exists_open_set_nhds
    (by
      simpa using h)

/-- If a predicate is true in a neighbourhood of `a`, then for `y` sufficiently close
to `a` this predicate is true in a neighbourhood of `y`. -/
theorem Filter.Eventually.eventually_nhds {p : α → Prop} {a : α} (h : ∀ᶠ y in 𝓝 a, p y) :
    ∀ᶠ y in 𝓝 a, ∀ᶠ x in 𝓝 y, p x :=
  let ⟨t, htp, hto, ha⟩ := eventually_nhds_iff.1 h
  eventually_nhds_iff.2 ⟨t, fun x hx => eventually_nhds_iff.2 ⟨t, htp, hto, hx⟩, hto, ha⟩

@[simp]
theorem eventually_eventually_nhds {p : α → Prop} {a : α} : (∀ᶠ y in 𝓝 a, ∀ᶠ x in 𝓝 y, p x) ↔ ∀ᶠ x in 𝓝 a, p x :=
  ⟨fun h => h.self_of_nhds, fun h => h.eventually_nhds⟩

@[simp]
theorem eventually_mem_nhds {s : Set α} {a : α} : (∀ᶠ x in 𝓝 a, s ∈ 𝓝 x) ↔ s ∈ 𝓝 a :=
  eventually_eventually_nhds

@[simp]
theorem nhds_bind_nhds : (𝓝 a).bind 𝓝 = 𝓝 a :=
  Filter.ext fun s => eventually_eventually_nhds

@[simp]
theorem eventually_eventually_eq_nhds {f g : α → β} {a : α} : (∀ᶠ y in 𝓝 a, f =ᶠ[𝓝 y] g) ↔ f =ᶠ[𝓝 a] g :=
  eventually_eventually_nhds

theorem Filter.EventuallyEq.eq_of_nhds {f g : α → β} {a : α} (h : f =ᶠ[𝓝 a] g) : f a = g a :=
  h.self_of_nhds

@[simp]
theorem eventually_eventually_le_nhds [LE β] {f g : α → β} {a : α} : (∀ᶠ y in 𝓝 a, f ≤ᶠ[𝓝 y] g) ↔ f ≤ᶠ[𝓝 a] g :=
  eventually_eventually_nhds

/-- If two functions are equal in a neighbourhood of `a`, then for `y` sufficiently close
to `a` these functions are equal in a neighbourhood of `y`. -/
theorem Filter.EventuallyEq.eventually_eq_nhds {f g : α → β} {a : α} (h : f =ᶠ[𝓝 a] g) : ∀ᶠ y in 𝓝 a, f =ᶠ[𝓝 y] g :=
  h.eventually_nhds

/-- If `f x ≤ g x` in a neighbourhood of `a`, then for `y` sufficiently close to `a` we have
`f x ≤ g x` in a neighbourhood of `y`. -/
theorem Filter.EventuallyLe.eventually_le_nhds [LE β] {f g : α → β} {a : α} (h : f ≤ᶠ[𝓝 a] g) :
    ∀ᶠ y in 𝓝 a, f ≤ᶠ[𝓝 y] g :=
  h.eventually_nhds

theorem all_mem_nhds (x : α) (P : Set α → Prop) (hP : ∀ s t, s ⊆ t → P s → P t) :
    (∀, ∀ s ∈ 𝓝 x, ∀, P s) ↔ ∀ s, IsOpen s → x ∈ s → P s :=
  ((nhds_basis_opens x).forall_iff hP).trans <| by
    simp only [← and_comm (x ∈ _), ← and_imp]

theorem all_mem_nhds_filter (x : α) (f : Set α → Set β) (hf : ∀ s t, s ⊆ t → f s ⊆ f t) (l : Filter β) :
    (∀, ∀ s ∈ 𝓝 x, ∀, f s ∈ l) ↔ ∀ s, IsOpen s → x ∈ s → f s ∈ l :=
  all_mem_nhds _ _ fun s t ssubt h => mem_of_superset h (hf s t ssubt)

theorem rtendsto_nhds {r : Rel β α} {l : Filter β} {a : α} :
    Rtendsto r l (𝓝 a) ↔ ∀ s, IsOpen s → a ∈ s → r.Core s ∈ l :=
  all_mem_nhds_filter _ _ (fun s t => id) _

theorem rtendsto'_nhds {r : Rel β α} {l : Filter β} {a : α} :
    Rtendsto' r l (𝓝 a) ↔ ∀ s, IsOpen s → a ∈ s → r.Preimage s ∈ l := by
  rw [rtendsto'_def]
  apply all_mem_nhds_filter
  apply Rel.preimage_mono

theorem ptendsto_nhds {f : β →. α} {l : Filter β} {a : α} : Ptendsto f l (𝓝 a) ↔ ∀ s, IsOpen s → a ∈ s → f.Core s ∈ l :=
  rtendsto_nhds

theorem ptendsto'_nhds {f : β →. α} {l : Filter β} {a : α} :
    Ptendsto' f l (𝓝 a) ↔ ∀ s, IsOpen s → a ∈ s → f.Preimage s ∈ l :=
  rtendsto'_nhds

theorem tendsto_nhds {f : β → α} {l : Filter β} {a : α} : Tendsto f l (𝓝 a) ↔ ∀ s, IsOpen s → a ∈ s → f ⁻¹' s ∈ l :=
  all_mem_nhds_filter _ _ (fun s t h => preimage_mono h) _

theorem tendsto_at_top_nhds [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} :
    Tendsto f atTop (𝓝 a) ↔ ∀ U : Set α, a ∈ U → IsOpen U → ∃ N, ∀ n, N ≤ n → f n ∈ U :=
  (at_top_basis.tendsto_iff (nhds_basis_opens a)).trans <| by
    simp only [← and_imp, ← exists_prop, ← true_andₓ, ← mem_Ici, ← ge_iff_le]

theorem tendsto_const_nhds {a : α} {f : Filter β} : Tendsto (fun b : β => a) f (𝓝 a) :=
  tendsto_nhds.mpr fun s hs ha => univ_mem' fun _ => ha

theorem tendsto_at_top_of_eventually_const {ι : Type _} [SemilatticeSup ι] [Nonempty ι] {x : α} {u : ι → α} {i₀ : ι}
    (h : ∀, ∀ i ≥ i₀, ∀, u i = x) : Tendsto u atTop (𝓝 x) :=
  Tendsto.congr' (EventuallyEq.symm (eventually_at_top.mpr ⟨i₀, h⟩)) tendsto_const_nhds

theorem tendsto_at_bot_of_eventually_const {ι : Type _} [SemilatticeInf ι] [Nonempty ι] {x : α} {u : ι → α} {i₀ : ι}
    (h : ∀, ∀ i ≤ i₀, ∀, u i = x) : Tendsto u atBot (𝓝 x) :=
  Tendsto.congr' (EventuallyEq.symm (eventually_at_bot.mpr ⟨i₀, h⟩)) tendsto_const_nhds

theorem pure_le_nhds : pure ≤ (𝓝 : α → Filter α) := fun a s hs => mem_pure.2 <| mem_of_mem_nhds hs

theorem tendsto_pure_nhds {α : Type _} [TopologicalSpace β] (f : α → β) (a : α) : Tendsto f (pure a) (𝓝 (f a)) :=
  (tendsto_pure_pure f a).mono_right (pure_le_nhds _)

theorem OrderTop.tendsto_at_top_nhds {α : Type _} [PartialOrderₓ α] [OrderTop α] [TopologicalSpace β] (f : α → β) :
    Tendsto f atTop (𝓝 <| f ⊤) :=
  (tendsto_at_top_pure f).mono_right (pure_le_nhds _)

@[simp]
instance nhds_ne_bot {a : α} : NeBot (𝓝 a) :=
  ne_bot_of_le (pure_le_nhds a)

/-!
### Cluster points

In this section we define [cluster points](https://en.wikipedia.org/wiki/Limit_point)
(also known as limit points and accumulation points) of a filter and of a sequence.
-/


/-- A point `x` is a cluster point of a filter `F` if 𝓝 x ⊓ F ≠ ⊥. Also known as
an accumulation point or a limit point. -/
def ClusterPt (x : α) (F : Filter α) : Prop :=
  NeBot (𝓝 x⊓F)

theorem ClusterPt.ne_bot {x : α} {F : Filter α} (h : ClusterPt x F) : NeBot (𝓝 x⊓F) :=
  h

theorem Filter.HasBasis.cluster_pt_iff {ιa ιF} {pa : ιa → Prop} {sa : ιa → Set α} {pF : ιF → Prop} {sF : ιF → Set α}
    {F : Filter α} (ha : (𝓝 a).HasBasis pa sa) (hF : F.HasBasis pF sF) :
    ClusterPt a F ↔ ∀ ⦃i⦄ (hi : pa i) ⦃j⦄ (hj : pF j), (sa i ∩ sF j).Nonempty :=
  ha.inf_basis_ne_bot_iff hF

theorem cluster_pt_iff {x : α} {F : Filter α} :
    ClusterPt x F ↔ ∀ ⦃U : Set α⦄ (hU : U ∈ 𝓝 x) ⦃V⦄ (hV : V ∈ F), (U ∩ V).Nonempty :=
  inf_ne_bot_iff

/-- `x` is a cluster point of a set `s` if every neighbourhood of `x` meets `s` on a nonempty
set. -/
theorem cluster_pt_principal_iff {x : α} {s : Set α} : ClusterPt x (𝓟 s) ↔ ∀, ∀ U ∈ 𝓝 x, ∀, (U ∩ s).Nonempty :=
  inf_principal_ne_bot_iff

theorem cluster_pt_principal_iff_frequently {x : α} {s : Set α} : ClusterPt x (𝓟 s) ↔ ∃ᶠ y in 𝓝 x, y ∈ s := by
  simp only [← cluster_pt_principal_iff, ← frequently_iff, ← Set.Nonempty, ← exists_prop, ← mem_inter_iff]

theorem ClusterPt.of_le_nhds {x : α} {f : Filter α} (H : f ≤ 𝓝 x) [NeBot f] : ClusterPt x f := by
  rwa [ClusterPt, inf_eq_right.mpr H]

theorem ClusterPt.of_le_nhds' {x : α} {f : Filter α} (H : f ≤ 𝓝 x) (hf : NeBot f) : ClusterPt x f :=
  ClusterPt.of_le_nhds H

theorem ClusterPt.of_nhds_le {x : α} {f : Filter α} (H : 𝓝 x ≤ f) : ClusterPt x f := by
  simp only [← ClusterPt, ← inf_eq_left.mpr H, ← nhds_ne_bot]

theorem ClusterPt.mono {x : α} {f g : Filter α} (H : ClusterPt x f) (h : f ≤ g) : ClusterPt x g :=
  ⟨ne_bot_of_le_ne_bot H.Ne <| inf_le_inf_left _ h⟩

theorem ClusterPt.of_inf_left {x : α} {f g : Filter α} (H : ClusterPt x <| f⊓g) : ClusterPt x f :=
  H.mono inf_le_left

theorem ClusterPt.of_inf_right {x : α} {f g : Filter α} (H : ClusterPt x <| f⊓g) : ClusterPt x g :=
  H.mono inf_le_right

theorem Ultrafilter.cluster_pt_iff {x : α} {f : Ultrafilter α} : ClusterPt x f ↔ ↑f ≤ 𝓝 x :=
  ⟨f.le_of_inf_ne_bot', fun h => ClusterPt.of_le_nhds h⟩

/-- A point `x` is a cluster point of a sequence `u` along a filter `F` if it is a cluster point
of `map u F`. -/
def MapClusterPt {ι : Type _} (x : α) (F : Filter ι) (u : ι → α) : Prop :=
  ClusterPt x (map u F)

theorem map_cluster_pt_iff {ι : Type _} (x : α) (F : Filter ι) (u : ι → α) :
    MapClusterPt x F u ↔ ∀, ∀ s ∈ 𝓝 x, ∀, ∃ᶠ a in F, u a ∈ s := by
  simp_rw [MapClusterPt, ClusterPt, inf_ne_bot_iff_frequently_left, frequently_map]
  rfl

theorem map_cluster_pt_of_comp {ι δ : Type _} {F : Filter ι} {φ : δ → ι} {p : Filter δ} {x : α} {u : ι → α} [NeBot p]
    (h : Tendsto φ p F) (H : Tendsto (u ∘ φ) p (𝓝 x)) : MapClusterPt x F u := by
  have :=
    calc
      map (u ∘ φ) p = map u (map φ p) := map_map
      _ ≤ map u F := map_mono h
      
  have : map (u ∘ φ) p ≤ 𝓝 x⊓map u F := le_inf H this
  exact ne_bot_of_le this

/-!
### Interior, closure and frontier in terms of neighborhoods
-/


theorem interior_eq_nhds' {s : Set α} : Interior s = { a | s ∈ 𝓝 a } :=
  Set.ext fun x => by
    simp only [← mem_interior, ← mem_nhds_iff, ← mem_set_of_eq]

theorem interior_eq_nhds {s : Set α} : Interior s = { a | 𝓝 a ≤ 𝓟 s } :=
  interior_eq_nhds'.trans <| by
    simp only [← le_principal_iff]

theorem mem_interior_iff_mem_nhds {s : Set α} {a : α} : a ∈ Interior s ↔ s ∈ 𝓝 a := by
  rw [interior_eq_nhds', mem_set_of_eq]

@[simp]
theorem interior_mem_nhds {s : Set α} {a : α} : Interior s ∈ 𝓝 a ↔ s ∈ 𝓝 a :=
  ⟨fun h => mem_of_superset h interior_subset, fun h =>
    IsOpen.mem_nhds is_open_interior (mem_interior_iff_mem_nhds.2 h)⟩

theorem interior_set_of_eq {p : α → Prop} : Interior { x | p x } = { x | ∀ᶠ y in 𝓝 x, p y } :=
  interior_eq_nhds'

theorem is_open_set_of_eventually_nhds {p : α → Prop} : IsOpen { x | ∀ᶠ y in 𝓝 x, p y } := by
  simp only [interior_set_of_eq, ← is_open_interior]

theorem subset_interior_iff_nhds {s V : Set α} : s ⊆ Interior V ↔ ∀, ∀ x ∈ s, ∀, V ∈ 𝓝 x :=
  show (∀ x, x ∈ s → x ∈ _) ↔ _ by
    simp_rw [mem_interior_iff_mem_nhds]

theorem is_open_iff_nhds {s : Set α} : IsOpen s ↔ ∀, ∀ a ∈ s, ∀, 𝓝 a ≤ 𝓟 s :=
  calc
    IsOpen s ↔ s ⊆ Interior s := subset_interior_iff_open.symm
    _ ↔ ∀, ∀ a ∈ s, ∀, 𝓝 a ≤ 𝓟 s := by
      rw [interior_eq_nhds] <;> rfl
    

theorem is_open_iff_mem_nhds {s : Set α} : IsOpen s ↔ ∀, ∀ a ∈ s, ∀, s ∈ 𝓝 a :=
  is_open_iff_nhds.trans <| forall_congrₓ fun _ => imp_congr_right fun _ => le_principal_iff

theorem is_open_iff_ultrafilter {s : Set α} : IsOpen s ↔ ∀, ∀ x ∈ s, ∀ (l : Ultrafilter α), ↑l ≤ 𝓝 x → s ∈ l := by
  simp_rw [is_open_iff_mem_nhds, ← mem_iff_ultrafilter]

theorem is_open_singleton_iff_nhds_eq_pure {α : Type _} [TopologicalSpace α] (a : α) :
    IsOpen ({a} : Set α) ↔ 𝓝 a = pure a := by
  constructor
  · intro h
    apply le_antisymmₓ _ (pure_le_nhds a)
    rw [le_pure_iff]
    exact h.mem_nhds (mem_singleton a)
    
  · intro h
    simp [← is_open_iff_nhds, ← h]
    

theorem mem_closure_iff_frequently {s : Set α} {a : α} : a ∈ Closure s ↔ ∃ᶠ x in 𝓝 a, x ∈ s := by
  rw [Filter.Frequently, Filter.Eventually, ← mem_interior_iff_mem_nhds, closure_eq_compl_interior_compl] <;> rfl

alias mem_closure_iff_frequently ↔ _ Filter.Frequently.mem_closure

/-- The set of cluster points of a filter is closed. In particular, the set of limit points
of a sequence is closed. -/
theorem is_closed_set_of_cluster_pt {f : Filter α} : IsClosed { x | ClusterPt x f } := by
  simp only [← ClusterPt, ← inf_ne_bot_iff_frequently_left, ← set_of_forall, ← imp_iff_not_or]
  refine' is_closed_Inter fun p => IsClosed.union _ _ <;> apply is_closed_compl_iff.2
  exacts[is_open_set_of_eventually_nhds, is_open_const]

theorem mem_closure_iff_cluster_pt {s : Set α} {a : α} : a ∈ Closure s ↔ ClusterPt a (𝓟 s) :=
  mem_closure_iff_frequently.trans cluster_pt_principal_iff_frequently.symm

theorem mem_closure_iff_nhds_ne_bot {s : Set α} : a ∈ Closure s ↔ 𝓝 a⊓𝓟 s ≠ ⊥ :=
  mem_closure_iff_cluster_pt.trans ne_bot_iff

theorem mem_closure_iff_nhds_within_ne_bot {s : Set α} {x : α} : x ∈ Closure s ↔ NeBot (𝓝[s] x) :=
  mem_closure_iff_cluster_pt

/-- If `x` is not an isolated point of a topological space, then `{x}ᶜ` is dense in the whole
space. -/
theorem dense_compl_singleton (x : α) [NeBot (𝓝[≠] x)] : Dense ({x}ᶜ : Set α) := by
  intro y
  rcases eq_or_ne y x with (rfl | hne)
  · rwa [mem_closure_iff_nhds_within_ne_bot]
    
  · exact subset_closure hne
    

/-- If `x` is not an isolated point of a topological space, then the closure of `{x}ᶜ` is the whole
space. -/
@[simp]
theorem closure_compl_singleton (x : α) [NeBot (𝓝[≠] x)] : Closure ({x}ᶜ) = (Univ : Set α) :=
  (dense_compl_singleton x).closure_eq

/-- If `x` is not an isolated point of a topological space, then the interior of `{x}` is empty. -/
@[simp]
theorem interior_singleton (x : α) [NeBot (𝓝[≠] x)] : Interior {x} = (∅ : Set α) :=
  interior_eq_empty_iff_dense_compl.2 (dense_compl_singleton x)

theorem closure_eq_cluster_pts {s : Set α} : Closure s = { a | ClusterPt a (𝓟 s) } :=
  Set.ext fun x => mem_closure_iff_cluster_pt

theorem mem_closure_iff_nhds {s : Set α} {a : α} : a ∈ Closure s ↔ ∀, ∀ t ∈ 𝓝 a, ∀, (t ∩ s).Nonempty :=
  mem_closure_iff_cluster_pt.trans cluster_pt_principal_iff

theorem mem_closure_iff_nhds' {s : Set α} {a : α} : a ∈ Closure s ↔ ∀, ∀ t ∈ 𝓝 a, ∀, ∃ y : s, ↑y ∈ t := by
  simp only [← mem_closure_iff_nhds, ← Set.nonempty_inter_iff_exists_right]

theorem mem_closure_iff_comap_ne_bot {A : Set α} {x : α} : x ∈ Closure A ↔ NeBot (comap (coe : A → α) (𝓝 x)) := by
  simp_rw [mem_closure_iff_nhds, comap_ne_bot_iff, Set.nonempty_inter_iff_exists_right]

theorem mem_closure_iff_nhds_basis' {a : α} {p : ι → Prop} {s : ι → Set α} (h : (𝓝 a).HasBasis p s) {t : Set α} :
    a ∈ Closure t ↔ ∀ i, p i → (s i ∩ t).Nonempty :=
  mem_closure_iff_cluster_pt.trans <|
    (h.cluster_pt_iff (has_basis_principal _)).trans <| by
      simp only [← exists_prop, ← forall_const]

theorem mem_closure_iff_nhds_basis {a : α} {p : ι → Prop} {s : ι → Set α} (h : (𝓝 a).HasBasis p s) {t : Set α} :
    a ∈ Closure t ↔ ∀ i, p i → ∃ y ∈ t, y ∈ s i :=
  (mem_closure_iff_nhds_basis' h).trans <| by
    simp only [← Set.Nonempty, ← mem_inter_eq, ← exists_prop, ← and_comm]

/-- `x` belongs to the closure of `s` if and only if some ultrafilter
  supported on `s` converges to `x`. -/
theorem mem_closure_iff_ultrafilter {s : Set α} {x : α} : x ∈ Closure s ↔ ∃ u : Ultrafilter α, s ∈ u ∧ ↑u ≤ 𝓝 x := by
  simp [← closure_eq_cluster_pts, ← ClusterPt, exists_ultrafilter_iff, ← And.comm]

theorem is_closed_iff_cluster_pt {s : Set α} : IsClosed s ↔ ∀ a, ClusterPt a (𝓟 s) → a ∈ s :=
  calc
    IsClosed s ↔ Closure s ⊆ s := closure_subset_iff_is_closed.symm
    _ ↔ ∀ a, ClusterPt a (𝓟 s) → a ∈ s := by
      simp only [← subset_def, ← mem_closure_iff_cluster_pt]
    

theorem is_closed_iff_nhds {s : Set α} : IsClosed s ↔ ∀ x, (∀, ∀ U ∈ 𝓝 x, ∀, (U ∩ s).Nonempty) → x ∈ s := by
  simp_rw [is_closed_iff_cluster_pt, ClusterPt, inf_principal_ne_bot_iff]

theorem closure_inter_open {s t : Set α} (h : IsOpen s) : s ∩ Closure t ⊆ Closure (s ∩ t) := by
  rintro a ⟨hs, ht⟩
  have : s ∈ 𝓝 a := IsOpen.mem_nhds h hs
  rw [mem_closure_iff_nhds_ne_bot] at ht⊢
  rwa [← inf_principal, ← inf_assoc, inf_eq_left.2 (le_principal_iff.2 this)]

theorem closure_inter_open' {s t : Set α} (h : IsOpen t) : Closure s ∩ t ⊆ Closure (s ∩ t) := by
  simpa only [← inter_comm] using closure_inter_open h

theorem Dense.open_subset_closure_inter {s t : Set α} (hs : Dense s) (ht : IsOpen t) : t ⊆ Closure (t ∩ s) :=
  calc
    t = t ∩ Closure s := by
      rw [hs.closure_eq, inter_univ]
    _ ⊆ Closure (t ∩ s) := closure_inter_open ht
    

theorem mem_closure_of_mem_closure_union {s₁ s₂ : Set α} {x : α} (h : x ∈ Closure (s₁ ∪ s₂)) (h₁ : s₁ᶜ ∈ 𝓝 x) :
    x ∈ Closure s₂ := by
  rw [mem_closure_iff_nhds_ne_bot] at *
  rwa [←
    calc
      𝓝 x⊓principal (s₁ ∪ s₂) = 𝓝 x⊓(principal s₁⊔principal s₂) := by
        rw [sup_principal]
      _ = 𝓝 x⊓principal s₁⊔𝓝 x⊓principal s₂ := inf_sup_left
      _ = ⊥⊔𝓝 x⊓principal s₂ := by
        rw [inf_principal_eq_bot.mpr h₁]
      _ = 𝓝 x⊓principal s₂ := bot_sup_eq
      ]

/-- The intersection of an open dense set with a dense set is a dense set. -/
theorem Dense.inter_of_open_left {s t : Set α} (hs : Dense s) (ht : Dense t) (hso : IsOpen s) : Dense (s ∩ t) :=
  fun x =>
  closure_minimal (closure_inter_open hso) is_closed_closure <| by
    simp [← hs.closure_eq, ← ht.closure_eq]

/-- The intersection of a dense set with an open dense set is a dense set. -/
theorem Dense.inter_of_open_right {s t : Set α} (hs : Dense s) (ht : Dense t) (hto : IsOpen t) : Dense (s ∩ t) :=
  inter_comm t s ▸ ht.inter_of_open_left hs hto

theorem Dense.inter_nhds_nonempty {s t : Set α} (hs : Dense s) {x : α} (ht : t ∈ 𝓝 x) : (s ∩ t).Nonempty :=
  let ⟨U, hsub, ho, hx⟩ := mem_nhds_iff.1 ht
  (hs.inter_open_nonempty U ho ⟨x, hx⟩).mono fun y hy => ⟨hy.2, hsub hy.1⟩

theorem closure_diff {s t : Set α} : Closure s \ Closure t ⊆ Closure (s \ t) :=
  calc
    Closure s \ Closure t = Closure tᶜ ∩ Closure s := by
      simp only [← diff_eq, ← inter_comm]
    _ ⊆ Closure (Closure tᶜ ∩ s) := closure_inter_open <| is_open_compl_iff.mpr <| is_closed_closure
    _ = Closure (s \ Closure t) := by
      simp only [← diff_eq, ← inter_comm]
    _ ⊆ Closure (s \ t) := closure_mono <| diff_subset_diff (Subset.refl s) subset_closure
    

theorem Filter.Frequently.mem_of_closed {a : α} {s : Set α} (h : ∃ᶠ x in 𝓝 a, x ∈ s) (hs : IsClosed s) : a ∈ s :=
  hs.closure_subset h.mem_closure

theorem IsClosed.mem_of_frequently_of_tendsto {f : β → α} {b : Filter β} {a : α} {s : Set α} (hs : IsClosed s)
    (h : ∃ᶠ x in b, f x ∈ s) (hf : Tendsto f b (𝓝 a)) : a ∈ s :=
  (hf.Frequently <| show ∃ᶠ x in b, (fun y => y ∈ s) (f x) from h).mem_of_closed hs

theorem IsClosed.mem_of_tendsto {f : β → α} {b : Filter β} {a : α} {s : Set α} [NeBot b] (hs : IsClosed s)
    (hf : Tendsto f b (𝓝 a)) (h : ∀ᶠ x in b, f x ∈ s) : a ∈ s :=
  hs.mem_of_frequently_of_tendsto h.Frequently hf

theorem mem_closure_of_frequently_of_tendsto {f : β → α} {b : Filter β} {a : α} {s : Set α} (h : ∃ᶠ x in b, f x ∈ s)
    (hf : Tendsto f b (𝓝 a)) : a ∈ Closure s :=
  Filter.Frequently.mem_closure <| hf.Frequently h

theorem mem_closure_of_tendsto {f : β → α} {b : Filter β} {a : α} {s : Set α} [NeBot b] (hf : Tendsto f b (𝓝 a))
    (h : ∀ᶠ x in b, f x ∈ s) : a ∈ Closure s :=
  mem_closure_of_frequently_of_tendsto h.Frequently hf

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ∉ » s)
/-- Suppose that `f` sends the complement to `s` to a single point `a`, and `l` is some filter.
Then `f` tends to `a` along `l` restricted to `s` if and only if it tends to `a` along `l`. -/
theorem tendsto_inf_principal_nhds_iff_of_forall_eq {f : β → α} {l : Filter β} {s : Set β} {a : α}
    (h : ∀ (x) (_ : x ∉ s), f x = a) : Tendsto f (l⊓𝓟 s) (𝓝 a) ↔ Tendsto f l (𝓝 a) := by
  rw [tendsto_iff_comap, tendsto_iff_comap]
  replace h : 𝓟 (sᶜ) ≤ comap f (𝓝 a)
  · rintro U ⟨t, ht, htU⟩ x hx
    have : f x ∈ t := (h x hx).symm ▸ mem_of_mem_nhds ht
    exact htU this
    
  refine' ⟨fun h' => _, le_transₓ inf_le_left⟩
  have := sup_le h' h
  rw [sup_inf_right, sup_principal, union_compl_self, principal_univ, inf_top_eq, sup_le_iff] at this
  exact this.1

/-!
### Limits of filters in topological spaces
-/


section limₓ

/-- If `f` is a filter, then `Lim f` is a limit of the filter, if it exists. -/
noncomputable def lim [Nonempty α] (f : Filter α) : α :=
  epsilon fun a => f ≤ 𝓝 a

/-- If `f` is a filter satisfying `ne_bot f`, then `Lim' f` is a limit of the filter, if it exists.
-/
def lim' (f : Filter α) [NeBot f] : α :=
  @lim _ _ (nonempty_of_ne_bot f) f

/-- If `F` is an ultrafilter, then `filter.ultrafilter.Lim F` is a limit of the filter, if it exists.
Note that dot notation `F.Lim` can be used for `F : ultrafilter α`.
-/
def Ultrafilter.lim : Ultrafilter α → α := fun F => lim' F

/-- If `f` is a filter in `β` and `g : β → α` is a function, then `lim f` is a limit of `g` at `f`,
if it exists. -/
noncomputable def limₓ [Nonempty α] (f : Filter β) (g : β → α) : α :=
  lim (f.map g)

/-- If a filter `f` is majorated by some `𝓝 a`, then it is majorated by `𝓝 (Lim f)`. We formulate
this lemma with a `[nonempty α]` argument of `Lim` derived from `h` to make it useful for types
without a `[nonempty α]` instance. Because of the built-in proof irrelevance, Lean will unify
this instance with any other instance. -/
theorem le_nhds_Lim {f : Filter α} (h : ∃ a, f ≤ 𝓝 a) : f ≤ 𝓝 (@lim _ _ (nonempty_of_exists h) f) :=
  epsilon_spec h

/-- If `g` tends to some `𝓝 a` along `f`, then it tends to `𝓝 (lim f g)`. We formulate
this lemma with a `[nonempty α]` argument of `lim` derived from `h` to make it useful for types
without a `[nonempty α]` instance. Because of the built-in proof irrelevance, Lean will unify
this instance with any other instance. -/
theorem tendsto_nhds_lim {f : Filter β} {g : β → α} (h : ∃ a, Tendsto g f (𝓝 a)) :
    Tendsto g f (𝓝 <| @limₓ _ _ _ (nonempty_of_exists h) f g) :=
  le_nhds_Lim h

end limₓ

/-!
### Locally finite families
-/


-- locally finite family [General Topology (Bourbaki, 1995)]
section LocallyFinite

/-- A family of sets in `set α` is locally finite if at every point `x:α`,
  there is a neighborhood of `x` which meets only finitely many sets in the family -/
def LocallyFinite (f : β → Set α) :=
  ∀ x : α, ∃ t ∈ 𝓝 x, { i | (f i ∩ t).Nonempty }.Finite

theorem LocallyFinite.point_finite {f : β → Set α} (hf : LocallyFinite f) (x : α) : { b | x ∈ f b }.Finite :=
  let ⟨t, hxt, ht⟩ := hf x
  ht.Subset fun b hb => ⟨x, hb, mem_of_mem_nhds hxt⟩

theorem locally_finite_of_finite [Finite β] (f : β → Set α) : LocallyFinite f := fun x => ⟨Univ, univ_mem, to_finite _⟩

theorem LocallyFinite.subset {f₁ f₂ : β → Set α} (hf₂ : LocallyFinite f₂) (hf : ∀ b, f₁ b ⊆ f₂ b) : LocallyFinite f₁ :=
  fun a =>
  let ⟨t, ht₁, ht₂⟩ := hf₂ a
  ⟨t, ht₁, ht₂.Subset fun i hi => hi.mono <| inter_subset_inter (hf i) <| Subset.refl _⟩

theorem LocallyFinite.comp_injective {ι} {f : β → Set α} {g : ι → β} (hf : LocallyFinite f)
    (hg : Function.Injective g) : LocallyFinite (f ∘ g) := fun x =>
  let ⟨t, htx, htf⟩ := hf x
  ⟨t, htx, htf.Preimage (hg.InjOn _)⟩

theorem LocallyFinite.eventually_finite {f : β → Set α} (hf : LocallyFinite f) (x : α) :
    ∀ᶠ s in (𝓝 x).smallSets, { i | (f i ∩ s).Nonempty }.Finite :=
  eventually_small_sets.2 <|
    let ⟨s, hsx, hs⟩ := hf x
    ⟨s, hsx, fun t hts => hs.Subset fun i hi => hi.out.mono <| inter_subset_inter_right _ hts⟩

theorem LocallyFinite.sum_elim {γ} {f : β → Set α} {g : γ → Set α} (hf : LocallyFinite f) (hg : LocallyFinite g) :
    LocallyFinite (Sum.elim f g) := by
  intro x
  obtain ⟨s, hsx, hsf, hsg⟩ : ∃ s, s ∈ 𝓝 x ∧ { i | (f i ∩ s).Nonempty }.Finite ∧ { j | (g j ∩ s).Nonempty }.Finite
  exact ((𝓝 x).frequently_small_sets_mem.and_eventually ((hf.eventually_finite x).And (hg.eventually_finite x))).exists
  refine' ⟨s, hsx, _⟩
  convert (hsf.image Sum.inl).union (hsg.image Sum.inr) using 1
  ext (i | j) <;> simp

theorem LocallyFinite.closure {f : β → Set α} (hf : LocallyFinite f) : LocallyFinite fun i => Closure (f i) := by
  intro x
  rcases hf x with ⟨s, hsx, hsf⟩
  refine' ⟨Interior s, interior_mem_nhds.2 hsx, hsf.subset fun i hi => _⟩
  exact (hi.mono (closure_inter_open' is_open_interior)).of_closure.mono (inter_subset_inter_right _ interior_subset)

theorem LocallyFinite.is_closed_Union {f : β → Set α} (h₁ : LocallyFinite f) (h₂ : ∀ i, IsClosed (f i)) :
    IsClosed (⋃ i, f i) := by
  simp only [is_open_compl_iff, ← compl_Union, ← is_open_iff_mem_nhds, ← mem_Inter]
  intro a ha
  replace ha : ∀ i, f iᶜ ∈ 𝓝 a := fun i => (h₂ i).is_open_compl.mem_nhds (ha i)
  rcases h₁ a with ⟨t, h_nhds, h_fin⟩
  have : (t ∩ ⋂ i ∈ { i | (f i ∩ t).Nonempty }, f iᶜ) ∈ 𝓝 a := inter_mem h_nhds ((bInter_mem h_fin).2 fun i _ => ha i)
  filter_upwards [this]
  simp only [← mem_inter_eq, ← mem_Inter]
  rintro b ⟨hbt, hn⟩ i hfb
  exact hn i ⟨b, hfb, hbt⟩ hfb

theorem LocallyFinite.closure_Union {f : β → Set α} (h : LocallyFinite f) : Closure (⋃ i, f i) = ⋃ i, Closure (f i) :=
  Subset.antisymm
    (closure_minimal (Union_mono fun _ => subset_closure) <| h.closure.is_closed_Union fun _ => is_closed_closure)
    (Union_subset fun i => closure_mono <| subset_Union _ _)

end LocallyFinite

end TopologicalSpace

/-!
### Continuity
-/


section Continuous

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

open TopologicalSpace

/-- A function between topological spaces is continuous if the preimage
  of every open set is open. Registered as a structure to make sure it is not unfolded by Lean. -/
structure Continuous (f : α → β) : Prop where
  is_open_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

theorem continuous_def {f : α → β} : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  ⟨fun hf s hs => hf.is_open_preimage s hs, fun h => ⟨h⟩⟩

theorem IsOpen.preimage {f : α → β} (hf : Continuous f) {s : Set β} (h : IsOpen s) : IsOpen (f ⁻¹' s) :=
  hf.is_open_preimage s h

theorem Continuous.congr {f g : α → β} (h : Continuous f) (h' : ∀ x, f x = g x) : Continuous g := by
  convert h
  ext
  rw [h']

/-- A function between topological spaces is continuous at a point `x₀`
if `f x` tends to `f x₀` when `x` tends to `x₀`. -/
def ContinuousAt (f : α → β) (x : α) :=
  Tendsto f (𝓝 x) (𝓝 (f x))

theorem ContinuousAt.tendsto {f : α → β} {x : α} (h : ContinuousAt f x) : Tendsto f (𝓝 x) (𝓝 (f x)) :=
  h

theorem continuous_at_def {f : α → β} {x : α} : ContinuousAt f x ↔ ∀, ∀ A ∈ 𝓝 (f x), ∀, f ⁻¹' A ∈ 𝓝 x :=
  Iff.rfl

theorem continuous_at_congr {f g : α → β} {x : α} (h : f =ᶠ[𝓝 x] g) : ContinuousAt f x ↔ ContinuousAt g x := by
  simp only [← ContinuousAt, ← tendsto_congr' h, ← h.eq_of_nhds]

theorem ContinuousAt.congr {f g : α → β} {x : α} (hf : ContinuousAt f x) (h : f =ᶠ[𝓝 x] g) : ContinuousAt g x :=
  (continuous_at_congr h).1 hf

theorem ContinuousAt.preimage_mem_nhds {f : α → β} {x : α} {t : Set β} (h : ContinuousAt f x) (ht : t ∈ 𝓝 (f x)) :
    f ⁻¹' t ∈ 𝓝 x :=
  h ht

theorem eventually_eq_zero_nhds {M₀} [Zero M₀] {a : α} {f : α → M₀} : f =ᶠ[𝓝 a] 0 ↔ a ∉ Closure (Function.Support f) :=
  by
  rw [← mem_compl_eq, ← interior_compl, mem_interior_iff_mem_nhds, Function.compl_support] <;> rfl

theorem ClusterPt.map {x : α} {la : Filter α} {lb : Filter β} (H : ClusterPt x la) {f : α → β} (hfc : ContinuousAt f x)
    (hf : Tendsto f la lb) : ClusterPt (f x) lb :=
  ⟨ne_bot_of_le_ne_bot ((map_ne_bot_iff f).2 H).Ne <| hfc.Tendsto.inf hf⟩

/-- See also `interior_preimage_subset_preimage_interior`. -/
theorem preimage_interior_subset_interior_preimage {f : α → β} {s : Set β} (hf : Continuous f) :
    f ⁻¹' Interior s ⊆ Interior (f ⁻¹' s) :=
  interior_maximal (preimage_mono interior_subset) (is_open_interior.Preimage hf)

theorem continuous_id : Continuous (id : α → α) :=
  continuous_def.2 fun s h => h

theorem Continuous.comp {g : β → γ} {f : α → β} (hg : Continuous g) (hf : Continuous f) : Continuous (g ∘ f) :=
  continuous_def.2 fun s h => (h.Preimage hg).Preimage hf

theorem Continuous.iterate {f : α → α} (h : Continuous f) (n : ℕ) : Continuous (f^[n]) :=
  Nat.recOn n continuous_id fun n ihn => ihn.comp h

theorem ContinuousAt.comp {g : β → γ} {f : α → β} {x : α} (hg : ContinuousAt g (f x)) (hf : ContinuousAt f x) :
    ContinuousAt (g ∘ f) x :=
  hg.comp hf

theorem Continuous.tendsto {f : α → β} (hf : Continuous f) (x) : Tendsto f (𝓝 x) (𝓝 (f x)) :=
  ((nhds_basis_opens x).tendsto_iff <| nhds_basis_opens <| f x).2 fun t ⟨hxt, ht⟩ =>
    ⟨f ⁻¹' t, ⟨hxt, ht.Preimage hf⟩, Subset.refl _⟩

/-- A version of `continuous.tendsto` that allows one to specify a simpler form of the limit.
E.g., one can write `continuous_exp.tendsto' 0 1 exp_zero`. -/
theorem Continuous.tendsto' {f : α → β} (hf : Continuous f) (x : α) (y : β) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y) :=
  h ▸ hf.Tendsto x

theorem Continuous.continuous_at {f : α → β} {x : α} (h : Continuous f) : ContinuousAt f x :=
  h.Tendsto x

theorem continuous_iff_continuous_at {f : α → β} : Continuous f ↔ ∀ x, ContinuousAt f x :=
  ⟨Continuous.tendsto, fun hf : ∀ x, Tendsto f (𝓝 x) (𝓝 (f x)) =>
    continuous_def.2 fun s => fun hs : IsOpen s =>
      have : ∀ a, f a ∈ s → s ∈ 𝓝 (f a) := fun a ha => IsOpen.mem_nhds hs ha
      show IsOpen (f ⁻¹' s) from is_open_iff_nhds.2 fun a ha => le_principal_iff.2 <| hf _ (this a ha)⟩

theorem continuous_at_const {x : α} {b : β} : ContinuousAt (fun a : α => b) x :=
  tendsto_const_nhds

theorem continuous_const {b : β} : Continuous fun a : α => b :=
  continuous_iff_continuous_at.mpr fun a => continuous_at_const

theorem Filter.EventuallyEq.continuous_at {x : α} {f : α → β} {y : β} (h : f =ᶠ[𝓝 x] fun _ => y) : ContinuousAt f x :=
  (continuous_at_congr h).2 tendsto_const_nhds

theorem continuous_of_const {f : α → β} (h : ∀ x y, f x = f y) : Continuous f :=
  continuous_iff_continuous_at.mpr fun x => Filter.EventuallyEq.continuous_at <| eventually_of_forall fun y => h y x

theorem continuous_at_id {x : α} : ContinuousAt id x :=
  continuous_id.ContinuousAt

theorem ContinuousAt.iterate {f : α → α} {x : α} (hf : ContinuousAt f x) (hx : f x = x) (n : ℕ) :
    ContinuousAt (f^[n]) x :=
  (Nat.recOn n continuous_at_id) fun n ihn => show ContinuousAt (f^[n] ∘ f) x from ContinuousAt.comp (hx.symm ▸ ihn) hf

theorem LocallyFinite.preimage_continuous {ι} {f : ι → Set α} {g : β → α} (hf : LocallyFinite f) (hg : Continuous g) :
    LocallyFinite fun i => g ⁻¹' f i := fun x =>
  let ⟨s, hsx, hs⟩ := hf (g x)
  ⟨g ⁻¹' s, hg.ContinuousAt hsx, hs.Subset fun i ⟨y, hy⟩ => ⟨g y, hy⟩⟩

theorem continuous_iff_is_closed {f : α → β} : Continuous f ↔ ∀ s, IsClosed s → IsClosed (f ⁻¹' s) :=
  ⟨fun hf s hs => by
    simpa using (continuous_def.1 hf (sᶜ) hs.is_open_compl).is_closed_compl, fun hf =>
    continuous_def.2 fun s => by
      rw [← is_closed_compl_iff, ← is_closed_compl_iff] <;> exact hf _⟩

theorem IsClosed.preimage {f : α → β} (hf : Continuous f) {s : Set β} (h : IsClosed s) : IsClosed (f ⁻¹' s) :=
  continuous_iff_is_closed.mp hf s h

theorem mem_closure_image {f : α → β} {x : α} {s : Set α} (hf : ContinuousAt f x) (hx : x ∈ Closure s) :
    f x ∈ Closure (f '' s) :=
  mem_closure_of_frequently_of_tendsto ((mem_closure_iff_frequently.1 hx).mono fun x => mem_image_of_mem _) hf

theorem continuous_at_iff_ultrafilter {f : α → β} {x} :
    ContinuousAt f x ↔ ∀ g : Ultrafilter α, ↑g ≤ 𝓝 x → Tendsto f g (𝓝 (f x)) :=
  tendsto_iff_ultrafilter f (𝓝 x) (𝓝 (f x))

theorem continuous_iff_ultrafilter {f : α → β} :
    Continuous f ↔ ∀ (x) (g : Ultrafilter α), ↑g ≤ 𝓝 x → Tendsto f g (𝓝 (f x)) := by
  simp only [← continuous_iff_continuous_at, ← continuous_at_iff_ultrafilter]

theorem Continuous.closure_preimage_subset {f : α → β} (hf : Continuous f) (t : Set β) :
    Closure (f ⁻¹' t) ⊆ f ⁻¹' Closure t := by
  rw [← (is_closed_closure.preimage hf).closure_eq]
  exact closure_mono (preimage_mono subset_closure)

theorem Continuous.frontier_preimage_subset {f : α → β} (hf : Continuous f) (t : Set β) :
    Frontier (f ⁻¹' t) ⊆ f ⁻¹' Frontier t :=
  diff_subset_diff (hf.closure_preimage_subset t) (preimage_interior_subset_interior_preimage hf)

/-! ### Continuity and partial functions -/


/-- Continuity of a partial function -/
def Pcontinuous (f : α →. β) :=
  ∀ s, IsOpen s → IsOpen (f.Preimage s)

theorem open_dom_of_pcontinuous {f : α →. β} (h : Pcontinuous f) : IsOpen f.Dom := by
  rw [← Pfun.preimage_univ] <;> exact h _ is_open_univ

theorem pcontinuous_iff' {f : α →. β} : Pcontinuous f ↔ ∀ {x y} (h : y ∈ f x), Ptendsto' f (𝓝 x) (𝓝 y) := by
  constructor
  · intro h x y h'
    simp only [← ptendsto'_def, ← mem_nhds_iff]
    rintro s ⟨t, tsubs, opent, yt⟩
    exact ⟨f.preimage t, Pfun.preimage_mono _ tsubs, h _ opent, ⟨y, yt, h'⟩⟩
    
  intro hf s os
  rw [is_open_iff_nhds]
  rintro x ⟨y, ys, fxy⟩ t
  rw [mem_principal]
  intro (h : f.preimage s ⊆ t)
  change t ∈ 𝓝 x
  apply mem_of_superset _ h
  have h' : ∀, ∀ s ∈ 𝓝 y, ∀, f.preimage s ∈ 𝓝 x := by
    intro s hs
    have : ptendsto' f (𝓝 x) (𝓝 y) := hf fxy
    rw [ptendsto'_def] at this
    exact this s hs
  show f.preimage s ∈ 𝓝 x
  apply h'
  rw [mem_nhds_iff]
  exact ⟨s, Set.Subset.refl _, os, ys⟩

/-- If a continuous map `f` maps `s` to `t`, then it maps `closure s` to `closure t`. -/
theorem Set.MapsTo.closure {s : Set α} {t : Set β} {f : α → β} (h : MapsTo f s t) (hc : Continuous f) :
    MapsTo f (Closure s) (Closure t) := by
  simp only [← maps_to, ← mem_closure_iff_cluster_pt]
  exact fun x hx => hx.map hc.continuous_at (tendsto_principal_principal.2 h)

theorem image_closure_subset_closure_image {f : α → β} {s : Set α} (h : Continuous f) :
    f '' Closure s ⊆ Closure (f '' s) :=
  ((maps_to_image f s).closure h).image_subset

theorem closure_subset_preimage_closure_image {f : α → β} {s : Set α} (h : Continuous f) :
    Closure s ⊆ f ⁻¹' Closure (f '' s) := by
  rw [← Set.image_subset_iff]
  exact image_closure_subset_closure_image h

theorem map_mem_closure {s : Set α} {t : Set β} {f : α → β} {a : α} (hf : Continuous f) (ha : a ∈ Closure s)
    (ht : ∀, ∀ a ∈ s, ∀, f a ∈ t) : f a ∈ Closure t :=
  Set.MapsTo.closure ht hf ha

/-!
### Function with dense range
-/


section DenseRange

variable {κ ι : Type _} (f : κ → β) (g : β → γ)

/-- `f : ι → β` has dense range if its range (image) is a dense subset of β. -/
def DenseRange :=
  Dense (Range f)

variable {f}

/-- A surjective map has dense range. -/
theorem Function.Surjective.dense_range (hf : Function.Surjective f) : DenseRange f := fun x => by
  simp [← hf.range_eq]

theorem dense_range_iff_closure_range : DenseRange f ↔ Closure (Range f) = univ :=
  dense_iff_closure_eq

theorem DenseRange.closure_range (h : DenseRange f) : Closure (Range f) = univ :=
  h.closure_eq

theorem Dense.dense_range_coe {s : Set α} (h : Dense s) : DenseRange (coe : s → α) := by
  simpa only [← DenseRange, ← Subtype.range_coe_subtype]

theorem Continuous.range_subset_closure_image_dense {f : α → β} (hf : Continuous f) {s : Set α} (hs : Dense s) :
    Range f ⊆ Closure (f '' s) := by
  rw [← image_univ, ← hs.closure_eq]
  exact image_closure_subset_closure_image hf

/-- The image of a dense set under a continuous map with dense range is a dense set. -/
theorem DenseRange.dense_image {f : α → β} (hf' : DenseRange f) (hf : Continuous f) {s : Set α} (hs : Dense s) :
    Dense (f '' s) :=
  (hf'.mono <| hf.range_subset_closure_image_dense hs).of_closure

/-- If `f` has dense range and `s` is an open set in the codomain of `f`, then the image of the
preimage of `s` under `f` is dense in `s`. -/
theorem DenseRange.subset_closure_image_preimage_of_is_open (hf : DenseRange f) {s : Set β} (hs : IsOpen s) :
    s ⊆ Closure (f '' (f ⁻¹' s)) := by
  rw [image_preimage_eq_inter_range]
  exact hf.open_subset_closure_inter hs

/-- If a continuous map with dense range maps a dense set to a subset of `t`, then `t` is a dense
set. -/
theorem DenseRange.dense_of_maps_to {f : α → β} (hf' : DenseRange f) (hf : Continuous f) {s : Set α} (hs : Dense s)
    {t : Set β} (ht : MapsTo f s t) : Dense t :=
  (hf'.dense_image hf hs).mono ht.image_subset

/-- Composition of a continuous map with dense range and a function with dense range has dense
range. -/
theorem DenseRange.comp {g : β → γ} {f : κ → β} (hg : DenseRange g) (hf : DenseRange f) (cg : Continuous g) :
    DenseRange (g ∘ f) := by
  rw [DenseRange, range_comp]
  exact hg.dense_image cg hf

theorem DenseRange.nonempty_iff (hf : DenseRange f) : Nonempty κ ↔ Nonempty β :=
  range_nonempty_iff_nonempty.symm.trans hf.nonempty_iff

theorem DenseRange.nonempty [h : Nonempty β] (hf : DenseRange f) : Nonempty κ :=
  hf.nonempty_iff.mpr h

/-- Given a function `f : α → β` with dense range and `b : β`, returns some `a : α`. -/
def DenseRange.some (hf : DenseRange f) (b : β) : κ :=
  Classical.choice <| hf.nonempty_iff.mpr ⟨b⟩

theorem DenseRange.exists_mem_open (hf : DenseRange f) {s : Set β} (ho : IsOpen s) (hs : s.Nonempty) : ∃ a, f a ∈ s :=
  exists_range_iff.1 <| hf.exists_mem_open ho hs

theorem DenseRange.mem_nhds {f : κ → β} (h : DenseRange f) {b : β} {U : Set β} (U_in : U ∈ 𝓝 b) : ∃ a, f a ∈ U :=
  let ⟨a, ha⟩ := h.exists_mem_open is_open_interior ⟨b, mem_interior_iff_mem_nhds.2 U_in⟩
  ⟨a, interior_subset ha⟩

end DenseRange

end Continuous

library_note "continuity lemma statement"/--
The library contains many lemmas stating that functions/operations are continuous. There are many
ways to formulate the continuity of operations. Some are more convenient than others.
Note: for the most part this note also applies to other properties
(`measurable`, `differentiable`, `continuous_on`, ...).

### The traditional way
As an example, let's look at addition `(+) : M → M → M`. We can state that this is continuous
in different definitionally equal ways (omitting some typing information)
* `continuous (λ p, p.1 + p.2)`;
* `continuous (function.uncurry (+))`;
* `continuous ↿(+)`. (`↿` is notation for recursively uncurrying a function)

However, lemmas with this conclusion are not nice to use in practice because
1. They confuse the elaborator. The following two examples fail, because of limitations in the
  elaboration process.
  ```
  variables {M : Type*} [has_add M] [topological_space M] [has_continuous_add M]
  example : continuous (λ x : M, x + x) :=
  continuous_add.comp _

  example : continuous (λ x : M, x + x) :=
  continuous_add.comp (continuous_id.prod_mk continuous_id)
  ```
  The second is a valid proof, which is accepted if you write it as
  `continuous_add.comp (continuous_id.prod_mk continuous_id : _)`

2. If the operation has more than 2 arguments, they are impractical to use, because in your
  application the arguments in the domain might be in a different order or associated differently.

### The convenient way
A much more convenient way to write continuity lemmas is like `continuous.add`:
```
continuous.add {f g : X → M} (hf : continuous f) (hg : continuous g) : continuous (λ x, f x + g x)
```
The conclusion can be `continuous (f + g)`, which is definitionally equal.
This has the following advantages
* It supports projection notation, so is shorter to write.
* `continuous.add _ _` is recognized correctly by the elaborator and gives useful new goals.
* It works generally, since the domain is a variable.

As an example for an unary operation, we have `continuous.neg`.
```
continuous.neg {f : α → G} (hf : continuous f) : continuous (λ x, -f x)
```
For unary functions, the elaborator is not confused when applying the traditional lemma
(like `continuous_neg`), but it's still convenient to have the short version available (compare
`hf.neg.neg.neg` with `continuous_neg.comp $ continuous_neg.comp $ continuous_neg.comp hf`).

As a harder example, consider an operation of the following type:
```
def strans {x : F} (γ γ' : path x x) (t₀ : I) : path x x
```
The precise definition is not important, only its type.
The correct continuity principle for this operation is something like this:
```
{f : X → F} {γ γ' : ∀ x, path (f x) (f x)} {t₀ s : X → I}
  (hγ : continuous ↿γ) (hγ' : continuous ↿γ')
  (ht : continuous t₀) (hs : continuous s) :
  continuous (λ x, strans (γ x) (γ' x) (t x) (s x))
```
Note that *all* arguments of `strans` are indexed over `X`, even the basepoint `x`, and the last
argument `s` that arises since `path x x` has a coercion to `I → F`. The paths `γ` and `γ'` (which
are unary functions from `I`) become binary functions in the continuity lemma.

### Summary
* Make sure that your continuity lemmas are stated in the most general way, and in a convenient
  form. That means that:
  - The conclusion has a variable `X` as domain (not something like `Y × Z`);
  - Wherever possible, all point arguments `c : Y` are replaced by functions `c : X → Y`;
  - All `n`-ary function arguments are replaced by `n+1`-ary functions
    (`f : Y → Z` becomes `f : X → Y → Z`);
  - All (relevant) arguments have continuity assumptions, and perhaps there are additional
    assumptions needed to make the operation continuous;
  - The function in the conclusion is fully applied.
* These remarks are mostly about the format of the *conclusion* of a continuity lemma.
  In assumptions it's fine to state that a function with more than 1 argument is continuous using
  `↿` or `function.uncurry`.

### Functions with discontinuities

In some cases, you want to work with discontinuous functions, and in certain expressions they are
still continuous. For example, consider the fractional part of a number, `fract : ℝ → ℝ`.
In this case, you want to add conditions to when a function involving `fract` is continuous, so you
get something like this: (assumption `hf` could be weakened, but the important thing is the shape
of the conclusion)
```
lemma continuous_on.comp_fract {X Y : Type*} [topological_space X] [topological_space Y]
  {f : X → ℝ → Y} {g : X → ℝ} (hf : continuous ↿f) (hg : continuous g) (h : ∀ s, f s 0 = f s 1) :
  continuous (λ x, f x (fract (g x)))
```
With `continuous_at` you can be even more precise about what to prove in case of discontinuities,
see e.g. `continuous_at.comp_div_cases`.
-/



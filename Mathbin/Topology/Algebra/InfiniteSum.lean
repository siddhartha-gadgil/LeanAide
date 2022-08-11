/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Algebra.BigOperators.Intervals
import Mathbin.Algebra.BigOperators.NatAntidiagonal
import Mathbin.Logic.Encodable.Lattice
import Mathbin.Topology.Algebra.MulAction
import Mathbin.Topology.Algebra.Order.MonotoneConvergence
import Mathbin.Topology.Instances.Real

/-!
# Infinite sum over a topological monoid

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations. For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
convergence.

Note: There are summable sequences which are not unconditionally convergent! The other way holds
generally, see `has_sum.tendsto_sum_nat`.

## References

* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/


noncomputable section

open Finset Filter Function Classical

open TopologicalSpace Classical BigOperators Nnreal

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

section HasSum

variable [AddCommMonoidₓ α] [TopologicalSpace α]

/-- Infinite sum on a topological monoid

The `at_top` filter on `finset β` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is invariant under reordering. In particular,
the function `ℕ → ℝ` sending `n` to `(-1)^n / (n+1)` does not have a
sum for this definition, but a series which is absolutely convergent will have the correct sum.

This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

For the definition or many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant.
-/
def HasSum (f : β → α) (a : α) : Prop :=
  Tendsto (fun s : Finset β => ∑ b in s, f b) atTop (𝓝 a)

/-- `summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/
def Summable (f : β → α) : Prop :=
  ∃ a, HasSum f a

/-- `∑' i, f i` is the sum of `f` it exists, or 0 otherwise -/
irreducible_def tsum {β} (f : β → α) :=
  if h : Summable f then Classical.some h else 0

-- mathport name: «expr∑' , »
notation3"∑' "-- see Note [operator precedence of big operators]
(...)", "r:(scoped f => tsum f) => r

variable {f g : β → α} {a b : α} {s : Finset β}

theorem Summable.has_sum (ha : Summable f) : HasSum f (∑' b, f b) := by
  simp [← ha, ← tsum] <;> exact some_spec ha

theorem HasSum.summable (h : HasSum f a) : Summable f :=
  ⟨a, h⟩

/-- Constant zero function has sum `0` -/
theorem has_sum_zero : HasSum (fun b => 0 : β → α) 0 := by
  simp [← HasSum, ← tendsto_const_nhds]

theorem has_sum_empty [IsEmpty β] : HasSum f 0 := by
  convert has_sum_zero

theorem summable_zero : Summable (fun b => 0 : β → α) :=
  has_sum_zero.Summable

theorem summable_empty [IsEmpty β] : Summable f :=
  has_sum_empty.Summable

theorem tsum_eq_zero_of_not_summable (h : ¬Summable f) : (∑' b, f b) = 0 := by
  simp [← tsum, ← h]

theorem summable_congr (hfg : ∀ b, f b = g b) : Summable f ↔ Summable g :=
  iff_of_eq (congr_arg Summable <| funext hfg)

theorem Summable.congr (hf : Summable f) (hfg : ∀ b, f b = g b) : Summable g :=
  (summable_congr hfg).mp hf

theorem HasSum.has_sum_of_sum_eq {g : γ → α}
    (h_eq : ∀ u : Finset γ, ∃ v : Finset β, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ (∑ x in u', g x) = ∑ b in v', f b)
    (hf : HasSum g a) : HasSum f a :=
  le_transₓ (map_at_top_finset_sum_le_of_sum_eq h_eq) hf

theorem has_sum_iff_has_sum {g : γ → α}
    (h₁ : ∀ u : Finset γ, ∃ v : Finset β, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ (∑ x in u', g x) = ∑ b in v', f b)
    (h₂ : ∀ v : Finset β, ∃ u : Finset γ, ∀ u', u ⊆ u' → ∃ v', v ⊆ v' ∧ (∑ b in v', f b) = ∑ x in u', g x) :
    HasSum f a ↔ HasSum g a :=
  ⟨HasSum.has_sum_of_sum_eq h₂, HasSum.has_sum_of_sum_eq h₁⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ∉ » set.range g)
theorem Function.Injective.has_sum_iff {g : γ → β} (hg : Injective g) (hf : ∀ (x) (_ : x ∉ Set.Range g), f x = 0) :
    HasSum (f ∘ g) a ↔ HasSum f a := by
  simp only [← HasSum, ← tendsto, ← hg.map_at_top_finset_sum_eq hf]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ∉ » set.range g)
theorem Function.Injective.summable_iff {g : γ → β} (hg : Injective g) (hf : ∀ (x) (_ : x ∉ Set.Range g), f x = 0) :
    Summable (f ∘ g) ↔ Summable f :=
  exists_congr fun _ => hg.has_sum_iff hf

theorem has_sum_subtype_iff_of_support_subset {s : Set β} (hf : Support f ⊆ s) :
    HasSum (f ∘ coe : s → α) a ↔ HasSum f a :=
  Subtype.coe_injective.has_sum_iff <| by
    simpa using support_subset_iff'.1 hf

theorem has_sum_subtype_iff_indicator {s : Set β} : HasSum (f ∘ coe : s → α) a ↔ HasSum (s.indicator f) a := by
  rw [← Set.indicator_range_comp, Subtype.range_coe, has_sum_subtype_iff_of_support_subset Set.support_indicator_subset]

theorem summable_subtype_iff_indicator {s : Set β} : Summable (f ∘ coe : s → α) ↔ Summable (s.indicator f) :=
  exists_congr fun _ => has_sum_subtype_iff_indicator

@[simp]
theorem has_sum_subtype_support : HasSum (f ∘ coe : Support f → α) a ↔ HasSum f a :=
  has_sum_subtype_iff_of_support_subset <| Set.Subset.refl _

theorem has_sum_fintype [Fintype β] (f : β → α) : HasSum f (∑ b, f b) :=
  OrderTop.tendsto_at_top_nhds _

protected theorem Finset.has_sum (s : Finset β) (f : β → α) : HasSum (f ∘ coe : (↑s : Set β) → α) (∑ b in s, f b) := by
  rw [← sum_attach]
  exact has_sum_fintype _

protected theorem Finset.summable (s : Finset β) (f : β → α) : Summable (f ∘ coe : (↑s : Set β) → α) :=
  (s.HasSum f).Summable

protected theorem Set.Finite.summable {s : Set β} (hs : s.Finite) (f : β → α) : Summable (f ∘ coe : s → α) := by
  convert hs.to_finset.summable f <;> simp only [← hs.coe_to_finset]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b «expr ∉ » s)
/-- If a function `f` vanishes outside of a finite set `s`, then it `has_sum` `∑ b in s, f b`. -/
theorem has_sum_sum_of_ne_finset_zero (hf : ∀ (b) (_ : b ∉ s), f b = 0) : HasSum f (∑ b in s, f b) :=
  (has_sum_subtype_iff_of_support_subset <| support_subset_iff'.2 hf).1 <| s.HasSum f

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b «expr ∉ » s)
theorem summable_of_ne_finset_zero (hf : ∀ (b) (_ : b ∉ s), f b = 0) : Summable f :=
  (has_sum_sum_of_ne_finset_zero hf).Summable

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b' «expr ≠ » b)
theorem has_sum_single {f : β → α} (b : β) (hf : ∀ (b') (_ : b' ≠ b), f b' = 0) : HasSum f (f b) :=
  suffices HasSum f (∑ b' in {b}, f b') by
    simpa using this
  has_sum_sum_of_ne_finset_zero <| by
    simpa [← hf]

theorem has_sum_ite_eq (b : β) [DecidablePred (· = b)] (a : α) : HasSum (fun b' => if b' = b then a else 0) a := by
  convert has_sum_single b _
  · exact (if_pos rfl).symm
    
  intro b' hb'
  exact if_neg hb'

theorem Equivₓ.has_sum_iff (e : γ ≃ β) : HasSum (f ∘ e) a ↔ HasSum f a :=
  e.Injective.has_sum_iff <| by
    simp

theorem Function.Injective.has_sum_range_iff {g : γ → β} (hg : Injective g) :
    HasSum (fun x : Set.Range g => f x) a ↔ HasSum (f ∘ g) a :=
  (Equivₓ.ofInjective g hg).has_sum_iff.symm

theorem Equivₓ.summable_iff (e : γ ≃ β) : Summable (f ∘ e) ↔ Summable f :=
  exists_congr fun a => e.has_sum_iff

theorem Summable.prod_symm {f : β × γ → α} (hf : Summable f) : Summable fun p : γ × β => f p.swap :=
  (Equivₓ.prodComm γ β).summable_iff.2 hf

theorem Equivₓ.has_sum_iff_of_support {g : γ → α} (e : Support f ≃ Support g) (he : ∀ x : Support f, g (e x) = f x) :
    HasSum f a ↔ HasSum g a := by
  have : (g ∘ coe) ∘ e = f ∘ coe := funext he
  rw [← has_sum_subtype_support, ← this, e.has_sum_iff, has_sum_subtype_support]

theorem has_sum_iff_has_sum_of_ne_zero_bij {g : γ → α} (i : Support g → β) (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y)
    (hf : Support f ⊆ Set.Range i) (hfg : ∀ x, f (i x) = g x) : HasSum f a ↔ HasSum g a :=
  Iff.symm <|
    Equivₓ.has_sum_iff_of_support
      (Equivₓ.ofBijective (fun x => ⟨i x, fun hx => x.coe_prop <| hfg x ▸ hx⟩)
        ⟨fun x y h => Subtype.ext <| hi <| Subtype.ext_iff.1 h, fun y =>
          (hf y.coe_prop).imp fun x hx => Subtype.ext hx⟩)
      hfg

theorem Equivₓ.summable_iff_of_support {g : γ → α} (e : Support f ≃ Support g) (he : ∀ x : Support f, g (e x) = f x) :
    Summable f ↔ Summable g :=
  exists_congr fun _ => e.has_sum_iff_of_support he

protected theorem HasSum.map [AddCommMonoidₓ γ] [TopologicalSpace γ] (hf : HasSum f a) {G} [AddMonoidHomClass G α γ]
    (g : G) (hg : Continuous g) : HasSum (g ∘ f) (g a) :=
  have : (g ∘ fun s : Finset β => ∑ b in s, f b) = fun s : Finset β => ∑ b in s, g (f b) := funext <| map_sum g _
  show Tendsto (fun s : Finset β => ∑ b in s, g (f b)) atTop (𝓝 (g a)) from this ▸ (hg.Tendsto a).comp hf

protected theorem Summable.map [AddCommMonoidₓ γ] [TopologicalSpace γ] (hf : Summable f) {G} [AddMonoidHomClass G α γ]
    (g : G) (hg : Continuous g) : Summable (g ∘ f) :=
  (hf.HasSum.map g hg).Summable

protected theorem Summable.map_iff_of_left_inverse [AddCommMonoidₓ γ] [TopologicalSpace γ] {G G'}
    [AddMonoidHomClass G α γ] [AddMonoidHomClass G' γ α] (g : G) (g' : G') (hg : Continuous g) (hg' : Continuous g')
    (hinv : Function.LeftInverse g' g) : Summable (g ∘ f) ↔ Summable f :=
  ⟨fun h => by
    have := h.map _ hg'
    rwa [← Function.comp.assoc, hinv.id] at this, fun h => h.map _ hg⟩

/-- A special case of `summable.map_iff_of_left_inverse` for convenience -/
protected theorem Summable.map_iff_of_equiv [AddCommMonoidₓ γ] [TopologicalSpace γ] {G} [AddEquivClass G α γ] (g : G)
    (hg : Continuous g) (hg' : Continuous (AddEquivClass.inv g : γ → α)) : Summable (g ∘ f) ↔ Summable f :=
  Summable.map_iff_of_left_inverse g (g : α ≃+ γ).symm hg hg' (AddEquivClass.left_inv g)

/-- If `f : ℕ → α` has sum `a`, then the partial sums `∑_{i=0}^{n-1} f i` converge to `a`. -/
theorem HasSum.tendsto_sum_nat {f : ℕ → α} (h : HasSum f a) : Tendsto (fun n : ℕ => ∑ i in range n, f i) atTop (𝓝 a) :=
  h.comp tendsto_finset_range

theorem HasSum.unique {a₁ a₂ : α} [T2Space α] : HasSum f a₁ → HasSum f a₂ → a₁ = a₂ :=
  tendsto_nhds_unique

theorem Summable.has_sum_iff_tendsto_nat [T2Space α] {f : ℕ → α} {a : α} (hf : Summable f) :
    HasSum f a ↔ Tendsto (fun n : ℕ => ∑ i in range n, f i) atTop (𝓝 a) := by
  refine' ⟨fun h => h.tendsto_sum_nat, fun h => _⟩
  rw [tendsto_nhds_unique h hf.has_sum.tendsto_sum_nat]
  exact hf.has_sum

theorem Function.Surjective.summable_iff_of_has_sum_iff {α' : Type _} [AddCommMonoidₓ α'] [TopologicalSpace α']
    {e : α' → α} (hes : Function.Surjective e) {f : β → α} {g : γ → α'} (he : ∀ {a}, HasSum f (e a) ↔ HasSum g a) :
    Summable f ↔ Summable g :=
  hes.exists.trans <| exists_congr <| @he

section MulOpposite

open MulOpposite

theorem HasSum.op (hf : HasSum f a) : HasSum (fun a => op (f a)) (op a) :=
  (hf.map (@opAddEquiv α _) continuous_op : _)

theorem Summable.op (hf : Summable f) : Summable (op ∘ f) :=
  hf.HasSum.op.Summable

theorem HasSum.unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} (hf : HasSum f a) : HasSum (fun a => unop (f a)) (unop a) :=
  (hf.map (@opAddEquiv α _).symm continuous_unop : _)

theorem Summable.unop {f : β → αᵐᵒᵖ} (hf : Summable f) : Summable (unop ∘ f) :=
  hf.HasSum.unop.Summable

@[simp]
theorem has_sum_op : HasSum (fun a => op (f a)) (op a) ↔ HasSum f a :=
  ⟨HasSum.unop, HasSum.op⟩

@[simp]
theorem has_sum_unop {f : β → αᵐᵒᵖ} {a : αᵐᵒᵖ} : HasSum (fun a => unop (f a)) (unop a) ↔ HasSum f a :=
  ⟨HasSum.op, HasSum.unop⟩

@[simp]
theorem summable_op : (Summable fun a => op (f a)) ↔ Summable f :=
  ⟨Summable.unop, Summable.op⟩

@[simp]
theorem summable_unop {f : β → αᵐᵒᵖ} : (Summable fun a => unop (f a)) ↔ Summable f :=
  ⟨Summable.op, Summable.unop⟩

end MulOpposite

section HasContinuousStar

variable [StarAddMonoid α] [HasContinuousStar α]

theorem HasSum.star (h : HasSum f a) : HasSum (fun b => star (f b)) (star a) := by
  simpa only using h.map (starAddEquiv : α ≃+ α) continuous_star

theorem Summable.star (hf : Summable f) : Summable fun b => star (f b) :=
  hf.HasSum.star.Summable

theorem Summable.of_star (hf : Summable fun b => star (f b)) : Summable f := by
  simpa only [← star_star] using hf.star

@[simp]
theorem summable_star_iff : (Summable fun b => star (f b)) ↔ Summable f :=
  ⟨Summable.of_star, Summable.star⟩

@[simp]
theorem summable_star_iff' : Summable (star f) ↔ Summable f :=
  summable_star_iff

end HasContinuousStar

variable [HasContinuousAdd α]

theorem HasSum.add (hf : HasSum f a) (hg : HasSum g b) : HasSum (fun b => f b + g b) (a + b) := by
  simp only [← HasSum, ← sum_add_distrib] <;> exact hf.add hg

theorem Summable.add (hf : Summable f) (hg : Summable g) : Summable fun b => f b + g b :=
  (hf.HasSum.add hg.HasSum).Summable

theorem has_sum_sum {f : γ → β → α} {a : γ → α} {s : Finset γ} :
    (∀, ∀ i ∈ s, ∀, HasSum (f i) (a i)) → HasSum (fun b => ∑ i in s, f i b) (∑ i in s, a i) :=
  Finset.induction_on s
    (by
      simp only [← has_sum_zero, ← sum_empty, ← forall_true_iff])
    (by
      simp (config := { contextual := true })only [← HasSum.add, ← sum_insert, ← mem_insert, ← forall_eq_or_imp, ←
        forall_2_true_iff, ← not_false_iff, ← forall_true_iff])

theorem summable_sum {f : γ → β → α} {s : Finset γ} (hf : ∀, ∀ i ∈ s, ∀, Summable (f i)) :
    Summable fun b => ∑ i in s, f i b :=
  (has_sum_sum fun i hi => (hf i hi).HasSum).Summable

theorem HasSum.add_disjoint {s t : Set β} (hs : Disjoint s t) (ha : HasSum (f ∘ coe : s → α) a)
    (hb : HasSum (f ∘ coe : t → α) b) : HasSum (f ∘ coe : s ∪ t → α) (a + b) := by
  rw [has_sum_subtype_iff_indicator] at *
  rw [Set.indicator_union_of_disjoint hs]
  exact ha.add hb

theorem HasSum.add_is_compl {s t : Set β} (hs : IsCompl s t) (ha : HasSum (f ∘ coe : s → α) a)
    (hb : HasSum (f ∘ coe : t → α) b) : HasSum f (a + b) := by
  simpa [hs.compl_eq] using (has_sum_subtype_iff_indicator.1 ha).add (has_sum_subtype_iff_indicator.1 hb)

theorem HasSum.add_compl {s : Set β} (ha : HasSum (f ∘ coe : s → α) a) (hb : HasSum (f ∘ coe : sᶜ → α) b) :
    HasSum f (a + b) :=
  ha.add_is_compl is_compl_compl hb

theorem Summable.add_compl {s : Set β} (hs : Summable (f ∘ coe : s → α)) (hsc : Summable (f ∘ coe : sᶜ → α)) :
    Summable f :=
  (hs.HasSum.add_compl hsc.HasSum).Summable

theorem HasSum.compl_add {s : Set β} (ha : HasSum (f ∘ coe : sᶜ → α) a) (hb : HasSum (f ∘ coe : s → α) b) :
    HasSum f (a + b) :=
  ha.add_is_compl is_compl_compl.symm hb

theorem HasSum.even_add_odd {f : ℕ → α} (he : HasSum (fun k => f (2 * k)) a) (ho : HasSum (fun k => f (2 * k + 1)) b) :
    HasSum f (a + b) := by
  have := mul_right_injective₀ (@two_ne_zero ℕ _ _)
  replace he := this.has_sum_range_iff.2 he
  replace ho := ((add_left_injective 1).comp this).has_sum_range_iff.2 ho
  refine' he.add_is_compl _ ho
  simpa [← (· ∘ ·)] using Nat.is_compl_even_odd

theorem Summable.compl_add {s : Set β} (hs : Summable (f ∘ coe : sᶜ → α)) (hsc : Summable (f ∘ coe : s → α)) :
    Summable f :=
  (hs.HasSum.compl_add hsc.HasSum).Summable

theorem Summable.even_add_odd {f : ℕ → α} (he : Summable fun k => f (2 * k)) (ho : Summable fun k => f (2 * k + 1)) :
    Summable f :=
  (he.HasSum.even_add_odd ho.HasSum).Summable

theorem HasSum.sigma [T3Space α] {γ : β → Type _} {f : (Σb : β, γ b) → α} {g : β → α} {a : α} (ha : HasSum f a)
    (hf : ∀ b, HasSum (fun c => f ⟨b, c⟩) (g b)) : HasSum g a := by
  refine' (at_top_basis.tendsto_iff (closed_nhds_basis a)).mpr _
  rintro s ⟨hs, hsc⟩
  rcases mem_at_top_sets.mp (ha hs) with ⟨u, hu⟩
  use u.image Sigma.fst, trivialₓ
  intro bs hbs
  simp only [← Set.mem_preimage, ← ge_iff_le, ← Finset.le_iff_subset] at hu
  have : tendsto (fun t : Finset (Σb, γ b) => ∑ p in t.filter fun p => p.1 ∈ bs, f p) at_top (𝓝 <| ∑ b in bs, g b) := by
    simp only [sigma_preimage_mk, ← sum_sigma]
    refine' tendsto_finset_sum _ fun b hb => _
    change tendsto (fun t => (fun t => ∑ s in t, f ⟨b, s⟩) (preimage t (Sigma.mk b) _)) at_top (𝓝 (g b))
    exact tendsto.comp (hf b) (tendsto_finset_preimage_at_top_at_top _)
  refine' hsc.mem_of_tendsto this (eventually_at_top.2 ⟨u, fun t ht => hu _ fun x hx => _⟩)
  exact mem_filter.2 ⟨ht hx, hbs <| mem_image_of_mem _ hx⟩

/-- If a series `f` on `β × γ` has sum `a` and for each `b` the restriction of `f` to `{b} × γ`
has sum `g b`, then the series `g` has sum `a`. -/
theorem HasSum.prod_fiberwise [T3Space α] {f : β × γ → α} {g : β → α} {a : α} (ha : HasSum f a)
    (hf : ∀ b, HasSum (fun c => f (b, c)) (g b)) : HasSum g a :=
  HasSum.sigma ((Equivₓ.sigmaEquivProd β γ).has_sum_iff.2 ha) hf

theorem Summable.sigma' [T3Space α] {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f)
    (hf : ∀ b, Summable fun c => f ⟨b, c⟩) : Summable fun b => ∑' c, f ⟨b, c⟩ :=
  (ha.HasSum.Sigma fun b => (hf b).HasSum).Summable

theorem HasSum.sigma_of_has_sum [T3Space α] {γ : β → Type _} {f : (Σb : β, γ b) → α} {g : β → α} {a : α}
    (ha : HasSum g a) (hf : ∀ b, HasSum (fun c => f ⟨b, c⟩) (g b)) (hf' : Summable f) : HasSum f a := by
  simpa [← (hf'.has_sum.sigma hf).unique ha] using hf'.has_sum

end HasSum

section tsum

variable [AddCommMonoidₓ α] [TopologicalSpace α]

theorem tsum_congr_subtype (f : β → α) {s t : Set β} (h : s = t) : (∑' x : s, f x) = ∑' x : t, f x := by
  rw [h]

variable [T2Space α] {f g : β → α} {a a₁ a₂ : α}

theorem HasSum.tsum_eq (ha : HasSum f a) : (∑' b, f b) = a :=
  (Summable.has_sum ⟨a, ha⟩).unique ha

theorem Summable.has_sum_iff (h : Summable f) : HasSum f a ↔ (∑' b, f b) = a :=
  Iff.intro HasSum.tsum_eq fun eq => Eq ▸ h.HasSum

@[simp]
theorem tsum_zero : (∑' b : β, (0 : α)) = 0 :=
  has_sum_zero.tsum_eq

@[simp]
theorem tsum_empty [IsEmpty β] : (∑' b, f b) = 0 :=
  has_sum_empty.tsum_eq

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b «expr ∉ » s)
theorem tsum_eq_sum {f : β → α} {s : Finset β} (hf : ∀ (b) (_ : b ∉ s), f b = 0) : (∑' b, f b) = ∑ b in s, f b :=
  (has_sum_sum_of_ne_finset_zero hf).tsum_eq

theorem tsum_congr {α β : Type _} [AddCommMonoidₓ α] [TopologicalSpace α] {f g : β → α} (hfg : ∀ b, f b = g b) :
    (∑' b, f b) = ∑' b, g b :=
  congr_arg tsum (funext hfg)

theorem tsum_fintype [Fintype β] (f : β → α) : (∑' b, f b) = ∑ b, f b :=
  (has_sum_fintype f).tsum_eq

theorem tsum_bool (f : Bool → α) : (∑' i : Bool, f i) = f False + f True := by
  rw [tsum_fintype, Finset.sum_eq_add] <;> simp

@[simp]
theorem Finset.tsum_subtype (s : Finset β) (f : β → α) : (∑' x : { x // x ∈ s }, f x) = ∑ x in s, f x :=
  (s.HasSum f).tsum_eq

@[simp]
theorem Finset.tsum_subtype' (s : Finset β) (f : β → α) : (∑' x : (s : Set β), f x) = ∑ x in s, f x :=
  s.tsum_subtype f

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b' «expr ≠ » b)
theorem tsum_eq_single {f : β → α} (b : β) (hf : ∀ (b') (_ : b' ≠ b), f b' = 0) : (∑' b, f b) = f b :=
  (has_sum_single b hf).tsum_eq

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (b' c')
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b' «expr ≠ » b)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (b' c')
theorem tsum_tsum_eq_single (f : β → γ → α) (b : β) (c : γ) (hfb : ∀ (b') (_ : b' ≠ b), f b' c = 0)
    (hfc : ∀ (b' : β) (c' : γ), c' ≠ c → f b' c' = 0) : (∑' (b') (c'), f b' c') = f b c :=
  calc
    (∑' (b') (c'), f b' c') = ∑' b', f b' c := tsum_congr fun b' => tsum_eq_single _ (hfc b')
    _ = f b c := tsum_eq_single _ hfb
    

@[simp]
theorem tsum_ite_eq (b : β) [DecidablePred (· = b)] (a : α) : (∑' b', if b' = b then a else 0) = a :=
  (has_sum_ite_eq b a).tsum_eq

theorem tsum_dite_right (P : Prop) [Decidable P] (x : β → ¬P → α) :
    (∑' b : β, if h : P then (0 : α) else x b h) = if h : P then (0 : α) else ∑' b : β, x b h := by
  by_cases' hP : P <;> simp [← hP]

theorem tsum_dite_left (P : Prop) [Decidable P] (x : β → P → α) :
    (∑' b : β, if h : P then x b h else 0) = if h : P then ∑' b : β, x b h else 0 := by
  by_cases' hP : P <;> simp [← hP]

theorem Function.Surjective.tsum_eq_tsum_of_has_sum_iff_has_sum {α' : Type _} [AddCommMonoidₓ α'] [TopologicalSpace α']
    {e : α' → α} (hes : Function.Surjective e) (h0 : e 0 = 0) {f : β → α} {g : γ → α'}
    (h : ∀ {a}, HasSum f (e a) ↔ HasSum g a) : (∑' b, f b) = e (∑' c, g c) :=
  by_cases (fun this : Summable g => (h.mpr this.HasSum).tsum_eq) fun hg : ¬Summable g => by
    have hf : ¬Summable f := mt (hes.summable_iff_of_has_sum_iff @h).1 hg
    simp [← tsum, ← hf, ← hg, ← h0]

theorem tsum_eq_tsum_of_has_sum_iff_has_sum {f : β → α} {g : γ → α} (h : ∀ {a}, HasSum f a ↔ HasSum g a) :
    (∑' b, f b) = ∑' c, g c :=
  surjective_id.tsum_eq_tsum_of_has_sum_iff_has_sum rfl @h

theorem Equivₓ.tsum_eq (j : γ ≃ β) (f : β → α) : (∑' c, f (j c)) = ∑' b, f b :=
  tsum_eq_tsum_of_has_sum_iff_has_sum fun a => j.has_sum_iff

theorem Equivₓ.tsum_eq_tsum_of_support {f : β → α} {g : γ → α} (e : Support f ≃ Support g) (he : ∀ x, g (e x) = f x) :
    (∑' x, f x) = ∑' y, g y :=
  tsum_eq_tsum_of_has_sum_iff_has_sum fun _ => e.has_sum_iff_of_support he

theorem tsum_eq_tsum_of_ne_zero_bij {g : γ → α} (i : Support g → β) (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y)
    (hf : Support f ⊆ Set.Range i) (hfg : ∀ x, f (i x) = g x) : (∑' x, f x) = ∑' y, g y :=
  tsum_eq_tsum_of_has_sum_iff_has_sum fun _ => has_sum_iff_has_sum_of_ne_zero_bij i hi hf hfg

theorem tsum_subtype (s : Set β) (f : β → α) : (∑' x : s, f x) = ∑' x, s.indicator f x :=
  tsum_eq_tsum_of_has_sum_iff_has_sum fun _ => has_sum_subtype_iff_indicator

theorem tsum_op : (∑' x, MulOpposite.op (f x)) = MulOpposite.op (∑' x, f x) := by
  by_cases' h : Summable f
  · exact h.has_sum.op.tsum_eq
    
  · have ho := summable_op.not.mpr h
    rw [tsum_eq_zero_of_not_summable h, tsum_eq_zero_of_not_summable ho, MulOpposite.op_zero]
    

theorem tsum_unop {f : β → αᵐᵒᵖ} : (∑' x, MulOpposite.unop (f x)) = MulOpposite.unop (∑' x, f x) :=
  MulOpposite.op_injective tsum_op.symm

section HasContinuousAdd

variable [HasContinuousAdd α]

theorem tsum_add (hf : Summable f) (hg : Summable g) : (∑' b, f b + g b) = (∑' b, f b) + ∑' b, g b :=
  (hf.HasSum.add hg.HasSum).tsum_eq

theorem tsum_sum {f : γ → β → α} {s : Finset γ} (hf : ∀, ∀ i ∈ s, ∀, Summable (f i)) :
    (∑' b, ∑ i in s, f i b) = ∑ i in s, ∑' b, f i b :=
  (has_sum_sum fun i hi => (hf i hi).HasSum).tsum_eq

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (b c)
theorem tsum_sigma' [T3Space α] {γ : β → Type _} {f : (Σb : β, γ b) → α} (h₁ : ∀ b, Summable fun c => f ⟨b, c⟩)
    (h₂ : Summable f) : (∑' p, f p) = ∑' (b) (c), f ⟨b, c⟩ :=
  (h₂.HasSum.Sigma fun b => (h₁ b).HasSum).tsum_eq.symm

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (b c)
theorem tsum_prod' [T3Space α] {f : β × γ → α} (h : Summable f) (h₁ : ∀ b, Summable fun c => f (b, c)) :
    (∑' p, f p) = ∑' (b) (c), f (b, c) :=
  (h.HasSum.prod_fiberwise fun b => (h₁ b).HasSum).tsum_eq.symm

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (c b)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (b c)
theorem tsum_comm' [T3Space α] {f : β → γ → α} (h : Summable (Function.uncurry f)) (h₁ : ∀ b, Summable (f b))
    (h₂ : ∀ c, Summable fun b => f b c) : (∑' (c) (b), f b c) = ∑' (b) (c), f b c := by
  erw [← tsum_prod' h h₁, ← tsum_prod' h.prod_symm h₂, ← (Equivₓ.prodComm β γ).tsum_eq]
  rfl
  assumption

end HasContinuousAdd

section HasContinuousStar

variable [StarAddMonoid α] [HasContinuousStar α]

theorem tsum_star : star (∑' b, f b) = ∑' b, star (f b) := by
  by_cases' hf : Summable f
  · exact hf.has_sum.star.tsum_eq.symm
    
  · rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt Summable.of_star hf), star_zero]
    

end HasContinuousStar

section Encodable

open Encodable

variable [Encodable γ]

/-- You can compute a sum over an encodably type by summing over the natural numbers and
  taking a supremum. This is useful for outer measures. -/
theorem tsum_supr_decode₂ [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (s : γ → β) :
    (∑' i : ℕ, m (⨆ b ∈ decode₂ γ i, s b)) = ∑' b : γ, m (s b) := by
  have H : ∀ n, m (⨆ b ∈ decode₂ γ n, s b) ≠ 0 → (decode₂ γ n).isSome := by
    intro n h
    cases' decode₂ γ n with b
    · refine'
        (h <| by
            simp [← m0]).elim
      
    · exact rfl
      
  symm
  refine' tsum_eq_tsum_of_ne_zero_bij (fun a => Option.getₓ (H a.1 a.2)) _ _ _
  · rintro ⟨m, hm⟩ ⟨n, hn⟩ e
    have := mem_decode₂.1 (Option.get_memₓ (H n hn))
    rwa [← e, mem_decode₂.1 (Option.get_memₓ (H m hm))] at this
    
  · intro b h
    refine' ⟨⟨encode b, _⟩, _⟩
    · simp only [← mem_support, ← encodek₂] at h⊢
      convert h
      simp [← Set.ext_iff, ← encodek₂]
      
    · exact Option.get_of_memₓ _ (encodek₂ _)
      
    
  · rintro ⟨n, h⟩
    dsimp' only [← Subtype.coe_mk]
    trans
    swap
    rw [show decode₂ γ n = _ from Option.get_memₓ (H n h)]
    congr
    simp [← ext_iff, -Option.some_getₓ]
    

/-- `tsum_supr_decode₂` specialized to the complete lattice of sets. -/
theorem tsum_Union_decode₂ (m : Set β → α) (m0 : m ∅ = 0) (s : γ → Set β) :
    (∑' i, m (⋃ b ∈ decode₂ γ i, s b)) = ∑' b, m (s b) :=
  tsum_supr_decode₂ m m0 s

/-! Some properties about measure-like functions.
  These could also be functions defined on complete sublattices of sets, with the property
  that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/


/-- If a function is countably sub-additive then it is sub-additive on encodable types -/
theorem rel_supr_tsum [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s : γ → β) : R (m (⨆ b : γ, s b)) (∑' b : γ, m (s b)) :=
  by
  rw [← supr_decode₂, ← tsum_supr_decode₂ _ m0 s]
  exact m_supr _

/-- If a function is countably sub-additive then it is sub-additive on finite sets -/
theorem rel_supr_sum [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s : δ → β) (t : Finset δ) :
    R (m (⨆ d ∈ t, s d)) (∑ d in t, m (s d)) := by
  cases t.nonempty_encodable
  rw [supr_subtype']
  convert rel_supr_tsum m m0 R m_supr _
  rw [← Finset.tsum_subtype]
  assumption

/-- If a function is countably sub-additive then it is binary sub-additive -/
theorem rel_sup_add [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_supr : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s₁ s₂ : β) : R (m (s₁⊔s₂)) (m s₁ + m s₂) := by
  convert rel_supr_tsum m m0 R m_supr fun b => cond b s₁ s₂
  · simp only [← supr_bool_eq, ← cond]
    
  · rw [tsum_fintype, Fintype.sum_bool, cond, cond]
    

end Encodable

variable [HasContinuousAdd α]

theorem tsum_add_tsum_compl {s : Set β} (hs : Summable (f ∘ coe : s → α)) (hsc : Summable (f ∘ coe : sᶜ → α)) :
    ((∑' x : s, f x) + ∑' x : sᶜ, f x) = ∑' x, f x :=
  (hs.HasSum.add_compl hsc.HasSum).tsum_eq.symm

theorem tsum_union_disjoint {s t : Set β} (hd : Disjoint s t) (hs : Summable (f ∘ coe : s → α))
    (ht : Summable (f ∘ coe : t → α)) : (∑' x : s ∪ t, f x) = (∑' x : s, f x) + ∑' x : t, f x :=
  (hs.HasSum.add_disjoint hd ht.HasSum).tsum_eq

theorem tsum_even_add_odd {f : ℕ → α} (he : Summable fun k => f (2 * k)) (ho : Summable fun k => f (2 * k + 1)) :
    ((∑' k, f (2 * k)) + ∑' k, f (2 * k + 1)) = ∑' k, f k :=
  (he.HasSum.even_add_odd ho.HasSum).tsum_eq.symm

end tsum

section Prod

variable [AddCommMonoidₓ α] [TopologicalSpace α] [AddCommMonoidₓ γ] [TopologicalSpace γ]

theorem HasSum.prod_mk {f : β → α} {g : β → γ} {a : α} {b : γ} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun x => (⟨f x, g x⟩ : α × γ)) ⟨a, b⟩ := by
  simp [← HasSum, prod_mk_sum, ← Filter.Tendsto.prod_mk_nhds hf hg]

end Prod

section Pi

variable {ι : Type _} {π : α → Type _} [∀ x, AddCommMonoidₓ (π x)] [∀ x, TopologicalSpace (π x)]

theorem Pi.has_sum {f : ι → ∀ x, π x} {g : ∀ x, π x} : HasSum f g ↔ ∀ x, HasSum (fun i => f i x) (g x) := by
  simp only [← HasSum, ← tendsto_pi_nhds, ← sum_apply]

theorem Pi.summable {f : ι → ∀ x, π x} : Summable f ↔ ∀ x, Summable fun i => f i x := by
  simp only [← Summable, ← Pi.has_sum, ← skolem]

theorem tsum_apply [∀ x, T2Space (π x)] {f : ι → ∀ x, π x} {x : α} (hf : Summable f) : (∑' i, f i) x = ∑' i, f i x :=
  (Pi.has_sum.mp hf.HasSum x).tsum_eq.symm

end Pi

section TopologicalGroup

variable [AddCommGroupₓ α] [TopologicalSpace α] [TopologicalAddGroup α]

variable {f g : β → α} {a a₁ a₂ : α}

-- `by simpa using` speeds up elaboration. Why?
theorem HasSum.neg (h : HasSum f a) : HasSum (fun b => -f b) (-a) := by
  simpa only using h.map (-AddMonoidHom.id α) continuous_neg

theorem Summable.neg (hf : Summable f) : Summable fun b => -f b :=
  hf.HasSum.neg.Summable

theorem Summable.of_neg (hf : Summable fun b => -f b) : Summable f := by
  simpa only [← neg_negₓ] using hf.neg

theorem summable_neg_iff : (Summable fun b => -f b) ↔ Summable f :=
  ⟨Summable.of_neg, Summable.neg⟩

theorem HasSum.sub (hf : HasSum f a₁) (hg : HasSum g a₂) : HasSum (fun b => f b - g b) (a₁ - a₂) := by
  simp only [← sub_eq_add_neg]
  exact hf.add hg.neg

theorem Summable.sub (hf : Summable f) (hg : Summable g) : Summable fun b => f b - g b :=
  (hf.HasSum.sub hg.HasSum).Summable

theorem Summable.trans_sub (hg : Summable g) (hfg : Summable fun b => f b - g b) : Summable f := by
  simpa only [← sub_add_cancel] using hfg.add hg

theorem summable_iff_of_summable_sub (hfg : Summable fun b => f b - g b) : Summable f ↔ Summable g :=
  ⟨fun hf =>
    hf.trans_sub <| by
      simpa only [← neg_sub] using hfg.neg,
    fun hg => hg.trans_sub hfg⟩

theorem HasSum.update (hf : HasSum f a₁) (b : β) [DecidableEq β] (a : α) : HasSum (update f b a) (a - f b + a₁) := by
  convert (has_sum_ite_eq b _).add hf
  ext b'
  by_cases' h : b' = b
  · rw [h, update_same]
    simp only [← eq_self_iff_true, ← if_true, ← sub_add_cancel]
    
  simp only [← h, ← update_noteq, ← if_false, ← Ne.def, ← zero_addₓ, ← not_false_iff]

theorem Summable.update (hf : Summable f) (b : β) [DecidableEq β] (a : α) : Summable (update f b a) :=
  (hf.HasSum.update b a).Summable

theorem HasSum.has_sum_compl_iff {s : Set β} (hf : HasSum (f ∘ coe : s → α) a₁) :
    HasSum (f ∘ coe : sᶜ → α) a₂ ↔ HasSum f (a₁ + a₂) := by
  refine' ⟨fun h => hf.add_compl h, fun h => _⟩
  rw [has_sum_subtype_iff_indicator] at hf⊢
  rw [Set.indicator_compl]
  simpa only [← add_sub_cancel'] using h.sub hf

theorem HasSum.has_sum_iff_compl {s : Set β} (hf : HasSum (f ∘ coe : s → α) a₁) :
    HasSum f a₂ ↔ HasSum (f ∘ coe : sᶜ → α) (a₂ - a₁) :=
  Iff.symm <|
    hf.has_sum_compl_iff.trans <| by
      rw [add_sub_cancel'_right]

theorem Summable.summable_compl_iff {s : Set β} (hf : Summable (f ∘ coe : s → α)) :
    Summable (f ∘ coe : sᶜ → α) ↔ Summable f :=
  ⟨fun ⟨a, ha⟩ => (hf.HasSum.has_sum_compl_iff.1 ha).Summable, fun ⟨a, ha⟩ =>
    (hf.HasSum.has_sum_iff_compl.1 ha).Summable⟩

protected theorem Finset.has_sum_compl_iff (s : Finset β) :
    HasSum (fun x : { x // x ∉ s } => f x) a ↔ HasSum f (a + ∑ i in s, f i) :=
  (s.HasSum f).has_sum_compl_iff.trans <| by
    rw [add_commₓ]

protected theorem Finset.has_sum_iff_compl (s : Finset β) :
    HasSum f a ↔ HasSum (fun x : { x // x ∉ s } => f x) (a - ∑ i in s, f i) :=
  (s.HasSum f).has_sum_iff_compl

protected theorem Finset.summable_compl_iff (s : Finset β) : (Summable fun x : { x // x ∉ s } => f x) ↔ Summable f :=
  (s.Summable f).summable_compl_iff

theorem Set.Finite.summable_compl_iff {s : Set β} (hs : s.Finite) : Summable (f ∘ coe : sᶜ → α) ↔ Summable f :=
  (hs.Summable f).summable_compl_iff

theorem has_sum_ite_eq_extract [DecidableEq β] (hf : HasSum f a) (b : β) :
    HasSum (fun n => ite (n = b) 0 (f n)) (a - f b) := by
  convert hf.update b 0 using 1
  · ext n
    rw [Function.update_apply]
    
  · rw [sub_add_eq_add_sub, zero_addₓ]
    

section tsum

variable [T2Space α]

theorem tsum_neg : (∑' b, -f b) = -∑' b, f b := by
  by_cases' hf : Summable f
  · exact hf.has_sum.neg.tsum_eq
    
  · simp [← tsum_eq_zero_of_not_summable hf, ← tsum_eq_zero_of_not_summable (mt Summable.of_neg hf)]
    

theorem tsum_sub (hf : Summable f) (hg : Summable g) : (∑' b, f b - g b) = (∑' b, f b) - ∑' b, g b :=
  (hf.HasSum.sub hg.HasSum).tsum_eq

theorem sum_add_tsum_compl {s : Finset β} (hf : Summable f) :
    ((∑ x in s, f x) + ∑' x : (↑s : Set β)ᶜ, f x) = ∑' x, f x :=
  ((s.HasSum f).add_compl (s.summable_compl_iff.2 hf).HasSum).tsum_eq.symm

/-- Let `f : β → α` be a sequence with summable series and let `b ∈ β` be an index.
Lemma `tsum_ite_eq_extract` writes `Σ f n` as the sum of `f b` plus the series of the
remaining terms. -/
theorem tsum_ite_eq_extract [DecidableEq β] (hf : Summable f) (b : β) : (∑' n, f n) = f b + ∑' n, ite (n = b) 0 (f n) :=
  by
  rw [(has_sum_ite_eq_extract hf.has_sum b).tsum_eq]
  exact (add_sub_cancel'_right _ _).symm

end tsum

/-!
### Sums on subtypes

If `s` is a finset of `α`, we show that the summability of `f` in the whole space and on the subtype
`univ - s` are equivalent, and relate their sums. For a function defined on `ℕ`, we deduce the
formula `(∑ i in range k, f i) + (∑' i, f (i + k)) = (∑' i, f i)`, in `sum_add_tsum_nat_add`.
-/


section Subtype

theorem has_sum_nat_add_iff {f : ℕ → α} (k : ℕ) {a : α} :
    HasSum (fun n => f (n + k)) a ↔ HasSum f (a + ∑ i in range k, f i) := by
  refine' Iff.trans _ (range k).has_sum_compl_iff
  rw [← (notMemRangeEquiv k).symm.has_sum_iff]
  rfl

theorem summable_nat_add_iff {f : ℕ → α} (k : ℕ) : (Summable fun n => f (n + k)) ↔ Summable f :=
  Iff.symm <|
    (Equivₓ.addRight (∑ i in range k, f i)).Surjective.summable_iff_of_has_sum_iff fun a => (has_sum_nat_add_iff k).symm

theorem has_sum_nat_add_iff' {f : ℕ → α} (k : ℕ) {a : α} :
    HasSum (fun n => f (n + k)) (a - ∑ i in range k, f i) ↔ HasSum f a := by
  simp [← has_sum_nat_add_iff]

theorem sum_add_tsum_nat_add [T2Space α] {f : ℕ → α} (k : ℕ) (h : Summable f) :
    ((∑ i in range k, f i) + ∑' i, f (i + k)) = ∑' i, f i := by
  simpa only [← add_commₓ] using ((has_sum_nat_add_iff k).1 ((summable_nat_add_iff k).2 h).HasSum).unique h.has_sum

theorem tsum_eq_zero_add [T2Space α] {f : ℕ → α} (hf : Summable f) : (∑' b, f b) = f 0 + ∑' b, f (b + 1) := by
  simpa only [← sum_range_one] using (sum_add_tsum_nat_add 1 hf).symm

/-- For `f : ℕ → α`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
theorem tendsto_sum_nat_add [T2Space α] (f : ℕ → α) : Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) := by
  by_cases' hf : Summable f
  · have h₀ : (fun i => (∑' i, f i) - ∑ j in range i, f j) = fun i => ∑' k : ℕ, f (k + i) := by
      ext1 i
      rw [sub_eq_iff_eq_add, add_commₓ, sum_add_tsum_nat_add i hf]
    have h₁ : tendsto (fun i : ℕ => ∑' i, f i) at_top (𝓝 (∑' i, f i)) := tendsto_const_nhds
    simpa only [← h₀, ← sub_self] using tendsto.sub h₁ hf.has_sum.tendsto_sum_nat
    
  · convert tendsto_const_nhds
    ext1 i
    rw [← summable_nat_add_iff i] at hf
    · exact tsum_eq_zero_of_not_summable hf
      
    · infer_instance
      
    

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both convergent then so is the `ℤ`-indexed
sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...`. -/
theorem HasSum.int_rec {b : α} {f g : ℕ → α} (hf : HasSum f a) (hg : HasSum g b) :
    @HasSum α _ _ _ (@Int.rec (fun _ => α) f g : ℤ → α) (a + b) := by
  -- note this proof works for any two-case inductive
  have h₁ : injective (coe : ℕ → ℤ) := @Int.ofNat.injₓ
  have h₂ : injective Int.negSucc := @Int.negSucc.injₓ
  have : IsCompl (Set.Range (coe : ℕ → ℤ)) (Set.Range Int.negSucc) := by
    constructor
    · rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
      
    · rintro (i | j) h
      exacts[Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]
      
  exact HasSum.add_is_compl this (h₁.has_sum_range_iff.mpr hf) (h₂.has_sum_range_iff.mpr hg)

theorem HasSum.nonneg_add_neg {b : α} {f : ℤ → α} (hnonneg : HasSum (fun n : ℕ => f n) a)
    (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + b) := by
  simp_rw [← Int.neg_succ_of_nat_coe] at hneg
  convert hnonneg.int_rec hneg using 1
  ext (i | j) <;> rfl

theorem HasSum.pos_add_zero_add_neg {b : α} {f : ℤ → α} (hpos : HasSum (fun n : ℕ => f (n + 1)) a)
    (hneg : HasSum (fun n : ℕ => f (-n.succ)) b) : HasSum f (a + f 0 + b) := by
  have : ∀ g : ℕ → α, HasSum (fun k => g (k + 1)) a → HasSum g (a + g 0) := by
    intro g hg
    simpa using (has_sum_nat_add_iff _).mp hg
  exact (this (fun n => f n) hpos).nonneg_add_neg hneg

end Subtype

end TopologicalGroup

section TopologicalSemiring

variable [NonUnitalNonAssocSemiringₓ α] [TopologicalSpace α] [TopologicalSemiring α]

variable {f g : β → α} {a a₁ a₂ : α}

theorem HasSum.mul_left (a₂) (h : HasSum f a₁) : HasSum (fun b => a₂ * f b) (a₂ * a₁) := by
  simpa only using h.map (AddMonoidHom.mulLeft a₂) (continuous_const.mul continuous_id)

theorem HasSum.mul_right (a₂) (hf : HasSum f a₁) : HasSum (fun b => f b * a₂) (a₁ * a₂) := by
  simpa only using hf.map (AddMonoidHom.mulRight a₂) (continuous_id.mul continuous_const)

theorem Summable.mul_left (a) (hf : Summable f) : Summable fun b => a * f b :=
  (hf.HasSum.mul_left _).Summable

theorem Summable.mul_right (a) (hf : Summable f) : Summable fun b => f b * a :=
  (hf.HasSum.mul_right _).Summable

section tsum

variable [T2Space α]

theorem Summable.tsum_mul_left (a) (hf : Summable f) : (∑' b, a * f b) = a * ∑' b, f b :=
  (hf.HasSum.mul_left _).tsum_eq

theorem Summable.tsum_mul_right (a) (hf : Summable f) : (∑' b, f b * a) = (∑' b, f b) * a :=
  (hf.HasSum.mul_right _).tsum_eq

theorem Commute.tsum_right (a) (h : ∀ b, Commute a (f b)) : Commute a (∑' b, f b) :=
  if hf : Summable f then (hf.tsum_mul_left a).symm.trans ((congr_arg _ <| funext h).trans (hf.tsum_mul_right a))
  else (tsum_eq_zero_of_not_summable hf).symm ▸ Commute.zero_right _

theorem Commute.tsum_left (a) (h : ∀ b, Commute (f b) a) : Commute (∑' b, f b) a :=
  ((Commute.tsum_right _) fun b => (h b).symm).symm

end tsum

end TopologicalSemiring

section ConstSmul

variable {R : Type _} [Monoidₓ R] [TopologicalSpace α] [AddCommMonoidₓ α] [DistribMulAction R α]
  [HasContinuousConstSmul R α] {f : β → α}

theorem HasSum.const_smul {a : α} {r : R} (hf : HasSum f a) : HasSum (fun z => r • f z) (r • a) :=
  hf.map (DistribMulAction.toAddMonoidHom α r) (continuous_const_smul r)

theorem Summable.const_smul {r : R} (hf : Summable f) : Summable fun z => r • f z :=
  hf.HasSum.const_smul.Summable

theorem tsum_const_smul [T2Space α] {r : R} (hf : Summable f) : (∑' z, r • f z) = r • ∑' z, f z :=
  hf.HasSum.const_smul.tsum_eq

end ConstSmul

section SmulConst

variable {R : Type _} [Semiringₓ R] [TopologicalSpace R] [TopologicalSpace α] [AddCommMonoidₓ α] [Module R α]
  [HasContinuousSmul R α] {f : β → R}

theorem HasSum.smul_const {a : α} {r : R} (hf : HasSum f r) : HasSum (fun z => f z • a) (r • a) :=
  hf.map ((smulAddHom R α).flip a) (continuous_id.smul continuous_const)

theorem Summable.smul_const {a : α} (hf : Summable f) : Summable fun z => f z • a :=
  hf.HasSum.smul_const.Summable

theorem tsum_smul_const [T2Space α] {a : α} (hf : Summable f) : (∑' z, f z • a) = (∑' z, f z) • a :=
  hf.HasSum.smul_const.tsum_eq

end SmulConst

section DivisionRing

variable [DivisionRing α] [TopologicalSpace α] [TopologicalRing α] {f g : β → α} {a a₁ a₂ : α}

theorem HasSum.div_const (h : HasSum f a) (b : α) : HasSum (fun x => f x / b) (a / b) := by
  simp only [← div_eq_mul_inv, ← h.mul_right b⁻¹]

theorem Summable.div_const (h : Summable f) (b : α) : Summable fun x => f x / b :=
  (h.HasSum.div_const b).Summable

theorem has_sum_mul_left_iff (h : a₂ ≠ 0) : HasSum f a₁ ↔ HasSum (fun b => a₂ * f b) (a₂ * a₁) :=
  ⟨HasSum.mul_left _, fun H => by
    simpa only [← inv_mul_cancel_left₀ h] using H.mul_left a₂⁻¹⟩

theorem has_sum_mul_right_iff (h : a₂ ≠ 0) : HasSum f a₁ ↔ HasSum (fun b => f b * a₂) (a₁ * a₂) :=
  ⟨HasSum.mul_right _, fun H => by
    simpa only [← mul_inv_cancel_right₀ h] using H.mul_right a₂⁻¹⟩

theorem summable_mul_left_iff (h : a ≠ 0) : Summable f ↔ Summable fun b => a * f b :=
  ⟨fun H => H.mul_left _, fun H => by
    simpa only [← inv_mul_cancel_left₀ h] using H.mul_left a⁻¹⟩

theorem summable_mul_right_iff (h : a ≠ 0) : Summable f ↔ Summable fun b => f b * a :=
  ⟨fun H => H.mul_right _, fun H => by
    simpa only [← mul_inv_cancel_right₀ h] using H.mul_right a⁻¹⟩

theorem tsum_mul_left [T2Space α] : (∑' x, a * f x) = a * ∑' x, f x :=
  if hf : Summable f then hf.tsum_mul_left a
  else
    if ha : a = 0 then by
      simp [← ha]
    else by
      rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt (summable_mul_left_iff ha).2 hf), mul_zero]

theorem tsum_mul_right [T2Space α] : (∑' x, f x * a) = (∑' x, f x) * a :=
  if hf : Summable f then hf.tsum_mul_right a
  else
    if ha : a = 0 then by
      simp [← ha]
    else by
      rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt (summable_mul_right_iff ha).2 hf), zero_mul]

end DivisionRing

section OrderTopology

variable [OrderedAddCommMonoid α] [TopologicalSpace α] [OrderClosedTopology α]

variable {f g : β → α} {a a₁ a₂ : α}

theorem has_sum_le (h : ∀ b, f b ≤ g b) (hf : HasSum f a₁) (hg : HasSum g a₂) : a₁ ≤ a₂ :=
  (le_of_tendsto_of_tendsto' hf hg) fun s => sum_le_sum fun b _ => h b

@[mono]
theorem has_sum_mono (hf : HasSum f a₁) (hg : HasSum g a₂) (h : f ≤ g) : a₁ ≤ a₂ :=
  has_sum_le h hf hg

theorem has_sum_le_of_sum_le (hf : HasSum f a) (h : ∀ s : Finset β, (∑ b in s, f b) ≤ a₂) : a ≤ a₂ :=
  le_of_tendsto' hf h

theorem le_has_sum_of_le_sum (hf : HasSum f a) (h : ∀ s : Finset β, a₂ ≤ ∑ b in s, f b) : a₂ ≤ a :=
  ge_of_tendsto' hf h

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (c «expr ∉ » set.range i)
theorem has_sum_le_inj {g : γ → α} (i : β → γ) (hi : Injective i) (hs : ∀ (c) (_ : c ∉ Set.Range i), 0 ≤ g c)
    (h : ∀ b, f b ≤ g (i b)) (hf : HasSum f a₁) (hg : HasSum g a₂) : a₁ ≤ a₂ := by
  have : HasSum (fun c => (partialInv i c).casesOn' 0 f) a₁ := by
    refine' (has_sum_iff_has_sum_of_ne_zero_bij (i ∘ coe) _ _ _).2 hf
    · exact fun c₁ c₂ eq => hi Eq
      
    · intro c hc
      rw [mem_support] at hc
      cases' eq : partial_inv i c with b <;> rw [Eq] at hc
      · contradiction
        
      · rw [partial_inv_of_injective hi] at eq
        exact ⟨⟨b, hc⟩, Eq⟩
        
      
    · intro c
      simp [← partial_inv_left hi, ← Option.casesOn']
      
  refine' has_sum_le (fun c => _) this hg
  by_cases' c ∈ Set.Range i
  · rcases h with ⟨b, rfl⟩
    rw [partial_inv_left hi, Option.casesOn']
    exact h _
    
  · have : partial_inv i c = none := dif_neg h
    rw [this, Option.casesOn']
    exact hs _ h
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (c «expr ∉ » set.range i)
theorem tsum_le_tsum_of_inj {g : γ → α} (i : β → γ) (hi : Injective i) (hs : ∀ (c) (_ : c ∉ Set.Range i), 0 ≤ g c)
    (h : ∀ b, f b ≤ g (i b)) (hf : Summable f) (hg : Summable g) : tsum f ≤ tsum g :=
  has_sum_le_inj i hi hs h hf.HasSum hg.HasSum

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b «expr ∉ » s)
theorem sum_le_has_sum (s : Finset β) (hs : ∀ (b) (_ : b ∉ s), 0 ≤ f b) (hf : HasSum f a) : (∑ b in s, f b) ≤ a :=
  ge_of_tendsto hf
    (eventually_at_top.2 ⟨s, fun t hst => (sum_le_sum_of_subset_of_nonneg hst) fun b hbt hbs => hs b hbs⟩)

theorem is_lub_has_sum (h : ∀ b, 0 ≤ f b) (hf : HasSum f a) : IsLub (Set.Range fun s : Finset β => ∑ b in s, f b) a :=
  is_lub_of_tendsto_at_top (Finset.sum_mono_set_of_nonneg h) hf

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b' «expr ≠ » b)
theorem le_has_sum (hf : HasSum f a) (b : β) (hb : ∀ (b') (_ : b' ≠ b), 0 ≤ f b') : f b ≤ a :=
  calc
    f b = ∑ b in {b}, f b := Finset.sum_singleton.symm
    _ ≤ a :=
      sum_le_has_sum _
        (by
          convert hb
          simp )
        hf
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b «expr ∉ » s)
theorem sum_le_tsum {f : β → α} (s : Finset β) (hs : ∀ (b) (_ : b ∉ s), 0 ≤ f b) (hf : Summable f) :
    (∑ b in s, f b) ≤ ∑' b, f b :=
  sum_le_has_sum s hs hf.HasSum

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b' «expr ≠ » b)
theorem le_tsum (hf : Summable f) (b : β) (hb : ∀ (b') (_ : b' ≠ b), 0 ≤ f b') : f b ≤ ∑' b, f b :=
  le_has_sum (Summable.has_sum hf) b hb

theorem tsum_le_tsum (h : ∀ b, f b ≤ g b) (hf : Summable f) (hg : Summable g) : (∑' b, f b) ≤ ∑' b, g b :=
  has_sum_le h hf.HasSum hg.HasSum

@[mono]
theorem tsum_mono (hf : Summable f) (hg : Summable g) (h : f ≤ g) : (∑' n, f n) ≤ ∑' n, g n :=
  tsum_le_tsum h hf hg

theorem tsum_le_of_sum_le (hf : Summable f) (h : ∀ s : Finset β, (∑ b in s, f b) ≤ a₂) : (∑' b, f b) ≤ a₂ :=
  has_sum_le_of_sum_le hf.HasSum h

theorem tsum_le_of_sum_le' (ha₂ : 0 ≤ a₂) (h : ∀ s : Finset β, (∑ b in s, f b) ≤ a₂) : (∑' b, f b) ≤ a₂ := by
  by_cases' hf : Summable f
  · exact tsum_le_of_sum_le hf h
    
  · rw [tsum_eq_zero_of_not_summable hf]
    exact ha₂
    

theorem HasSum.nonneg (h : ∀ b, 0 ≤ g b) (ha : HasSum g a) : 0 ≤ a :=
  has_sum_le h has_sum_zero ha

theorem HasSum.nonpos (h : ∀ b, g b ≤ 0) (ha : HasSum g a) : a ≤ 0 :=
  has_sum_le h ha has_sum_zero

theorem tsum_nonneg (h : ∀ b, 0 ≤ g b) : 0 ≤ ∑' b, g b := by
  by_cases' hg : Summable g
  · exact hg.has_sum.nonneg h
    
  · simp [← tsum_eq_zero_of_not_summable hg]
    

theorem tsum_nonpos (h : ∀ b, f b ≤ 0) : (∑' b, f b) ≤ 0 := by
  by_cases' hf : Summable f
  · exact hf.has_sum.nonpos h
    
  · simp [← tsum_eq_zero_of_not_summable hf]
    

end OrderTopology

section OrderedTopologicalGroup

variable [OrderedAddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α] [OrderClosedTopology α] {f g : β → α}
  {a₁ a₂ : α}

theorem has_sum_lt {i : β} (h : ∀ b : β, f b ≤ g b) (hi : f i < g i) (hf : HasSum f a₁) (hg : HasSum g a₂) : a₁ < a₂ :=
  by
  have : update f i 0 ≤ update g i 0 := update_le_update_iff.mpr ⟨rfl.le, fun i _ => h i⟩
  have : 0 - f i + a₁ ≤ 0 - g i + a₂ := has_sum_le this (hf.update i 0) (hg.update i 0)
  simpa only [← zero_sub, ← add_neg_cancel_left] using add_lt_add_of_lt_of_le hi this

@[mono]
theorem has_sum_strict_mono (hf : HasSum f a₁) (hg : HasSum g a₂) (h : f < g) : a₁ < a₂ :=
  let ⟨hle, i, hi⟩ := Pi.lt_def.mp h
  has_sum_lt hle hi hf hg

theorem tsum_lt_tsum {i : β} (h : ∀ b : β, f b ≤ g b) (hi : f i < g i) (hf : Summable f) (hg : Summable g) :
    (∑' n, f n) < ∑' n, g n :=
  has_sum_lt h hi hf.HasSum hg.HasSum

@[mono]
theorem tsum_strict_mono (hf : Summable f) (hg : Summable g) (h : f < g) : (∑' n, f n) < ∑' n, g n :=
  let ⟨hle, i, hi⟩ := Pi.lt_def.mp h
  tsum_lt_tsum hle hi hf hg

theorem tsum_pos (hsum : Summable g) (hg : ∀ b, 0 ≤ g b) (i : β) (hi : 0 < g i) : 0 < ∑' b, g b := by
  rw [← tsum_zero]
  exact tsum_lt_tsum hg hi summable_zero hsum

theorem has_sum_zero_iff_of_nonneg (hf : ∀ i, 0 ≤ f i) : HasSum f 0 ↔ f = 0 := by
  constructor
  · intro hf'
    ext i
    by_contra hi'
    have hi : 0 < f i := lt_of_le_of_neₓ (hf i) (Ne.symm hi')
    simpa using has_sum_lt hf hi has_sum_zero hf'
    
  · rintro rfl
    exact has_sum_zero
    

end OrderedTopologicalGroup

section CanonicallyOrdered

variable [CanonicallyOrderedAddMonoid α] [TopologicalSpace α] [OrderClosedTopology α]

variable {f : β → α} {a : α}

theorem le_has_sum' (hf : HasSum f a) (b : β) : f b ≤ a :=
  (le_has_sum hf b) fun _ _ => zero_le _

theorem le_tsum' (hf : Summable f) (b : β) : f b ≤ ∑' b, f b :=
  (le_tsum hf b) fun _ _ => zero_le _

theorem has_sum_zero_iff : HasSum f 0 ↔ ∀ x, f x = 0 := by
  refine' ⟨_, fun h => _⟩
  · contrapose!
    exact fun ⟨x, hx⟩ h => irrefl _ (lt_of_lt_of_leₓ (pos_iff_ne_zero.2 hx) (le_has_sum' h x))
    
  · convert has_sum_zero
    exact funext h
    

theorem tsum_eq_zero_iff (hf : Summable f) : (∑' i, f i) = 0 ↔ ∀ x, f x = 0 := by
  rw [← has_sum_zero_iff, hf.has_sum_iff]

theorem tsum_ne_zero_iff (hf : Summable f) : (∑' i, f i) ≠ 0 ↔ ∃ x, f x ≠ 0 := by
  rw [Ne.def, tsum_eq_zero_iff hf, not_forall]

theorem is_lub_has_sum' (hf : HasSum f a) : IsLub (Set.Range fun s : Finset β => ∑ b in s, f b) a :=
  is_lub_of_tendsto_at_top (Finset.sum_mono_set f) hf

end CanonicallyOrdered

section UniformGroup

variable [AddCommGroupₓ α] [UniformSpace α]

/-- The **Cauchy criterion** for infinite sums, also known as the **Cauchy convergence test** -/
theorem summable_iff_cauchy_seq_finset [CompleteSpace α] {f : β → α} :
    Summable f ↔ CauchySeq fun s : Finset β => ∑ b in s, f b :=
  cauchy_map_iff_exists_tendsto.symm

variable [UniformAddGroup α] {f g : β → α} {a a₁ a₂ : α}

theorem cauchy_seq_finset_iff_vanishing :
    (CauchySeq fun s : Finset β => ∑ b in s, f b) ↔
      ∀, ∀ e ∈ 𝓝 (0 : α), ∀, ∃ s : Finset β, ∀ t, Disjoint t s → (∑ b in t, f b) ∈ e :=
  by
  simp only [← CauchySeq, ← cauchy_map_iff, ← and_iff_right at_top_ne_bot, ← prod_at_top_at_top_eq, ←
    uniformity_eq_comap_nhds_zero α, ← tendsto_comap_iff, ← (· ∘ ·)]
  rw [tendsto_at_top']
  constructor
  · intro h e he
    rcases h e he with ⟨⟨s₁, s₂⟩, h⟩
    use s₁ ∪ s₂
    intro t ht
    specialize h (s₁ ∪ s₂, s₁ ∪ s₂ ∪ t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩
    simpa only [← Finset.sum_union ht.symm, ← add_sub_cancel'] using h
    
  · intro h e he
    rcases exists_nhds_half_neg he with ⟨d, hd, hde⟩
    rcases h d hd with ⟨s, h⟩
    use (s, s)
    rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
    have : ((∑ b in t₂, f b) - ∑ b in t₁, f b) = (∑ b in t₂ \ s, f b) - ∑ b in t₁ \ s, f b := by
      simp only [← (Finset.sum_sdiff ht₁).symm, ← (Finset.sum_sdiff ht₂).symm, ← add_sub_add_right_eq_sub]
    simp only [← this]
    exact hde _ (h _ Finset.sdiff_disjoint) _ (h _ Finset.sdiff_disjoint)
    

attribute [local instance] TopologicalAddGroup.t3_space

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
theorem tendsto_tsum_compl_at_top_zero [T1Space α] (f : β → α) :
    Tendsto (fun s : Finset β => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) := by
  by_cases' H : Summable f
  · intro e he
    rcases nhds_is_closed he with ⟨o, ho, oe, o_closed⟩
    simp only [← le_eq_subset, ← Set.mem_preimage, ← mem_at_top_sets, ← Filter.mem_map, ← ge_iff_le]
    obtain ⟨s, hs⟩ : ∃ s : Finset β, ∀ t : Finset β, Disjoint t s → (∑ b : β in t, f b) ∈ o :=
      cauchy_seq_finset_iff_vanishing.1 (tendsto.cauchy_seq H.has_sum) o ho
    refine' ⟨s, fun a sa => oe _⟩
    have A : Summable fun b : { x // x ∉ a } => f b := a.summable_compl_iff.2 H
    apply IsClosed.mem_of_tendsto o_closed A.has_sum (eventually_of_forall fun b => _)
    have : Disjoint (Finset.image (fun i : { x // x ∉ a } => (i : β)) b) s := by
      apply disjoint_left.2 fun i hi his => _
      rcases mem_image.1 hi with ⟨i', hi', rfl⟩
      exact i'.2 (sa his)
    convert hs _ this using 1
    rw [sum_image]
    intro i hi j hj hij
    exact Subtype.ext hij
    
  · convert tendsto_const_nhds
    ext s
    apply tsum_eq_zero_of_not_summable
    rwa [Finset.summable_compl_iff]
    

variable [CompleteSpace α]

theorem summable_iff_vanishing :
    Summable f ↔ ∀, ∀ e ∈ 𝓝 (0 : α), ∀, ∃ s : Finset β, ∀ t, Disjoint t s → (∑ b in t, f b) ∈ e := by
  rw [summable_iff_cauchy_seq_finset, cauchy_seq_finset_iff_vanishing]

-- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a`
theorem Summable.summable_of_eq_zero_or_self (hf : Summable f) (h : ∀ b, g b = 0 ∨ g b = f b) : Summable g :=
  summable_iff_vanishing.2 fun e he =>
    let ⟨s, hs⟩ := summable_iff_vanishing.1 hf e he
    ⟨s, fun t ht =>
      have eq : (∑ b in t.filter fun b => g b = f b, f b) = ∑ b in t, g b :=
        calc
          (∑ b in t.filter fun b => g b = f b, f b) = ∑ b in t.filter fun b => g b = f b, g b :=
            Finset.sum_congr rfl fun b hb => (Finset.mem_filter.1 hb).2.symm
          _ = ∑ b in t, g b := by
            refine' Finset.sum_subset (Finset.filter_subset _ _) _
            intro b hbt hb
            simp only [← (· ∉ ·), ← Finset.mem_filter, ← and_iff_right hbt] at hb
            exact (h b).resolve_right hb
          
      Eq ▸ hs _ <| Finset.disjoint_of_subset_left (Finset.filter_subset _ _) ht⟩

protected theorem Summable.indicator (hf : Summable f) (s : Set β) : Summable (s.indicator f) :=
  hf.summable_of_eq_zero_or_self <| Set.indicator_eq_zero_or_self _ _

theorem Summable.comp_injective {i : γ → β} (hf : Summable f) (hi : Injective i) : Summable (f ∘ i) := by
  simpa only [← Set.indicator_range_comp] using (hi.summable_iff _).2 (hf.indicator (Set.Range i))
  exact fun x hx => Set.indicator_of_not_mem hx _

theorem Summable.subtype (hf : Summable f) (s : Set β) : Summable (f ∘ coe : s → α) :=
  hf.comp_injective Subtype.coe_injective

theorem summable_subtype_and_compl {s : Set β} :
    ((Summable fun x : s => f x) ∧ Summable fun x : sᶜ => f x) ↔ Summable f :=
  ⟨and_imp.2 Summable.add_compl, fun h => ⟨h.Subtype s, h.Subtype (sᶜ)⟩⟩

theorem Summable.sigma_factor {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f) (b : β) :
    Summable fun c => f ⟨b, c⟩ :=
  ha.comp_injective sigma_mk_injective

theorem Summable.sigma [T1Space α] {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f) :
    Summable fun b => ∑' c, f ⟨b, c⟩ :=
  ha.sigma' fun b => ha.sigma_factor b

theorem Summable.prod_factor {f : β × γ → α} (h : Summable f) (b : β) : Summable fun c => f (b, c) :=
  h.comp_injective fun c₁ c₂ h => (Prod.ext_iff.1 h).2

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (b c)
theorem tsum_sigma [T1Space α] {γ : β → Type _} {f : (Σb : β, γ b) → α} (ha : Summable f) :
    (∑' p, f p) = ∑' (b) (c), f ⟨b, c⟩ :=
  tsum_sigma' (fun b => ha.sigma_factor b) ha

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (b c)
theorem tsum_prod [T1Space α] {f : β × γ → α} (h : Summable f) : (∑' p, f p) = ∑' (b) (c), f ⟨b, c⟩ :=
  tsum_prod' h h.prod_factor

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (c b)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (b c)
theorem tsum_comm [T1Space α] {f : β → γ → α} (h : Summable (Function.uncurry f)) :
    (∑' (c) (b), f b c) = ∑' (b) (c), f b c :=
  tsum_comm' h h.prod_factor h.prod_symm.prod_factor

theorem HasSum.sum_nat_of_sum_int [T2Space α] {f : ℤ → α} (hf : HasSum f a) :
    HasSum (fun n : ℕ => f (n + 1) + f (-n.succ)) (a - f 0) := by
  obtain ⟨b₁, h₁⟩ : Summable fun n : ℕ => f (n + 1) :=
    hf.summable.comp_injective fun x₁ x₂ => by
      simp
  obtain ⟨b₂, h₂⟩ : Summable fun n : ℕ => f (-n.succ) :=
    hf.summable.comp_injective fun x₁ x₂ => by
      simp
  convert h₁.add h₂
  rw [hf.unique (h₁.pos_add_zero_add_neg h₂)]
  abel

end UniformGroup

section TopologicalGroup

variable {G : Type _} [TopologicalSpace G] [AddCommGroupₓ G] [TopologicalAddGroup G] {f : α → G}

theorem Summable.vanishing (hf : Summable f) ⦃e : Set G⦄ (he : e ∈ 𝓝 (0 : G)) :
    ∃ s : Finset α, ∀ t, Disjoint t s → (∑ k in t, f k) ∈ e := by
  let this : UniformSpace G := TopologicalAddGroup.toUniformSpace G
  let this : UniformAddGroup G := topological_add_group_is_uniform
  rcases hf with ⟨y, hy⟩
  exact cauchy_seq_finset_iff_vanishing.1 hy.cauchy_seq e he

/-- Series divergence test: if `f` is a convergent series, then `f x` tends to zero along
`cofinite`. -/
theorem Summable.tendsto_cofinite_zero (hf : Summable f) : Tendsto f cofinite (𝓝 0) := by
  intro e he
  rw [Filter.mem_map]
  rcases hf.vanishing he with ⟨s, hs⟩
  refine' s.eventually_cofinite_nmem.mono fun x hx => _
  · simpa using hs {x} (disjoint_singleton_left.2 hx)
    

theorem Summable.tendsto_at_top_zero {f : ℕ → G} (hf : Summable f) : Tendsto f atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_at_top]
  exact hf.tendsto_cofinite_zero

theorem Summable.tendsto_top_of_pos {α : Type _} [LinearOrderedField α] [TopologicalSpace α] [OrderTopology α]
    {f : ℕ → α} (hf : Summable f⁻¹) (hf' : ∀ n, 0 < f n) : Tendsto f atTop atTop := by
  rw
    [show f = f⁻¹⁻¹ by
      ext
      simp ]
  apply Filter.Tendsto.inv_tendsto_zero
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (Summable.tendsto_at_top_zero hf)
  rw [eventually_iff_exists_mem]
  refine' ⟨Set.Ioi 0, Ioi_mem_at_top _, fun _ _ => _⟩
  rw [Set.mem_Ioi, inv_eq_one_div, one_div, Pi.inv_apply, _root_.inv_pos]
  exact hf' _

end TopologicalGroup

section LinearOrderₓ

/-! For infinite sums taking values in a linearly ordered monoid, the existence of a least upper
bound for the finite sums is a criterion for summability.

This criterion is useful when applied in a linearly ordered monoid which is also a complete or
conditionally complete linear order, such as `ℝ`, `ℝ≥0`, `ℝ≥0∞`, because it is then easy to check
the existence of a least upper bound.
-/


theorem has_sum_of_is_lub_of_nonneg [LinearOrderedAddCommMonoid β] [TopologicalSpace β] [OrderTopology β] {f : α → β}
    (b : β) (h : ∀ b, 0 ≤ f b) (hf : IsLub (Set.Range fun s => ∑ a in s, f a) b) : HasSum f b :=
  tendsto_at_top_is_lub (Finset.sum_mono_set_of_nonneg h) hf

theorem has_sum_of_is_lub [CanonicallyLinearOrderedAddMonoid β] [TopologicalSpace β] [OrderTopology β] {f : α → β}
    (b : β) (hf : IsLub (Set.Range fun s => ∑ a in s, f a) b) : HasSum f b :=
  tendsto_at_top_is_lub (Finset.sum_mono_set f) hf

theorem summable_abs_iff [LinearOrderedAddCommGroup β] [UniformSpace β] [UniformAddGroup β] [CompleteSpace β]
    {f : α → β} : (Summable fun x => abs (f x)) ↔ Summable f :=
  have h1 : ∀ x : { x | 0 ≤ f x }, abs (f x) = f x := fun x => abs_of_nonneg x.2
  have h2 : ∀ x : { x | 0 ≤ f x }ᶜ, abs (f x) = -f x := fun x => abs_of_neg (not_leₓ.1 x.2)
  calc
    (Summable fun x => abs (f x)) ↔
        (Summable fun x : { x | 0 ≤ f x } => abs (f x)) ∧ Summable fun x : { x | 0 ≤ f x }ᶜ => abs (f x) :=
      summable_subtype_and_compl.symm
    _ ↔ (Summable fun x : { x | 0 ≤ f x } => f x) ∧ Summable fun x : { x | 0 ≤ f x }ᶜ => -f x := by
      simp only [← h1, ← h2]
    _ ↔ _ := by
      simp only [← summable_neg_iff, ← summable_subtype_and_compl]
    

alias summable_abs_iff ↔ Summable.of_abs Summable.abs

theorem finite_of_summable_const [LinearOrderedAddCommGroup β] [Archimedean β] [TopologicalSpace β]
    [OrderClosedTopology β] {b : β} (hb : 0 < b) (hf : Summable fun a : α => b) : Set.Finite (Set.Univ : Set α) := by
  have H : ∀ s : Finset α, s.card • b ≤ ∑' a : α, b := by
    intro s
    simpa using sum_le_has_sum s (fun a ha => hb.le) hf.has_sum
  obtain ⟨n, hn⟩ := Archimedean.arch (∑' a : α, b) hb
  have : ∀ s : Finset α, s.card ≤ n := by
    intro s
    simpa [← nsmul_le_nsmul_iff hb] using (H s).trans hn
  have : Fintype α := fintypeOfFinsetCardLe n this
  exact Set.finite_univ

end LinearOrderₓ

section CauchySeq

open Filter

/-- If the extended distance between consecutive points of a sequence is estimated
by a summable series of `nnreal`s, then the original sequence is a Cauchy sequence. -/
theorem cauchy_seq_of_edist_le_of_summable [PseudoEmetricSpace α] {f : ℕ → α} (d : ℕ → ℝ≥0 )
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : Summable d) : CauchySeq f := by
  refine' Emetric.cauchy_seq_iff_nnreal.2 fun ε εpos => _
  -- Actually we need partial sums of `d` to be a Cauchy sequence
  replace hd : CauchySeq fun n : ℕ => ∑ x in range n, d x :=
    let ⟨_, H⟩ := hd
    H.tendsto_sum_nat.cauchy_seq
  -- Now we take the same `N` as in one of the definitions of a Cauchy sequence
  refine' (Metric.cauchy_seq_iff'.1 hd ε (Nnreal.coe_pos.2 εpos)).imp fun N hN n hn => _
  have hsum := hN n hn
  -- We simplify the known inequality
  rw [dist_nndist, Nnreal.nndist_eq, ← sum_range_add_sum_Ico _ hn, add_tsub_cancel_left] at hsum
  norm_cast  at hsum
  replace hsum := lt_of_le_of_ltₓ (le_max_leftₓ _ _) hsum
  rw [edist_comm]
  -- Then use `hf` to simplify the goal to the same form
  apply lt_of_le_of_ltₓ (edist_le_Ico_sum_of_edist_le hn fun k _ _ => hf k)
  assumption_mod_cast

/-- If the distance between consecutive points of a sequence is estimated by a summable series,
then the original sequence is a Cauchy sequence. -/
theorem cauchy_seq_of_dist_le_of_summable [PseudoMetricSpace α] {f : ℕ → α} (d : ℕ → ℝ)
    (hf : ∀ n, dist (f n) (f n.succ) ≤ d n) (hd : Summable d) : CauchySeq f := by
  refine' Metric.cauchy_seq_iff'.2 fun ε εpos => _
  replace hd : CauchySeq fun n : ℕ => ∑ x in range n, d x :=
    let ⟨_, H⟩ := hd
    H.tendsto_sum_nat.cauchy_seq
  refine' (Metric.cauchy_seq_iff'.1 hd ε εpos).imp fun N hN n hn => _
  have hsum := hN n hn
  rw [Real.dist_eq, ← sum_Ico_eq_sub _ hn] at hsum
  calc dist (f n) (f N) = dist (f N) (f n) := dist_comm _ _ _ ≤ ∑ x in Ico N n, d x :=
      dist_le_Ico_sum_of_dist_le hn fun k _ _ => hf k _ ≤ abs (∑ x in Ico N n, d x) := le_abs_self _ _ < ε := hsum

theorem cauchy_seq_of_summable_dist [PseudoMetricSpace α] {f : ℕ → α} (h : Summable fun n => dist (f n) (f n.succ)) :
    CauchySeq f :=
  cauchy_seq_of_dist_le_of_summable _ (fun _ => le_rfl) h

theorem dist_le_tsum_of_dist_le_of_tendsto [PseudoMetricSpace α] {f : ℕ → α} (d : ℕ → ℝ)
    (hf : ∀ n, dist (f n) (f n.succ) ≤ d n) (hd : Summable d) {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ ∑' m, d (n + m) := by
  refine' le_of_tendsto (tendsto_const_nhds.dist ha) (eventually_at_top.2 ⟨n, fun m hnm => _⟩)
  refine' le_transₓ (dist_le_Ico_sum_of_dist_le hnm fun k _ _ => hf k) _
  rw [sum_Ico_eq_sum_range]
  refine' sum_le_tsum (range _) (fun _ _ => le_transₓ dist_nonneg (hf _)) _
  exact hd.comp_injective (add_right_injective n)

theorem dist_le_tsum_of_dist_le_of_tendsto₀ [PseudoMetricSpace α] {f : ℕ → α} (d : ℕ → ℝ)
    (hf : ∀ n, dist (f n) (f n.succ) ≤ d n) (hd : Summable d) {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    dist (f 0) a ≤ tsum d := by
  simpa only [← zero_addₓ] using dist_le_tsum_of_dist_le_of_tendsto d hf hd ha 0

theorem dist_le_tsum_dist_of_tendsto [PseudoMetricSpace α] {f : ℕ → α} (h : Summable fun n => dist (f n) (f n.succ))
    {a : α} (ha : Tendsto f atTop (𝓝 a)) (n) : dist (f n) a ≤ ∑' m, dist (f (n + m)) (f (n + m).succ) :=
  show dist (f n) a ≤ ∑' m, (fun x => dist (f x) (f x.succ)) (n + m) from
    dist_le_tsum_of_dist_le_of_tendsto (fun n => dist (f n) (f n.succ)) (fun _ => le_rfl) h ha n

theorem dist_le_tsum_dist_of_tendsto₀ [PseudoMetricSpace α] {f : ℕ → α} (h : Summable fun n => dist (f n) (f n.succ))
    {a : α} (ha : Tendsto f atTop (𝓝 a)) : dist (f 0) a ≤ ∑' n, dist (f n) (f n.succ) := by
  simpa only [← zero_addₓ] using dist_le_tsum_dist_of_tendsto h ha 0

end CauchySeq

/-! ## Multipliying two infinite sums

In this section, we prove various results about `(∑' x : β, f x) * (∑' y : γ, g y)`. Note that we
always assume that the family `λ x : β × γ, f x.1 * g x.2` is summable, since there is no way to
deduce this from the summmabilities of `f` and `g` in general, but if you are working in a normed
space, you may want to use the analogous lemmas in `analysis/normed_space/basic`
(e.g `tsum_mul_tsum_of_summable_norm`).

We first establish results about arbitrary index types, `β` and `γ`, and then we specialize to
`β = γ = ℕ` to prove the Cauchy product formula (see `tsum_mul_tsum_eq_tsum_sum_antidiagonal`).

### Arbitrary index types
-/


section tsum_mul_tsum

variable [TopologicalSpace α] [T3Space α] [NonUnitalNonAssocSemiringₓ α] [TopologicalSemiring α] {f : β → α} {g : γ → α}
  {s t u : α}

theorem HasSum.mul_eq (hf : HasSum f s) (hg : HasSum g t) (hfg : HasSum (fun x : β × γ => f x.1 * g x.2) u) :
    s * t = u :=
  have key₁ : HasSum (fun b => f b * t) (s * t) := hf.mul_right t
  have this : ∀ b : β, HasSum (fun c : γ => f b * g c) (f b * t) := fun b => hg.mul_left (f b)
  have key₂ : HasSum (fun b => f b * t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂

theorem HasSum.mul (hf : HasSum f s) (hg : HasSum g t) (hfg : Summable fun x : β × γ => f x.1 * g x.2) :
    HasSum (fun x : β × γ => f x.1 * g x.2) (s * t) :=
  let ⟨u, hu⟩ := hfg
  (hf.mul_eq hg hu).symm ▸ hu

/-- Product of two infinites sums indexed by arbitrary types.
    See also `tsum_mul_tsum_of_summable_norm` if `f` and `g` are abolutely summable. -/
theorem tsum_mul_tsum (hf : Summable f) (hg : Summable g) (hfg : Summable fun x : β × γ => f x.1 * g x.2) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : β × γ, f z.1 * g z.2 :=
  hf.HasSum.mul_eq hg.HasSum hfg.HasSum

end tsum_mul_tsum

section CauchyProduct

/-! ### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range`, where the `n`-th term is a sum over `finset.range (n+1)`
involving `nat` substraction.
In order to avoid `nat` substraction, we also provide `tsum_mul_tsum_eq_tsum_sum_antidiagonal`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`finset` `finset.nat.antidiagonal n` -/


variable {f : ℕ → α} {g : ℕ → α}

open Finset

variable [TopologicalSpace α] [NonUnitalNonAssocSemiringₓ α]

/- The family `(k, l) : ℕ × ℕ ↦ f k * g l` is summable if and only if the family
`(n, k, l) : Σ (n : ℕ), nat.antidiagonal n ↦ f k * g l` is summable. -/
theorem summable_mul_prod_iff_summable_mul_sigma_antidiagonal {f g : ℕ → α} :
    (Summable fun x : ℕ × ℕ => f x.1 * g x.2) ↔
      Summable fun x : Σn : ℕ, Nat.antidiagonal n => f (x.2 : ℕ × ℕ).1 * g (x.2 : ℕ × ℕ).2 :=
  Nat.sigmaAntidiagonalEquivProd.summable_iff.symm

variable [T3Space α] [TopologicalSemiring α]

theorem summable_sum_mul_antidiagonal_of_summable_mul {f g : ℕ → α} (h : Summable fun x : ℕ × ℕ => f x.1 * g x.2) :
    Summable fun n => ∑ kl in Nat.antidiagonal n, f kl.1 * g kl.2 := by
  rw [summable_mul_prod_iff_summable_mul_sigma_antidiagonal] at h
  conv => congr ext rw [← Finset.sum_finset_coe, ← tsum_fintype]
  exact h.sigma' fun n => (has_sum_fintype _).Summable

/-- The Cauchy product formula for the product of two infinites sums indexed by `ℕ`,
    expressed by summing on `finset.nat.antidiagonal`.
    See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`
    if `f` and `g` are absolutely summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ℕ × ℕ => f x.1 * g x.2) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl in Nat.antidiagonal n, f kl.1 * g kl.2 := by
  conv_rhs => congr ext rw [← Finset.sum_finset_coe, ← tsum_fintype]
  rw [tsum_mul_tsum hf hg hfg, ← nat.sigma_antidiagonal_equiv_prod.tsum_eq (_ : ℕ × ℕ → α)]
  exact
    tsum_sigma' (fun n => (has_sum_fintype _).Summable) (summable_mul_prod_iff_summable_mul_sigma_antidiagonal.mp hfg)

theorem summable_sum_mul_range_of_summable_mul {f g : ℕ → α} (h : Summable fun x : ℕ × ℕ => f x.1 * g x.2) :
    Summable fun n => ∑ k in range (n + 1), f k * g (n - k) := by
  simp_rw [← nat.sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_sum_mul_antidiagonal_of_summable_mul h

/-- The Cauchy product formula for the product of two infinites sums indexed by `ℕ`,
    expressed by summing on `finset.range`.
    See also `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`
    if `f` and `g` are absolutely summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_range (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ℕ × ℕ => f x.1 * g x.2) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k in range (n + 1), f k * g (n - k) := by
  simp_rw [← nat.sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal hf hg hfg

end CauchyProduct


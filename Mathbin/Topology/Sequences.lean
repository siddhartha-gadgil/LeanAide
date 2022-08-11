/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot
-/
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.MetricSpace.Basic

/-!
# Sequences in topological spaces

In this file we define sequences in topological spaces and show how they are related to
filters and the topology. In particular, we
* define the sequential closure of a set and prove that it's contained in the closure,
* define a type class "sequential_space" in which closure and sequential closure agree,
* define sequential continuity and show that it coincides with continuity in sequential spaces,
* provide an instance that shows that every first-countable (and in particular metric) space is
  a sequential space.
* define sequential compactness, prove that compactness implies sequential compactness in first
  countable spaces, and prove they are equivalent for uniform spaces having a countable uniformity
  basis (in particular metric spaces).
-/


open Set Function Filter

open TopologicalSpace

variable {X Y : Type _}

-- mathport name: «expr ⟶ »
local notation x " ⟶ " a => Tendsto x atTop (𝓝 a)

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/


section TopologicalSpace

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- The sequential closure of a set `s : set X` in a topological space `X` is
the set of all `a : X` which arise as limit of sequences in `s`. -/
def SeqClosure (s : Set X) : Set X :=
  { a | ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ x ⟶ a }

theorem subset_seq_closure (s : Set X) : s ⊆ SeqClosure s := fun a ha => ⟨const ℕ a, fun n => ha, tendsto_const_nhds⟩

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`,
the limit belongs to `s` as well. -/
def IsSeqClosed (s : Set X) : Prop :=
  s = SeqClosure s

/-- A convenience lemma for showing that a set is sequentially closed. -/
theorem is_seq_closed_of_def {s : Set X} (h : ∀ (x : ℕ → X) (a : X), (∀ n : ℕ, x n ∈ s) → (x ⟶ a) → a ∈ s) :
    IsSeqClosed s :=
  show s = SeqClosure s from
    Subset.antisymm (subset_seq_closure s)
      (show ∀ a, a ∈ SeqClosure s → a ∈ s from fun a ⟨x, _, _⟩ => show a ∈ s from h x a ‹∀ n : ℕ, x n ∈ s› ‹x ⟶ a›)

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
theorem seq_closure_subset_closure (s : Set X) : SeqClosure s ⊆ Closure s := fun a ⟨x, xM, xa⟩ =>
  mem_closure_of_tendsto xa (eventually_of_forall xM)

/-- A set is sequentially closed if it is closed. -/
theorem IsClosed.is_seq_closed {s : Set X} (hs : IsClosed s) : IsSeqClosed s :=
  suffices SeqClosure s ⊆ s from (subset_seq_closure s).antisymm this
  calc
    SeqClosure s ⊆ Closure s := seq_closure_subset_closure s
    _ = s := hs.closure_eq
    

/-- The limit of a convergent sequence in a sequentially closed set is in that set.-/
theorem IsSeqClosed.mem_of_tendsto {s : Set X} (hs : IsSeqClosed s) {x : ℕ → X} (hmem : ∀ n, x n ∈ s) {a : X}
    (ha : x ⟶ a) : a ∈ s :=
  have : a ∈ SeqClosure s := show ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ x ⟶ a from ⟨x, ‹∀ n, x n ∈ s›, ‹x ⟶ a›⟩
  Eq.subst (Eq.symm ‹IsSeqClosed s›) ‹a ∈ SeqClosure s›

/-- A sequential space is a space in which 'sequences are enough to probe the topology'. This can be
 formalised by demanding that the sequential closure and the closure coincide. The following
 statements show that other topological properties can be deduced from sequences in sequential
 spaces. -/
class SequentialSpace (X : Type _) [TopologicalSpace X] : Prop where
  seq_closure_eq_closure : ∀ s : Set X, SeqClosure s = Closure s

/-- In a sequential space, a set is closed iff it's sequentially closed. -/
theorem is_seq_closed_iff_is_closed [SequentialSpace X] {s : Set X} : IsSeqClosed s ↔ IsClosed s :=
  Iff.intro
    (fun _ =>
      closure_eq_iff_is_closed.mp
        (Eq.symm
          (calc
            s = SeqClosure s := by
              assumption
            _ = Closure s := SequentialSpace.seq_closure_eq_closure s
            )))
    IsClosed.is_seq_closed

alias is_seq_closed_iff_is_closed ↔ IsSeqClosed.is_closed _

/-- In a sequential space, a point belongs to the closure of a set iff it is a limit of a sequence
taking values in this set. -/
theorem mem_closure_iff_seq_limit [SequentialSpace X] {s : Set X} {a : X} :
    a ∈ Closure s ↔ ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ x ⟶ a := by
  rw [← SequentialSpace.seq_closure_eq_closure]
  exact Iff.rfl

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def SeqContinuous (f : X → Y) : Prop :=
  ∀ x : ℕ → X, ∀ {a : X}, (x ⟶ a) → (f ∘ x) ⟶ f a

-- A continuous function is sequentially continuous.
protected theorem Continuous.seq_continuous {f : X → Y} (hf : Continuous f) : SeqContinuous f := fun x a (_ : x ⟶ a) =>
  have : Tendsto f (𝓝 a) (𝓝 (f a)) := Continuous.tendsto ‹Continuous f› a
  show (f ∘ x) ⟶ f a from Tendsto.comp this ‹x ⟶ a›

/-- In a sequential space, continuity and sequential continuity coincide. -/
theorem continuous_iff_seq_continuous {f : X → Y} [SequentialSpace X] : Continuous f ↔ SeqContinuous f :=
  Iff.intro Continuous.seq_continuous fun this : SeqContinuous f =>
    show Continuous f from
      suffices h : ∀ {s : Set Y}, IsClosed s → IsSeqClosed (f ⁻¹' s) from
        continuous_iff_is_closed.mpr fun s _ => is_seq_closed_iff_is_closed.mp <| h ‹IsClosed s›
      fun s (_ : IsClosed s) =>
      is_seq_closed_of_def fun (x : ℕ → X) a (_ : ∀ n, f (x n) ∈ s) (_ : x ⟶ a) =>
        have : (f ∘ x) ⟶ f a := ‹SeqContinuous f› x ‹x ⟶ a›
        show f a ∈ s from ‹IsClosed s›.IsSeqClosed.mem_of_tendsto ‹∀ n, f (x n) ∈ s› ‹(f ∘ x) ⟶ f a›

alias continuous_iff_seq_continuous ↔ _ SeqContinuous.continuous

end TopologicalSpace

namespace TopologicalSpace

namespace FirstCountableTopology

variable [TopologicalSpace X] [FirstCountableTopology X]

/-- Every first-countable space is sequential. -/
-- see Note [lower instance priority]
instance (priority := 100) : SequentialSpace X :=
  ⟨show ∀ s, SeqClosure s = Closure s from fun s =>
      suffices Closure s ⊆ SeqClosure s from Set.Subset.antisymm (seq_closure_subset_closure s) this
      -- For every a ∈ closure s, we need to construct a sequence `x` in `s` that converges to `a`:
    fun (a : X) (ha : a ∈ Closure s) =>
      -- Since we are in a first-countable space, the neighborhood filter around `a` has a decreasing
    -- basis `U` indexed by `ℕ`.
    by
      let ⟨U, hU⟩ := (𝓝 a).exists_antitone_basis
      -- Since `p ∈ closure M`, there is an element in each `M ∩ U i`
      have ha : ∀ i : ℕ, ∃ y : X, y ∈ s ∧ y ∈ U i := by
        simpa using (mem_closure_iff_nhds_basis hU.1).mp ha
      -- The axiom of (countable) choice builds our sequence from the later fact
      choose u hu using ha
      rw [forall_and_distrib] at hu
      -- It clearly takes values in `M`
      use u, hu.1
      -- and converges to `p` because the basis is decreasing.
      apply hU.tendsto hu.2⟩

end FirstCountableTopology

end TopologicalSpace

section SeqCompact

open TopologicalSpace TopologicalSpace.FirstCountableTopology

variable [TopologicalSpace X]

/-- A set `s` is sequentially compact if every sequence taking values in `s` has a
converging subsequence. -/
def IsSeqCompact (s : Set X) :=
  ∀ ⦃x : ℕ → X⦄, (∀ n, x n ∈ s) → ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (x ∘ φ) ⟶ a

/-- A space `X` is sequentially compact if every sequence in `X` has a
converging subsequence. -/
class SeqCompactSpace (X : Type _) [TopologicalSpace X] : Prop where
  seq_compact_univ : IsSeqCompact (Univ : Set X)

theorem IsSeqCompact.subseq_of_frequently_in {s : Set X} (hs : IsSeqCompact s) {x : ℕ → X}
    (hx : ∃ᶠ n in at_top, x n ∈ s) : ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (x ∘ φ) ⟶ a :=
  let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_at_top hx
  let ⟨a, a_in, φ, hφ, h⟩ := hs huψ
  ⟨a, a_in, ψ ∘ φ, hψ.comp hφ, h⟩

theorem SeqCompactSpace.tendsto_subseq [SeqCompactSpace X] (x : ℕ → X) :
    ∃ (a : _)(φ : ℕ → ℕ), StrictMono φ ∧ (x ∘ φ) ⟶ a :=
  let ⟨a, _, φ, mono, h⟩ := SeqCompactSpace.seq_compact_univ fun n => mem_univ (x n)
  ⟨a, φ, mono, h⟩

section FirstCountableTopology

variable [FirstCountableTopology X]

open TopologicalSpace.FirstCountableTopology

theorem IsCompact.is_seq_compact {s : Set X} (hs : IsCompact s) : IsSeqCompact s := fun x x_in =>
  let ⟨a, a_in, ha⟩ := @hs (map x atTop) _ (le_principal_iff.mpr (univ_mem' x_in : _))
  ⟨a, a_in, tendsto_subseq ha⟩

theorem IsCompact.tendsto_subseq' {s : Set X} {x : ℕ → X} (hs : IsCompact s) (hx : ∃ᶠ n in at_top, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (x ∘ φ) ⟶ a :=
  hs.IsSeqCompact.subseq_of_frequently_in hx

theorem IsCompact.tendsto_subseq {s : Set X} {x : ℕ → X} (hs : IsCompact s) (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (x ∘ φ) ⟶ a :=
  hs.IsSeqCompact hx

-- see Note [lower instance priority]
instance (priority := 100) FirstCountableTopology.seq_compact_of_compact [CompactSpace X] : SeqCompactSpace X :=
  ⟨compact_univ.IsSeqCompact⟩

theorem CompactSpace.tendsto_subseq [CompactSpace X] (x : ℕ → X) : ∃ (a : _)(φ : ℕ → ℕ), StrictMono φ ∧ (x ∘ φ) ⟶ a :=
  SeqCompactSpace.tendsto_subseq x

end FirstCountableTopology

end SeqCompact

section UniformSpaceSeqCompact

open uniformity

open UniformSpace Prod

variable [UniformSpace X] {s : Set X}

theorem lebesgue_number_lemma_seq {ι : Type _} [IsCountablyGenerated (𝓤 X)] {c : ι → Set X} (hs : IsSeqCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ V ∈ 𝓤 X, SymmetricRel V ∧ ∀, ∀ x ∈ s, ∀, ∃ i, Ball x V ⊆ c i :=
  by
  classical
  obtain ⟨V, hV, Vsymm⟩ : ∃ V : ℕ → Set (X × X), (𝓤 X).HasAntitoneBasis V ∧ ∀ n, swap ⁻¹' V n = V n
  exact UniformSpace.has_seq_basis X
  suffices ∃ n, ∀, ∀ x ∈ s, ∀, ∃ i, ball x (V n) ⊆ c i by
    cases' this with n hn
    exact ⟨V n, hV.to_has_basis.mem_of_mem trivialₓ, Vsymm n, hn⟩
  by_contra H
  obtain ⟨x, x_in, hx⟩ : ∃ x : ℕ → X, (∀ n, x n ∈ s) ∧ ∀ n i, ¬ball (x n) (V n) ⊆ c i := by
    push_neg  at H
    choose x hx using H
    exact ⟨x, forall_and_distrib.mp hx⟩
  clear H
  obtain ⟨x₀, x₀_in, φ, φ_mono, hlim⟩ : ∃ x₀ ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (x ∘ φ) ⟶ x₀
  exact hs x_in
  clear hs
  obtain ⟨i₀, x₀_in⟩ : ∃ i₀, x₀ ∈ c i₀ := by
    rcases hc₂ x₀_in with ⟨_, ⟨i₀, rfl⟩, x₀_in_c⟩
    exact ⟨i₀, x₀_in_c⟩
  clear hc₂
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ball x₀ (V n₀) ⊆ c i₀ := by
    rcases(nhds_basis_uniformity hV.to_has_basis).mem_iff.mp (is_open_iff_mem_nhds.mp (hc₁ i₀) _ x₀_in) with ⟨n₀, _, h⟩
    use n₀
    rwa [← ball_eq_of_symmetry (Vsymm n₀)] at h
  clear hc₁
  obtain ⟨W, W_in, hWW⟩ : ∃ W ∈ 𝓤 X, W ○ W ⊆ V n₀
  exact comp_mem_uniformity_sets (hV.to_has_basis.mem_of_mem trivialₓ)
  obtain ⟨N, x_φ_N_in, hVNW⟩ : ∃ N, x (φ N) ∈ ball x₀ W ∧ V (φ N) ⊆ W := by
    obtain ⟨N₁, h₁⟩ : ∃ N₁, ∀, ∀ n ≥ N₁, ∀, x (φ n) ∈ ball x₀ W
    exact tendsto_at_top'.mp hlim _ (mem_nhds_left x₀ W_in)
    obtain ⟨N₂, h₂⟩ : ∃ N₂, V (φ N₂) ⊆ W := by
      rcases hV.to_has_basis.mem_iff.mp W_in with ⟨N, _, hN⟩
      use N
      exact subset.trans (hV.antitone <| φ_mono.id_le _) hN
    have : φ N₂ ≤ φ (max N₁ N₂) := φ_mono.le_iff_le.mpr (le_max_rightₓ _ _)
    exact ⟨max N₁ N₂, h₁ _ (le_max_leftₓ _ _), trans (hV.antitone this) h₂⟩
  suffices : ball (x (φ N)) (V (φ N)) ⊆ c i₀
  exact hx (φ N) i₀ this
  calc ball (x <| φ N) (V <| φ N) ⊆ ball (x <| φ N) W := preimage_mono hVNW _ ⊆ ball x₀ (V n₀) :=
      ball_subset_of_comp_subset x_φ_N_in hWW _ ⊆ c i₀ := hn₀

theorem IsSeqCompact.totally_bounded (h : IsSeqCompact s) : TotallyBounded s := by
  classical
  apply totally_bounded_of_forall_symm
  unfold IsSeqCompact  at h
  contrapose! h
  rcases h with ⟨V, V_in, V_symm, h⟩
  simp_rw [not_subset] at h
  have : ∀ t : Set X, t.Finite → ∃ a, a ∈ s ∧ a ∉ ⋃ y ∈ t, ball y V := by
    intro t ht
    obtain ⟨a, a_in, H⟩ : ∃ a ∈ s, ∀, ∀ x ∈ t, ∀, (x, a) ∉ V := by
      simpa [← ht] using h t
    use a, a_in
    intro H'
    obtain ⟨x, x_in, hx⟩ := mem_Union₂.mp H'
    exact H x x_in hx
  cases' seq_of_forall_finite_exists this with u hu
  clear h this
  simp [← forall_and_distrib] at hu
  cases' hu with u_in hu
  use u, u_in
  clear u_in
  intro x x_in φ
  intro hφ huφ
  obtain ⟨N, hN⟩ : ∃ N, ∀ p q, p ≥ N → q ≥ N → (u (φ p), u (φ q)) ∈ V
  exact huφ.cauchy_seq.mem_entourage V_in
  specialize hN N (N + 1) (le_reflₓ N) (Nat.le_succₓ N)
  specialize hu (φ <| N + 1) (φ N) (hφ <| lt_add_one N)
  exact hu hN

protected theorem IsSeqCompact.is_compact [is_countably_generated <| 𝓤 X] (hs : IsSeqCompact s) : IsCompact s := by
  classical
  rw [is_compact_iff_finite_subcover]
  intro ι U Uop s_sub
  rcases lebesgue_number_lemma_seq hs Uop s_sub with ⟨V, V_in, Vsymm, H⟩
  rcases totally_bounded_iff_subset.mp hs.totally_bounded V V_in with ⟨t, t_sub, tfin, ht⟩
  have : ∀ x : t, ∃ i : ι, ball x.val V ⊆ U i := by
    rintro ⟨x, x_in⟩
    exact H x (t_sub x_in)
  choose i hi using this
  have : Fintype t := tfin.fintype
  use Finset.image i Finset.univ
  trans ⋃ y ∈ t, ball y V
  · intro x x_in
    specialize ht x_in
    rw [mem_Union₂] at *
    simp_rw [ball_eq_of_symmetry Vsymm]
    exact ht
    
  · refine' Union₂_mono' fun x x_in => _
    exact ⟨i ⟨x, x_in⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), hi ⟨x, x_in⟩⟩
    

/-- A version of Bolzano-Weistrass: in a uniform space with countably generated uniformity filter
(e.g., in a metric space), a set is compact if and only if it is sequentially compact. -/
protected theorem UniformSpace.compact_iff_seq_compact [is_countably_generated <| 𝓤 X] : IsCompact s ↔ IsSeqCompact s :=
  ⟨fun H => H.IsSeqCompact, fun H => H.IsCompact⟩

theorem UniformSpace.compact_space_iff_seq_compact_space [is_countably_generated <| 𝓤 X] :
    CompactSpace X ↔ SeqCompactSpace X :=
  have key : IsCompact (Univ : Set X) ↔ IsSeqCompact Univ := UniformSpace.compact_iff_seq_compact
  ⟨fun ⟨h⟩ => ⟨key.mp h⟩, fun ⟨h⟩ => ⟨key.mpr h⟩⟩

end UniformSpaceSeqCompact

section MetricSeqCompact

variable [PseudoMetricSpace X]

open Metric

theorem SeqCompact.lebesgue_number_lemma_of_metric {ι : Sort _} {c : ι → Set X} {s : Set X} (hs : IsSeqCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ δ > 0, ∀, ∀ a ∈ s, ∀, ∃ i, Ball a δ ⊆ c i :=
  lebesgue_number_lemma_of_metric hs.IsCompact hc₁ hc₂

variable [ProperSpace X] {s : Set X}

/-- A version of **Bolzano-Weistrass**: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. This version assumes only
that the sequence is frequently in some bounded set. -/
theorem tendsto_subseq_of_frequently_bounded (hs : Bounded s) {x : ℕ → X} (hx : ∃ᶠ n in at_top, x n ∈ s) :
    ∃ a ∈ Closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (x ∘ φ) ⟶ a :=
  have hcs : IsSeqCompact (Closure s) := hs.is_compact_closure.IsSeqCompact
  have hu' : ∃ᶠ n in at_top, x n ∈ Closure s := hx.mono fun n hn => subset_closure hn
  hcs.subseq_of_frequently_in hu'

/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. -/
theorem tendsto_subseq_of_bounded (hs : Bounded s) {x : ℕ → X} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ Closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (x ∘ φ) ⟶ a :=
  tendsto_subseq_of_frequently_bounded hs <| frequently_of_forall hx

end MetricSeqCompact


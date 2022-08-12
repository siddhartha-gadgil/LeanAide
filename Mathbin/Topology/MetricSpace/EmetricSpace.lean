/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathbin.Data.Nat.Interval
import Mathbin.Data.Real.Ennreal
import Mathbin.Topology.UniformSpace.Pi
import Mathbin.Topology.UniformSpace.UniformConvergence
import Mathbin.Topology.UniformSpace.UniformEmbedding

/-!
# Extended metric spaces

This file is devoted to the definition and study of `emetric_spaces`, i.e., metric
spaces in which the distance is allowed to take the value ∞. This extended distance is
called `edist`, and takes values in `ℝ≥0∞`.

Many definitions and theorems expected on emetric spaces are already introduced on uniform spaces
and topological spaces. For example: open and closed sets, compactness, completeness, continuity and
uniform continuity.

The class `emetric_space` therefore extends `uniform_space` (and `topological_space`).

Since a lot of elementary properties don't require `eq_of_edist_eq_zero` we start setting up the
theory of `pseudo_emetric_space`, where we don't require `edist x y = 0 → x = y` and we specialize
to `emetric_space` at the end.
-/


open Set Filter Classical

noncomputable section

open uniformity TopologicalSpace BigOperators Filter Nnreal Ennreal

universe u v w

variable {α : Type u} {β : Type v}

/-- Characterizing uniformities associated to a (generalized) distance function `D`
in terms of the elements of the uniformity. -/
theorem uniformity_dist_of_mem_uniformity [LinearOrderₓ β] {U : Filter (α × α)} (z : β) (D : α → α → β)
    (H : ∀ s, s ∈ U ↔ ∃ ε > z, ∀ {a b : α}, D a b < ε → (a, b) ∈ s) : U = ⨅ ε > z, 𝓟 { p : α × α | D p.1 p.2 < ε } :=
  le_antisymmₓ (le_infi fun ε => le_infi fun ε0 => le_principal_iff.2 <| (H _).2 ⟨ε, ε0, fun a b => id⟩) fun r ur =>
    let ⟨ε, ε0, h⟩ := (H _).1 ur
    mem_infi_of_mem ε <| mem_infi_of_mem ε0 <| mem_principal.2 fun ⟨a, b⟩ => h

/-- `has_edist α` means that `α` is equipped with an extended distance. -/
class HasEdist (α : Type _) where
  edist : α → α → ℝ≥0∞

export HasEdist (edist)

/-- Creating a uniform space from an extended distance. -/
def uniformSpaceOfEdist (edist : α → α → ℝ≥0∞) (edist_self : ∀ x : α, edist x x = 0)
    (edist_comm : ∀ x y : α, edist x y = edist y x) (edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z) :
    UniformSpace α :=
  UniformSpace.ofCore
    { uniformity := ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε },
      refl :=
        le_infi fun ε =>
          le_infi <| by
            simp (config := { contextual := true })[← Set.subset_def, ← IdRel, ← edist_self, ← (· > ·)],
      comp :=
        le_infi fun ε =>
          le_infi fun h =>
            have : (2 : ℝ≥0∞) = (2 : ℕ) := by
              simp
            have A : 0 < ε / 2 :=
              Ennreal.div_pos_iff.2
                ⟨ne_of_gtₓ h, by
                  convert Ennreal.nat_ne_top 2⟩
            lift'_le (mem_infi_of_mem (ε / 2) <| mem_infi_of_mem A (Subset.refl _)) <| by
              have : ∀ a b c : α, edist a c < ε / 2 → edist c b < ε / 2 → edist a b < ε := fun a b c hac hcb =>
                calc
                  edist a b ≤ edist a c + edist c b := edist_triangle _ _ _
                  _ < ε / 2 + ε / 2 := Ennreal.add_lt_add hac hcb
                  _ = ε := by
                    rw [Ennreal.add_halves]
                  
              simpa [← CompRel] ,
      symm :=
        tendsto_infi.2 fun ε =>
          tendsto_infi.2 fun h =>
            tendsto_infi' ε <|
              tendsto_infi' h <|
                tendsto_principal_principal.2 <| by
                  simp [← edist_comm] }

/-- Extended (pseudo) metric spaces, with an extended distance `edist` possibly taking the
value ∞

Each pseudo_emetric space induces a canonical `uniform_space` and hence a canonical
`topological_space`.
This is enforced in the type class definition, by extending the `uniform_space` structure. When
instantiating a `pseudo_emetric_space` structure, the uniformity fields are not necessary, they
will be filled in by default. There is a default value for the uniformity, that can be substituted
in cases of interest, for instance when instantiating a `pseudo_emetric_space` structure
on a product.

Continuity of `edist` is proved in `topology.instances.ennreal`
-/
-- the uniform structure is embedded in the emetric space structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
class PseudoEmetricSpace (α : Type u) extends HasEdist α : Type u where
  edist_self : ∀ x : α, edist x x = 0
  edist_comm : ∀ x y : α, edist x y = edist y x
  edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z
  toUniformSpace : UniformSpace α := uniformSpaceOfEdist edist edist_self edist_comm edist_triangle
  uniformity_edist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } := by
    run_tac
      control_laws_tac

attribute [instance] PseudoEmetricSpace.toUniformSpace

/- Pseudoemetric spaces are less common than metric spaces. Therefore, we work in a dedicated
namespace, while notions associated to metric spaces are mostly in the root namespace. -/
variable [PseudoEmetricSpace α]

export PseudoEmetricSpace (edist_self edist_comm edist_triangle)

attribute [simp] edist_self

/-- Triangle inequality for the extended distance -/
theorem edist_triangle_left (x y z : α) : edist x y ≤ edist z x + edist z y := by
  rw [edist_comm z] <;> apply edist_triangle

theorem edist_triangle_right (x y z : α) : edist x y ≤ edist x z + edist y z := by
  rw [edist_comm y] <;> apply edist_triangle

theorem edist_triangle4 (x y z t : α) : edist x t ≤ edist x y + edist y z + edist z t :=
  calc
    edist x t ≤ edist x z + edist z t := edist_triangle x z t
    _ ≤ edist x y + edist y z + edist z t := add_le_add_right (edist_triangle x y z) _
    

/-- The triangle (polygon) inequality for sequences of points; `finset.Ico` version. -/
theorem edist_le_Ico_sum_edist (f : ℕ → α) {m n} (h : m ≤ n) :
    edist (f m) (f n) ≤ ∑ i in Finset.ico m n, edist (f i) (f (i + 1)) := by
  revert n
  refine' Nat.le_induction _ _
  · simp only [← Finset.sum_empty, ← Finset.Ico_self, ← edist_self]
    -- TODO: Why doesn't Lean close this goal automatically? `exact le_rfl` fails too.
    exact le_reflₓ (0 : ℝ≥0∞)
    
  · intro n hn hrec
    calc edist (f m) (f (n + 1)) ≤ edist (f m) (f n) + edist (f n) (f (n + 1)) :=
        edist_triangle _ _ _ _ ≤ (∑ i in Finset.ico m n, _) + _ :=
        add_le_add hrec le_rfl _ = ∑ i in Finset.ico m (n + 1), _ := by
        rw [Nat.Ico_succ_right_eq_insert_Ico hn, Finset.sum_insert, add_commₓ] <;> simp
    

/-- The triangle (polygon) inequality for sequences of points; `finset.range` version. -/
theorem edist_le_range_sum_edist (f : ℕ → α) (n : ℕ) :
    edist (f 0) (f n) ≤ ∑ i in Finset.range n, edist (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range ▸ edist_le_Ico_sum_edist f (Nat.zero_leₓ n)

/-- A version of `edist_le_Ico_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
theorem edist_le_Ico_sum_of_edist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ≥0∞}
    (hd : ∀ {k}, m ≤ k → k < n → edist (f k) (f (k + 1)) ≤ d k) : edist (f m) (f n) ≤ ∑ i in Finset.ico m n, d i :=
  le_transₓ (edist_le_Ico_sum_edist f hmn) <|
    Finset.sum_le_sum fun k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

/-- A version of `edist_le_range_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
theorem edist_le_range_sum_of_edist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ≥0∞}
    (hd : ∀ {k}, k < n → edist (f k) (f (k + 1)) ≤ d k) : edist (f 0) (f n) ≤ ∑ i in Finset.range n, d i :=
  Nat.Ico_zero_eq_range ▸ edist_le_Ico_sum_of_edist_le (zero_le n) fun _ _ => hd

/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_pseudoedist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } :=
  PseudoEmetricSpace.uniformity_edist

theorem uniformity_basis_edist : (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  (@uniformity_pseudoedist α _).symm ▸
    has_basis_binfi_principal
      (fun r hr p hp =>
        ⟨min r p, lt_minₓ hr hp, fun x hx => lt_of_lt_of_leₓ hx (min_le_leftₓ _ _), fun x hx =>
          lt_of_lt_of_leₓ hx (min_le_rightₓ _ _)⟩)
      ⟨1, Ennreal.zero_lt_one⟩

/-- Characterization of the elements of the uniformity in terms of the extended distance -/
theorem mem_uniformity_edist {s : Set (α × α)} : s ∈ 𝓤 α ↔ ∃ ε > 0, ∀ {a b : α}, edist a b < ε → (a, b) ∈ s :=
  uniformity_basis_edist.mem_uniformity_iff

/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist`, `uniformity_basis_edist'`,
`uniformity_basis_edist_nnreal`, and `uniformity_basis_edist_inv_nat`. -/
protected theorem Emetric.mk_uniformity_basis {β : Type _} {p : β → Prop} {f : β → ℝ≥0∞} (hf₀ : ∀ x, p x → 0 < f x)
    (hf : ∀ ε, 0 < ε → ∃ (x : _)(hx : p x), f x ≤ ε) : (𝓤 α).HasBasis p fun x => { p : α × α | edist p.1 p.2 < f x } :=
  by
  refine' ⟨fun s => uniformity_basis_edist.mem_iff.trans _⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases hf ε ε₀ with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x hx => hε <| lt_of_lt_of_leₓ hx H⟩
    
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩
    

/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist_le` and `uniformity_basis_edist_le'`. -/
protected theorem Emetric.mk_uniformity_basis_le {β : Type _} {p : β → Prop} {f : β → ℝ≥0∞} (hf₀ : ∀ x, p x → 0 < f x)
    (hf : ∀ ε, 0 < ε → ∃ (x : _)(hx : p x), f x ≤ ε) : (𝓤 α).HasBasis p fun x => { p : α × α | edist p.1 p.2 ≤ f x } :=
  by
  refine' ⟨fun s => uniformity_basis_edist.mem_iff.trans _⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x hx => hε <| lt_of_le_of_ltₓ (le_transₓ hx H) hε'.2⟩
    
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fun x hx => H (le_of_ltₓ hx)⟩
    

theorem uniformity_basis_edist_le : (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 ≤ ε } :=
  Emetric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_reflₓ ε⟩

theorem uniformity_basis_edist' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => ε ∈ Ioo 0 ε') fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  Emetric.mk_uniformity_basis (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_minₓ ε₀ hδ.1, lt_of_le_of_ltₓ (min_le_rightₓ _ _) hδ.2⟩, min_le_leftₓ _ _⟩

theorem uniformity_basis_edist_le' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => ε ∈ Ioo 0 ε') fun ε => { p : α × α | edist p.1 p.2 ≤ ε } :=
  Emetric.mk_uniformity_basis_le (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_minₓ ε₀ hδ.1, lt_of_le_of_ltₓ (min_le_rightₓ _ _) hδ.2⟩, min_le_leftₓ _ _⟩

theorem uniformity_basis_edist_nnreal :
    (𝓤 α).HasBasis (fun ε : ℝ≥0 => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  Emetric.mk_uniformity_basis (fun _ => Ennreal.coe_pos.2) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := Ennreal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, Ennreal.coe_pos.1 hδ.1, le_of_ltₓ hδ.2⟩

theorem uniformity_basis_edist_inv_nat :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | edist p.1 p.2 < (↑n)⁻¹ } :=
  Emetric.mk_uniformity_basis (fun n _ => Ennreal.inv_pos.2 <| Ennreal.nat_ne_top n) fun ε ε₀ =>
    let ⟨n, hn⟩ := Ennreal.exists_inv_nat_lt (ne_of_gtₓ ε₀)
    ⟨n, trivialₓ, le_of_ltₓ hn⟩

theorem uniformity_basis_edist_inv_two_pow :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | edist p.1 p.2 < 2⁻¹ ^ n } :=
  Emetric.mk_uniformity_basis (fun n _ => Ennreal.pow_pos (Ennreal.inv_pos.2 Ennreal.two_ne_top) _) fun ε ε₀ =>
    let ⟨n, hn⟩ := Ennreal.exists_inv_two_pow_lt (ne_of_gtₓ ε₀)
    ⟨n, trivialₓ, le_of_ltₓ hn⟩

/-- Fixed size neighborhoods of the diagonal belong to the uniform structure -/
theorem edist_mem_uniformity {ε : ℝ≥0∞} (ε0 : 0 < ε) : { p : α × α | edist p.1 p.2 < ε } ∈ 𝓤 α :=
  mem_uniformity_edist.2 ⟨ε, ε0, fun a b => id⟩

namespace Emetric

instance (priority := 900) : IsCountablyGenerated (𝓤 α) :=
  is_countably_generated_of_seq ⟨_, uniformity_basis_edist_inv_nat.eq_infi⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection {a b «expr ∈ » s}
/-- ε-δ characterization of uniform continuity on a set for pseudoemetric spaces -/
theorem uniform_continuous_on_iff [PseudoEmetricSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔
      ∀, ∀ ε > 0, ∀, ∃ δ > 0, ∀ {a b} {_ : a ∈ s} {_ : b ∈ s}, edist a b < δ → edist (f a) (f b) < ε :=
  uniformity_basis_edist.uniform_continuous_on_iff uniformity_basis_edist

/-- ε-δ characterization of uniform continuity on pseudoemetric spaces -/
theorem uniform_continuous_iff [PseudoEmetricSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀, ∀ ε > 0, ∀, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε :=
  uniformity_basis_edist.uniform_continuous_iff uniformity_basis_edist

/-- ε-δ characterization of uniform embeddings on pseudoemetric spaces -/
theorem uniform_embedding_iff [PseudoEmetricSpace β] {f : α → β} :
    UniformEmbedding f ↔
      Function.Injective f ∧
        UniformContinuous f ∧ ∀, ∀ δ > 0, ∀, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  uniform_embedding_def'.trans <|
    and_congr Iff.rfl <|
      and_congr Iff.rfl
        ⟨fun H δ δ0 =>
          let ⟨t, tu, ht⟩ := H _ (edist_mem_uniformity δ0)
          let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 tu
          ⟨ε, ε0, fun a b h => ht _ _ (hε h)⟩,
          fun H s su =>
          let ⟨δ, δ0, hδ⟩ := mem_uniformity_edist.1 su
          let ⟨ε, ε0, hε⟩ := H _ δ0
          ⟨_, edist_mem_uniformity ε0, fun a b h => hδ (hε h)⟩⟩

/-- If a map between pseudoemetric spaces is a uniform embedding then the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`. -/
theorem controlled_of_uniform_embedding [PseudoEmetricSpace β] {f : α → β} :
    UniformEmbedding f →
      (∀, ∀ ε > 0, ∀, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε) ∧
        ∀, ∀ δ > 0, ∀, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  by
  intro h
  exact ⟨uniform_continuous_iff.1 (uniform_embedding_iff.1 h).2.1, (uniform_embedding_iff.1 h).2.2⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » t)
/-- ε-δ characterization of Cauchy sequences on pseudoemetric spaces -/
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ f ≠ ⊥ ∧ ∀, ∀ ε > 0, ∀, ∃ t ∈ f, ∀ (x y) (_ : x ∈ t) (_ : y ∈ t), edist x y < ε := by
  rw [← ne_bot_iff] <;> exact uniformity_basis_edist.cauchy_iff

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `edist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem complete_of_convergent_controlled_sequences (B : ℕ → ℝ≥0∞) (hB : ∀ n, 0 < B n)
    (H : ∀ u : ℕ → α, (∀ N n m : ℕ, N ≤ n → N ≤ m → edist (u n) (u m) < B N) → ∃ x, Tendsto u atTop (𝓝 x)) :
    CompleteSpace α :=
  UniformSpace.complete_of_convergent_controlled_sequences (fun n => { p : α × α | edist p.1 p.2 < B n })
    (fun n => edist_mem_uniformity <| hB n) H

/-- A sequentially complete pseudoemetric space is complete. -/
theorem complete_of_cauchy_seq_tendsto : (∀ u : ℕ → α, CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) → CompleteSpace α :=
  UniformSpace.complete_of_cauchy_seq_tendsto

/-- Expressing locally uniform convergence on a set using `edist`. -/
theorem tendsto_locally_uniformly_on_iff {ι : Type _} [TopologicalSpace β] {F : ι → β → α} {f : β → α} {p : Filter ι}
    {s : Set β} :
    TendstoLocallyUniformlyOn F f p s ↔
      ∀, ∀ ε > 0, ∀, ∀, ∀ x ∈ s, ∀, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀, ∀ y ∈ t, ∀, edist (f y) (F n y) < ε :=
  by
  refine' ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu x hx => _⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩

/-- Expressing uniform convergence on a set using `edist`. -/
theorem tendsto_uniformly_on_iff {ι : Type _} {F : ι → β → α} {f : β → α} {p : Filter ι} {s : Set β} :
    TendstoUniformlyOn F f p s ↔ ∀, ∀ ε > 0, ∀, ∀ᶠ n in p, ∀, ∀ x ∈ s, ∀, edist (f x) (F n x) < ε := by
  refine' ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu => _⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)

/-- Expressing locally uniform convergence using `edist`. -/
theorem tendsto_locally_uniformly_iff {ι : Type _} [TopologicalSpace β] {F : ι → β → α} {f : β → α} {p : Filter ι} :
    TendstoLocallyUniformly F f p ↔
      ∀, ∀ ε > 0, ∀, ∀ x : β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀, ∀ y ∈ t, ∀, edist (f y) (F n y) < ε :=
  by
  simp only [tendsto_locally_uniformly_on_univ, ← tendsto_locally_uniformly_on_iff, ← mem_univ, ← forall_const, ←
    exists_prop, ← nhds_within_univ]

/-- Expressing uniform convergence using `edist`. -/
theorem tendsto_uniformly_iff {ι : Type _} {F : ι → β → α} {f : β → α} {p : Filter ι} :
    TendstoUniformly F f p ↔ ∀, ∀ ε > 0, ∀, ∀ᶠ n in p, ∀ x, edist (f x) (F n x) < ε := by
  simp only [tendsto_uniformly_on_univ, ← tendsto_uniformly_on_iff, ← mem_univ, ← forall_const]

end Emetric

open Emetric

/-- Auxiliary function to replace the uniformity on a pseudoemetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct a pseudoemetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
-/
def PseudoEmetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoEmetricSpace α)
    (H : @uniformity _ U = @uniformity _ PseudoEmetricSpace.toUniformSpace) : PseudoEmetricSpace α where
  edist := @edist _ m.toHasEdist
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEmetricSpace.uniformity_edist α _)

/-- The extended pseudometric induced by a function taking values in a pseudoemetric space. -/
def PseudoEmetricSpace.induced {α β} (f : α → β) (m : PseudoEmetricSpace β) : PseudoEmetricSpace α where
  edist := fun x y => edist (f x) (f y)
  edist_self := fun x => edist_self _
  edist_comm := fun x y => edist_comm _ _
  edist_triangle := fun x y z => edist_triangle _ _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_edist := by
    apply @uniformity_dist_of_mem_uniformity _ _ _ _ _ fun x y => edist (f x) (f y)
    refine' fun s => mem_comap.trans _
    constructor <;> intro H
    · rcases H with ⟨r, ru, rs⟩
      rcases mem_uniformity_edist.1 ru with ⟨ε, ε0, hε⟩
      refine' ⟨ε, ε0, fun a b h => rs (hε _)⟩
      exact h
      
    · rcases H with ⟨ε, ε0, hε⟩
      exact ⟨_, edist_mem_uniformity ε0, fun ⟨a, b⟩ => hε⟩
      

/-- Pseudoemetric space instance on subsets of pseudoemetric spaces -/
instance {α : Type _} {p : α → Prop} [PseudoEmetricSpace α] : PseudoEmetricSpace (Subtype p) :=
  PseudoEmetricSpace.induced coe ‹_›

/-- The extended psuedodistance on a subset of a pseudoemetric space is the restriction of
the original pseudodistance, by definition -/
theorem Subtype.edist_eq {p : α → Prop} (x y : Subtype p) : edist x y = edist (x : α) y :=
  rfl

namespace MulOpposite

/-- Pseudoemetric space instance on the multiplicative opposite of a pseudoemetric space. -/
@[to_additive "Pseudoemetric space instance on the additive opposite of a pseudoemetric space."]
instance {α : Type _} [PseudoEmetricSpace α] : PseudoEmetricSpace αᵐᵒᵖ :=
  PseudoEmetricSpace.induced unop ‹_›

@[to_additive]
theorem edist_unop (x y : αᵐᵒᵖ) : edist (unop x) (unop y) = edist x y :=
  rfl

@[to_additive]
theorem edist_op (x y : α) : edist (op x) (op y) = edist x y :=
  rfl

end MulOpposite

section ULift

instance : PseudoEmetricSpace (ULift α) :=
  PseudoEmetricSpace.induced ULift.down ‹_›

theorem ULift.edist_eq (x y : ULift α) : edist x y = edist x.down y.down :=
  rfl

@[simp]
theorem ULift.edist_up_up (x y : α) : edist (ULift.up x) (ULift.up y) = edist x y :=
  rfl

end ULift

/-- The product of two pseudoemetric spaces, with the max distance, is an extended
pseudometric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance Prod.pseudoEmetricSpaceMax [PseudoEmetricSpace β] : PseudoEmetricSpace (α × β) where
  edist := fun x y => max (edist x.1 y.1) (edist x.2 y.2)
  edist_self := fun x => by
    simp
  edist_comm := fun x y => by
    simp [← edist_comm]
  edist_triangle := fun x y z =>
    max_leₓ (le_transₓ (edist_triangle _ _ _) (add_le_add (le_max_leftₓ _ _) (le_max_leftₓ _ _)))
      (le_transₓ (edist_triangle _ _ _) (add_le_add (le_max_rightₓ _ _) (le_max_rightₓ _ _)))
  uniformity_edist := by
    refine' uniformity_prod.trans _
    simp only [← PseudoEmetricSpace.uniformity_edist, ← comap_infi]
    rw [← infi_inf_eq]
    congr
    funext
    rw [← infi_inf_eq]
    congr
    funext
    simp [← inf_principal, ← ext_iff, ← max_lt_iff]
  toUniformSpace := Prod.uniformSpace

theorem Prod.edist_eq [PseudoEmetricSpace β] (x y : α × β) : edist x y = max (edist x.1 y.1) (edist x.2 y.2) :=
  rfl

section Pi

open Finset

variable {π : β → Type _} [Fintype β]

/-- The product of a finite number of pseudoemetric spaces, with the max distance, is still
a pseudoemetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
instance pseudoEmetricSpacePi [∀ b, PseudoEmetricSpace (π b)] : PseudoEmetricSpace (∀ b, π b) where
  edist := fun f g => Finset.sup univ fun b => edist (f b) (g b)
  edist_self := fun f =>
    bot_unique <|
      Finset.sup_le <| by
        simp
  edist_comm := fun f g => by
    unfold edist <;> congr <;> funext a <;> exact edist_comm _ _
  edist_triangle := fun f g h => by
    simp only [← Finset.sup_le_iff]
    intro b hb
    exact le_transₓ (edist_triangle _ (g b) _) (add_le_add (le_sup hb) (le_sup hb))
  toUniformSpace := Pi.uniformSpace _
  uniformity_edist := by
    simp only [← Pi.uniformity, ← PseudoEmetricSpace.uniformity_edist, ← comap_infi, ← gt_iff_lt, ← preimage_set_of_eq,
      ← comap_principal]
    rw [infi_comm]
    congr
    funext ε
    rw [infi_comm]
    congr
    funext εpos
    change 0 < ε at εpos
    simp [← Set.ext_iff, ← εpos]

theorem edist_pi_def [∀ b, PseudoEmetricSpace (π b)] (f g : ∀ b, π b) :
    edist f g = Finset.sup univ fun b => edist (f b) (g b) :=
  rfl

@[simp]
theorem edist_pi_const [Nonempty β] (a b : α) : (edist (fun x : β => a) fun _ => b) = edist a b :=
  Finset.sup_const univ_nonempty (edist a b)

theorem edist_le_pi_edist [∀ b, PseudoEmetricSpace (π b)] (f g : ∀ b, π b) (b : β) : edist (f b) (g b) ≤ edist f g :=
  Finset.le_sup (Finset.mem_univ b)

theorem edist_pi_le_iff [∀ b, PseudoEmetricSpace (π b)] {f g : ∀ b, π b} {d : ℝ≥0∞} :
    edist f g ≤ d ↔ ∀ b, edist (f b) (g b) ≤ d :=
  Finset.sup_le_iff.trans <| by
    simp only [← Finset.mem_univ, ← forall_const]

end Pi

namespace Emetric

variable {x y z : α} {ε ε₁ ε₂ : ℝ≥0∞} {s : Set α}

/-- `emetric.ball x ε` is the set of all points `y` with `edist y x < ε` -/
def Ball (x : α) (ε : ℝ≥0∞) : Set α :=
  { y | edist y x < ε }

@[simp]
theorem mem_ball : y ∈ Ball x ε ↔ edist y x < ε :=
  Iff.rfl

theorem mem_ball' : y ∈ Ball x ε ↔ edist x y < ε := by
  rw [edist_comm, mem_ball]

/-- `emetric.closed_ball x ε` is the set of all points `y` with `edist y x ≤ ε` -/
def ClosedBall (x : α) (ε : ℝ≥0∞) :=
  { y | edist y x ≤ ε }

@[simp]
theorem mem_closed_ball : y ∈ ClosedBall x ε ↔ edist y x ≤ ε :=
  Iff.rfl

theorem mem_closed_ball' : y ∈ ClosedBall x ε ↔ edist x y ≤ ε := by
  rw [edist_comm, mem_closed_ball]

@[simp]
theorem closed_ball_top (x : α) : ClosedBall x ∞ = univ :=
  eq_univ_of_forall fun y => le_top

theorem ball_subset_closed_ball : Ball x ε ⊆ ClosedBall x ε := fun y hy => le_of_ltₓ hy

theorem pos_of_mem_ball (hy : y ∈ Ball x ε) : 0 < ε :=
  lt_of_le_of_ltₓ (zero_le _) hy

theorem mem_ball_self (h : 0 < ε) : x ∈ Ball x ε :=
  show edist x x < ε by
    rw [edist_self] <;> assumption

theorem mem_closed_ball_self : x ∈ ClosedBall x ε :=
  show edist x x ≤ ε by
    rw [edist_self] <;> exact bot_le

theorem mem_ball_comm : x ∈ Ball y ε ↔ y ∈ Ball x ε := by
  rw [mem_ball', mem_ball]

theorem mem_closed_ball_comm : x ∈ ClosedBall y ε ↔ y ∈ ClosedBall x ε := by
  rw [mem_closed_ball', mem_closed_ball]

theorem ball_subset_ball (h : ε₁ ≤ ε₂) : Ball x ε₁ ⊆ Ball x ε₂ := fun y (yx : _ < ε₁) => lt_of_lt_of_leₓ yx h

theorem closed_ball_subset_closed_ball (h : ε₁ ≤ ε₂) : ClosedBall x ε₁ ⊆ ClosedBall x ε₂ := fun y (yx : _ ≤ ε₁) =>
  le_transₓ yx h

theorem ball_disjoint (h : ε₁ + ε₂ ≤ edist x y) : Disjoint (Ball x ε₁) (Ball y ε₂) := fun z ⟨h₁, h₂⟩ =>
  (edist_triangle_left x y z).not_lt <| (Ennreal.add_lt_add h₁ h₂).trans_le h

theorem ball_subset (h : edist x y + ε₁ ≤ ε₂) (h' : edist x y ≠ ∞) : Ball x ε₁ ⊆ Ball y ε₂ := fun z zx =>
  calc
    edist z y ≤ edist z x + edist x y := edist_triangle _ _ _
    _ = edist x y + edist z x := add_commₓ _ _
    _ < edist x y + ε₁ := Ennreal.add_lt_add_left h' zx
    _ ≤ ε₂ := h
    

theorem exists_ball_subset_ball (h : y ∈ Ball x ε) : ∃ ε' > 0, Ball y ε' ⊆ Ball x ε := by
  have : 0 < ε - edist y x := by
    simpa using h
  refine' ⟨ε - edist y x, this, ball_subset _ (ne_top_of_lt h)⟩
  exact (add_tsub_cancel_of_le (mem_ball.mp h).le).le

theorem ball_eq_empty_iff : Ball x ε = ∅ ↔ ε = 0 :=
  eq_empty_iff_forall_not_mem.trans
    ⟨fun h => le_bot_iff.1 (le_of_not_gtₓ fun ε0 => h _ (mem_ball_self ε0)), fun ε0 y h =>
      not_lt_of_le (le_of_eqₓ ε0) (pos_of_mem_ball h)⟩

/-- Relation “two points are at a finite edistance” is an equivalence relation. -/
def edistLtTopSetoid : Setoidₓ α where
  R := fun x y => edist x y < ⊤
  iseqv :=
    ⟨fun x => by
      rw [edist_self]
      exact Ennreal.coe_lt_top, fun x y h => by
      rwa [edist_comm], fun x y z hxy hyz => lt_of_le_of_ltₓ (edist_triangle x y z) (Ennreal.add_lt_top.2 ⟨hxy, hyz⟩)⟩

@[simp]
theorem ball_zero : Ball x 0 = ∅ := by
  rw [Emetric.ball_eq_empty_iff]

theorem nhds_basis_eball : (𝓝 x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) (Ball x) :=
  nhds_basis_uniformity uniformity_basis_edist

theorem nhds_basis_closed_eball : (𝓝 x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) (ClosedBall x) :=
  nhds_basis_uniformity uniformity_basis_edist_le

theorem nhds_eq : 𝓝 x = ⨅ ε > 0, 𝓟 (Ball x ε) :=
  nhds_basis_eball.eq_binfi

theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ ε > 0, Ball x ε ⊆ s :=
  nhds_basis_eball.mem_iff

theorem is_open_iff : IsOpen s ↔ ∀, ∀ x ∈ s, ∀, ∃ ε > 0, Ball x ε ⊆ s := by
  simp [← is_open_iff_nhds, ← mem_nhds_iff]

theorem is_open_ball : IsOpen (Ball x ε) :=
  is_open_iff.2 fun y => exists_ball_subset_ball

theorem is_closed_ball_top : IsClosed (Ball x ⊤) :=
  is_open_compl_iff.1 <|
    is_open_iff.2 fun y hy =>
      ⟨⊤, Ennreal.coe_lt_top,
        (ball_disjoint <| by
            rw [Ennreal.top_add]
            exact le_of_not_ltₓ hy).subset_compl_right⟩

theorem ball_mem_nhds (x : α) {ε : ℝ≥0∞} (ε0 : 0 < ε) : Ball x ε ∈ 𝓝 x :=
  is_open_ball.mem_nhds (mem_ball_self ε0)

theorem closed_ball_mem_nhds (x : α) {ε : ℝ≥0∞} (ε0 : 0 < ε) : ClosedBall x ε ∈ 𝓝 x :=
  mem_of_superset (ball_mem_nhds x ε0) ball_subset_closed_ball

theorem ball_prod_same [PseudoEmetricSpace β] (x : α) (y : β) (r : ℝ≥0∞) : Ball x r ×ˢ Ball y r = Ball (x, y) r :=
  ext fun z => max_lt_iff.symm

theorem closed_ball_prod_same [PseudoEmetricSpace β] (x : α) (y : β) (r : ℝ≥0∞) :
    ClosedBall x r ×ˢ ClosedBall y r = ClosedBall (x, y) r :=
  ext fun z => max_le_iff.symm

/-- ε-characterization of the closure in pseudoemetric spaces -/
theorem mem_closure_iff : x ∈ Closure s ↔ ∀, ∀ ε > 0, ∀, ∃ y ∈ s, edist x y < ε :=
  (mem_closure_iff_nhds_basis nhds_basis_eball).trans <| by
    simp only [← mem_ball, ← edist_comm x]

theorem tendsto_nhds {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ ∀, ∀ ε > 0, ∀, ∀ᶠ x in f, edist (u x) a < ε :=
  nhds_basis_eball.tendsto_right_iff

theorem tendsto_at_top [Nonempty β] [SemilatticeSup β] {u : β → α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ ∀, ∀ ε > 0, ∀, ∃ N, ∀, ∀ n ≥ N, ∀, edist (u n) a < ε :=
  (at_top_basis.tendsto_iff nhds_basis_eball).trans <| by
    simp only [← exists_prop, ← true_andₓ, ← mem_Ici, ← mem_ball]

theorem inseparable_iff : Inseparable x y ↔ edist x y = 0 := by
  simp [← inseparable_iff_mem_closure, ← mem_closure_iff, ← edist_comm, ← forall_lt_iff_le']

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (m n «expr ≥ » N)
/-- In a pseudoemetric space, Cauchy sequences are characterized by the fact that, eventually,
the pseudoedistance between its elements is arbitrarily small -/
-- see Note [nolint_ge]
@[nolint ge_or_gt]
theorem cauchy_seq_iff [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀, ∀ ε > 0, ∀, ∃ N, ∀ (m n) (_ : m ≥ N) (_ : n ≥ N), edist (u m) (u n) < ε :=
  uniformity_basis_edist.cauchy_seq_iff

/-- A variation around the emetric characterization of Cauchy sequences -/
theorem cauchy_seq_iff' [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀, ∀ ε > (0 : ℝ≥0∞), ∀, ∃ N, ∀, ∀ n ≥ N, ∀, edist (u n) (u N) < ε :=
  uniformity_basis_edist.cauchy_seq_iff'

/-- A variation of the emetric characterization of Cauchy sequences that deals with
`ℝ≥0` upper bounds. -/
theorem cauchy_seq_iff_nnreal [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε : ℝ≥0 , 0 < ε → ∃ N, ∀ n, N ≤ n → edist (u n) (u N) < ε :=
  uniformity_basis_edist_nnreal.cauchy_seq_iff'

theorem totally_bounded_iff {s : Set α} :
    TotallyBounded s ↔ ∀, ∀ ε > 0, ∀, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, Ball y ε :=
  ⟨fun H ε ε0 => H _ (edist_mem_uniformity ε0), fun H r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, ft, h⟩ := H ε ε0
    ⟨t, ft, h.trans <| Union₂_mono fun y yt z => hε⟩⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem totally_bounded_iff' {s : Set α} :
    TotallyBounded s ↔ ∀, ∀ ε > 0, ∀, ∃ (t : _)(_ : t ⊆ s), Set.Finite t ∧ s ⊆ ⋃ y ∈ t, Ball y ε :=
  ⟨fun H ε ε0 => (totally_bounded_iff_subset.1 H) _ (edist_mem_uniformity ε0), fun H r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, _, ft, h⟩ := H ε ε0
    ⟨t, ft, h.trans <| Union₂_mono fun y yt z => hε⟩⟩

section Compact

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
/-- For a set `s` in a pseudo emetric space, if for every `ε > 0` there exists a countable
set that is `ε`-dense in `s`, then there exists a countable subset `t ⊆ s` that is dense in `s`. -/
theorem subset_countable_closure_of_almost_dense_set (s : Set α)
    (hs : ∀, ∀ ε > 0, ∀, ∃ t : Set α, t.Countable ∧ s ⊆ ⋃ x ∈ t, ClosedBall x ε) :
    ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ s ⊆ Closure t := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨x₀, hx₀⟩)
  · exact ⟨∅, empty_subset _, countable_empty, empty_subset _⟩
    
  choose! T hTc hsT using fun n : ℕ =>
    hs n⁻¹
      (by
        simp )
  have : ∀ r x, ∃ y ∈ s, closed_ball x r ∩ s ⊆ closed_ball y (r * 2) := by
    intro r x
    rcases(closed_ball x r ∩ s).eq_empty_or_nonempty with (he | ⟨y, hxy, hys⟩)
    · refine' ⟨x₀, hx₀, _⟩
      rw [he]
      exact empty_subset _
      
    · refine' ⟨y, hys, fun z hz => _⟩
      calc edist z y ≤ edist z x + edist y x := edist_triangle_right _ _ _ _ ≤ r + r := add_le_add hz.1 hxy _ = r * 2 :=
          (mul_two r).symm
      
  choose f hfs hf
  refine'
    ⟨⋃ n : ℕ, f n⁻¹ '' T n, Union_subset fun n => image_subset_iff.2 fun z hz => hfs _ _,
      countable_Union fun n => (hTc n).Image _, _⟩
  refine' fun x hx => mem_closure_iff.2 fun ε ε0 => _
  rcases Ennreal.exists_inv_nat_lt (Ennreal.half_pos ε0.lt.ne').ne' with ⟨n, hn⟩
  rcases mem_Union₂.1 (hsT n hx) with ⟨y, hyn, hyx⟩
  refine' ⟨f n⁻¹ y, mem_Union.2 ⟨n, mem_image_of_mem _ hyn⟩, _⟩
  calc edist x (f n⁻¹ y) ≤ n⁻¹ * 2 := hf _ _ ⟨hyx, hx⟩_ < ε := Ennreal.mul_lt_of_lt_div hn

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
/-- A compact set in a pseudo emetric space is separable, i.e., it is a subset of the closure of a
countable set.  -/
theorem subset_countable_closure_of_compact {s : Set α} (hs : IsCompact s) :
    ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ s ⊆ Closure t := by
  refine' subset_countable_closure_of_almost_dense_set s fun ε hε => _
  rcases totally_bounded_iff'.1 hs.totally_bounded ε hε with ⟨t, hts, htf, hst⟩
  exact ⟨t, htf.countable, subset.trans hst <| Union₂_mono fun _ _ => ball_subset_closed_ball⟩

end Compact

section SecondCountable

open _Root_.TopologicalSpace

variable (α)

/-- A sigma compact pseudo emetric space has second countable topology. This is not an instance
to avoid a loop with `sigma_compact_space_of_locally_compact_second_countable`.  -/
theorem second_countable_of_sigma_compact [SigmaCompactSpace α] : SecondCountableTopology α := by
  suffices separable_space α by
    exact UniformSpace.second_countable_of_separable α
  choose T hTsub hTc hsubT using fun n => subset_countable_closure_of_compact (is_compact_compact_covering α n)
  refine' ⟨⟨⋃ n, T n, countable_Union hTc, fun x => _⟩⟩
  rcases Union_eq_univ_iff.1 (Union_compact_covering α) x with ⟨n, hn⟩
  exact closure_mono (subset_Union _ n) (hsubT _ hn)

variable {α}

theorem second_countable_of_almost_dense_set
    (hs : ∀, ∀ ε > 0, ∀, ∃ t : Set α, t.Countable ∧ (⋃ x ∈ t, ClosedBall x ε) = univ) : SecondCountableTopology α := by
  suffices separable_space α by
    exact UniformSpace.second_countable_of_separable α
  rcases subset_countable_closure_of_almost_dense_set (univ : Set α) fun ε ε0 => _ with ⟨t, -, htc, ht⟩
  · exact ⟨⟨t, htc, fun x => ht (mem_univ x)⟩⟩
    
  · rcases hs ε ε0 with ⟨t, htc, ht⟩
    exact ⟨t, htc, univ_subset_iff.2 ht⟩
    

end SecondCountable

section Diam

/-- The diameter of a set in a pseudoemetric space, named `emetric.diam` -/
def diam (s : Set α) :=
  ⨆ (x ∈ s) (y ∈ s), edist x y

theorem diam_le_iff {d : ℝ≥0∞} : diam s ≤ d ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, edist x y ≤ d := by
  simp only [← diam, ← supr_le_iff]

theorem diam_image_le_iff {d : ℝ≥0∞} {f : β → α} {s : Set β} :
    diam (f '' s) ≤ d ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, edist (f x) (f y) ≤ d := by
  simp only [← diam_le_iff, ← ball_image_iff]

theorem edist_le_of_diam_le {d} (hx : x ∈ s) (hy : y ∈ s) (hd : diam s ≤ d) : edist x y ≤ d :=
  diam_le_iff.1 hd x hx y hy

/-- If two points belong to some set, their edistance is bounded by the diameter of the set -/
theorem edist_le_diam_of_mem (hx : x ∈ s) (hy : y ∈ s) : edist x y ≤ diam s :=
  edist_le_of_diam_le hx hy le_rfl

/-- If the distance between any two points in a set is bounded by some constant, this constant
bounds the diameter. -/
theorem diam_le {d : ℝ≥0∞} (h : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, edist x y ≤ d) : diam s ≤ d :=
  diam_le_iff.2 h

/-- The diameter of a subsingleton vanishes. -/
theorem diam_subsingleton (hs : s.Subsingleton) : diam s = 0 :=
  nonpos_iff_eq_zero.1 <| diam_le fun x hx y hy => (hs hx hy).symm ▸ edist_self y ▸ le_rfl

/-- The diameter of the empty set vanishes -/
@[simp]
theorem diam_empty : diam (∅ : Set α) = 0 :=
  diam_subsingleton subsingleton_empty

/-- The diameter of a singleton vanishes -/
@[simp]
theorem diam_singleton : diam ({x} : Set α) = 0 :=
  diam_subsingleton subsingleton_singleton

theorem diam_Union_mem_option {ι : Type _} (o : Option ι) (s : ι → Set α) : diam (⋃ i ∈ o, s i) = ⨆ i ∈ o, diam (s i) :=
  by
  cases o <;> simp

theorem diam_insert : diam (insert x s) = max (⨆ y ∈ s, edist x y) (diam s) :=
  eq_of_forall_ge_iff fun d => by
    simp only [← diam_le_iff, ← ball_insert_iff, ← edist_self, ← edist_comm x, ← max_le_iff, ← supr_le_iff, ← zero_le, ←
      true_andₓ, ← forall_and_distrib, ← and_selfₓ, and_assoc]

theorem diam_pair : diam ({x, y} : Set α) = edist x y := by
  simp only [← supr_singleton, ← diam_insert, ← diam_singleton, ← Ennreal.max_zero_right]

theorem diam_triple : diam ({x, y, z} : Set α) = max (max (edist x y) (edist x z)) (edist y z) := by
  simp only [← diam_insert, ← supr_insert, ← supr_singleton, ← diam_singleton, ← Ennreal.max_zero_right, ←
    Ennreal.sup_eq_max]

/-- The diameter is monotonous with respect to inclusion -/
theorem diam_mono {s t : Set α} (h : s ⊆ t) : diam s ≤ diam t :=
  diam_le fun x hx y hy => edist_le_diam_of_mem (h hx) (h hy)

/-- The diameter of a union is controlled by the diameter of the sets, and the edistance
between two points in the sets. -/
theorem diam_union {t : Set α} (xs : x ∈ s) (yt : y ∈ t) : diam (s ∪ t) ≤ diam s + edist x y + diam t := by
  have A : ∀, ∀ a ∈ s, ∀, ∀, ∀ b ∈ t, ∀, edist a b ≤ diam s + edist x y + diam t := fun a ha b hb =>
    calc
      edist a b ≤ edist a x + edist x y + edist y b := edist_triangle4 _ _ _ _
      _ ≤ diam s + edist x y + diam t :=
        add_le_add (add_le_add (edist_le_diam_of_mem ha xs) le_rfl) (edist_le_diam_of_mem yt hb)
      
  refine' diam_le fun a ha b hb => _
  cases' (mem_union _ _ _).1 ha with h'a h'a <;> cases' (mem_union _ _ _).1 hb with h'b h'b
  · calc edist a b ≤ diam s := edist_le_diam_of_mem h'a h'b _ ≤ diam s + (edist x y + diam t) :=
        le_self_add _ = diam s + edist x y + diam t := (add_assocₓ _ _ _).symm
    
  · exact A a h'a b h'b
    
  · have Z := A b h'b a h'a
    rwa [edist_comm] at Z
    
  · calc edist a b ≤ diam t := edist_le_diam_of_mem h'a h'b _ ≤ diam s + edist x y + diam t := le_add_self
    

theorem diam_union' {t : Set α} (h : (s ∩ t).Nonempty) : diam (s ∪ t) ≤ diam s + diam t := by
  let ⟨x, ⟨xs, xt⟩⟩ := h
  simpa using diam_union xs xt

theorem diam_closed_ball {r : ℝ≥0∞} : diam (ClosedBall x r) ≤ 2 * r :=
  diam_le fun a ha b hb =>
    calc
      edist a b ≤ edist a x + edist b x := edist_triangle_right _ _ _
      _ ≤ r + r := add_le_add ha hb
      _ = 2 * r := (two_mul r).symm
      

theorem diam_ball {r : ℝ≥0∞} : diam (Ball x r) ≤ 2 * r :=
  le_transₓ (diam_mono ball_subset_closed_ball) diam_closed_ball

theorem diam_pi_le_of_le {π : β → Type _} [Fintype β] [∀ b, PseudoEmetricSpace (π b)] {s : ∀ b : β, Set (π b)}
    {c : ℝ≥0∞} (h : ∀ b, diam (s b) ≤ c) : diam (Set.Pi Univ s) ≤ c := by
  apply diam_le fun x hx y hy => edist_pi_le_iff.mpr _
  rw [mem_univ_pi] at hx hy
  exact fun b => diam_le_iff.1 (h b) (x b) (hx b) (y b) (hy b)

end Diam

end Emetric

/-- We now define `emetric_space`, extending `pseudo_emetric_space`. -/
--namespace
class EmetricSpace (α : Type u) extends PseudoEmetricSpace α : Type u where
  eq_of_edist_eq_zero : ∀ {x y : α}, edist x y = 0 → x = y

variable {γ : Type w} [EmetricSpace γ]

export EmetricSpace (eq_of_edist_eq_zero)

/-- Characterize the equality of points by the vanishing of their extended distance -/
@[simp]
theorem edist_eq_zero {x y : γ} : edist x y = 0 ↔ x = y :=
  Iff.intro eq_of_edist_eq_zero fun this : x = y => this ▸ edist_self _

@[simp]
theorem zero_eq_edist {x y : γ} : 0 = edist x y ↔ x = y :=
  Iff.intro (fun h => eq_of_edist_eq_zero h.symm) fun this : x = y => this ▸ (edist_self _).symm

theorem edist_le_zero {x y : γ} : edist x y ≤ 0 ↔ x = y :=
  nonpos_iff_eq_zero.trans edist_eq_zero

@[simp]
theorem edist_pos {x y : γ} : 0 < edist x y ↔ x ≠ y := by
  simp [not_leₓ]

/-- Two points coincide if their distance is `< ε` for all positive ε -/
theorem eq_of_forall_edist_le {x y : γ} (h : ∀, ∀ ε > 0, ∀, edist x y ≤ ε) : x = y :=
  eq_of_edist_eq_zero (eq_of_le_of_forall_le_of_dense bot_le h)

/-- A map between emetric spaces is a uniform embedding if and only if the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
theorem uniform_embedding_iff' [EmetricSpace β] {f : γ → β} :
    UniformEmbedding f ↔
      (∀, ∀ ε > 0, ∀, ∃ δ > 0, ∀ {a b : γ}, edist a b < δ → edist (f a) (f b) < ε) ∧
        ∀, ∀ δ > 0, ∀, ∃ ε > 0, ∀ {a b : γ}, edist (f a) (f b) < ε → edist a b < δ :=
  by
  constructor
  · intro h
    exact ⟨Emetric.uniform_continuous_iff.1 (uniform_embedding_iff.1 h).2.1, (uniform_embedding_iff.1 h).2.2⟩
    
  · rintro ⟨h₁, h₂⟩
    refine' uniform_embedding_iff.2 ⟨_, Emetric.uniform_continuous_iff.2 h₁, h₂⟩
    intro x y hxy
    have : edist x y ≤ 0 := by
      refine' le_of_forall_lt' fun δ δpos => _
      rcases h₂ δ δpos with ⟨ε, εpos, hε⟩
      have : edist (f x) (f y) < ε := by
        simpa [← hxy]
      exact hε this
    simpa using this
    

/-- An emetric space is separated -/
-- see Note [lower instance priority]
instance (priority := 100) to_separated : SeparatedSpace γ :=
  separated_def.2 fun x y h => eq_of_forall_edist_le fun ε ε0 => le_of_ltₓ (h _ (edist_mem_uniformity ε0))

/-- If a `pseudo_emetric_space` is a T₀ space, then it is an `emetric_space`. -/
def Emetric.ofT0PseudoEmetricSpace (α : Type _) [PseudoEmetricSpace α] [T0Space α] : EmetricSpace α :=
  { ‹PseudoEmetricSpace α› with
    eq_of_edist_eq_zero := fun x y hdist => Inseparable.eq <| Emetric.inseparable_iff.2 hdist }

/-- Auxiliary function to replace the uniformity on an emetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
-/
def EmetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : EmetricSpace γ)
    (H : @uniformity _ U = @uniformity _ PseudoEmetricSpace.toUniformSpace) : EmetricSpace γ where
  edist := @edist _ m.toHasEdist
  edist_self := edist_self
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEmetricSpace.uniformity_edist γ _)

/-- The extended metric induced by an injective function taking values in a emetric space. -/
def EmetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : EmetricSpace β) : EmetricSpace γ where
  edist := fun x y => edist (f x) (f y)
  edist_self := fun x => edist_self _
  eq_of_edist_eq_zero := fun x y h => hf (edist_eq_zero.1 h)
  edist_comm := fun x y => edist_comm _ _
  edist_triangle := fun x y z => edist_triangle _ _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_edist := by
    apply @uniformity_dist_of_mem_uniformity _ _ _ _ _ fun x y => edist (f x) (f y)
    refine' fun s => mem_comap.trans _
    constructor <;> intro H
    · rcases H with ⟨r, ru, rs⟩
      rcases mem_uniformity_edist.1 ru with ⟨ε, ε0, hε⟩
      refine' ⟨ε, ε0, fun a b h => rs (hε _)⟩
      exact h
      
    · rcases H with ⟨ε, ε0, hε⟩
      exact ⟨_, edist_mem_uniformity ε0, fun ⟨a, b⟩ => hε⟩
      

/-- Emetric space instance on subsets of emetric spaces -/
instance {α : Type _} {p : α → Prop} [EmetricSpace α] : EmetricSpace (Subtype p) :=
  EmetricSpace.induced coe Subtype.coe_injective ‹_›

/-- Emetric space instance on the multiplicative opposite of an emetric space. -/
@[to_additive "Emetric space instance on the additive opposite of an emetric space."]
instance {α : Type _} [EmetricSpace α] : EmetricSpace αᵐᵒᵖ :=
  EmetricSpace.induced MulOpposite.unop MulOpposite.unop_injective ‹_›

instance {α : Type _} [EmetricSpace α] : EmetricSpace (ULift α) :=
  EmetricSpace.induced ULift.down ULift.down_injective ‹_›

/-- The product of two emetric spaces, with the max distance, is an extended
metric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance Prod.emetricSpaceMax [EmetricSpace β] : EmetricSpace (γ × β) :=
  { Prod.pseudoEmetricSpaceMax with
    eq_of_edist_eq_zero := fun x y h => by
      cases' max_le_iff.1 (le_of_eqₓ h) with h₁ h₂
      have A : x.fst = y.fst := edist_le_zero.1 h₁
      have B : x.snd = y.snd := edist_le_zero.1 h₂
      exact Prod.ext_iff.2 ⟨A, B⟩ }

/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_edist : 𝓤 γ = ⨅ ε > 0, 𝓟 { p : γ × γ | edist p.1 p.2 < ε } :=
  PseudoEmetricSpace.uniformity_edist

section Pi

open Finset

variable {π : β → Type _} [Fintype β]

/-- The product of a finite number of emetric spaces, with the max distance, is still
an emetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
instance emetricSpacePi [∀ b, EmetricSpace (π b)] : EmetricSpace (∀ b, π b) :=
  { pseudoEmetricSpacePi with
    eq_of_edist_eq_zero := fun f g eq0 => by
      have eq1 : (sup univ fun b : β => edist (f b) (g b)) ≤ 0 := le_of_eqₓ eq0
      simp only [← Finset.sup_le_iff] at eq1
      exact funext fun b => edist_le_zero.1 <| eq1 b <| mem_univ b }

end Pi

namespace Emetric

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t «expr ⊆ » s)
/-- A compact set in an emetric space is separable, i.e., it is the closure of a countable set. -/
theorem countable_closure_of_compact {s : Set γ} (hs : IsCompact s) :
    ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ s = Closure t := by
  rcases subset_countable_closure_of_compact hs with ⟨t, hts, htc, hsub⟩
  exact ⟨t, hts, htc, subset.antisymm hsub (closure_minimal hts hs.is_closed)⟩

section Diam

variable {s : Set γ}

theorem diam_eq_zero_iff : diam s = 0 ↔ s.Subsingleton :=
  ⟨fun h x hx y hy => edist_le_zero.1 <| h ▸ edist_le_diam_of_mem hx hy, diam_subsingleton⟩

theorem diam_pos_iff : 0 < diam s ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  simp only [← pos_iff_ne_zero, ← Ne.def, ← diam_eq_zero_iff, ← Set.Subsingleton, ← not_forall]

end Diam

end Emetric


/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Analysis.MeanInequalities

/-!
# `L^p` distance on finite products of metric spaces
Given finitely many metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a real parameter `p ∈ [1, ∞)`, that also induce
the product topology. We define them in this file. The distance on `Π i, α i` is given by
$$
d(x, y) = \left(\sum d(x_i, y_i)^p\right)^{1/p}.
$$

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Pi type, named
`pi_Lp p α`. The assumpion `[fact (1 ≤ p)]` is required for the metric and normed space instances.

We ensure that the topology and uniform structure on `pi_Lp p α` are (defeq to) the product
topology and product uniformity, to be able to use freely continuity statements for the coordinate
functions, for instance.

## Implementation notes

We only deal with the `L^p` distance on a product of finitely many metric spaces, which may be
distinct. A closely related construction is `lp`, the `L^p` norm on a product of (possibly
infinitely many) normed spaces, where the norm is
$$
\left(\sum ∥f (x)∥^p \right)^{1/p}.
$$
However, the topology induced by this construction is not the product topology, and some functions
have infinite `L^p` norm. These subtleties are not present in the case of finitely many metric
spaces, hence it is worth devoting a file to this specific case which is particularly well behaved.

Another related construction is `measure_theory.Lp`, the `L^p` norm on the space of functions from
a measure space to a normed space, where the norm is
$$
\left(\int ∥f (x)∥^p dμ\right)^{1/p}.
$$
This has all the same subtleties as `lp`, and the further subtlety that this only
defines a seminorm (as almost everywhere zero functions have zero `L^p` norm).
The construction `pi_Lp` corresponds to the special case of `measure_theory.Lp` in which the basis
is a finite space equipped with the counting measure.

To prove that the topology (and the uniform structure) on a finite product with the `L^p` distance
are the same as those coming from the `L^∞` distance, we could argue that the `L^p` and `L^∞` norms
are equivalent on `ℝ^n` for abstract (norm equivalence) reasons. Instead, we give a more explicit
(easy) proof which provides a comparison between these two norms with explicit constants.

We also set up the theory for `pseudo_emetric_space` and `pseudo_metric_space`.
-/


open Real Set Filter IsROrC Bornology

open BigOperators uniformity TopologicalSpace Nnreal Ennreal

noncomputable section

variable {ι : Type _}

/-- A copy of a Pi type, on which we will put the `L^p` distance. Since the Pi type itself is
already endowed with the `L^∞` distance, we need the type synonym to avoid confusing typeclass
resolution. Also, we let it depend on `p`, to get a whole family of type on which we can put
different distances. -/
@[nolint unused_arguments]
def PiLp {ι : Type _} (p : ℝ) (α : ι → Type _) : Type _ :=
  ∀ i : ι, α i

instance {ι : Type _} (p : ℝ) (α : ι → Type _) [∀ i, Inhabited (α i)] : Inhabited (PiLp p α) :=
  ⟨fun i => default⟩

instance fact_one_le_one_real : Fact ((1 : ℝ) ≤ 1) :=
  ⟨rfl.le⟩

instance fact_one_le_two_real : Fact ((1 : ℝ) ≤ 2) :=
  ⟨one_le_two⟩

namespace PiLp

variable (p : ℝ) [fact_one_le_p : Fact (1 ≤ p)] (𝕜 : Type _) (α : ι → Type _) (β : ι → Type _)

/-- Canonical bijection between `pi_Lp p α` and the original Pi type. We introduce it to be able
to compare the `L^p` and `L^∞` distances through it. -/
protected def equiv : PiLp p α ≃ ∀ i : ι, α i :=
  Equivₓ.refl _

theorem equiv_apply (x : PiLp p α) (i : ι) : PiLp.equiv p α x i = x i :=
  rfl

theorem equiv_symm_apply (x : ∀ i, α i) (i : ι) : (PiLp.equiv p α).symm x i = x i :=
  rfl

@[simp]
theorem equiv_apply' (x : PiLp p α) : PiLp.equiv p α x = x :=
  rfl

@[simp]
theorem equiv_symm_apply' (x : ∀ i, α i) : (PiLp.equiv p α).symm x = x :=
  rfl

section

/-!
### The uniformity on finite `L^p` products is the product uniformity

In this section, we put the `L^p` edistance on `pi_Lp p α`, and we check that the uniformity
coming from this edistance coincides with the product uniformity, by showing that the canonical
map to the Pi type (with the `L^∞` distance) is a uniform embedding, as it is both Lipschitz and
antiLipschitz.

We only register this emetric space structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.
-/


variable [∀ i, PseudoMetricSpace (α i)] [∀ i, PseudoEmetricSpace (β i)] [Fintype ι]

include fact_one_le_p

private theorem pos : 0 < p :=
  zero_lt_one.trans_le fact_one_le_p.out

/-- Endowing the space `pi_Lp p β` with the `L^p` pseudoedistance. This definition is not
satisfactory, as it does not register the fact that the topology and the uniform structure coincide
with the product one. Therefore, we do not register it as an instance. Using this as a temporary
pseudoemetric space instance, we will show that the uniform structure is equal (but not defeq) to
the product one, and then register an instance in which we replace the uniform structure by the
product one using this pseudoemetric space and `pseudo_emetric_space.replace_uniformity`. -/
def pseudoEmetricAux : PseudoEmetricSpace (PiLp p β) where
  edist := fun f g => (∑ i, edist (f i) (g i) ^ p) ^ (1 / p)
  edist_self := fun f => by
    simp [← edist, ← Ennreal.zero_rpow_of_pos (Pos p), ← Ennreal.zero_rpow_of_pos (inv_pos.2 <| Pos p)]
  edist_comm := fun f g => by
    simp [← edist, ← edist_comm]
  edist_triangle := fun f g h =>
    calc
      (∑ i, edist (f i) (h i) ^ p) ^ (1 / p) ≤ (∑ i, (edist (f i) (g i) + edist (g i) (h i)) ^ p) ^ (1 / p) := by
        apply Ennreal.rpow_le_rpow _ (one_div_nonneg.2 (Pos p).le)
        refine' Finset.sum_le_sum fun i hi => _
        exact Ennreal.rpow_le_rpow (edist_triangle _ _ _) (Pos p).le
      _ ≤ (∑ i, edist (f i) (g i) ^ p) ^ (1 / p) + (∑ i, edist (g i) (h i) ^ p) ^ (1 / p) :=
        Ennreal.Lp_add_le _ _ _ fact_one_le_p.out
      

attribute [local instance] PiLp.pseudoEmetricAux

/-- Endowing the space `pi_Lp p β` with the `L^p` pseudodistance. This definition is not
satisfactory, as it does not register the fact that the topology, the uniform structure, and the
bornology coincide with the product ones. Therefore, we do not register it as an instance. Using
this as a temporary pseudoemetric space instance, we will show that the uniform structure is equal
(but not defeq) to the product one, and then register an instance in which we replace the uniform
structure and the bornology by the product ones using this pseudometric space,
`pseudo_metric_space.replace_uniformity`, and `pseudo_metric_space.replace_bornology`.

See note [reducible non-instances] -/
@[reducible]
def pseudoMetricAux : PseudoMetricSpace (PiLp p α) :=
  PseudoEmetricSpace.toPseudoMetricSpaceOfDist (fun f g => (∑ i, dist (f i) (g i) ^ p) ^ (1 / p))
    (fun f g =>
      Ennreal.rpow_ne_top_of_nonneg (one_div_nonneg.2 (Pos p).le) <|
        ne_of_ltₓ <| Ennreal.sum_lt_top fun i hi => Ennreal.rpow_ne_top_of_nonneg (Pos p).le (edist_ne_top _ _))
    fun f g => by
    have A : ∀ i, edist (f i) (g i) ^ p ≠ ⊤ := fun i => Ennreal.rpow_ne_top_of_nonneg (Pos p).le (edist_ne_top _ _)
    have B : edist f g = (∑ i, edist (f i) (g i) ^ p) ^ (1 / p) := rfl
    simp only [← B, ← dist_edist, ← Ennreal.to_real_rpow, Ennreal.to_real_sum fun i _ => A i]

attribute [local instance] PiLp.pseudoMetricAux

theorem lipschitz_with_equiv_aux : LipschitzWith 1 (PiLp.equiv p β) := by
  have cancel : p * (1 / p) = 1 := mul_div_cancel' 1 (Pos p).ne'
  intro x y
  simp only [← edist, ← forall_prop_of_true, ← one_mulₓ, ← Finset.mem_univ, ← Finset.sup_le_iff, ← Ennreal.coe_one]
  intro i
  calc edist (x i) (y i) = (edist (x i) (y i) ^ p) ^ (1 / p) := by
      simp [Ennreal.rpow_mul, ← cancel, -one_div]_ ≤ (∑ i, edist (x i) (y i) ^ p) ^ (1 / p) := by
      apply Ennreal.rpow_le_rpow _ (one_div_nonneg.2 <| (Pos p).le)
      exact Finset.single_le_sum (fun i hi => (bot_le : (0 : ℝ≥0∞) ≤ _)) (Finset.mem_univ i)

theorem antilipschitz_with_equiv_aux : AntilipschitzWith ((Fintype.card ι : ℝ≥0 ) ^ (1 / p)) (PiLp.equiv p β) := by
  have pos : 0 < p := lt_of_lt_of_leₓ zero_lt_one fact_one_le_p.out
  have nonneg : 0 ≤ 1 / p := one_div_nonneg.2 (le_of_ltₓ Pos)
  have cancel : p * (1 / p) = 1 := mul_div_cancel' 1 (ne_of_gtₓ Pos)
  intro x y
  simp [← edist, -one_div]
  calc (∑ i, edist (x i) (y i) ^ p) ^ (1 / p) ≤ (∑ i, edist (PiLp.equiv p β x) (PiLp.equiv p β y) ^ p) ^ (1 / p) := by
      apply Ennreal.rpow_le_rpow _ nonneg
      apply Finset.sum_le_sum fun i hi => _
      apply Ennreal.rpow_le_rpow _ (le_of_ltₓ Pos)
      exact
        Finset.le_sup
          (Finset.mem_univ
            i)_ = ((Fintype.card ι : ℝ≥0 ) ^ (1 / p) : ℝ≥0 ) * edist (PiLp.equiv p β x) (PiLp.equiv p β y) :=
      by
      simp only [← nsmul_eq_mul, ← Finset.card_univ, ← Ennreal.rpow_one, ← Finset.sum_const, ←
        Ennreal.mul_rpow_of_nonneg _ _ nonneg, Ennreal.rpow_mul, ← cancel]
      have : (Fintype.card ι : ℝ≥0∞) = (Fintype.card ι : ℝ≥0 ) := (Ennreal.coe_nat (Fintype.card ι)).symm
      rw [this, Ennreal.coe_rpow_of_nonneg _ nonneg]

theorem aux_uniformity_eq : 𝓤 (PiLp p β) = @uniformity _ (Pi.uniformSpace _) := by
  have A : UniformInducing (PiLp.equiv p β) :=
    (antilipschitz_with_equiv_aux p β).UniformInducing (lipschitz_with_equiv_aux p β).UniformContinuous
  have : (fun x : PiLp p β × PiLp p β => ((PiLp.equiv p β) x.fst, (PiLp.equiv p β) x.snd)) = id := by
    ext i <;> rfl
  rw [← A.comap_uniformity, this, comap_id]

theorem aux_cobounded_eq : cobounded (PiLp p α) = @cobounded _ Pi.bornology :=
  calc
    cobounded (PiLp p α) = comap (PiLp.equiv p α) (cobounded _) :=
      le_antisymmₓ (antilipschitz_with_equiv_aux p α).tendsto_cobounded.le_comap
        (lipschitz_with_equiv_aux p α).comap_cobounded_le
    _ = _ := comap_id
    

end

/-! ### Instances on finite `L^p` products -/


instance uniformSpace [∀ i, UniformSpace (β i)] : UniformSpace (PiLp p β) :=
  Pi.uniformSpace _

variable [Fintype ι]

instance bornology [∀ i, Bornology (β i)] : Bornology (PiLp p β) :=
  Pi.bornology

include fact_one_le_p

/-- pseudoemetric space instance on the product of finitely many pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
instance [∀ i, PseudoEmetricSpace (β i)] : PseudoEmetricSpace (PiLp p β) :=
  (pseudoEmetricAux p β).replaceUniformity (aux_uniformity_eq p β).symm

/-- emetric space instance on the product of finitely many emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
instance [∀ i, EmetricSpace (α i)] : EmetricSpace (PiLp p α) :=
  @Emetric.ofT0PseudoEmetricSpace (PiLp p α) _ Pi.t0_space

variable {p β}

theorem edist_eq [∀ i, PseudoEmetricSpace (β i)] (x y : PiLp p β) :
    edist x y = (∑ i, edist (x i) (y i) ^ p) ^ (1 / p) :=
  rfl

variable (p β)

/-- pseudometric space instance on the product of finitely many psuedometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
instance [∀ i, PseudoMetricSpace (β i)] : PseudoMetricSpace (PiLp p β) :=
  ((pseudoMetricAux p β).replaceUniformity (aux_uniformity_eq p β).symm).replaceBornology fun s =>
    Filter.ext_iff.1 (aux_cobounded_eq p β).symm (sᶜ)

/-- metric space instance on the product of finitely many metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/
instance [∀ i, MetricSpace (α i)] : MetricSpace (PiLp p α) :=
  Metric.ofT0PseudoMetricSpace _

omit fact_one_le_p

theorem dist_eq {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, PseudoMetricSpace (β i)] (x y : PiLp p β) :
    dist x y = (∑ i : ι, dist (x i) (y i) ^ p) ^ (1 / p) :=
  rfl

theorem nndist_eq {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, PseudoMetricSpace (β i)] (x y : PiLp p β) :
    nndist x y = (∑ i : ι, nndist (x i) (y i) ^ p) ^ (1 / p) :=
  Subtype.ext <| by
    push_cast
    exact dist_eq _ _

include fact_one_le_p

theorem lipschitz_with_equiv [∀ i, PseudoEmetricSpace (β i)] : LipschitzWith 1 (PiLp.equiv p β) :=
  lipschitz_with_equiv_aux p β

theorem antilipschitz_with_equiv [∀ i, PseudoEmetricSpace (β i)] :
    AntilipschitzWith ((Fintype.card ι : ℝ≥0 ) ^ (1 / p)) (PiLp.equiv p β) :=
  antilipschitz_with_equiv_aux p β

/-- seminormed group instance on the product of finitely many normed groups, using the `L^p`
norm. -/
instance semiNormedGroup [∀ i, SemiNormedGroup (β i)] : SemiNormedGroup (PiLp p β) :=
  { Pi.addCommGroup with norm := fun f => (∑ i, ∥f i∥ ^ p) ^ (1 / p),
    dist_eq := fun x y => by
      simp [← PiLp.dist_eq, ← dist_eq_norm, ← sub_eq_add_neg] }

/-- normed group instance on the product of finitely many normed groups, using the `L^p` norm. -/
instance normedGroup [∀ i, NormedGroup (α i)] : NormedGroup (PiLp p α) :=
  { PiLp.semiNormedGroup p α with }

omit fact_one_le_p

theorem norm_eq {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (f : PiLp p β) :
    ∥f∥ = (∑ i, ∥f i∥ ^ p) ^ (1 / p) :=
  rfl

theorem nnnorm_eq {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (f : PiLp p β) :
    ∥f∥₊ = (∑ i, ∥f i∥₊ ^ p) ^ (1 / p) := by
  ext
  simp [← Nnreal.coe_sum, ← norm_eq]

theorem norm_eq_of_nat {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (n : ℕ) (h : p = n)
    (f : PiLp p β) : ∥f∥ = (∑ i, ∥f i∥ ^ n) ^ (1 / (n : ℝ)) := by
  simp [← norm_eq, ← h, ← Real.sqrt_eq_rpow, Real.rpow_nat_cast]

theorem norm_eq_of_L2 {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (x : PiLp 2 β) : ∥x∥ = sqrt (∑ i : ι, ∥x i∥ ^ 2) :=
  by
  rw [norm_eq_of_nat 2] <;> simp [← sqrt_eq_rpow]

theorem nnnorm_eq_of_L2 {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (x : PiLp 2 β) :
    ∥x∥₊ = Nnreal.sqrt (∑ i : ι, ∥x i∥₊ ^ 2) :=
  Subtype.ext <| by
    push_cast
    exact norm_eq_of_L2 x

theorem dist_eq_of_L2 {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (x y : PiLp 2 β) :
    dist x y = (∑ i, dist (x i) (y i) ^ 2).sqrt := by
  simp_rw [dist_eq_norm, norm_eq_of_L2, Pi.sub_apply]

theorem nndist_eq_of_L2 {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (x y : PiLp 2 β) :
    nndist x y = (∑ i, nndist (x i) (y i) ^ 2).sqrt :=
  Subtype.ext <| by
    push_cast
    exact dist_eq_of_L2 _ _

theorem edist_eq_of_L2 {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (x y : PiLp 2 β) :
    edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : ℝ) := by
  simp_rw [PiLp.edist_eq, Ennreal.rpow_two]

include fact_one_le_p

variable [NormedField 𝕜]

/-- The product of finitely many normed spaces is a normed space, with the `L^p` norm. -/
instance normedSpace [∀ i, SemiNormedGroup (β i)] [∀ i, NormedSpace 𝕜 (β i)] : NormedSpace 𝕜 (PiLp p β) :=
  { Pi.module ι β 𝕜 with
    norm_smul_le := by
      intro c f
      have : p * (1 / p) = 1 := mul_div_cancel' 1 (lt_of_lt_of_leₓ zero_lt_one fact_one_le_p.out).ne'
      simp only [← PiLp.norm_eq, ← norm_smul, ← mul_rpow, ← norm_nonneg, Finset.mul_sum, ← Pi.smul_apply]
      rw [mul_rpow (rpow_nonneg_of_nonneg (norm_nonneg _) _), ← rpow_mul (norm_nonneg _), this, rpow_one]
      exact Finset.sum_nonneg fun i hi => rpow_nonneg_of_nonneg (norm_nonneg _) _ }

/- Register simplification lemmas for the applications of `pi_Lp` elements, as the usual lemmas
for Pi types will not trigger. -/
variable {𝕜 p α} [∀ i, SemiNormedGroup (β i)] [∀ i, NormedSpace 𝕜 (β i)] (c : 𝕜)

variable (x y : PiLp p β) (x' y' : ∀ i, β i) (i : ι)

@[simp]
theorem zero_apply : (0 : PiLp p β) i = 0 :=
  rfl

@[simp]
theorem add_apply : (x + y) i = x i + y i :=
  rfl

@[simp]
theorem sub_apply : (x - y) i = x i - y i :=
  rfl

@[simp]
theorem smul_apply : (c • x) i = c • x i :=
  rfl

@[simp]
theorem neg_apply : (-x) i = -x i :=
  rfl

variable {ι' : Type _}

variable [Fintype ι']

variable (p 𝕜) (E : Type _) [NormedGroup E] [NormedSpace 𝕜 E]

/-- An equivalence of finite domains induces a linearly isometric equivalence of finitely supported
functions-/
def _root_.linear_isometry_equiv.pi_Lp_congr_left (e : ι ≃ ι') :
    (PiLp p fun i : ι => E) ≃ₗᵢ[𝕜] PiLp p fun i : ι' => E where
  toLinearEquiv := LinearEquiv.piCongrLeft' 𝕜 (fun i : ι => E) e
  norm_map' := by
    intro x
    simp only [← norm]
    simp_rw [LinearEquiv.Pi_congr_left'_apply 𝕜 (fun i : ι => E) e x _]
    congr
    rw [Fintype.sum_equiv e.symm]
    exact fun i => rfl

variable {p 𝕜 E}

@[simp]
theorem _root_.linear_isometry_equiv.pi_Lp_congr_left_apply (e : ι ≃ ι') (v : PiLp p fun i : ι => E) :
    LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e v = Equivₓ.piCongrLeft' (fun i : ι => E) e v :=
  rfl

@[simp]
theorem _root_.linear_isometry_equiv.pi_Lp_congr_left_symm (e : ι ≃ ι') :
    (LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e).symm = LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e.symm :=
  LinearIsometryEquiv.ext fun x => rfl

@[simp]
theorem _root_.linear_isometry_equiv.pi_Lp_congr_left_single [DecidableEq ι] [DecidableEq ι'] (e : ι ≃ ι') (i : ι)
    (v : E) : LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e (Pi.single i v) = Pi.single (e i) v := by
  funext x
  simp [← LinearIsometryEquiv.piLpCongrLeft, ← LinearEquiv.piCongrLeft', ← Equivₓ.piCongrLeft', ← Pi.single, ←
    Function.update, ← Equivₓ.symm_apply_eq]

@[simp]
theorem equiv_zero : PiLp.equiv p β 0 = 0 :=
  rfl

@[simp]
theorem equiv_symm_zero : (PiLp.equiv p β).symm 0 = 0 :=
  rfl

@[simp]
theorem equiv_add : PiLp.equiv p β (x + y) = PiLp.equiv p β x + PiLp.equiv p β y :=
  rfl

@[simp]
theorem equiv_symm_add : (PiLp.equiv p β).symm (x' + y') = (PiLp.equiv p β).symm x' + (PiLp.equiv p β).symm y' :=
  rfl

@[simp]
theorem equiv_sub : PiLp.equiv p β (x - y) = PiLp.equiv p β x - PiLp.equiv p β y :=
  rfl

@[simp]
theorem equiv_symm_sub : (PiLp.equiv p β).symm (x' - y') = (PiLp.equiv p β).symm x' - (PiLp.equiv p β).symm y' :=
  rfl

@[simp]
theorem equiv_neg : PiLp.equiv p β (-x) = -PiLp.equiv p β x :=
  rfl

@[simp]
theorem equiv_symm_neg : (PiLp.equiv p β).symm (-x') = -(PiLp.equiv p β).symm x' :=
  rfl

@[simp]
theorem equiv_smul : PiLp.equiv p β (c • x) = c • PiLp.equiv p β x :=
  rfl

@[simp]
theorem equiv_symm_smul : (PiLp.equiv p β).symm (c • x') = c • (PiLp.equiv p β).symm x' :=
  rfl

theorem nnnorm_equiv_symm_const {β} [SemiNormedGroup β] (b : β) :
    ∥(PiLp.equiv p fun _ : ι => β).symm (Function.const _ b)∥₊ = Fintype.card ι ^ (1 / p) * ∥b∥₊ := by
  have : p ≠ 0 := (zero_lt_one.trans_le (Fact.out <| 1 ≤ p)).ne'
  simp_rw [PiLp.nnnorm_eq, equiv_symm_apply, Function.const_applyₓ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nnreal.mul_rpow, ← Nnreal.rpow_mul, mul_one_div_cancel this, Nnreal.rpow_one]

theorem norm_equiv_symm_const {β} [SemiNormedGroup β] (b : β) :
    ∥(PiLp.equiv p fun _ : ι => β).symm (Function.const _ b)∥ = Fintype.card ι ^ (1 / p) * ∥b∥ :=
  (congr_arg coe <| nnnorm_equiv_symm_const b).trans <| by
    simp

theorem nnnorm_equiv_symm_one {β} [SemiNormedGroup β] [One β] :
    ∥(PiLp.equiv p fun _ : ι => β).symm 1∥₊ = Fintype.card ι ^ (1 / p) * ∥(1 : β)∥₊ :=
  (nnnorm_equiv_symm_const (1 : β)).trans rfl

theorem norm_equiv_symm_one {β} [SemiNormedGroup β] [One β] :
    ∥(PiLp.equiv p fun _ : ι => β).symm 1∥ = Fintype.card ι ^ (1 / p) * ∥(1 : β)∥ :=
  (norm_equiv_symm_const (1 : β)).trans rfl

variable (𝕜)

/-- `pi_Lp.equiv` as a linear map. -/
@[simps (config := { fullyApplied := false })]
protected def linearEquiv : PiLp p β ≃ₗ[𝕜] ∀ i, β i :=
  { LinearEquiv.refl _ _ with toFun := PiLp.equiv _ _, invFun := (PiLp.equiv _ _).symm }

end PiLp


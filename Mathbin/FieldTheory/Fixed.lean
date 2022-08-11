/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.Polynomial.GroupRingAction
import Mathbin.FieldTheory.Normal
import Mathbin.FieldTheory.Separable
import Mathbin.FieldTheory.Tower

/-!
# Fixed field under a group action.

This is the basis of the Fundamental Theorem of Galois Theory.
Given a (finite) group `G` that acts on a field `F`, we define `fixed_points G F`,
the subfield consisting of elements of `F` fixed_points by every element of `G`.

This subfield is then normal and separable, and in addition (TODO) if `G` acts faithfully on `F`
then `finrank (fixed_points G F) F = fintype.card G`.

## Main Definitions

- `fixed_points G F`, the subfield consisting of elements of `F` fixed_points by every element of
`G`, where `G` is a group that acts on `F`.

-/


noncomputable section

open Classical BigOperators

open MulAction Finset FiniteDimensional

universe u v w

variable {M : Type u} [Monoidₓ M]

variable (G : Type u) [Groupₓ G]

variable (F : Type v) [Field F] [MulSemiringAction M F] [MulSemiringAction G F] (m : M)

/-- The subfield of F fixed by the field endomorphism `m`. -/
def FixedBy.subfield : Subfield F where
  Carrier := FixedBy M F m
  zero_mem' := smul_zero m
  add_mem' := fun x y hx hy => (smul_add m x y).trans <| congr_arg2ₓ _ hx hy
  neg_mem' := fun x hx => (smul_neg m x).trans <| congr_arg _ hx
  one_mem' := smul_one m
  mul_mem' := fun x y hx hy => (smul_mul' m x y).trans <| congr_arg2ₓ _ hx hy
  inv_mem' := fun x hx => (smul_inv'' m x).trans <| congr_arg _ hx

section InvariantSubfields

variable (M) {F}

/-- A typeclass for subrings invariant under a `mul_semiring_action`. -/
class IsInvariantSubfield (S : Subfield F) : Prop where
  smul_mem : ∀ (m : M) {x : F}, x ∈ S → m • x ∈ S

variable (S : Subfield F)

instance IsInvariantSubfield.toMulSemiringAction [IsInvariantSubfield M S] : MulSemiringAction M S where
  smul := fun m x => ⟨m • x, IsInvariantSubfield.smul_mem m x.2⟩
  one_smul := fun s => Subtype.eq <| one_smul M s
  mul_smul := fun m₁ m₂ s => Subtype.eq <| mul_smul m₁ m₂ s
  smul_add := fun m s₁ s₂ => Subtype.eq <| smul_add m s₁ s₂
  smul_zero := fun m => Subtype.eq <| smul_zero m
  smul_one := fun m => Subtype.eq <| smul_one m
  smul_mul := fun m s₁ s₂ => Subtype.eq <| smul_mul' m s₁ s₂

instance [IsInvariantSubfield M S] : IsInvariantSubring M S.toSubring where smul_mem := IsInvariantSubfield.smul_mem

end InvariantSubfields

namespace FixedPoints

variable (M)

/-- The subfield of fixed points by a monoid action. -/
-- we use `subfield.copy` so that the underlying set is `fixed_points M F`
def subfield : Subfield F :=
  Subfield.copy (⨅ m : M, FixedBy.subfield F m) (FixedPoints M F)
    (by
      ext z
      simp [← fixed_points, ← FixedBy.subfield, ← infi, ← Subfield.mem_Inf])

instance :
    IsInvariantSubfield M (FixedPoints.subfield M F) where smul_mem := fun g x hx g' => by
    rw [hx, hx]

instance :
    SmulCommClass M (FixedPoints.subfield M F) F where smul_comm := fun m f f' =>
    show m • (↑f * f') = f * m • f' by
      rw [smul_mul', f.prop m]

instance smul_comm_class' : SmulCommClass (FixedPoints.subfield M F) M F :=
  SmulCommClass.symm _ _ _

@[simp]
theorem smul (m : M) (x : FixedPoints.subfield M F) : m • x = x :=
  Subtype.eq <| x.2 m

-- Why is this so slow?
@[simp]
theorem smul_polynomial (m : M) (p : Polynomial (FixedPoints.subfield M F)) : m • p = p :=
  Polynomial.induction_on p
    (fun x => by
      rw [Polynomial.smul_C, smul])
    (fun p q ihp ihq => by
      rw [smul_add, ihp, ihq])
    fun n x ih => by
    rw [smul_mul', Polynomial.smul_C, smul, smul_pow', Polynomial.smul_X]

instance : Algebra (FixedPoints.subfield M F) F := by
  infer_instance

theorem coe_algebra_map : algebraMap (FixedPoints.subfield M F) F = Subfield.subtype (FixedPoints.subfield M F) :=
  rfl

theorem linear_independent_smul_of_linear_independent {s : Finset F} :
    (LinearIndependent (FixedPoints.subfield G F) fun i : (s : Set F) => (i : F)) →
      LinearIndependent F fun i : (s : Set F) => MulAction.toFun G F i :=
  by
  have : IsEmpty ((∅ : Finset F) : Set F) := ⟨Subtype.prop⟩
  refine' Finset.induction_on s (fun _ => linear_independent_empty_type) fun a s has ih hs => _
  rw [coe_insert] at hs⊢
  rw [linear_independent_insert (mt mem_coe.1 has)] at hs
  rw [linear_independent_insert' (mt mem_coe.1 has)]
  refine' ⟨ih hs.1, fun ha => _⟩
  rw [Finsupp.mem_span_image_iff_total] at ha
  rcases ha with ⟨l, hl, hla⟩
  rw [Finsupp.total_apply_of_mem_supported F hl] at hla
  suffices ∀, ∀ i ∈ s, ∀, l i ∈ FixedPoints.subfield G F by
    replace hla := (sum_apply _ _ fun i => l i • to_fun G F i).symm.trans (congr_fun hla 1)
    simp_rw [Pi.smul_apply, to_fun_apply, one_smul] at hla
    refine' hs.2 (hla ▸ Submodule.sum_mem _ fun c hcs => _)
    change (⟨l c, this c hcs⟩ : FixedPoints.subfield G F) • c ∈ _
    exact Submodule.smul_mem _ _ (Submodule.subset_span <| mem_coe.2 hcs)
  intro i his g
  refine'
    eq_of_sub_eq_zero
      (linear_independent_iff'.1 (ih hs.1) s.attach (fun i => g • l i - l i) _ ⟨i, his⟩ (mem_attach _ _) : _)
  refine' (@sum_attach _ _ s _ fun i => (g • l i - l i) • MulAction.toFun G F i).trans _
  ext g'
  dsimp' only
  conv_lhs => rw [sum_apply]congr skip ext rw [Pi.smul_apply, sub_smul, smul_eq_mul]
  rw [sum_sub_distrib, Pi.zero_apply, sub_eq_zero]
  conv_lhs => congr skip ext rw [to_fun_apply, ← mul_inv_cancel_left g g', mul_smul, ← smul_mul', ← to_fun_apply _ x]
  show
    (∑ x in s, g • (fun y => l y • MulAction.toFun G F y) x (g⁻¹ * g')) =
      ∑ x in s, (fun y => l y • MulAction.toFun G F y) x g'
  rw [← smul_sum, ← sum_apply _ _ fun y => l y • to_fun G F y, ← sum_apply _ _ fun y => l y • to_fun G F y]
  dsimp' only
  rw [hla, to_fun_apply, to_fun_apply, smul_smul, mul_inv_cancel_left]

variable [Fintype G] (x : F)

/-- `minpoly G F x` is the minimal polynomial of `(x : F)` over `fixed_points G F`. -/
def minpoly : Polynomial (FixedPoints.subfield G F) :=
  ((prodXSubSmul G F x).toSubring (FixedPoints.subfield G F).toSubring) fun c hc g =>
    let ⟨n, hc0, hn⟩ := Polynomial.mem_frange_iff.1 hc
    hn.symm ▸ prodXSubSmul.coeff G F x g n

namespace minpoly

theorem monic : (minpoly G F x).Monic := by
  simp only [← minpoly, ← Polynomial.monic_to_subring]
  exact prodXSubSmul.monic G F x

theorem eval₂ : Polynomial.eval₂ (Subring.subtype <| (FixedPoints.subfield G F).toSubring) x (minpoly G F x) = 0 := by
  rw [← prodXSubSmul.eval G F x, Polynomial.eval₂_eq_eval_map]
  simp only [← minpoly, ← Polynomial.map_to_subring]

theorem eval₂' : Polynomial.eval₂ (Subfield.subtype <| FixedPoints.subfield G F) x (minpoly G F x) = 0 :=
  eval₂ G F x

theorem ne_one : minpoly G F x ≠ (1 : Polynomial (FixedPoints.subfield G F)) := fun H =>
  have := eval₂ G F x
  (one_ne_zero : (1 : F) ≠ 0) <| by
    rwa [H, Polynomial.eval₂_one] at this

theorem of_eval₂ (f : Polynomial (FixedPoints.subfield G F))
    (hf : Polynomial.eval₂ (Subfield.subtype <| FixedPoints.subfield G F) x f = 0) : minpoly G F x ∣ f := by
  erw [← Polynomial.map_dvd_map' (Subfield.subtype <| FixedPoints.subfield G F), minpoly,
    Polynomial.map_to_subring _ (Subfield G F).toSubring, prodXSubSmul]
  refine'
    Fintype.prod_dvd_of_coprime (Polynomial.pairwise_coprime_X_sub_C <| MulAction.injective_of_quotient_stabilizer G x)
      fun y => (QuotientGroup.induction_on y) fun g => _
  rw [Polynomial.dvd_iff_is_root, Polynomial.IsRoot.def, MulAction.of_quotient_stabilizer_mk, Polynomial.eval_smul', ←
    Subfield.toSubring.subtype_eq_subtype, ← IsInvariantSubring.coe_subtype_hom' G (FixedPoints.subfield G F).toSubring,
    ← MulSemiringActionHom.coe_polynomial, ← MulSemiringActionHom.map_smul, smul_polynomial,
    MulSemiringActionHom.coe_polynomial, IsInvariantSubring.coe_subtype_hom', Polynomial.eval_map,
    Subfield.toSubring.subtype_eq_subtype, hf, smul_zero]

-- Why is this so slow?
theorem irreducible_aux (f g : Polynomial (FixedPoints.subfield G F)) (hf : f.Monic) (hg : g.Monic)
    (hfg : f * g = minpoly G F x) : f = 1 ∨ g = 1 := by
  have hf2 : f ∣ minpoly G F x := by
    rw [← hfg]
    exact dvd_mul_right _ _
  have hg2 : g ∣ minpoly G F x := by
    rw [← hfg]
    exact dvd_mul_left _ _
  have := eval₂ G F x
  rw [← hfg, Polynomial.eval₂_mul, mul_eq_zero] at this
  cases this
  · right
    have hf3 : f = minpoly G F x :=
      Polynomial.eq_of_monic_of_associated hf (monic G F x)
        (associated_of_dvd_dvd hf2 <| @of_eval₂ G _ F _ _ _ x f this)
    rwa [← mul_oneₓ (minpoly G F x), hf3, mul_right_inj' (monic G F x).ne_zero] at hfg
    
  · left
    have hg3 : g = minpoly G F x :=
      Polynomial.eq_of_monic_of_associated hg (monic G F x)
        (associated_of_dvd_dvd hg2 <| @of_eval₂ G _ F _ _ _ x g this)
    rwa [← one_mulₓ (minpoly G F x), hg3, mul_left_inj' (monic G F x).ne_zero] at hfg
    

theorem irreducible : Irreducible (minpoly G F x) :=
  (Polynomial.irreducible_of_monic (monic G F x) (ne_one G F x)).2 (irreducible_aux G F x)

end minpoly

theorem is_integral : IsIntegral (FixedPoints.subfield G F) x :=
  ⟨minpoly G F x, minpoly.monic G F x, minpoly.eval₂ G F x⟩

theorem minpoly_eq_minpoly : minpoly G F x = minpoly (FixedPoints.subfield G F) x :=
  minpoly.eq_of_irreducible_of_monic (minpoly.irreducible G F x) (minpoly.eval₂ G F x) (minpoly.monic G F x)

instance normal : Normal (FixedPoints.subfield G F) F :=
  ⟨fun x => is_integral G F x, fun x =>
    (Polynomial.splits_id_iff_splits _).1 <| by
      rw [← minpoly_eq_minpoly, minpoly, coe_algebra_map, ← Subfield.toSubring.subtype_eq_subtype,
        Polynomial.map_to_subring _ (FixedPoints.subfield G F).toSubring, prodXSubSmul]
      exact Polynomial.splits_prod _ fun _ _ => Polynomial.splits_X_sub_C _⟩

instance separable : IsSeparable (FixedPoints.subfield G F) F :=
  ⟨fun x => is_integral G F x, fun x => by
    -- this was a plain rw when we were using unbundled subrings
    erw [← minpoly_eq_minpoly, ← Polynomial.separable_map (FixedPoints.subfield G F).Subtype, minpoly,
      Polynomial.map_to_subring _ (Subfield G F).toSubring]
    exact Polynomial.separable_prod_X_sub_C_iff.2 (injective_of_quotient_stabilizer G x)⟩

theorem dim_le_card : Module.rank (FixedPoints.subfield G F) F ≤ Fintype.card G :=
  dim_le fun s hs => by
    simpa only [← dim_fun', ← Cardinal.mk_coe_finset, ← Finset.coe_sort_coe, ← Cardinal.lift_nat_cast, ←
      Cardinal.nat_cast_le] using
      cardinal_lift_le_dim_of_linear_independent' (linear_independent_smul_of_linear_independent G F hs)

instance : FiniteDimensional (FixedPoints.subfield G F) F :=
  IsNoetherian.iff_fg.1 <|
    IsNoetherian.iff_dim_lt_aleph_0.2 <| lt_of_le_of_ltₓ (dim_le_card G F) (Cardinal.nat_lt_aleph_0 _)

theorem finrank_le_card : finrank (FixedPoints.subfield G F) F ≤ Fintype.card G := by
  rw [← Cardinal.nat_cast_le, finrank_eq_dim]
  apply dim_le_card

end FixedPoints

theorem linear_independent_to_linear_map (R : Type u) (A : Type v) (B : Type w) [CommSemiringₓ R] [Ringₓ A]
    [Algebra R A] [CommRingₓ B] [IsDomain B] [Algebra R B] :
    LinearIndependent B (AlgHom.toLinearMap : (A →ₐ[R] B) → A →ₗ[R] B) :=
  have : LinearIndependent B (LinearMap.ltoFun R A B ∘ AlgHom.toLinearMap) :=
    ((linear_independent_monoid_hom A B).comp (coe : (A →ₐ[R] B) → A →* B) fun f g hfg =>
      AlgHom.ext <| MonoidHom.ext_iff.1 hfg :
      _)
  this.of_comp _

theorem cardinal_mk_alg_hom (K : Type u) (V : Type v) (W : Type w) [Field K] [Field V] [Algebra K V]
    [FiniteDimensional K V] [Field W] [Algebra K W] [FiniteDimensional K W] :
    Cardinal.mk (V →ₐ[K] W) ≤ finrank W (V →ₗ[K] W) :=
  cardinal_mk_le_finrank_of_linear_independent <| linear_independent_to_linear_map K V W

section AlgHomFintype

/-- A technical finiteness result. -/
noncomputable def Fintype.subtypeProd {E : Type _} {X : Set E} (hX : X.Finite) {L : Type _} (F : E → Multiset L) :
    Fintype (∀ x : X, { l : L // l ∈ F x }) := by
  classical
  let this : Fintype X := Set.Finite.fintype hX
  exact Pi.fintype

variable (E K : Type _) [Field E] [Field K] [Algebra F E] [Algebra F K] [FiniteDimensional F E]

/-- Function from Hom_K(E,L) to pi type Π (x : basis), roots of min poly of x -/
-- Marked as `noncomputable!` since this definition takes multiple seconds to compile,
-- and isn't very computable in practice (since neither `finrank` nor `fin_basis` are).
noncomputable def rootsOfMinPolyPiType (φ : E →ₐ[F] K) (x : Set.Range (FiniteDimensional.finBasis F E : _ → E)) :
    { l : K // l ∈ (((minpoly F x.1).map (algebraMap F K)).roots : Multiset K) } :=
  ⟨φ x, by
    rw [Polynomial.mem_roots_map (minpoly.ne_zero_of_finite_field_extension F x.val), ←
      Polynomial.alg_hom_eval₂_algebra_map, ← φ.map_zero]
    exact congr_arg φ (minpoly.aeval F (x : E))⟩

theorem aux_inj_roots_of_min_poly : Function.Injective (rootsOfMinPolyPiType F E K) := by
  intro f g h
  suffices (f : E →ₗ[F] K) = g by
    rw [LinearMap.ext_iff] at this
    ext x
    exact this x
  rw [Function.funext_iffₓ] at h
  apply LinearMap.ext_on (FiniteDimensional.finBasis F E).span_eq
  rintro e he
  have := h ⟨e, he⟩
  apply_fun Subtype.val  at this
  exact this

/-- Given field extensions `E/F` and `K/F`, with `E/F` finite, there are finitely many `F`-algebra
  homomorphisms `E →ₐ[K] K`. -/
noncomputable instance AlgHom.fintype : Fintype (E →ₐ[F] K) := by
  let n := FiniteDimensional.finrank F E
  let B : Basis (Finₓ n) F E := FiniteDimensional.finBasis F E
  let X := Set.Range (B : Finₓ n → E)
  have hX : X.finite := Set.finite_range ⇑B
  refine'
    @Fintype.ofInjective _ _ (Fintype.subtypeProd hX fun e => ((minpoly F e).map (algebraMap F K)).roots) _
      (aux_inj_roots_of_min_poly F E K)

end AlgHomFintype

noncomputable instance AlgEquiv.fintype (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V]
    [FiniteDimensional K V] : Fintype (V ≃ₐ[K] V) :=
  Fintype.ofEquiv (V →ₐ[K] V) (algEquivEquivAlgHom K V).symm

theorem finrank_alg_hom (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V] [FiniteDimensional K V] :
    Fintype.card (V →ₐ[K] V) ≤ finrank V (V →ₗ[K] V) :=
  fintype_card_le_finrank_of_linear_independent <| linear_independent_to_linear_map K V V

namespace FixedPoints

theorem finrank_eq_card (G : Type u) (F : Type v) [Groupₓ G] [Field F] [Fintype G] [MulSemiringAction G F]
    [HasFaithfulSmul G F] : finrank (FixedPoints.subfield G F) F = Fintype.card G :=
  le_antisymmₓ (FixedPoints.finrank_le_card G F) <|
    calc
      Fintype.card G ≤ Fintype.card (F →ₐ[FixedPoints.subfield G F] F) :=
        Fintype.card_le_of_injective _ (MulSemiringAction.to_alg_hom_injective _ F)
      _ ≤ finrank F (F →ₗ[FixedPoints.subfield G F] F) := finrank_alg_hom (FixedPoints G F) F
      _ = finrank (FixedPoints.subfield G F) F := finrank_linear_map' _ _ _
      

/-- `mul_semiring_action.to_alg_hom` is bijective. -/
theorem to_alg_hom_bijective (G : Type u) (F : Type v) [Groupₓ G] [Field F] [Fintype G] [MulSemiringAction G F]
    [HasFaithfulSmul G F] : Function.Bijective (MulSemiringAction.toAlgHom _ _ : G → F →ₐ[subfield G F] F) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · exact MulSemiringAction.to_alg_hom_injective _ F
    
  · apply le_antisymmₓ
    · exact Fintype.card_le_of_injective _ (MulSemiringAction.to_alg_hom_injective _ F)
      
    · rw [← finrank_eq_card G F]
      exact LE.le.trans_eq (finrank_alg_hom _ F) (finrank_linear_map' _ _ _)
      
    

/-- Bijection between G and algebra homomorphisms that fix the fixed points -/
def toAlgHomEquiv (G : Type u) (F : Type v) [Groupₓ G] [Field F] [Fintype G] [MulSemiringAction G F]
    [HasFaithfulSmul G F] : G ≃ (F →ₐ[FixedPoints.subfield G F] F) :=
  Equivₓ.ofBijective _ (to_alg_hom_bijective G F)

end FixedPoints


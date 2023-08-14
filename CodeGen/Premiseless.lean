import Mathlib
#check Ordnode.balance.proof_22
example: ∀ {α : Type u_1} (r : Ordnode α), id r = Ordnode.nil → Ordnode.nil = id r := by
  intro α r h
  simp_all only [id_eq]



#print NonarchAddGroupSeminorm.add_le_max'

#check NonUnitalSubring.neg_mem'
example: ∀ {R : Type u} [inst : NonUnitalNonAssocRing R] (self : NonUnitalSubring R) {x : R},
  x ∈ self.carrier → -x ∈ self.carrier := by
  intro R inst self x a
  simp_all only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, NonUnitalSubsemiring.mem_toAddSubmonoid,
    NonUnitalSubring.mem_toNonUnitalSubsemiring, neg_mem_iff]



#print LinearMap.polar_mem_iff

#print Equiv.left_inv

#check SmoothBumpCovering.isSubordinate_toBumpCovering -- not elaborated

#print Set.antitone_setOf


#check CategoryTheory.Limits.WidePushoutShape.fintypeHom.proof_6
example: ∀ {J : Type u_1} (j : CategoryTheory.Limits.WidePushoutShape J) (j_1 : J), j = some j_1 → some j_1 = j := by
  intro J j j_1 h
  aesop_subst h
  simp_all only



#check Filter.mem_map₂_iff
example: ∀ {α : Type u_2} {β : Type u_3} {γ : Type u_1} {m : α → β → γ} {f : Filter α} {g : Filter β} {u : Set γ},
  u ∈ Filter.map₂ m f g ↔ ∃ s t, s ∈ f ∧ t ∈ g ∧ Set.image2 m s t ⊆ u := by
  intro α β γ m f g u
  simp_all only [Filter.mem_map₂_iff, Set.image2_subset_iff, exists_and_left]



#check HasFDerivAt.restrictScalars
example: ∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {𝕜' : Type u_1} [inst_1 : NontriviallyNormedField 𝕜']
  [inst_2 : NormedAlgebra 𝕜 𝕜'] {E : Type u_2} [inst_3 : NormedAddCommGroup E] [inst_4 : NormedSpace 𝕜 E]
  [inst_5 : NormedSpace 𝕜' E] [inst_6 : IsScalarTower 𝕜 𝕜' E] {F : Type u_3} [inst_7 : NormedAddCommGroup F]
  [inst_8 : NormedSpace 𝕜 F] [inst_9 : NormedSpace 𝕜' F] [inst_10 : IsScalarTower 𝕜 𝕜' F] {f : E → F} {f' : E →L[𝕜'] F}
  {x : E}, HasFDerivAt f f' x → HasFDerivAt f (ContinuousLinearMap.restrictScalars 𝕜 f') x := by
  intro 𝕜 inst 𝕜' inst_1 inst_2 E inst_3 inst_4 inst_5 inst_6 F inst_7 inst_8 inst_9 inst_10 f f' x h
  exact h



#check HomologicalComplex.Hom.mk.sizeOf_spec -- not elaborated

#check ONote.decidableTopBelow.proof_1
example: ∀ (o a : ONote) (a_1 : ℕ+) (a_2 : ONote), o = ONote.oadd a a_1 a_2 → ONote.oadd a a_1 a_2 = o := by
  intro o a a_1 a_2 h
  aesop_subst h
  simp_all only



#print Int.ModEq.trans

#check not_of_eq_false
example: ∀ {p : Prop}, p = False → ¬p := by
  intro p h
  aesop_subst h
  simp_all only



#print Order.Ideal.coe_subset_coe

#print Int.ModEq.symm

#print IsRegular.right

#print Pretrivialization.proj_toFun

#print Part.right_dom_of_mod_dom

#check Ordnode.balance.proof_24
example: ∀ {α : Type u_1} (rr : Ordnode α), id rr = Ordnode.nil → Ordnode.nil = id rr := by
  intro α rr h
  simp_all only [id_eq]



#check isLowerSet_preimage_ofDual_iff
example: ∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSet (↑OrderDual.ofDual ⁻¹' s) ↔ IsUpperSet s := by
  intro α inst s
  simp_all only [isLowerSet_preimage_ofDual_iff]



#check MeasureTheory.OuterMeasure.isCaratheodory_iff -- not elaborated

#print mem_posSubmonoid

#check Subtype.coe_le_coe
example: ∀ {α : Type u} [inst : LE α] {p : α → Prop} {x y : Subtype p}, x ≤ y ↔ x ≤ y := by
  intro α inst p x y
  simp_all only



#check ConvexCone.Pointed.mono
example: ∀ {𝕜 : Type u_1} {E : Type u_2} [inst : OrderedSemiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : SMul 𝕜 E]
  {S T : ConvexCone 𝕜 E}, S ≤ T → ConvexCone.Pointed S → ConvexCone.Pointed T := by
  intro 𝕜 E inst inst_1 inst_2 S T h a
  apply h
  exact a



#check AddAction.mem_fixedPoints
example: ∀ {α : Type u} (β : Type v) [inst : AddMonoid α] [inst_1 : AddAction α β] {b : β},
  b ∈ AddAction.fixedPoints α β ↔ ∀ (x : α), x +ᵥ b = b := by
  intro α β inst inst_1 b
  simp_all only [AddAction.mem_fixedPoints]



#print Set.Subsingleton.injOn

#check lp.instNormSubtypePreLpMemAddSubgroupToAddGroupInstAddCommGroupPreLpInstMembershipInstSetLikeAddSubgroupLp.proof_2
example: ∀ {p : ENNReal}, p = 0 → 0 = p := by
  intro p hp
  aesop_subst hp
  simp_all only



#check FirstOrder.Language.Sentence.realize_not -- not elaborated

#check CategoryTheory.Limits.WidePushoutShape.struct.proof_6
example: ∀ {J : Type u_1} {Z : CategoryTheory.Limits.WidePushoutShape J}, Z = Z := by
  intro J Z
  simp_all only



#check FP.ofPosRatDn.proof_4
example: ∀ [C : FP.FloatCfg] (n d : ℕ+) (d₁ n₁ : ℕ),
  Int.shift2 (↑d) (↑n) (↑(Nat.size ↑n) - ↑(Nat.size ↑d) - ↑FP.prec + ↑FP.prec) = (d₁, n₁) →
    (d₁, n₁) = Int.shift2 (↑d) (↑n) (↑(Nat.size ↑n) - ↑(Nat.size ↑d) - ↑FP.prec + ↑FP.prec) := by
  intro C n d d₁ n₁ h
  simp_all only [sub_add_cancel]



#check CategoryTheory.Splitting.iso_comp_snd_eq
example: ∀ {𝒜 : Type u_1} [inst : CategoryTheory.Category 𝒜] {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C}
  [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 𝒜] [inst_2 : CategoryTheory.Limits.HasBinaryBiproducts 𝒜]
  (self : CategoryTheory.Splitting f g),
  CategoryTheory.CategoryStruct.comp self.iso.hom CategoryTheory.Limits.biprod.snd = g := by
  intro 𝒜 inst A B C f g inst_1 inst_2 self
  simp_all only [CategoryTheory.Splitting.iso_comp_snd_eq]



#print IsSubmonoid.mul_mem

#check CategoryTheory.discreteCategory.proof_6
example: ∀ (α : Type u_1) {Z : CategoryTheory.Discrete α} (as : α), Z = { as := as } → { as := as } = Z := by
  intro α Z as h
  aesop_subst h
  simp_all only



#print ContinuousMap.Homotopy.map_zero_left

#check BoxIntegral.Prepartition.mem_boxes
example: ∀ {ι : Type u_1} {I J : BoxIntegral.Box ι} (π : BoxIntegral.Prepartition I), J ∈ π.boxes ↔ J ∈ π := by
  intro ι I J π
  simp_all only [BoxIntegral.Prepartition.mem_boxes]



#print StructureGroupoid.liftPropWithinAt_self_target

#print Flag.mk.sizeOf_spec

#check LinearMap.mem_isPairSelfAdjointSubmodule
example: ∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : Module R M]
  {B F : M →ₗ[R] M →ₗ[R] R} (f : Module.End R M),
  f ∈ LinearMap.isPairSelfAdjointSubmodule B F ↔ LinearMap.IsPairSelfAdjoint B F f := by
  intro R M inst inst_1 inst_2 B F f
  simp_all only [LinearMap.mem_isPairSelfAdjointSubmodule]



#print Units.orderEmbeddingVal.proof_1

#check CategoryTheory.Limits.WidePushoutShape.struct.proof_2
example: ∀ {J : Type u_1} {X Y : CategoryTheory.Limits.WidePushoutShape J}, Y = X → X = Y := by
  intro J X Y h
  aesop_subst h
  simp_all only



#print Submonoid.one_mem'

#check ValuationRing.instLinearOrderValueGroup.proof_3 -- not elaborated

#check AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.toBasicOpen -- not elaborated

#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_70
example: ∀ (b q : Turing.PartrecToTM2.Λ'), b = Turing.PartrecToTM2.Λ'.copy q → Turing.PartrecToTM2.Λ'.copy q = b := by
  intro b q h
  aesop_subst h
  simp_all only



#check Subgroup.mem_inf
example: ∀ {G : Type u_1} [inst : Group G] {p p' : Subgroup G} {x : G}, x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := by
  intro G inst p p' x
  simp_all only [ge_iff_le, Subgroup.mem_inf]



#check CategoryTheory.Limits.IsImage.mk.sizeOf_spec -- not elaborated

#print AddSubgroup.IsCommutative.is_comm

#check PGame.fintypeLeftMoves.proof_2
example: ∀ (x : PGame) {α β : Type u_1} {L : α → PGame} {R : β → PGame}, x = PGame.mk α β L R → PGame.mk α β L R = x := by
  intro x α β L R h
  aesop_subst h
  simp_all only



#check Turing.ToPartrec.Cont.halt.sizeOf_spec
example: sizeOf Turing.ToPartrec.Cont.halt = 1 := by
simp_all only



#check CategoryTheory.ShortComplex.HomologyData.comm
example: ∀ {C : Type u_1} [inst : CategoryTheory.Category C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
  {S : CategoryTheory.ShortComplex C} (self : CategoryTheory.ShortComplex.HomologyData S),
  CategoryTheory.CategoryStruct.comp self.left.π (CategoryTheory.CategoryStruct.comp self.iso.hom self.right.ι) =
    CategoryTheory.CategoryStruct.comp self.left.i self.right.p := by
  intro C inst inst_1 S self
  simp_all only [CategoryTheory.ShortComplex.HomologyData.comm]



#print SModEq.trans

#check HasCompactMulSupport.isCompact
example: ∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : One β] {f : α → β},
  HasCompactMulSupport f → IsCompact (mulTSupport f) := by
  intro α β inst inst_1 f hf
  exact hf



#check LinearRecurrence.is_sol_iff_mem_solSpace
example: ∀ {α : Type u_1} [inst : CommSemiring α] (E : LinearRecurrence α) (u : ℕ → α),
  LinearRecurrence.IsSolution E u ↔ u ∈ LinearRecurrence.solSpace E := by
  intro α inst E u
  apply Iff.intro
  · intro a
    exact a
  · intro a
    exact a



#print Subsemiring.mem_prod

#check RegularExpression.zero.sizeOf_spec -- not elaborated

#check OrderRingHom.monotone' -- not elaborated

#check mem_lowerCentralSeries_succ_iff -- not elaborated

#print ContinuousMap.Homotopy.map_one_left

#print Set.pairwise_of_forall

#check Filter.eventually_curry_iff
example: ∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {g : Filter β} {p : α × β → Prop},
  (∀ᶠ (x : α × β) in Filter.curry f g, p x) ↔ ∀ᶠ (x : α) in f, ∀ᶠ (y : β) in g, p (x, y) := by
  intro α β f g p
  apply Iff.intro
  · intro a
    exact a
  · intro a
    exact a



#print IsMonoidHom.map_one

#check NonUnitalStarSubalgebra.mem_carrier
example: ∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : Module R A]
  [inst_3 : Star A] {s : NonUnitalStarSubalgebra R A} {x : A}, x ∈ s.carrier ↔ x ∈ s := by
  intro R A inst inst_1 inst_2 inst_3 s x
  simp_all only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, NonUnitalSubsemiring.mem_toAddSubmonoid,
    NonUnitalSubalgebra.mem_toNonUnitalSubsemiring, NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra]



#check CategoryTheory.Limits.isoZeroOfEpiEqZero.proof_1
example: ∀ {C : Type u_2} [inst : CategoryTheory.Category C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y : C}
  {f : X ⟶ Y}, f = 0 → 0 = f := by
  intro C inst inst_1 X Y f h
  aesop_subst h
  simp_all only



#print MeasureTheory.mem_ae_iff

#print NonUnitalStarSubalgebra.mem_comap

#print LipschitzWith.subtype_mk

#print CategoryTheory.CommSq.LiftStruct.fac_left

#print Setoid.inf_iff_and

#print MonovaryOn.comp_right

#check MeasureTheory.AEEqFun.liftRel_mk_mk
example: ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α}
  [inst_1 : TopologicalSpace β] [inst_2 : TopologicalSpace γ] {r : β → γ → Prop} {f : α → β} {g : α → γ}
  {hf : MeasureTheory.AEStronglyMeasurable f μ} {hg : MeasureTheory.AEStronglyMeasurable g μ},
  MeasureTheory.AEEqFun.LiftRel r (MeasureTheory.AEEqFun.mk f hf) (MeasureTheory.AEEqFun.mk g hg) ↔
    ∀ᵐ (a : α) ∂μ, r (f a) (g a) := by
  intro α β γ inst μ inst_1 inst_2 r f g hf hg
  apply Iff.intro
  · intro a
    exact a
  · intro a
    exact a



#check mem_nonZeroDivisors_iff
example: ∀ {M : Type u_1} [inst : MonoidWithZero M] {r : M}, r ∈ nonZeroDivisors M ↔ ∀ (x : M), x * r = 0 → x = 0 := by
  intro M inst r
  apply Iff.intro
  · intro a x a_1
    apply a
    simp_all only
  · intro a
    exact a



#print Sum.Lex.lt_def

#check AddAction.mem_stabilizer_iff
example: ∀ {α : Type u} {β : Type v} [inst : AddGroup α] [inst_1 : AddAction α β] {b : β} {a : α},
  a ∈ AddAction.stabilizer α b ↔ a +ᵥ b = b := by
  intro α β inst inst_1 b a
  simp_all only [AddAction.mem_stabilizer_iff]



#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_50
example: ∀ (b : Turing.PartrecToTM2.Λ') (p : Turing.PartrecToTM2.Γ' → Bool) (k₁ k₂ : Turing.PartrecToTM2.K')
  (q : Turing.PartrecToTM2.Λ'), b = Turing.PartrecToTM2.Λ'.move p k₁ k₂ q → Turing.PartrecToTM2.Λ'.move p k₁ k₂ q = b := by
  intro b p k₁ k₂ q h
  aesop_subst h
  simp_all only



#print Bipointed.Hom.map_snd

#check UpperSet.mem_inf_iff
example: ∀ {α : Type u_1} [inst : LE α] {s t : UpperSet α} {a : α}, a ∈ s ⊓ t ↔ a ∈ s ∨ a ∈ t := by
  intro α inst s t a
  simp_all only [ge_iff_le, UpperSet.mem_inf_iff]



#check Subgroup.mem_carrier
example: ∀ {G : Type u_1} [inst : Group G] {s : Subgroup G} {x : G}, x ∈ s.carrier ↔ x ∈ s := by
  intro G inst s x
  simp_all only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid]



#print BotHom.map_bot'

#check PUnit.biheytingAlgebra.proof_1
example: ∀ (x x_1 x_2 : PUnit), x ≤ x_1 ⇨ x_2 ↔ x ≤ x_1 ⇨ x_2 := by
  intro x x_1 x_2
  simp_all only [himp_self, PUnit.top_eq, le_refl]



#check IsSMulRegular.isLeftRegular
example: ∀ {R : Type u_1} [inst : Mul R] {a : R}, IsSMulRegular R a → IsLeftRegular a := by
  intro R inst a h
  exact h



#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_122
example: ∀ (b : Turing.PartrecToTM2.Λ') (f : Option Turing.PartrecToTM2.Γ' → Turing.PartrecToTM2.Λ'),
  b = Turing.PartrecToTM2.Λ'.read f → Turing.PartrecToTM2.Λ'.read f = b := by
  intro b f h
  aesop_subst h
  simp_all only



#check AbsoluteValue.nonneg'
example: ∀ {R : Type u_1} {S : Type u_2} [inst : Semiring R] [inst_1 : OrderedSemiring S] (self : AbsoluteValue R S) (x : R),
  0 ≤ MulHom.toFun self.toMulHom x := by
  intro R S inst inst_1 self x
  simp_all only [MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom, NonnegHomClass.map_nonneg]



#check NonUnitalSubalgebra.mem_toNonUnitalStarSubalgebra
example: ∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalSemiring A] [inst_2 : Module R A]
  [inst_3 : Star A] {s : NonUnitalSubalgebra R A} {h_star : ∀ (x : A), x ∈ s → star x ∈ s} {x : A},
  x ∈ NonUnitalSubalgebra.toNonUnitalStarSubalgebra s h_star ↔ x ∈ s := by
  intro R A inst inst_1 inst_2 inst_3 s h_star x
  simp_all only [NonUnitalSubalgebra.mem_toNonUnitalStarSubalgebra]



#check mem_convexAddSubmonoid
example: ∀ {𝕜 : Type u_2} {E : Type u_1} [inst : OrderedSemiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : Module 𝕜 E] {s : Set E},
  s ∈ convexAddSubmonoid 𝕜 E ↔ Convex 𝕜 s := by
  intro 𝕜 E inst inst_1 inst_2 s
  simp_all only [mem_convexAddSubmonoid]



#check CategoryTheory.IsSplitCoequalizer.leftSection_bottom
example: ∀ {C : Type u} [inst : CategoryTheory.Category C] {X Y : C} {f g : X ⟶ Y} {Z : C} {π : Y ⟶ Z}
  (self : CategoryTheory.IsSplitCoequalizer f g π),
  CategoryTheory.CategoryStruct.comp self.leftSection g = CategoryTheory.CategoryStruct.id Y := by
  intro C inst X Y f g Z π self
  simp_all only [CategoryTheory.IsSplitCoequalizer.leftSection_bottom]



#check Subalgebra.mem_star_iff
example: ∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : StarRing R] [inst_2 : Semiring A]
  [inst_3 : Algebra R A] [inst_4 : StarRing A] [inst_5 : StarModule R A] (S : Subalgebra R A) (x : A),
  x ∈ star S ↔ star x ∈ S := by
  intro R A inst inst_1 inst_2 inst_3 inst_4 inst_5 S x
  simp_all only [Subalgebra.mem_star_iff]



#print HasFPowerSeriesOnBall.hasSum

#check CategoryTheory.FreeMonoidalCategory.Unit.sizeOf_spec -- not elaborated

#print NonUnitalAlgHom.mem_equalizer

#check CategoryTheory.BiconeHom.decidableEq.proof_36
example: ∀ (J : Type u_1) {j : CategoryTheory.Bicone J} {j_1 : J},
  j = CategoryTheory.Bicone.diagram j_1 → CategoryTheory.Bicone.diagram j_1 = j := by
  intro J j j_1 h
  aesop_subst h
  simp_all only



#check WithTop.linearOrderedAddCommGroupWithTop.proof_9
example: ∀ {α : Type u_1} [inst : LinearOrderedAddCommGroup α] (a b : WithTop α), a - b = a - b := by
  intro α inst a b
  simp_all only



#check Equiv.Perm.permGroup.proof_4
example: ∀ {α : Type u_1} (a b : Equiv.Perm α), a / b = a / b := by
  intro α a b
  simp_all only



#print RingInvo.involution'

#check ContinuousAt.preimage_mem_nhds
example: ∀ {α : Type u_2} {β : Type u_1} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {x : α}
  {t : Set β}, ContinuousAt f x → t ∈ nhds (f x) → f ⁻¹' t ∈ nhds x := by
  intro α β inst inst_1 f x t h ht
  apply h
  simp_all only



#check ChainComplex.single₀IsoSingle.proof_1
example: ∀ (i n : ℕ), i = Nat.succ n → Nat.succ n = i := by
  intro i n h
  aesop_subst h
  simp_all only



#print WithTop.lt_toDual_iff

#print CategoryTheory.Sheaf.cond

#check Zsqrtd.decidableNonnegg.proof_2
example: ∀ (b : ℤ) (a : ℕ), b = Int.negSucc a → Int.negSucc a = b := by
  intro b a h
  aesop_subst h
  simp_all only



#check ModelWithCorners.source_eq
example: ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
  [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace H] (self : ModelWithCorners 𝕜 E H),
  self.source = Set.univ := by
  intro 𝕜 inst E inst_1 inst_2 H inst_3 self
  simp_all only [ModelWithCorners.source_eq]



#check Flag.mem_coe_iff
example: ∀ {α : Type u_1} [inst : LE α] {s : Flag α} {a : α}, a ∈ s ↔ a ∈ s := by
  intro α inst s a
  simp_all only



#check CategoryTheory.biconeCategoryStruct.proof_28
example: ∀ (J : Type u_1) {X : CategoryTheory.Bicone J} {j : J},
  X = CategoryTheory.Bicone.diagram j → CategoryTheory.Bicone.diagram j = X := by
  intro J X j h
  aesop_subst h
  simp_all only



#print UniqueDiffWithinAt.mem_closure

#print IsTop.isMax

#print CategoryTheory.GrothendieckTopology.Subpresheaf.map

#print CategoryTheory.Comonad.left_counit'

#print Polynomial.isPrimitive_iff_isUnit_of_C_dvd

#print isOpen_sum_iff

#check SubfieldClass.toField.proof_17
example: ∀ {K : Type u_1} [inst : Field K] (S : Type u_2) [inst_1 : SetLike S K] [h : SubfieldClass S K] (s : S)
  (x : { x // x ∈ s }) (n : ℤ), n • x = n • x := by
  intro K inst S inst_1 h s x n
  simp_all only [zsmul_eq_mul]



#check IdemSemiring.ofSemiring.proof_7
example: ∀ {α : Type u_1} [inst : Semiring α] (a b : α), a + b = a + b := by
  intro α inst a b
  simp_all only



#check CommRingCat.punitIsTerminal.proof_3
example: 1 = 1 := by
simp_all only



#check NNReal.coe_le_coe
example: ∀ {r₁ r₂ : NNReal}, r₁ ≤ r₂ ↔ r₁ ≤ r₂ := by
  intro r₁ r₂
  simp_all only



#check CategoryTheory.symmetricOfHasFiniteCoproducts_braiding -- not elaborated

#check Nat.succ_le_of_lt
example: ∀ {n m : ℕ}, n < m → Nat.succ n ≤ m := by
  intro n m h
  exact h



#print WithTop.le_toDual_iff

#print CategoryTheory.IsSplitCoequalizer.condition

#print TopCat.GlueData.MkCore.t_id

#check Nat.Partrec.Code.right.sizeOf_spec
example: sizeOf Nat.Partrec.Code.right = 1 := by
simp_all only



#check AddAction.orbitRel_apply
example: ∀ {α : Type u} {β : Type v} [inst : AddGroup α] [inst_1 : AddAction α β] {x y : β},
  Setoid.Rel (AddAction.orbitRel α β) x y ↔ x ∈ AddAction.orbit α y := by
  intro α β inst inst_1 x y
  apply Iff.intro
  · intro a
    exact a
  · intro a
    exact a



#check PFun.dom_toSubtype_apply_iff
example: ∀ {α : Type u_2} {β : Type u_1} {p : β → Prop} {f : α → β} {a : α}, (PFun.toSubtype p f a).Dom ↔ p (f a) := by
  intro α β p f a
  simp_all only [PFun.toSubtype_apply]



#print Filter.IsCountableBasis.countable

#check Num.zero.sizeOf_spec
example: sizeOf Num.zero = 1 := by
simp_all only



#check commGroupAddCommGroupEquivalence_functor_obj_str_zero
example: CommGroupCat → 0 = 0 := by
  intro X
  simp_all only



#print StructureGroupoid.eq_on_source'

#check Set.mem_mul -- not elaborated

#check DedekindDomain.mem_finiteAdeleRing_iff
example: ∀ {R : Type u_1} {K : Type u_2} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDedekindDomain R]
  [inst_3 : Field K] [inst_4 : Algebra R K] [inst_5 : IsFractionRing R K] (x : DedekindDomain.ProdAdicCompletions R K),
  x ∈ DedekindDomain.finiteAdeleRing R K ↔ DedekindDomain.ProdAdicCompletions.IsFiniteAdele x := by
  intro R K inst inst_1 inst_2 inst_3 inst_4 inst_5 x
  simp_all only [DedekindDomain.mem_finiteAdeleRing_iff]



#check Module.Core.smul_add -- not elaborated

#check Multiset.mem_coe
example: ∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l ↔ a ∈ l := by
  intro α a l
  simp_all only



#check Matrix.transpose_hasOrthogonalRows_iff_hasOrthogonalCols
example: ∀ {α : Type u_2} {n : Type u_3} {m : Type u_1} [inst : Mul α] [inst_1 : AddCommMonoid α] (A : Matrix m n α)
  [inst_2 : Fintype m], Matrix.HasOrthogonalRows (Matrix.transpose A) ↔ Matrix.HasOrthogonalCols A := by
  intro α n m inst inst_1 A inst_2
  simp_all only [Matrix.transpose_hasOrthogonalRows_iff_hasOrthogonalCols]



#check AddSubmonoid.mem_center_iff
example: ∀ {M : Type u_1} [inst : AddMonoid M] {z : M}, z ∈ AddSubmonoid.center M ↔ ∀ (g : M), g + z = z + g := by
  intro M inst z
  apply Iff.intro
  · intro a g
    apply a
  · intro a
    exact a



#check MeasureTheory.IsFundamentalDomain.aedisjoint -- not elaborated

#print FiberBundleCore.isOpen_baseSet

#print Ordnode.all_node'

#check Class.mem_def
-- example: ∀ (A B : Class), A ∈ B ↔ ∃ x, ↑x = A ∧ B x := by
--   intro A B
--   apply Iff.intro
--   · intro a
--     exact a
--   · intro a
--     unhygienic with_reducible aesop_destruct_products
--     aesop_subst left
--     simp_all only [Class.coe_mem]



#check Rack.PreEnvelGroup.unit.sizeOf_spec -- not elaborated

#check IsField.toSemifield.proof_8 -- not elaborated

#check TopologicalSpace.OpenNhds.partialOrder.proof_3 -- not elaborated

#print Polynomial.separable_def'

#print HolderOnWith.edist_le

#check CategoryTheory.Idempotents.Karoubi.Hom.comm
example: ∀ {C : Type u_1} [inst : CategoryTheory.Category C] {P Q : CategoryTheory.Idempotents.Karoubi C}
  (self : CategoryTheory.Idempotents.Karoubi.Hom P Q),
  self.f = CategoryTheory.CategoryStruct.comp P.p (CategoryTheory.CategoryStruct.comp self.f Q.p) := by
  intro C inst P Q self
  simp_all only [CategoryTheory.Idempotents.Karoubi.comp_p, CategoryTheory.Idempotents.Karoubi.p_comp]



#check BilinForm.iIsOrtho_def
example: ∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Module R M] {n : Type w}
  {B : BilinForm R M} {v : n → M}, BilinForm.iIsOrtho B v ↔ ∀ (i j : n), i ≠ j → BilinForm.bilin B (v i) (v j) = 0 := by
  intro R M inst inst_1 inst_2 n B v
  simp_all only [ne_eq]
  apply Iff.intro
  · intro a i j a_1
    apply a
    simp_all only [ne_eq, not_false_eq_true]
  · intro a
    exact a



#check Subfield.mem_toSubring
example: ∀ {K : Type u} [inst : Field K] (s : Subfield K) (x : K), x ∈ s.toSubring ↔ x ∈ s := by
  intro K inst s x
  simp_all only [Subfield.mem_toSubring]



#print Filter.Germ.coe_le

#check AddCon.mem_coe
example: ∀ {M : Type u_1} [inst : AddZeroClass M] {c : AddCon M} {x y : M}, (x, y) ∈ c ↔ (x, y) ∈ c := by
  intro M inst c x y
  simp_all only



#check Cycle.mem_coe_iff
example: ∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l ↔ a ∈ l := by
  intro α a l
  simp_all only



#print MultilinearMap.mk.sizeOf_spec

#print DenseInducing.toInducing

#check Nat.equivFinOfCardPos.proof_4
example: ∀ {α : Type u_1} (val : Infinite α), fintypeOrInfinite α = PSum.inr val → PSum.inr val = fintypeOrInfinite α := by
  intro α val h
  simp_all only



#check SubfieldClass.toField.proof_8
example: ∀ {K : Type u_1} [inst : Field K] (S : Type u_2) [inst_1 : SetLike S K] [h : SubfieldClass S K], S → 0 = 0 := by
  intro K inst S inst_1 h s
  simp_all only



#print Part.right_dom_of_div_dom

#print ofBoolAlg_inj

#check CategoryTheory.Subobject.isoOfEq.proof_2
example: ∀ {C : Type u_1} [inst : CategoryTheory.Category C] {B : C} (X Y : CategoryTheory.Subobject B), X = Y → Y ≤ X := by
  intro C inst B X Y h
  aesop_subst h
  simp_all only [le_refl]



#check GE.ge.le
example: ∀ {α : Type u} [inst : LE α] {x y : α}, x ≥ y → y ≤ x := by
  intro α inst x y h
  simp_all only [ge_iff_le]



#print Inseparable.trans

#check GT.gt.lt
example: ∀ {α : Type u} [inst : LT α] {x y : α}, x > y → y < x := by
  intro α inst x y h
  simp_all only [gt_iff_lt]



#print CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.inverts

#print UniformEquiv.uniformContinuous_toFun

#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_104
example: ∀ (b : Turing.PartrecToTM2.Λ') (k : Turing.PartrecToTM2.K')
  (s : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ') (q : Turing.PartrecToTM2.Λ'),
  b = Turing.PartrecToTM2.Λ'.push k s q → Turing.PartrecToTM2.Λ'.push k s q = b := by
  intro b k s q h
  aesop_subst h
  simp_all only



#print Symmetric.comap

#check AddGroupNorm.lt_def
example: ∀ {E : Type u_1} [inst : AddGroup E] {p q : AddGroupNorm E}, p < q ↔ p < q := by
  intro E inst p q
  simp_all only



#check SimpleGraph.sInf_adj
example: ∀ {V : Type u} {a b : V} {s : Set (SimpleGraph V)},
  SimpleGraph.Adj (sInf s) a b ↔ (∀ (G : SimpleGraph V), G ∈ s → SimpleGraph.Adj G a b) ∧ a ≠ b := by
  intro V a b s
  simp_all only [SimpleGraph.sInf_adj, ne_eq]



#check AddSubsemigroup.mem_carrier
example: ∀ {M : Type u_1} [inst : Add M] {s : AddSubsemigroup M} {x : M}, x ∈ s.carrier ↔ x ∈ s := by
  intro M inst s x
  simp_all only [AddSubsemigroup.mem_carrier]



#check OrderHom.coe_le_coe
example: ∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] {f g : α →o β}, f ≤ g ↔ f ≤ g := by
  intro α β inst inst_1 f g
  simp_all only



#print Matrix.IsAdjMatrix.zero_or_one

#check GroupCat.FilteredColimits.colimitGroup.proof_10 -- not elaborated

#check ClusterPt.neBot
example: ∀ {α : Type u} [inst : TopologicalSpace α] {x : α} {F : Filter α}, ClusterPt x F → Filter.NeBot (nhds x ⊓ F) := by
  intro α inst x F h
  exact h



#check Ordnode.balanceR.proof_13
example: ∀ {α : Type u_1} (l : Ordnode α), id l = Ordnode.nil → Ordnode.nil = id l := by
  intro α l h
  simp_all only [id_eq]



#check CategoryTheory.discreteCategory.proof_8
example: ∀ (α : Type u_1) {Y : CategoryTheory.Discrete α} (as : α), Y = { as := as } → { as := as } = Y := by
  intro α Y as h
  aesop_subst h
  simp_all only



#check CategoryTheory.biconeCategoryStruct.proof_6
example: ∀ (J : Type u_1) {X : CategoryTheory.Bicone J}, X = CategoryTheory.Bicone.right → CategoryTheory.Bicone.right = X := by
  intro J X h
  aesop_subst h
  simp_all only



#print ChartedSpaceCore.continuous_toFun

#print LocallyBoundedMap.comap_cobounded_le'

#check SimpleGraph.Subgraph.inf_adj
example: ∀ {V : Type u} {G : SimpleGraph V} {G₁ G₂ : SimpleGraph.Subgraph G} {a b : V},
  SimpleGraph.Subgraph.Adj (G₁ ⊓ G₂) a b ↔ SimpleGraph.Subgraph.Adj G₁ a b ∧ SimpleGraph.Subgraph.Adj G₂ a b := by
  intro V G G₁ G₂ a b
  simp_all only [ge_iff_le, SimpleGraph.Subgraph.inf_adj]



#print ConvexCone.smul_mem'

#check Ergodic.toMeasurePreserving -- not elaborated

#check IntermediateField.mem_restrictScalars
example: ∀ (K : Type u_3) {L : Type u_2} {L' : Type u_1} [inst : Field K] [inst_1 : Field L] [inst_2 : Field L']
  [inst_3 : Algebra K L] [inst_4 : Algebra K L'] [inst_5 : Algebra L' L] [inst_6 : IsScalarTower K L' L]
  {E : IntermediateField L' L} {x : L}, x ∈ IntermediateField.restrictScalars K E ↔ x ∈ E := by
  intro K L L' inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 E x
  simp_all only [IntermediateField.mem_restrictScalars]



#check SmoothPartitionOfUnity.sum_le_one' -- not elaborated

#print ProperCone.mem_comap

#print RingSubgroupsBasis.rightMul

#print ModuleFilterBasis.smul_right'

#check PUnit.addCommGroup.proof_2
example: ∀ (a : PUnit), 0 + a = 0 + a := by
  intro a
  simp_all only [PUnit.zero_eq, PUnit.add_eq]



#check Subsemigroup.mem_inf
example: ∀ {M : Type u_1} [inst : Mul M] {p p' : Subsemigroup M} {x : M}, x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := by
  intro M inst p p' x
  simp_all only [ge_iff_le, Subsemigroup.mem_inf]



#print Complex.IsExpCmpFilter.tendsto_re

#check hasStrictDerivAt_iff_hasStrictFDerivAt -- not elaborated

#print FirstOrder.Language.LHom.mk.sizeOf_spec

-- #check Affine.Simplex.PointsWithCircumcenterIndex.circumcenter_index.sizeOf_spec
-- example: ∀ {n : ℕ}, sizeOf Affine.Simplex.PointsWithCircumcenterIndex.circumcenter_index = 1 := by
--   intro n
--   apply Eq.refl
--   intro n
--   exact n



#check WeierstrassCurve.Point.zero.sizeOf_spec -- not elaborated

#check CategoryTheory.Limits.WidePushoutShape.fintypeHom.proof_1
example: ∀ {J : Type u_1} (j' : CategoryTheory.Limits.WidePushoutShape J), j' = none → none = j' := by
  intro J j' h
  aesop_subst h
  simp_all only



#check StructureGroupoid.liftPropWithinAt_univ
example: ∀ {H : Type u_1} {M : Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]
  [inst_1 : TopologicalSpace M] [inst_2 : ChartedSpace H M] [inst_3 : TopologicalSpace H']
  [inst_4 : TopologicalSpace M'] [inst_5 : ChartedSpace H' M'] {P : (H → H') → Set H → H → Prop} {g : M → M'} {x : M},
  ChartedSpace.LiftPropWithinAt P g Set.univ x ↔ ChartedSpace.LiftPropAt P g x := by
  intro H M H' M' inst inst_1 inst_2 inst_3 inst_4 inst_5 P g x
  apply Iff.intro
  · intro a
    exact a
  · intro a
    exact a



#print FirstOrder.Language.Hom.mem_range

#print Polynomial.powSubPowFactor.proof_4

#check MeasurableSet.mem_coe
example: ∀ {α : Type u_1} [inst : MeasurableSpace α] (a : α) (s : Subtype MeasurableSet), a ∈ s ↔ a ∈ s := by
  intro α inst a s
  simp_all only



#check CategoryTheory.MonadHom.app_η
example: ∀ {C : Type u₁} [inst : CategoryTheory.Category C] {T₁ T₂ : CategoryTheory.Monad C}
  (self : CategoryTheory.MonadHom T₁ T₂) (X : C),
  CategoryTheory.CategoryStruct.comp (CategoryTheory.NatTrans.app (CategoryTheory.Monad.η T₁) X)
      (CategoryTheory.NatTrans.app self.toNatTrans X) =
    CategoryTheory.NatTrans.app (CategoryTheory.Monad.η T₂) X := by
  intro C inst T₁ T₂ self X
  simp_all only [CategoryTheory.Functor.id_obj, CategoryTheory.MonadHom.app_η]



#check Set.mem_div -- not elaborated

#check CategoryTheory.biconeCategoryStruct.proof_16
example: ∀ (J : Type u_1) {Z : CategoryTheory.Bicone J} {k : J},
  Z = CategoryTheory.Bicone.diagram k → CategoryTheory.Bicone.diagram k = Z := by
  intro J Z k h
  aesop_subst h
  simp_all only



#print CategoryTheory.Monad.left_unit'

#check NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff
example: ∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : Module R A]
  [inst_3 : Star A] {S₁ S₂ : NonUnitalStarSubalgebra R A}, S₁.toNonUnitalSubalgebra ≤ S₂.toNonUnitalSubalgebra ↔ S₁ ≤ S₂ := by
  intro R A inst inst_1 inst_2 inst_3 S₁ S₂
  apply Iff.intro
  · intro a
    exact a
  · intro a
    exact a



#print AffineIsometry.norm_map

#check IntermediateField.mem_toSubfield
example: ∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (s : IntermediateField K L)
  (x : L), x ∈ IntermediateField.toSubfield s ↔ x ∈ s := by
  intro K L inst inst_1 inst_2 s x
  simp_all only [IntermediateField.mem_toSubfield]



#check CategoryTheory.OplaxFunctor.PseudoCore.mk.sizeOf_spec -- not elaborated

#print WellOrder.wo

#check Bimod.Hom.left_act_hom
example: ∀ {C : Type u₁} [inst : CategoryTheory.Category C] [inst_1 : CategoryTheory.MonoidalCategory C] {A B : Mon_ C}
  {M N : Bimod A B} (self : Bimod.Hom M N),
  CategoryTheory.CategoryStruct.comp M.actLeft self.hom =
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategory.tensorHom (CategoryTheory.CategoryStruct.id A.X) self.hom) N.actLeft := by
  intro C inst inst_1 A B M N self
  simp_all only [Bimod.Hom.left_act_hom]



#check Ideal.mem_pi
example: ∀ {α : Type u} [inst : Semiring α] (I : Ideal α) (ι : Type v) (x : ι → α), x ∈ Ideal.pi I ι ↔ ∀ (i : ι), x i ∈ I := by
  intro α inst I ι x
  apply Iff.intro
  · intro a i
    apply a
  · intro a
    exact a



#print CategoryTheory.GrothendieckTopology.transitive'

#check Subsemiring.mem_inf
example: ∀ {R : Type u} [inst : NonAssocSemiring R] {p p' : Subsemiring R} {x : R}, x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := by
  intro R inst p p' x
  simp_all only [ge_iff_le, Subsemiring.mem_inf]



#print CategoryTheory.ProjectiveResolution.projective

#print IsAddMonoidHom.map_zero

#check Set.preimage_subset_iff
example: ∀ {α : Type u_1} {β : Type u_2} {A : Set α} {B : Set β} {f : α → β}, f ⁻¹' B ⊆ A ↔ ∀ (a : α), f a ∈ B → a ∈ A := by
  intro α β A B f
  apply Iff.intro
  · intro a a_1 a_1_1
    apply a
    simp_all only [Set.mem_preimage]
  · intro a
    exact a



-- #check Fin.mk_le_of_le_val
-- example: ∀ {n : ℕ} {b : Fin n} {a : ℕ} (h : a ≤ ↑b), { val := a, isLt := (_ : a < n) } ≤ b := by
--   intro n b a h
--   exact h



#check CategoryTheory.biconeCategoryStruct.proof_20
example: ∀ (J : Type u_1) {Y : CategoryTheory.Bicone J} (j : J),
  Y = CategoryTheory.Bicone.diagram j → CategoryTheory.Bicone.diagram j = Y := by
  intro J Y j h
  aesop_subst h
  simp_all only



#check Equiv.Perm.VectorsProdEqOne.mem_iff
example: ∀ (G : Type u_1) [inst : Group G] {n : ℕ} (v : Vector G n),
  v ∈ Equiv.Perm.vectorsProdEqOne G n ↔ List.prod (Vector.toList v) = 1 := by
  intro G inst n v
  apply Iff.intro
  · intro a
    exact a
  · intro a
    exact a



#check Multiset.disjoint_left
-- example: ∀ {α : Type u_1} {s t : Multiset α}, Multiset.Disjoint s t ↔ ∀ {a : α}, a ∈ s → ¬a ∈ t := by
--   intro α s t
--   apply Iff.intro
--   · intro a a_1 a_1_1
--     apply Aesop.BuiltinRules.not_intro
--     intro a_2
--     apply a
--     on_goal 2 => exact a_2
--     simp_all only
--   · intro a
--     exact a



#print Urysohns.CU.subset

#check BilinForm.bilin_add_right
example: ∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Module R M]
  (self : BilinForm R M) (x y z : M),
  BilinForm.bilin self x (y + z) = BilinForm.bilin self x y + BilinForm.bilin self x z := by
  intro R M inst inst_1 inst_2 self x y z
  simp_all only [BilinForm.add_right]



#check Subalgebra.mem_carrier
example: ∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {s : Subalgebra R A}
  {x : A}, x ∈ s.carrier ↔ x ∈ s := by
  intro R A inst inst_1 inst_2 s x
  simp_all only [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring, SetLike.mem_coe]



#check CategoryTheory.Limits.WidePullbackShape.struct.proof_9
example: ∀ {J : Type u_1} {Y : CategoryTheory.Limits.WidePullbackShape J}, Y = none → none = Y := by
  intro J Y h
  aesop_subst h
  simp_all only



#check Bornology.isVonNBounded_iff
example: ∀ {𝕜 : Type u_2} {E : Type u_1} [inst : SeminormedRing 𝕜] [inst_1 : SMul 𝕜 E] [inst_2 : Zero E]
  [inst_3 : TopologicalSpace E] (s : Set E), Bornology.IsVonNBounded 𝕜 s ↔ ∀ (V : Set E), V ∈ nhds 0 → Absorbs 𝕜 V s := by
  intro 𝕜 E inst inst_1 inst_2 inst_3 s
  apply Iff.intro
  · intro a V a_1
    apply a
    simp_all only
  · intro a
    exact a



#check CategoryTheory.biconeCategoryStruct.proof_23
example: ∀ (J : Type u_1) {Z : CategoryTheory.Bicone J} {k : J},
  Z = CategoryTheory.Bicone.diagram k → CategoryTheory.Bicone.diagram k = Z := by
  intro J Z k h
  aesop_subst h
  simp_all only



#check Set.mem_vadd_set -- not elaborated

#print CategoryTheory.Limits.MonoFactorisation.m_mono

#print PicardLindelof.FunSpace.lipschitz'

#print AddLocalization.mk_le_mk

#check mem_upperClosure
example: ∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {x : α}, x ∈ upperClosure s ↔ ∃ a, a ∈ s ∧ a ≤ x := by
  intro α inst s x
  simp_all only [mem_upperClosure]



#print Subgroup.IsCommutative.is_comm

#check Game.PGame.lf_iff_game_lf
example: ∀ {x y : PGame}, PGame.Lf x y ↔ Game.Lf (Quotient.mk PGame.setoid x) (Quotient.mk PGame.setoid y) := by
  intro x y
  apply Iff.intro
  · intro a
    exact a
  · intro a
    exact a



#check IsSelfAdjoint.star_eq
example: ∀ {R : Type u_1} [inst : Star R] {x : R}, IsSelfAdjoint x → star x = x := by
  intro R inst x hx
  exact hx



#check Fintype.groupWithZeroOfCancel.proof_2 -- not elaborated

#check NonUnitalSubring.mem_carrier
example: ∀ {R : Type u} [inst : NonUnitalNonAssocRing R] {s : NonUnitalSubring R} {x : R}, x ∈ s.toNonUnitalSubsemiring ↔ x ∈ s := by
  intro R inst s x
  simp_all only [NonUnitalSubring.mem_toNonUnitalSubsemiring]



#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_78
example: ∀ (b q₁ q₂ : Turing.PartrecToTM2.Λ'), b = Turing.PartrecToTM2.Λ'.pred q₁ q₂ → Turing.PartrecToTM2.Λ'.pred q₁ q₂ = b := by
  intro b q₁ q₂ h
  aesop_subst h
  simp_all only



#print CategoryTheory.Adjunction.CoreHomEquiv.homEquiv_naturality_left_symm

#check SubfieldClass.toField.proof_9
example: ∀ {K : Type u_1} [inst : Field K] (S : Type u_2) [inst_1 : SetLike S K] [h : SubfieldClass S K], S → 1 = 1 := by
  intro K inst S inst_1 h s
  simp_all only



#check Subring.mem_toSubsemiring
example: ∀ {R : Type u} [inst : Ring R] {s : Subring R} {x : R}, x ∈ s.toSubsemiring ↔ x ∈ s := by
  intro R inst s x
  simp_all only [Subring.mem_toSubsemiring]



#check LieModule.mem_weightSpace
example: ∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (M : Type w)
  [inst_3 : AddCommGroup M] [inst_4 : Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]
  [inst_7 : LieAlgebra.IsNilpotent R L] (χ : L → R) (m : M),
  m ∈ LieModule.weightSpace M χ ↔ m ∈ LieModule.preWeightSpace M χ := by
  intro R L inst inst_1 inst_2 M inst_3 inst_4 inst_5 inst_6 inst_7 χ m
  apply Iff.intro
  · intro a
    exact a
  · intro a
    exact a



#print AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.RespectsIso

#check GroupTopology.toTopologicalGroup -- not elaborated

#check BoxIntegral.Prepartition.partialOrder.proof_3
example: ∀ {ι : Type u_1} {I : BoxIntegral.Box ι} (a b : BoxIntegral.Prepartition I), a < b ↔ a < b := by
  intro ι I a b
  simp_all only



#print Monotone.restrict

#print MeasurableSpace.measurableSet_empty

#check Sym2.toRel_prop
example: ∀ {α : Type u_1} (s : Set (Sym2 α)) (x y : α), Sym2.ToRel s x y ↔ Quotient.mk (Sym2.Rel.setoid α) (x, y) ∈ s := by
  intro α s x y
  simp_all only [Sym2.toRel_prop]



#check FirstOrder.Language.DefinableSet.mem_sup
example: ∀ {L : FirstOrder.Language} {M : Type w} [inst : FirstOrder.Language.Structure L M] {A : Set M} {α : Type u₁}
  {s t : FirstOrder.Language.DefinableSet L A α} {x : α → M}, x ∈ s ⊔ t ↔ x ∈ s ∨ x ∈ t := by
  intro L M inst A α s t x
  simp_all only [ge_iff_le, FirstOrder.Language.DefinableSet.mem_sup]



#check not_not_intro
example: ∀ {p : Prop}, p → ¬¬p := by
  intro p h
  simp_all only [not_true, not_false_eq_true]



#print MeasureTheory.Filtration.mk.sizeOf_spec

#print IsAddSubgroup.toIsAddSubmonoid

#check Ordnode.balanceR.proof_2
example: ∀ {α : Type u_1} (rl : Ordnode α), rl = Ordnode.nil → Ordnode.nil = rl := by
  intro α rl h
  aesop_subst h
  simp_all only



#print FirstOrder.Language.LHom.mem_substructureReduct

#check OrderAddMonoidHom.monotone' -- not elaborated

#check Bimod.middle_assoc
example: ∀ {C : Type u₁} [inst : CategoryTheory.Category C] [inst_1 : CategoryTheory.MonoidalCategory C] {A B : Mon_ C}
  (self : Bimod A B),
  CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategory.tensorHom self.actLeft (CategoryTheory.CategoryStruct.id B.X)) self.actRight =
    CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategory.associator A.X self.X B.X).hom
      (CategoryTheory.CategoryStruct.comp
        (CategoryTheory.MonoidalCategory.tensorHom (CategoryTheory.CategoryStruct.id A.X) self.actRight) self.actLeft) := by
  intro C inst inst_1 A B self
  simp_all only [Bimod.middle_assoc]



#print StructureGroupoid.id_mem'

#check Submodule.mem_toConvexCone
example: ∀ {𝕜 : Type u_1} {E : Type u_2} [inst : OrderedSemiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : Module 𝕜 E] {x : E}
  {S : Submodule 𝕜 E}, x ∈ Submodule.toConvexCone S ↔ x ∈ S := by
  intro 𝕜 E inst inst_1 inst_2 x S
  simp_all only [Submodule.mem_toConvexCone]



#check Multiset.subset_iff
example: ∀ {α : Type u_1} {s t : Multiset α}, s ⊆ t ↔ ∀ ⦃x : α⦄, x ∈ s → x ∈ t := by
  intro α s t
  apply Iff.intro
  · intro a x a_1
    apply a
    simp_all only
  · intro a
    exact a



#check Submodule.le_div_iff
example: ∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [inst_1 : CommSemiring A] [inst_2 : Algebra R A]
  {I J K : Submodule R A}, I ≤ J / K ↔ ∀ (x : A), x ∈ I → ∀ (z : A), z ∈ K → x * z ∈ J := by
  intro R inst A inst_1 inst_2 I J K
  apply Iff.intro
  · intro a x a_1 z a_2
    apply a
    · simp_all only
    · simp_all only
  · intro a
    exact a



#print Relator.LeftUnique.flip

#check Turing.PointedMap.map_pt'
example: ∀ {Γ : Type u} {Γ' : Type v} [inst : Inhabited Γ] [inst_1 : Inhabited Γ'] (self : Turing.PointedMap Γ Γ'),
  Turing.PointedMap.f self default = default := by
  intro Γ Γ' inst inst_1 self
  simp_all only [Turing.PointedMap.map_pt]



#print Rel.mem_preimage

#print ComplexShape.prev_eq

#print CategoryTheory.MonoidalFunctor.ε_isIso

#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_40
example: ∀ (b : Turing.PartrecToTM2.Λ') (k : Turing.PartrecToTM2.K')
  (s : Option Turing.PartrecToTM2.Γ' → Option Turing.PartrecToTM2.Γ') (q : Turing.PartrecToTM2.Λ'),
  b = Turing.PartrecToTM2.Λ'.push k s q → Turing.PartrecToTM2.Λ'.push k s q = b := by
  intro b k s q h
  aesop_subst h
  simp_all only



#check ProjectiveSpectrum.as_ideal_lt_as_ideal
example: ∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : CommRing A] [inst_2 : Algebra R A]
  (𝒜 : ℕ → Submodule R A) [inst_3 : GradedAlgebra 𝒜] (x y : ProjectiveSpectrum 𝒜),
  x.asHomogeneousIdeal < y.asHomogeneousIdeal ↔ x < y := by
  intro R A inst inst_1 inst_2 𝒜 inst_3 x y
  simp_all only [ProjectiveSpectrum.as_ideal_lt_as_ideal]



#print mem_galBasis_iff

#print MvPolynomial.le_vanishingIdeal_zeroLocus

#check LinearIndependent.restrict_of_comp_subtype
-- example: ∀ {ι : Type u'} {R : Type u_1} {M : Type u_2} {v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoid M]
--   [inst_2 : Module R M] {s : Set ι}, LinearIndependent R (v ∘ Subtype.val) → LinearIndependent R (Set.restrict s v) := by
--   intro ι R M v inst inst_1 inst_2 s hs
--   exact hs



#print Set.nonempty_def

#check ProperCone.mem_coe
example: ∀ {𝕜 : Type u_1} [inst : OrderedSemiring 𝕜] {E : Type u_2} [inst_1 : AddCommMonoid E] [inst_2 : TopologicalSpace E]
  [inst_3 : SMul 𝕜 E] {x : E} {K : ProperCone 𝕜 E}, x ∈ K.toConvexCone ↔ x ∈ K := by
  intro 𝕜 inst E inst_1 inst_2 inst_3 x K
  simp_all only [ProperCone.mem_coe]



#check PGame.uniquePowHalfLeftMoves.proof_1
example: ∀ (n n_1 : ℕ), n = Nat.succ n_1 → Nat.succ n_1 = n := by
  intro n n_1 h
  aesop_subst h
  simp_all only



#print RingNorm.eq_zero_of_map_eq_zero'

#print mem_commutatorSet_iff

#check SModEq.def -- not elaborated

#check IsTorsion.group.proof_5 -- not elaborated

#check CategoryTheory.quotientPathsEquiv.proof_2
example: ∀ (C : Type u_1) [inst : CategoryTheory.Category C] (X : CategoryTheory.Quotient (CategoryTheory.pathsHomRel C)), X = X := by
  intro C inst X
  simp_all only [CategoryTheory.pathsHomRel, CategoryTheory.pathComposition_obj, CategoryTheory.pathComposition_map]



#check CategoryTheory.finBiconeHom.proof_12
example: ∀ (J : Type u_1) (k : CategoryTheory.Bicone J), k = CategoryTheory.Bicone.right → CategoryTheory.Bicone.right = k := by
  intro J k h
  aesop_subst h
  simp_all only



#check Filter.mem_map
example: ∀ {α : Type u} {β : Type v} {f : Filter α} {m : α → β} {t : Set β}, t ∈ Filter.map m f ↔ m ⁻¹' t ∈ f := by
  intro α β f m t
  simp_all only [Filter.mem_map]



#check PosNum.lt_iff_cmp
example: ∀ {m n : PosNum}, m < n ↔ PosNum.cmp m n = Ordering.lt := by
  intro m n
  apply Iff.intro
  · intro a
    exact a
  · intro a
    exact a



#check FirstOrder.Language.DefinableSet.mem_compl
example: ∀ {L : FirstOrder.Language} {M : Type w} [inst : FirstOrder.Language.Structure L M] {A : Set M} {α : Type u₁}
  {s : FirstOrder.Language.DefinableSet L A α} {x : α → M}, x ∈ sᶜ ↔ ¬x ∈ s := by
  intro L M inst A α s x
  simp_all only [FirstOrder.Language.DefinableSet.mem_compl]



#check CategoryTheory.Limits.IsLimit.uniq -- not elaborated

#check SimpleGraph.bot_adj
example: ∀ {V : Type u} (v w : V), SimpleGraph.Adj ⊥ v w ↔ False := by
  intro V v w
  simp_all only [SimpleGraph.bot_adj]



#check unitary.instGroupSubtypeMemSubmonoidToMulOneClassInstMembershipInstSetLikeSubmonoidUnitary.proof_13
example: ∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarSemigroup R] (a b : { x // x ∈ unitary R }), a / b = a / b := by
  intro R inst inst_1 a b
  simp_all only



#check EMetric.mem_ball
example: ∀ {α : Type u} [inst : PseudoEMetricSpace α] {x y : α} {ε : ENNReal}, y ∈ EMetric.ball x ε ↔ edist y x < ε := by
  intro α inst x y ε
  simp_all only [EMetric.mem_ball]



#print AlgebraicGeometry.SheafedSpace.GlueData.f_open

#print StarAlgEquiv.map_smul'

#print IsCHSHTuple.A₀B₁_commutes

#check NonarchAddGroupSeminorm.coe_le_coe
example: ∀ {E : Type u_1} [inst : AddGroup E] {p q : NonarchAddGroupSeminorm E}, p ≤ q ↔ p ≤ q := by
  intro E inst p q
  simp_all only



#print TopologicalSpace.IsTopologicalBasis.sUnion_eq

#check CategoryTheory.MonoidalNatTrans.tensor
example: ∀ {C : Type u₁} [inst : CategoryTheory.Category C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : Type u₂}
  [inst_2 : CategoryTheory.Category D] [inst_3 : CategoryTheory.MonoidalCategory D]
  {F G : CategoryTheory.LaxMonoidalFunctor C D} (self : CategoryTheory.MonoidalNatTrans F G) (X Y : C),
  CategoryTheory.CategoryStruct.comp (CategoryTheory.LaxMonoidalFunctor.μ F X Y)
      (CategoryTheory.NatTrans.app self.toNatTrans (CategoryTheory.MonoidalCategory.tensorObj X Y)) =
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategory.tensorHom (CategoryTheory.NatTrans.app self.toNatTrans X)
        (CategoryTheory.NatTrans.app self.toNatTrans Y))
      (CategoryTheory.LaxMonoidalFunctor.μ G X Y) := by
  intro C inst inst_1 D inst_2 inst_3 F G self X Y
  simp_all only [CategoryTheory.MonoidalNatTrans.tensor]



#check TopCat.Presheaf.stalkCongr.proof_1 -- not elaborated

#print BilinForm.mk.sizeOf_spec

#check Finsupp.mem_supported
example: ∀ {α : Type u_1} {M : Type u_2} (R : Type u_3) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Module R M]
  {s : Set α} (p : α →₀ M), p ∈ Finsupp.supported M R s ↔ ↑p.support ⊆ s := by
  intro α M R inst inst_1 inst_2 s p
  apply Iff.intro
  · intro a
    exact a
  · intro a
    exact a



#print Sylow.isPGroup'

#print MeasurableEmbedding.measurable

#check ge_iff_le
example: ∀ {α : Type u} [inst : LE α] {a b : α}, a ≥ b ↔ b ≤ a := by
  intro α inst a b
  simp_all only [ge_iff_le]



#print NonUnitalStarSubalgebra.star_mem'

#print ValuationSubring.mem_comap

#check UniqueDiffWithinAt.congr_pt
example: ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
  [inst_2 : NormedSpace 𝕜 E] {x y : E} {s : Set E}, UniqueDiffWithinAt 𝕜 s x → x = y → UniqueDiffWithinAt 𝕜 s y := by
  intro 𝕜 inst E inst_1 inst_2 x y s h hy
  aesop_subst hy
  simp_all only



#check Filter.mem_sub -- not elaborated

#check Mon_.Hom.one_hom
example: ∀ {C : Type u₁} [inst : CategoryTheory.Category C] [inst_1 : CategoryTheory.MonoidalCategory C] {M N : Mon_ C}
  (self : Mon_.Hom M N), CategoryTheory.CategoryStruct.comp M.one self.hom = N.one := by
  intro C inst inst_1 M N self
  simp_all only [Mon_.Hom.one_hom]



#print NonUnitalRingHom.mem_range

#check CategoryTheory.Limits.PullbackCone.flipIsLimit.proof_1
example: ∀ {C : Type u_2} [inst : CategoryTheory.Category C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} {h : W ⟶ X} {k : W ⟶ Y}
  {comm : CategoryTheory.CategoryStruct.comp h f = CategoryTheory.CategoryStruct.comp k g},
  CategoryTheory.CategoryStruct.comp k g = CategoryTheory.CategoryStruct.comp h f := by
  intro C inst X Y Z f g W h k comm
  simp_all only



#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_84
example: ∀ (b : Turing.PartrecToTM2.Λ') (p : Turing.PartrecToTM2.Γ' → Bool) (k : Turing.PartrecToTM2.K')
  (q : Turing.PartrecToTM2.Λ'), b = Turing.PartrecToTM2.Λ'.clear p k q → Turing.PartrecToTM2.Λ'.clear p k q = b := by
  intro b p k q h
  aesop_subst h
  simp_all only



#check Filter.Eventually.filter_mono
example: ∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x := by
  intro α f₁ f₂ h p hp
  apply h
  simp_all only
  exact hp



#print Pmf.ofFinset_apply_of_not_mem

#print RelEmbedding.refl.proof_1

#check Monotone.codRestrict
example: ∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β},
  Monotone f → ∀ {s : Set β} (hs : ∀ (x : α), f x ∈ s), Monotone (Set.codRestrict f s hs) := by
  intro α β inst inst_1 f h s hs
  exact h



#check Subring.neg_mem'
example: ∀ {R : Type u} [inst : Ring R] (self : Subring R) {x : R}, x ∈ self.carrier → -x ∈ self.carrier := by
  intro R inst self x a
  simp_all only [Subsemiring.coe_carrier_toSubmonoid, Subring.coe_toSubsemiring, SetLike.mem_coe, neg_mem_iff]



#check EMetric.mem_closedBall
example: ∀ {α : Type u} [inst : PseudoEMetricSpace α] {x y : α} {ε : ENNReal}, y ∈ EMetric.closedBall x ε ↔ edist y x ≤ ε := by
  intro α inst x y ε
  simp_all only [EMetric.mem_closedBall]



#check AddSubgroup.mem_center_iff
example: ∀ {G : Type u_1} [inst : AddGroup G] {z : G}, z ∈ AddSubgroup.center G ↔ ∀ (g : G), g + z = z + g := by
  intro G inst z
  apply Iff.intro
  · intro a g
    apply a
  · intro a
    exact a



#check CategoryTheory.MorphismProperty.epimorphisms.iff
example: ∀ {C : Type u} [inst : CategoryTheory.Category C] {X Y : C} (f : X ⟶ Y),
  CategoryTheory.MorphismProperty.epimorphisms C f ↔ CategoryTheory.Epi f := by
  intro C inst X Y f
  simp_all only [CategoryTheory.MorphismProperty.epimorphisms.iff]



#print IsCHSHTuple.A₁_inv

#print UnionFind.model

#print AddSubsemigroup.add_mem'

#print IsMulHom.map_mul

#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_42
example: ∀ (b : Turing.PartrecToTM2.Λ') (f : Option Turing.PartrecToTM2.Γ' → Turing.PartrecToTM2.Λ'),
  b = Turing.PartrecToTM2.Λ'.read f → Turing.PartrecToTM2.Λ'.read f = b := by
  intro b f h
  aesop_subst h
  simp_all only



#check MeasureTheory.IsFundamentalDomain.nullMeasurableSet -- not elaborated

#check commGroupAddCommGroupEquivalence_functor_obj_str_sub
example: ∀ (X : CommGroupCat) (x y : Additive ↑X), x - y = x - y := by
  intro X x y
  simp_all only [commGroupAddCommGroupEquivalence_functor_obj_str_sub]



#check StarSubalgebra.mem_inf
example: ∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : StarRing R] [inst_2 : Semiring A]
  [inst_3 : Algebra R A] [inst_4 : StarRing A] [inst_5 : StarModule R A] {S T : StarSubalgebra R A} {x : A},
  x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := by
  intro R A inst inst_1 inst_2 inst_3 inst_4 inst_5 S T x
  simp_all only [ge_iff_le, StarSubalgebra.mem_inf]



#print Combinatorics.Line.proper

#print CategoryTheory.Monad.Algebra.unit

#check AddUnits.neg_val
example: ∀ {α : Type u} [inst : AddMonoid α] (self : AddUnits α), self.neg + ↑self = 0 := by
  intro α inst self
  simp_all only [AddUnits.neg_eq_val_neg, AddUnits.neg_add]



#check not_of_iff_false
example: ∀ {a : Prop}, (a ↔ False) → ¬a := by
  intro a a_1
  aesop_subst a_1
  simp_all only



#print Perfect.acc

#check Function.monotone_eval -- not elaborated

#print PFunctor.MIntl.mk.sizeOf_spec

#check GeneralizedBooleanAlgebra.toNonUnitalCommRing.proof_5 -- not elaborated

#check Module.Baer.ExtensionOf.le -- not elaborated

#check CategoryTheory.ThinSkeleton.preorder.proof_4
example: ∀ (C : Type u_2) [inst : CategoryTheory.Category C] (a b : CategoryTheory.ThinSkeleton C), a < b ↔ a < b := by
  intro C inst a b
  simp_all only



#check CategoryTheory.symmetricOfHasFiniteProducts_braiding -- not elaborated

#check UniformSpace.uniformContinuous_quotient
example: ∀ {α : Type u} {β : Type v} [inst : UniformSpace α] [inst_1 : UniformSpace β]
  {f : Quotient (UniformSpace.separationSetoid α) → β},
  (UniformContinuous fun x => f (Quotient.mk (UniformSpace.separationSetoid α) x)) → UniformContinuous f := by
  intro α β inst inst_1 f hf
  exact hf



#print Set.mem_vsub

#check PUnit.addCommGroup.proof_3
example: ∀ (a : PUnit), a + 0 = a + 0 := by
  intro a
  simp_all only [PUnit.zero_eq, PUnit.add_eq]



#print AddGroupSeminorm.add_le'

#check LowerSet.mem_prod
example: ∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] {x : α × β} {s : LowerSet α} {t : LowerSet β},
  x ∈ s ×ˢ t ↔ x.fst ∈ s ∧ x.snd ∈ t := by
  intro α β inst inst_1 x s t
  simp_all only [LowerSet.mem_prod]



#print QuadraticForm.Isometry.map_app'

#print ProperCone.mem_zero

#print MeasureTheory.VectorMeasure.not_measurable'

#print HahnSeries.isPwo_support'

#print FirstOrder.Language.LEquiv.right_inv

#check CategoryTheory.finBiconeHom.proof_19
example: ∀ (J : Type u_1) (k : CategoryTheory.Bicone J), k = CategoryTheory.Bicone.right → CategoryTheory.Bicone.right = k := by
  intro J k h
  aesop_subst h
  simp_all only



#check MeasureTheory.IsAddFundamentalDomain.ae_covers -- not elaborated

#check TopCat.Presheaf.stalkCongr.proof_2 -- not elaborated

#check ProofWidgets.LayoutKind.inline.sizeOf_spec
example: sizeOf ProofWidgets.LayoutKind.inline = 1 := by
simp_all only



#print ConvexBody.convex'

#print Sum.Lex.toLex_le_toLex

#check YoungDiagram.cells_subset_iff
example: ∀ {μ ν : YoungDiagram}, μ.cells ⊆ ν.cells ↔ μ ≤ ν := by
  intro μ ν
  simp_all only [YoungDiagram.cells_subset_iff]



#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_82
example: ∀ (b : Turing.PartrecToTM2.Λ') (p : Turing.PartrecToTM2.Γ' → Bool) (k₁ k₂ : Turing.PartrecToTM2.K')
  (q : Turing.PartrecToTM2.Λ'), b = Turing.PartrecToTM2.Λ'.move p k₁ k₂ q → Turing.PartrecToTM2.Λ'.move p k₁ k₂ q = b := by
  intro b p k₁ k₂ q h
  aesop_subst h
  simp_all only



#check CategoryTheory.finBiconeHom.proof_10
example: ∀ (J : Type u_1) (k : CategoryTheory.Bicone J), k = CategoryTheory.Bicone.left → CategoryTheory.Bicone.left = k := by
  intro J k h
  aesop_subst h
  simp_all only



#check YoungDiagram.isLowerSet -- not elaborated

#check CategoryTheory.SplitEpi.id
example: ∀ {C : Type u₁} [inst : CategoryTheory.Category C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.SplitEpi f),
  CategoryTheory.CategoryStruct.comp self.section_ f = CategoryTheory.CategoryStruct.id Y := by
  intro C inst X Y f self
  simp_all only [CategoryTheory.SplitEpi.id]



#check localCohomology.SelfLERadical.castIsEquivalence.proof_1
example: ∀ {R : Type u_1} [inst : CommRing R] {J K : Ideal R},
  Ideal.radical J = Ideal.radical K → Ideal.radical K = Ideal.radical J := by
  intro R inst J K hJK
  simp_all only



#print RingCon.rel_mk

#check AddSubmonoid.LocalizationMap.eq_iff_exists' -- not elaborated

#print CategoryTheory.Pretopology.mem_toGrothendieck

#check Set.mem_star -- not elaborated

#print OmegaCompletePartialOrder.ContinuousHom.cont

#print PGame.lt_iff_le_and_lf

#print MonoidHom.mem_range

#check isArtinianRing_iff
example: ∀ {R : Type u_1} [inst : Ring R], IsArtinianRing R ↔ IsArtinian R R := by
  intro R inst
  simp_all only



#check Membership.mem.out
example: ∀ {α : Type u} {p : α → Prop} {a : α}, a ∈ {x | p x} → p a := by
  intro α p a h
  simp_all only [Set.mem_setOf_eq]



#print NFA.mem_accepts


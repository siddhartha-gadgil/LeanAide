import Mathlib
#print FirstOrder.Language.Substructure.mem_comap

#check Set.preimage_mono
example: ∀ {α : Type u_1} {β : Type u_2} {f : α → β} {s t : Set β}, s ⊆ t → f ⁻¹' s ⊆ f ⁻¹' t := by
intro α β f s t h intro a a_1 simp_all only [Set.mem_preimage] apply h simp_all only



#check AlgHom.End_toSemigroup_toMul_mul
example: ∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (φ₁ φ₂ : A →ₐ[R] A),
  φ₁ * φ₂ = AlgHom.comp φ₁ φ₂ := by
intro R A inst inst_1 inst_2 φ₁ φ₂ apply Eq.refl



#check MulAction.mem_orbit_iff
example: ∀ {M : Type u} {α : Type v} [inst : Monoid M] [inst_1 : MulAction M α] {a₁ a₂ : α},
  a₂ ∈ MulAction.orbit M a₁ ↔ ∃ x, x • a₁ = a₂ := by
intro M α inst inst_1 a₁ a₂ apply Iff.rfl



#check OptionT.ext
example: ∀ {α : Type u} {m : Type u → Type v} {x x' : OptionT m α}, OptionT.run x = OptionT.run x' → x = x' := by
intro α m x x' h exact h



#check OrderRingIso.refl.proof_1
example: ∀ (α : Type u_1) [inst : Mul α] [inst_1 : Add α] [inst_2 : LE α] {a b : α},
  Equiv.toFun (RingEquiv.refl α).toEquiv a ≤ Equiv.toFun (RingEquiv.refl α).toEquiv b ↔
    Equiv.toFun (RingEquiv.refl α).toEquiv a ≤ Equiv.toFun (RingEquiv.refl α).toEquiv b := by
intro α inst inst_1 inst_2 a b simp_all only
    [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe_apply, RingEquiv.coe_toEquiv, RingEquiv.refl_apply]



#check Mathlib.Explode.Status.cintro.sizeOf_spec
example: sizeOf Mathlib.Explode.Status.cintro = 1 := by
simp_all only



#check UpperSet.mem_inf_iff
example: ∀ {α : Type u_1} [inst : LE α] {s t : UpperSet α} {a : α}, a ∈ s ⊓ t ↔ a ∈ s ∨ a ∈ t := by
intro α inst s t a simp_all only [ge_iff_le, UpperSet.mem_inf_iff]



#check Set.nonempty_def
example: ∀ {α : Type u} {s : Set α}, Set.Nonempty s ↔ ∃ x, x ∈ s := by
intro α s apply Iff.rfl



#check AddSubgroup.quotientEquivOfEq.proof_1 -- not elaborated

#check PUnit.unit.sizeOf_spec
example: sizeOf PUnit.unit = 1 := by
simp_all only [PUnit.unit.sizeOf_spec]



#check LieSubmodule.mem_normalizer
example: ∀ {R : Type u_1} {L : Type u_2} {M : Type u_3} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]
  [inst_3 : AddCommGroup M] [inst_4 : Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]
  (N : LieSubmodule R L M) (m : M), m ∈ LieSubmodule.normalizer N ↔ ∀ (x : L), ⁅x, m⁆ ∈ N := by
intro R L M inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 N m simp_all only [LieSubmodule.mem_normalizer]



#check FirstOrder.Language.Substructure.mem_inf
example: ∀ {L : FirstOrder.Language} {M : Type w} [inst : FirstOrder.Language.Structure L M]
  {p p' : FirstOrder.Language.Substructure L M} {x : M}, x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := by
intro L M inst p p' x simp_all only [ge_iff_le, FirstOrder.Language.Substructure.mem_inf]



#check WithLowerTopology.isOpen_preimage_ofLower -- not elaborated

#check FP.ofPosRatDn.proof_4
example: ∀ [C : FP.FloatCfg] (n d : ℕ+) (d₁ n₁ : ℕ),
  Int.shift2 (↑d) (↑n) (↑(Nat.size ↑n) - ↑(Nat.size ↑d) - ↑FP.prec + ↑FP.prec) = (d₁, n₁) →
    (d₁, n₁) = Int.shift2 (↑d) (↑n) (↑(Nat.size ↑n) - ↑(Nat.size ↑d) - ↑FP.prec + ↑FP.prec) := by
intro C n d d₁ n₁ h simp_all only [sub_add_cancel]



#check Metric.mem_ball
example: ∀ {α : Type u} [inst : PseudoMetricSpace α] {x y : α} {ε : ℝ}, y ∈ Metric.ball x ε ↔ dist y x < ε := by
intro α inst x y ε simp_all only [Metric.mem_ball]



#check Filter.eventuallyEq_bind
example: ∀ {α : Type u} {β : Type v} {γ : Type w} {f : Filter α} {m : α → Filter β} {g₁ g₂ : β → γ},
  g₁ =ᶠ[Filter.bind f m] g₂ ↔ ∀ᶠ (x : α) in f, g₁ =ᶠ[m x] g₂ := by
intro α β γ f m g₁ g₂ simp_all only [Filter.eventuallyEq_bind]



#check CategoryTheory.WithInitial.star.sizeOf_spec -- not elaborated

#check SimpleGraph.fromEdgeSet_adj
example: ∀ {V : Type u} {v w : V} (s : Set (Sym2 V)),
  SimpleGraph.Adj (SimpleGraph.fromEdgeSet s) v w ↔ Quotient.mk (Sym2.Rel.setoid V) (v, w) ∈ s ∧ v ≠ w := by
intro V v w s simp_all only [SimpleGraph.fromEdgeSet_adj, ne_eq]



#check Filter.mem_map
example: ∀ {α : Type u} {β : Type v} {f : Filter α} {m : α → β} {t : Set β}, t ∈ Filter.map m f ↔ m ⁻¹' t ∈ f := by
intro α β f m t simp_all only [Filter.mem_map]



#check isOpen_sum_iff
example: ∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] {s : Set (α ⊕ β)},
  IsOpen s ↔ IsOpen (Sum.inl ⁻¹' s) ∧ IsOpen (Sum.inr ⁻¹' s) := by
intro α β inst inst_1 s apply Iff.rfl



#check CategoryTheory.Limits.WalkingParallelPair.zero.sizeOf_spec
example: sizeOf CategoryTheory.Limits.WalkingParallelPair.zero = 1 := by
simp_all only



#check isMaxOn_dual_iff
example: ∀ {α : Type u} {β : Type v} [inst : Preorder β] {f : α → β} {s : Set α} {a : α},
  IsMaxOn (↑OrderDual.toDual ∘ f) s a ↔ IsMinOn f s a := by
intro α β inst f s a simp_all only apply Iff.rfl



#check Subring.mem_center_iff
example: ∀ {R : Type u} [inst : Ring R] {z : R}, z ∈ Subring.center R ↔ ∀ (g : R), g * z = z * g := by
intro R inst z apply Iff.rfl



#check OpenAddSubgroup.toAddSubgroup_le
example: ∀ {G : Type u_1} [inst : AddGroup G] [inst_1 : TopologicalSpace G] {U V : OpenAddSubgroup G}, U ≤ V ↔ U ≤ V := by
intro G inst inst_1 U V simp_all only



#check ComplexShape.down'_mk
example: ∀ {α : Type u_2} [inst : AddRightCancelSemigroup α] (a i j : α), j + a = i → ComplexShape.Rel (ComplexShape.down' a) i j := by
intro α inst a i j h aesop_subst h simp_all only [ComplexShape.down'_Rel]



#check MvPolynomial.mem_homogeneousSubmodule
example: ∀ {σ : Type u_1} {R : Type u_3} [inst : CommSemiring R] (n : ℕ) (p : MvPolynomial σ R),
  p ∈ MvPolynomial.homogeneousSubmodule σ R n ↔ MvPolynomial.IsHomogeneous p n := by
intro σ R inst n p simp_all only [MvPolynomial.mem_homogeneousSubmodule]



#check CategoryTheory.biconeCategoryStruct.proof_14
example: ∀ (J : Type u_1) {X : CategoryTheory.Bicone J}, X = CategoryTheory.Bicone.left → CategoryTheory.Bicone.left = X := by
intro J X h aesop_subst h simp_all only



#check CategoryTheory.Limits.WidePullbackShape.wideCospan.proof_5
example: ∀ {J : Type u_1} {X : CategoryTheory.Limits.WidePullbackShape J} (j : J), X = some j → some j = X := by
intro J X j h aesop_subst h simp_all only



#check NonUnitalSubalgebra.mem_carrier
example: ∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : Module R A]
  {s : NonUnitalSubalgebra R A} {x : A}, x ∈ s.carrier ↔ x ∈ s := by
intro R A inst inst_1 inst_2 s x simp_all only
    [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, NonUnitalSubsemiring.mem_toAddSubmonoid,
      NonUnitalSubalgebra.mem_toNonUnitalSubsemiring]



#check SetTheory.PGame.fintypeLeftMoves.proof_2
example: ∀ (x : SetTheory.PGame) {α β : Type u_1} {L : α → SetTheory.PGame} {R : β → SetTheory.PGame},
  x = SetTheory.PGame.mk α β L R → SetTheory.PGame.mk α β L R = x := by
intro x α β L R h aesop_subst h simp_all only



#check Bool.linearOrder.proof_3
example: ∀ (a b : Bool), a < b ↔ a < b := by
intro a b simp_all only



#check algebraicIndependent_iff_injective_aeval -- not elaborated

#check Turing.ToPartrec.Code.zero'.sizeOf_spec
example: sizeOf Turing.ToPartrec.Code.zero' = 1 := by
simp_all only



#check CategoryTheory.GrothendieckTopology.instPartialOrderGrothendieckTopology.proof_3
example: ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] (a b : CategoryTheory.GrothendieckTopology C),
  a < b ↔ a < b := by
intro C inst a b simp_all only



#check isLowerSet_preimage_ofDual_iff
example: ∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSet (↑OrderDual.ofDual ⁻¹' s) ↔ IsUpperSet s := by
intro α inst s simp_all only [isLowerSet_preimage_ofDual_iff]



#check ConvexCone.Pointed.mono
example: ∀ {𝕜 : Type u_1} {E : Type u_2} [inst : OrderedSemiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : SMul 𝕜 E]
  {S T : ConvexCone 𝕜 E}, S ≤ T → ConvexCone.Pointed S → ConvexCone.Pointed T := by
intro 𝕜 E inst inst_1 inst_2 S T h a apply h exact a



#check Submodule.mem_carrier
example: ∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst_1 : AddCommMonoid M] {module_M : Module R M} (p : Submodule R M)
  {x : M}, x ∈ p.carrier ↔ x ∈ p := by
intro R M inst inst_1 module_M p x simp_all only
    [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, Submodule.mem_toAddSubmonoid]



#check ZFSet.mk_mem_iff
example: ∀ {x y : PSet}, ZFSet.mk x ∈ ZFSet.mk y ↔ x ∈ y := by
intro x y simp_all only [ZFSet.mk_mem_iff]



#check SimpleGraph.mem_edgeSet
example: ∀ {V : Type u} (G : SimpleGraph V) {v w : V},
  Quotient.mk (Sym2.Rel.setoid V) (v, w) ∈ SimpleGraph.edgeSet G ↔ SimpleGraph.Adj G v w := by
intro V G v w simp_all only [SimpleGraph.mem_edgeSet]



#check PNat.bit0_le_bit0
example: ∀ (n m : ℕ+), bit0 n ≤ bit0 m ↔ bit0 n ≤ bit0 m := by
intro n m simp_all only [PNat.bit0_le_bit0, bit0_le_bit0, PNat.coe_le_coe]



#check Nat.Partrec.Code.zero.sizeOf_spec
example: sizeOf Nat.Partrec.Code.zero = 1 := by
simp_all only



#check Multiset.mem_coe
example: ∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l ↔ a ∈ l := by
intro α a l simp_all only



#print Ideal.mem_comap

#check Zsqrtd.decidableNonnegg.proof_3
example: ∀ (a : ℤ) (a_1 : ℕ), a = Int.ofNat a_1 → Int.ofNat a_1 = a := by
intro a a_1 h aesop_subst h simp_all only [Int.ofNat_eq_coe]



#check Metric.mem_cthickening_iff
example: ∀ {α : Type u} [inst : PseudoEMetricSpace α] {δ : ℝ} {s : Set α} {x : α},
  x ∈ Metric.cthickening δ s ↔ EMetric.infEdist x s ≤ ENNReal.ofReal δ := by
intro α inst δ s x simp_all only [Metric.mem_cthickening_iff]



#check SimpleGraph.hasse_adj
example: ∀ {α : Type u_1} [inst : Preorder α] {a b : α}, SimpleGraph.Adj (SimpleGraph.hasse α) a b ↔ a ⋖ b ∨ b ⋖ a := by
intro α inst a b simp_all only [SimpleGraph.hasse_adj]



#check CategoryTheory.biconeMk.proof_11
example: ∀ (J : Type u_1) {Y : CategoryTheory.Bicone J} (j : J),
  Y = CategoryTheory.Bicone.diagram j → CategoryTheory.Bicone.diagram j = Y := by
intro J Y j h aesop_subst h simp_all only



#check SmoothBumpCovering.isSubordinate_toBumpCovering -- not elaborated

#check SimpleGraph.Subgraph.Adj.coe
example: ∀ {V : Type u} {G : SimpleGraph V} {H : SimpleGraph.Subgraph G} {u v : V} (h : SimpleGraph.Subgraph.Adj H u v),
  SimpleGraph.Adj (SimpleGraph.Subgraph.coe H) { val := u, property := (_ : u ∈ H.verts) }
    { val := v, property := (_ : v ∈ H.verts) } := by
intro V G H u v h simp_all only [SimpleGraph.Subgraph.coe_Adj]



#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_20
example: ∀ (b : Turing.PartrecToTM2.Λ') (p : Turing.PartrecToTM2.Γ' → Bool) (k : Turing.PartrecToTM2.K')
  (q : Turing.PartrecToTM2.Λ'), b = Turing.PartrecToTM2.Λ'.clear p k q → Turing.PartrecToTM2.Λ'.clear p k q = b := by
intro b p k q h aesop_subst h simp_all only



#check Ideal.mem_ofPolynomial
example: ∀ {R : Type u} [inst : Semiring R] {I : Ideal (Polynomial R)} (x : Polynomial R), x ∈ Ideal.ofPolynomial I ↔ x ∈ I := by
intro R inst I x apply Iff.rfl



#print CategoryTheory.EffectiveEpiStruct.mk.sizeOf_spec

#check MvPolynomial.mem_weightedHomogeneousSubmodule
example: ∀ (R : Type u_1) {M : Type u_2} [inst : CommSemiring R] {σ : Type u_3} [inst_1 : AddCommMonoid M] (w : σ → M) (m : M)
  (p : MvPolynomial σ R), p ∈ MvPolynomial.weightedHomogeneousSubmodule R w m ↔ MvPolynomial.IsWeightedHomogeneous w p m := by
intro R M inst σ inst_1 w m p simp_all only [MvPolynomial.mem_weightedHomogeneousSubmodule]



#check CategoryTheory.biconeMk.proof_8
example: ∀ (J : Type u_1) {Y : CategoryTheory.Bicone J} (j : J),
  Y = CategoryTheory.Bicone.diagram j → CategoryTheory.Bicone.diagram j = Y := by
intro J Y j h aesop_subst h simp_all only



#check Filter.Germ.coe_tendsto -- not elaborated

#print Subring.mem_comap

#check CategoryTheory.Sieve.instCompleteLatticeSieve.proof_3
example: ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] {X : C} (a b : CategoryTheory.Sieve X), a < b ↔ a < b := by
intro C inst X a b simp_all only



#print AddSubgroup.mem_comap

#check Nat.lt_of_succ_le
example: ∀ {n m : ℕ}, Nat.succ n ≤ m → n < m := by
intro n m h exact h



#print MultilinearMap.mk.sizeOf_spec

#check CategoryTheory.Limits.WidePullbackShape.wideCospan.proof_7
example: ∀ {J : Type u_1} {Y : CategoryTheory.Limits.WidePullbackShape J}, Y = Y := by
intro J Y simp_all only



#check StarSubalgebra.subtype.proof_1
example: ∀ {R : Type u_2} {A : Type u_1} [inst : CommSemiring R] [inst_1 : StarRing R] [inst_2 : Semiring A]
  [inst_3 : StarRing A] [inst_4 : Algebra R A] [inst_5 : StarModule R A], StarSubalgebra R A → 1 = 1 := by
intro R A inst inst_1 inst_2 inst_3 inst_4 inst_5 S simp_all only



#check Sum.le_def
example: ∀ {α : Type u_1} {β : Type u_2} [inst : LE α] [inst_1 : LE β] {a b : α ⊕ β},
  a ≤ b ↔ Sum.LiftRel (fun x x_1 => x ≤ x_1) (fun x x_1 => x ≤ x_1) a b := by
intro α β inst inst_1 a b apply Iff.rfl



#check MvFunctor.of_mem_supp
example: ∀ {n : ℕ} {F : TypeVec n → Type v} [inst : MvFunctor F] {α : TypeVec n} {x : F α} {P : ⦃i : Fin2 n⦄ → α i → Prop},
  MvFunctor.LiftP P x → ∀ (i : Fin2 n) (y : α i), y ∈ MvFunctor.supp x i → P y := by
intro n F inst α x P h i y a apply a simp_all only



#check ConvexCone.mem_positive
example: ∀ (𝕜 : Type u_1) (E : Type u_2) [inst : OrderedSemiring 𝕜] [inst_1 : OrderedAddCommGroup E] [inst_2 : Module 𝕜 E]
  [inst_3 : OrderedSMul 𝕜 E] {x : E}, x ∈ ConvexCone.positive 𝕜 E ↔ 0 ≤ x := by
intro 𝕜 E inst inst_1 inst_2 inst_3 x simp_all only [ConvexCone.mem_positive]



#check QuotientAddGroup.equivQuotientAddSubgroupOfOfEq.proof_3
example: ∀ {G : Type u_1} [inst : AddGroup G] {A' B' : AddSubgroup G}, A' = B' → B' ≤ A' := by
intro G inst A' B' h' aesop_subst h' simp_all only [le_refl]



#print Matrix.mem_glpos

#check CategoryTheory.Limits.WidePullbackShape.struct.proof_2
example: ∀ {J : Type u_1} {X Y : CategoryTheory.Limits.WidePullbackShape J}, Y = X → X = Y := by
intro J X Y h aesop_subst h simp_all only



#check MeasurableSet.preimage
example: ∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m : MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},
  MeasurableSet t → Measurable f → MeasurableSet (f ⁻¹' t) := by
intro α β f m mβ t ht hf apply hf simp_all only



#print sInfHom.mk.sizeOf_spec

#check ZNum.zero.sizeOf_spec
example: sizeOf ZNum.zero = 1 := by
simp_all only



#print ofBoolRing_inj

#check Subfield.mem_toSubring
example: ∀ {K : Type u} [inst : Field K] (s : Subfield K) (x : K), x ∈ s.toSubring ↔ x ∈ s := by
intro K inst s x simp_all only [Subfield.mem_toSubring]



#check Num.zero.sizeOf_spec
example: sizeOf Num.zero = 1 := by
simp_all only



#print ChartedSpaceCore.mk.sizeOf_spec

#check Set.mem_symmDiff
example: ∀ {α : Type u} {a : α} {s t : Set α}, a ∈ s ∆ t ↔ a ∈ s ∧ ¬a ∈ t ∨ a ∈ t ∧ ¬a ∈ s := by
intro α a s t apply Iff.rfl



#print Nat.ModEq.symm

#check CategoryTheory.biconeMk.proof_6
example: ∀ (J : Type u_1) {X : CategoryTheory.Bicone J}, X = CategoryTheory.Bicone.right → CategoryTheory.Bicone.right = X := by
intro J X h aesop_subst h simp_all only



#check Ordnode.balanceR.proof_7
example: ∀ {α : Type u_1} (rl : Ordnode α) (rls : ℕ) (rll : Ordnode α) (rlx : α) (rlr : Ordnode α),
  id rl = Ordnode.node rls rll rlx rlr → Ordnode.node rls rll rlx rlr = id rl := by
intro α rl rls rll rlx rlr h simp_all only [id_eq]



#print WithTop.toDual_lt_iff

#check MeasureTheory.SimpleFunc.coe_le
example: ∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Preorder β] {f g : MeasureTheory.SimpleFunc α β},
  f ≤ g ↔ f ≤ g := by
intro α β inst inst_1 f g simp_all only



#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_42
example: ∀ (b : Turing.PartrecToTM2.Λ') (f : Option Turing.PartrecToTM2.Γ' → Turing.PartrecToTM2.Λ'),
  b = Turing.PartrecToTM2.Λ'.read f → Turing.PartrecToTM2.Λ'.read f = b := by
intro b f h aesop_subst h simp_all only



#print Order.Ideal.coe_subset_coe

#check ExceptT.ext
example: ∀ {m : Type u_1 → Type u_2} {ε α : Type u_1} [inst : Monad m] {x y : ExceptT ε m α},
  ExceptT.run x = ExceptT.run y → x = y := by
intro m ε α inst x y h exact h



#check NNRat.coe_pos
example: ∀ {q : NNRat}, 0 < q ↔ 0 < q := by
intro q simp_all only



#check CategoryTheory.Limits.WalkingParallelPairHom.right.sizeOf_spec
example: sizeOf CategoryTheory.Limits.WalkingParallelPairHom.right = 1 := by
simp_all only



#check CategoryTheory.biconeCategoryStruct.proof_27
example: ∀ (J : Type u_1) {Y : CategoryTheory.Bicone J} {k : J},
  Y = CategoryTheory.Bicone.diagram k → CategoryTheory.Bicone.diagram k = Y := by
intro J Y k h aesop_subst h simp_all only



#print OrderDual.toDual_lt

#check Multiset.subset_iff
example: ∀ {α : Type u_1} {s t : Multiset α}, s ⊆ t ↔ ∀ ⦃x : α⦄, x ∈ s → x ∈ t := by
intro α s t apply Iff.rfl



#print isBot_ofDual_iff

#check Set.mem_def
example: ∀ {α : Type u} {a : α} {s : Set α}, a ∈ s ↔ s a := by
intro α a s apply Iff.rfl



#check SimpleGraph.isClique_iff
example: ∀ {α : Type u_1} (G : SimpleGraph α) {s : Set α}, SimpleGraph.IsClique G s ↔ Set.Pairwise s G.Adj := by
intro α G s simp_all only



#check Ideal.mem_pi
example: ∀ {α : Type u} [inst : Semiring α] (I : Ideal α) (ι : Type v) (x : ι → α), x ∈ Ideal.pi I ι ↔ ∀ (i : ι), x i ∈ I := by
intro α inst I ι x apply Iff.rfl



#check Fin.le_iff_val_le_val
example: ∀ {n : ℕ} {a b : Fin n}, a ≤ b ↔ a ≤ b := by
intro n a b simp_all only



#check Finsupp.mem_supported
example: ∀ {α : Type u_1} {M : Type u_2} (R : Type u_5) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Module R M]
  {s : Set α} (p : α →₀ M), p ∈ Finsupp.supported M R s ↔ ↑p.support ⊆ s := by
intro α M R inst inst_1 inst_2 s p apply Iff.rfl



#check MeasureTheory.IntegrableOn.integrable -- not elaborated

#check BoxIntegral.Prepartition.partialOrder.proof_3
example: ∀ {ι : Type u_1} {I : BoxIntegral.Box ι} (a b : BoxIntegral.Prepartition I), a < b ↔ a < b := by
intro ι I a b simp_all only



#print Order.Cofinal.mk.sizeOf_spec

#check CategoryTheory.BiconeHom.decidableEq.proof_7
example: ∀ (J : Type u_1) {j : CategoryTheory.Bicone J}, j = CategoryTheory.Bicone.left → CategoryTheory.Bicone.left = j := by
intro J j h aesop_subst h simp_all only



#check CategoryTheory.finBiconeHom.proof_19
example: ∀ (J : Type u_1) (k : CategoryTheory.Bicone J), k = CategoryTheory.Bicone.right → CategoryTheory.Bicone.right = k := by
intro J k h aesop_subst h simp_all only



#check Function.Involutive.leftInverse
example: ∀ {α : Sort u} {f : α → α}, Function.Involutive f → Function.LeftInverse f f := by
intro α f h exact h



#check CategoryTheory.finBiconeHom.proof_2
example: ∀ (J : Type u_1) (k : CategoryTheory.Bicone J), k = CategoryTheory.Bicone.left → CategoryTheory.Bicone.left = k := by
intro J k h aesop_subst h simp_all only



#check CategoryTheory.biconeCategoryStruct.proof_3
example: ∀ (J : Type u_1) {X : CategoryTheory.Bicone J}, X = CategoryTheory.Bicone.left → CategoryTheory.Bicone.left = X := by
intro J X h aesop_subst h simp_all only



#check FirstOrder.Language.DefinableSet.mem_sdiff
example: ∀ {L : FirstOrder.Language} {M : Type w} [inst : FirstOrder.Language.Structure L M] {A : Set M} {α : Type u₁}
  {s t : FirstOrder.Language.DefinableSet L A α} {x : α → M}, x ∈ s \ t ↔ x ∈ s ∧ ¬x ∈ t := by
intro L M inst A α s t x simp_all only [FirstOrder.Language.DefinableSet.mem_sdiff]



#check Equiv.Perm.permGroup.proof_4
example: ∀ {α : Type u_1} (a b : Equiv.Perm α), a / b = a / b := by
intro α a b simp_all only



#print UpperSet.mk.sizeOf_spec

#check Pairwise.set_pairwise
example: ∀ {α : Type u_1} {r : α → α → Prop}, Pairwise r → ∀ (s : Set α), Set.Pairwise s r := by
intro α r h s intro x a y a_1 a_2 simp_all only [ne_eq] apply h simp_all only [ne_eq, not_false_eq_true]



#check isMaxFilter_dual_iff
example: ∀ {α : Type u} {β : Type v} [inst : Preorder β] {f : α → β} {l : Filter α} {a : α},
  IsMaxFilter (↑OrderDual.toDual ∘ f) l a ↔ IsMinFilter f l a := by
intro α β inst f l a simp_all only apply Iff.rfl



#check Relator.LeftUnique.flip
example: ∀ {α : Type u_1} {β : Type u_2} {r : α → β → Prop}, Relator.LeftUnique r → Relator.RightUnique (flip r) := by
sorry -- could not extract proof



#check LinearMap.le_eqLocus -- not elaborated

#check TopologicalSpace.Opens.nonempty_coe -- not elaborated

#check Submodule.instSMulSubtypeMemSubmoduleToSemiringInstMembershipSetLikeTorsion'_smul_coe
example: ∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : Module R M] (S : Type u_3)
  [inst_3 : CommMonoid S] [inst_4 : DistribMulAction S M] [inst_5 : SMulCommClass S R M] (s : S)
  (x : { x // x ∈ Submodule.torsion' R M S }), s • x = s • x := by
intro R M inst inst_1 inst_2 S inst_3 inst_4 inst_5 s x simp_all only



#check Ordnode.balanceR.proof_16
example: ∀ {α : Type u_1} (rl : Ordnode α), id rl = Ordnode.nil → Ordnode.nil = id rl := by
intro α rl h simp_all only [id_eq]



#check Ordinal.mem_brange
example: ∀ {α : Type u_1} {o : Ordinal.{u_4}} {f : (a : Ordinal.{u_4}) → a < o → α} {a : α},
  a ∈ Ordinal.brange o f ↔ ∃ i hi, f i hi = a := by
intro α o f a apply Iff.rfl



#check LinearMap.isOrthoᵢ_def -- not elaborated

#print Commute.symm

#check QuotientAddGroup.equivQuotientAddSubgroupOfOfEq.proof_4
example: ∀ {G : Type u_1} [inst : AddGroup G] {A B : AddSubgroup G}, A = B → B ≤ A := by
intro G inst A B h aesop_subst h simp_all only [le_refl]



#check NonemptyInterval.mem_def
example: ∀ {α : Type u_1} [inst : Preorder α] {s : NonemptyInterval α} {a : α}, a ∈ s ↔ s.fst ≤ a ∧ a ≤ s.snd := by
intro α inst s a apply Iff.rfl



#print NonUnitalRingHom.mem_range

#check supClosed_preimage_toDual
example: ∀ {α : Type u_1} [inst : Lattice α] {s : Set αᵒᵈ}, SupClosed (↑OrderDual.toDual ⁻¹' s) ↔ InfClosed s := by
intro α inst s simp_all only [supClosed_preimage_toDual]



#check CategoryTheory.Limits.WidePushoutShape.struct.proof_10
example: ∀ {J : Type u_1} {X : CategoryTheory.Limits.WidePushoutShape J}, X = none → none = X := by
intro J X h aesop_subst h simp_all only



#check CategoryTheory.regularOfIsPushoutFstOfRegular.proof_1
example: ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S}
  {k : R ⟶ S},
  CategoryTheory.CategoryStruct.comp f h = CategoryTheory.CategoryStruct.comp g k →
    CategoryTheory.CategoryStruct.comp g k = CategoryTheory.CategoryStruct.comp f h := by
intro C inst P Q R S f g h k comm simp_all only



#print OrderEmbedding.subtype.proof_1

#print PEquiv.mk.sizeOf_spec

#check NonUnitalStarSubalgebra.iSupLift.proof_9
example: ∀ {R : Type u_2} {A : Type u_1} [inst : CommSemiring R] [inst_1 : StarRing R] [inst_2 : NonUnitalSemiring A]
  [inst_3 : StarRing A] [inst_4 : Module R A] [inst_5 : IsScalarTower R A A] [inst_6 : SMulCommClass R A A]
  [inst_7 : StarModule R A] {ι : Type u_3} (K : ι → NonUnitalStarSubalgebra R A) (T : NonUnitalStarSubalgebra R A),
  T = iSup K → iSup K = T := by
intro R A inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 ι K T hT aesop_subst hT simp_all only



#check Hyperreal.infiniteNeg_def
example: ∀ {x : ℝ*}, Hyperreal.InfiniteNeg x ↔ ∀ (r : ℝ), x < ↑r := by
intro x apply Iff.rfl



#check CategoryTheory.MorphismProperty.epimorphisms.iff
example: ∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y),
  CategoryTheory.MorphismProperty.epimorphisms C f ↔ CategoryTheory.Epi f := by
intro C inst X Y f simp_all only [CategoryTheory.MorphismProperty.epimorphisms.iff]



#check QuotientAddGroup.circularPreorder.proof_3
example: ∀ {α : Type u_1} [inst : LinearOrderedAddCommGroup α] [hα : Archimedean α] {p : α} [hp' : Fact (0 < p)]
  {a b c : α ⧸ AddSubgroup.zmultiples p}, sbtw a b c ↔ sbtw a b c := by
intro α inst hα p hp' a b c simp_all only



#check Ultrafilter.eventually_add -- not elaborated

#check UpperSet.mem_Ici_iff
example: ∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ∈ UpperSet.Ici a ↔ a ≤ b := by
intro α inst a b simp_all only [UpperSet.mem_Ici_iff]



#print ShrinkingLemma.PartialRefinement.mk.sizeOf_spec

#check Function.Semiconj.eq
example: ∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α} {gb : β → β},
  Function.Semiconj f ga gb → ∀ (x : α), f (ga x) = gb (f x) := by
intro α β f ga gb h x apply h



#check CategoryTheory.OplaxNatTrans.Modification.mk.sizeOf_spec -- not elaborated

#check Subfield.mem_inf
example: ∀ {K : Type u} [inst : Field K] {p p' : Subfield K} {x : K}, x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := by
intro K inst p p' x simp_all only [ge_iff_le, Subfield.mem_inf]



#check CategoryTheory.Bicone.left.sizeOf_spec -- not elaborated

#print infIrred_toDual

#check MulAction.sigmaFixedByEquivOrbitsProdGroup.proof_1
example: ∀ (α : Type u_1) (β : Type u_2) [inst : Group α] [inst_1 : MulAction α β] (x : α × β),
  x.fst • x.snd = x.snd ↔ x.fst • x.snd = x.snd := by
intro α β inst inst_1 x simp_all only



#check CategoryTheory.discreteCategory.proof_7
example: ∀ (α : Type u_1) {Z : CategoryTheory.Discrete α}, Z = Z := by
intro α Z simp_all only



#check SimpleGraph.Subgraph.top_adj
example: ∀ {V : Type u} {G : SimpleGraph V} {a b : V}, SimpleGraph.Subgraph.Adj ⊤ a b ↔ SimpleGraph.Adj G a b := by
sorry -- could not extract proof



#check Set.mem_Icc
example: ∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b := by
intro α inst a b x simp_all only [ge_iff_le, gt_iff_lt, Set.mem_Icc]



#check Submonoid.mem_inf
example: ∀ {M : Type u_1} [inst : MulOneClass M] {p p' : Submonoid M} {x : M}, x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := by
intro M inst p p' x simp_all only [ge_iff_le, Submonoid.mem_inf]



#check Sym2.toRel_prop
example: ∀ {α : Type u_1} (s : Set (Sym2 α)) (x y : α), Sym2.ToRel s x y ↔ Quotient.mk (Sym2.Rel.setoid α) (x, y) ∈ s := by
intro α s x y simp_all only [Sym2.toRel_prop]



#check CategoryTheory.finBiconeHom.proof_22
example: ∀ (J : Type u_1) (j : CategoryTheory.Bicone J) (val : J),
  j = CategoryTheory.Bicone.diagram val → CategoryTheory.Bicone.diagram val = j := by
intro J j val h aesop_subst h simp_all only



#check SetTheory.Game.PGame.le_iff_game_le
example: ∀ {x y : SetTheory.PGame}, x ≤ y ↔ Quotient.mk SetTheory.PGame.setoid x ≤ Quotient.mk SetTheory.PGame.setoid y := by
intro x y apply Iff.rfl



#check CategoryTheory.Sieve.inter_apply -- not elaborated

#check Ne.elim
example: ∀ {α : Sort u} {a b : α}, a ≠ b → a = b → False := by
intro α a b h a_1 aesop_subst a_1 simp_all only [ne_eq, not_true]



#check LowerSet.mem_Iio_iff
example: ∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ∈ LowerSet.Iio a ↔ b < a := by
intro α inst a b simp_all only [LowerSet.mem_Iio_iff]



#print WithTop.ofDual_lt_iff

#print MvPolynomial.mem_zeroLocus_iff

#check mem_nonZeroDivisors_iff
example: ∀ {M : Type u_1} [inst : MonoidWithZero M] {r : M}, r ∈ nonZeroDivisors M ↔ ∀ (x : M), x * r = 0 → x = 0 := by
intro M inst r apply Iff.rfl



#print AddSubgroup.mem_mk

#check OpenSubgroup.mem_toSubgroup
example: ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G] {U : OpenSubgroup G} {g : G}, g ∈ U ↔ g ∈ U := by
intro G inst inst_1 U g simp_all only



#check SubfieldClass.toField.proof_13
example: ∀ {K : Type u_1} [inst : Field K] (S : Type u_2) [inst_1 : SetLike S K] [h : SubfieldClass S K] (s : S)
  (x y : { x // x ∈ s }), x - y = x - y := by
intro K inst S inst_1 h s x y simp_all only



#print DFinsupp.instDecidableEqLexDFinsupp.proof_1

#check ValuationRing.instLinearOrderValueGroup.proof_3 -- not elaborated

#print Gamma1_mem'

#print contMDiffWithinAt_iff

#check Mathlib.Notation3.BoundValueType.foldr.sizeOf_spec
example: sizeOf Mathlib.Notation3.BoundValueType.foldr = 1 := by
simp_all only



#print FirstOrder.Language.Substructure.mk.sizeOf_spec

#check Turing.PartrecToTM2.K'.main.sizeOf_spec
example: sizeOf Turing.PartrecToTM2.K'.main = 1 := by
simp_all only



#print Ideal.Filtration.mem_submodule

#check measurableSet_quotient
example: ∀ {α : Type u_1} [inst : MeasurableSpace α] {s : Setoid α} {t : Set (Quotient s)},
  MeasurableSet t ↔ MeasurableSet (Quotient.mk'' ⁻¹' t) := by
intro α inst s t apply Iff.rfl



#check CategoryTheory.Limits.WidePushoutShape.fintypeHom.proof_6
example: ∀ {J : Type u_1} (j : CategoryTheory.Limits.WidePushoutShape J) (j_1 : J), j = some j_1 → some j_1 = j := by
intro J j j_1 h aesop_subst h simp_all only



#check AddSemiconjBy.eq
example: ∀ {S : Type u_1} [inst : Add S] {a x y : S}, AddSemiconjBy a x y → a + x = y + a := by
intro S inst a x y h exact h



#check ContMDiff.contMDiffAt
example: ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
  [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}
  [inst_4 : TopologicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCommGroup E']
  [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type u_7} [inst_9 : TopologicalSpace M'] [inst_10 : ChartedSpace H' M'] {f : M → M'} {x : M} {n : ℕ∞},
  ContMDiff I I' n f → ContMDiffAt I I' n f x := by
intro 𝕜 inst E inst_1 inst_2 H inst_3 I M inst_4 inst_5 E' inst_6 inst_7 H' inst_8 I' M' inst_9 inst_10 f x n h apply h



#check Computability.Γ'.comma.sizeOf_spec
example: sizeOf Computability.Γ'.comma = 1 := by
simp_all only



#check FirstOrder.Language.ElementarilyEquivalent.completeTheory_eq
example: ∀ {L : FirstOrder.Language} {M : Type w} {N : Type u_1} [inst : FirstOrder.Language.Structure L M]
  [inst_1 : FirstOrder.Language.Structure L N],
  FirstOrder.Language.ElementarilyEquivalent L M N →
    FirstOrder.Language.completeTheory L M = FirstOrder.Language.completeTheory L N := by
intro L M N inst inst_1 h exact h



#check ZFSet.IsTransitive.subset_of_mem
example: ∀ {x y : ZFSet}, ZFSet.IsTransitive x → y ∈ x → y ⊆ x := by
intro x y h a apply h simp_all only



#print Polynomial.separable_def'

#check Set.mem_powerset_iff
example: ∀ {α : Type u} (x s : Set α), x ∈ 𝒫 s ↔ x ⊆ s := by
intro α x s simp_all only [Set.mem_powerset_iff]



#check Nat.ArithmeticFunction.instAddGroupArithmeticFunctionToZeroToNegZeroClassToSubNegZeroMonoidToSubtractionMonoid.proof_14
example: ∀ {R : Type u_1} [inst : AddGroup R] (a b : Nat.ArithmeticFunction R), a - b = a - b := by
intro R inst a b simp_all only



#check Complex.le_def -- not elaborated

#check Turing.TM2.Stmt.goto.sizeOf_spec -- not elaborated

#check NonarchAddGroupSeminorm.le_def
example: ∀ {E : Type u_4} [inst : AddGroup E] {p q : NonarchAddGroupSeminorm E}, p ≤ q ↔ p ≤ q := by
intro E inst p q simp_all only



#print Subsemiring.mem_comap

#check GroupNorm.coe_lt_coe
example: ∀ {E : Type u_4} [inst : Group E] {p q : GroupNorm E}, p < q ↔ p < q := by
intro E inst p q simp_all only



#check AddUnits.instAddGroupAddUnits.proof_7
example: ∀ {α : Type u_1} [inst : AddMonoid α] (a b : AddUnits α), a - b = a - b := by
intro α inst a b simp_all only



#check List.foldrRecOn.proof_2
example: ∀ {α : Type u_1} (l : List α) (head : α) (tail : List α), l = head :: tail → head :: tail = l := by
intro α l head tail h aesop_subst h simp_all only



#check Turing.Dir.left.sizeOf_spec
example: sizeOf Turing.Dir.left = 1 := by
simp_all only



#print MeasureTheory.mem_ae_iff

#check isArtinianRing_iff
example: ∀ {R : Type u_1} [inst : Ring R], IsArtinianRing R ↔ IsArtinian R R := by
intro R inst simp_all only



#print Finsupp.le_def

#check UniformSpace.uniformContinuous_quotient
example: ∀ {α : Type u} {β : Type v} [inst : UniformSpace α] [inst_1 : UniformSpace β]
  {f : Quotient (UniformSpace.separationSetoid α) → β},
  (UniformContinuous fun x => f (Quotient.mk (UniformSpace.separationSetoid α) x)) → UniformContinuous f := by
intro α β inst inst_1 f hf exact hf



#check Commute.eq
example: ∀ {S : Type u_2} [inst : Mul S] {a b : S}, Commute a b → a * b = b * a := by
intro S inst a b h exact h



#print Pmf.ofFinset_apply_of_not_mem

#check CategoryTheory.MonoidalOpposite.unop_inj_iff
example: ∀ {C : Type u₁} (x y : Cᴹᵒᵖ), CategoryTheory.MonoidalOpposite.unmop x = CategoryTheory.MonoidalOpposite.unmop y ↔ x = y := by
intro C x y simp_all only [CategoryTheory.MonoidalOpposite.unop_inj_iff]



#check Set.mem_addAntidiagonal
example: ∀ {α : Type u_1} [inst : Add α] {s t : Set α} {a : α} {x : α × α},
  x ∈ Set.addAntidiagonal s t a ↔ x.fst ∈ s ∧ x.snd ∈ t ∧ x.fst + x.snd = a := by
intro α inst s t a x simp_all only [Set.mem_addAntidiagonal]



#check Complex.lt_def -- not elaborated

#check BoxIntegral.Prepartition.mem_boxes
example: ∀ {ι : Type u_1} {I J : BoxIntegral.Box ι} (π : BoxIntegral.Prepartition I), J ∈ π.boxes ↔ J ∈ π := by
intro ι I J π simp_all only [BoxIntegral.Prepartition.mem_boxes]



#check WithUpperSetTopology.IsUpperSet_toUpperSet_preimage
example: ∀ {α : Type u_1} [inst : Preorder α] {s : Set (WithUpperSetTopology α)},
  IsUpperSet (↑WithUpperSetTopology.toUpperSet ⁻¹' s) ↔ IsOpen s := by
intro α inst s simp_all only [WithUpperSetTopology.IsUpperSet_toUpperSet_preimage]



#check SimpleGraph.fromRel_adj
example: ∀ {V : Type u} (r : V → V → Prop) (v w : V), SimpleGraph.Adj (SimpleGraph.fromRel r) v w ↔ v ≠ w ∧ (r v w ∨ r w v) := by
intro V r v w simp_all only [SimpleGraph.fromRel_adj, ne_eq]



#print AlgHom.mem_equalizer

#print isPrimePow_def

#check CategoryTheory.Limits.WidePullbackShape.struct.proof_6
example: ∀ {J : Type u_1} {Z : CategoryTheory.Limits.WidePullbackShape J}, Z = Z := by
intro J Z simp_all only



#check CategoryTheory.Limits.WalkingPair.right.sizeOf_spec
example: sizeOf CategoryTheory.Limits.WalkingPair.right = 1 := by
simp_all only



#check ContMDiffAt.smoothAt
example: ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
  [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}
  [inst_4 : TopologicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCommGroup E']
  [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type u_7} [inst_9 : TopologicalSpace M'] [inst_10 : ChartedSpace H' M'] {f : M → M'} {x : M},
  ContMDiffAt I I' ⊤ f x → SmoothAt I I' f x := by
intro 𝕜 inst E inst_1 inst_2 H inst_3 I M inst_4 inst_5 E' inst_6 inst_7 H' inst_8 I' M' inst_9 inst_10 f x h simp_all
    only



#check CommRingCat.punitIsTerminal.proof_4 -- not elaborated

#check CategoryTheory.biconeMk.proof_2
example: ∀ (J : Type u_1) {Y : CategoryTheory.Bicone J}, Y = CategoryTheory.Bicone.left → CategoryTheory.Bicone.left = Y := by
intro J Y h aesop_subst h simp_all only



#check NonUnitalStarSubalgebra.mem_carrier
example: ∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : NonUnitalNonAssocSemiring A] [inst_2 : Module R A]
  [inst_3 : Star A] {s : NonUnitalStarSubalgebra R A} {x : A}, x ∈ s.carrier ↔ x ∈ s := by
intro R A inst inst_1 inst_2 inst_3 s x simp_all only
    [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, NonUnitalSubsemiring.mem_toAddSubmonoid,
      NonUnitalSubalgebra.mem_toNonUnitalSubsemiring, NonUnitalStarSubalgebra.mem_toNonUnitalSubalgebra]



#check Ordnode.balanceL.proof_22
example: ∀ {α : Type u_1} (r : Ordnode α) (rs : ℕ) (l : Ordnode α) (x : α) (r_1 : Ordnode α),
  id r = Ordnode.node rs l x r_1 → Ordnode.node rs l x r_1 = id r := by
intro α r rs l x r_1 h simp_all only [id_eq]



#check Function.mem_periodicPts
example: ∀ {α : Type u_1} {f : α → α} {x : α}, x ∈ Function.periodicPts f ↔ ∃ n, n > 0 ∧ Function.IsPeriodicPt f n x := by
intro α f x simp_all only [gt_iff_lt] apply Iff.rfl



#check CategoryTheory.Coverage.ofGrothendieck_iff
example: ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] {X : C} {S : CategoryTheory.Presieve X}
  (J : CategoryTheory.GrothendieckTopology C),
  S ∈ CategoryTheory.Coverage.covering (CategoryTheory.Coverage.ofGrothendieck C J) X ↔
    CategoryTheory.Sieve.generate S ∈ CategoryTheory.GrothendieckTopology.sieves J X := by
intro C inst X S J apply Iff.rfl



#check Filter.IsBasis.mem_filterBasis_iff
example: ∀ {α : Type u_1} {ι : Sort u_4} {p : ι → Prop} {s : ι → Set α} (h : Filter.IsBasis p s) {U : Set α},
  U ∈ Filter.IsBasis.filterBasis h ↔ ∃ i, p i ∧ s i = U := by
intro α ι p s h U apply Iff.rfl



#check Set.mem_insert_iff
example: ∀ {α : Type u} {x a : α} {s : Set α}, x ∈ insert a s ↔ x = a ∨ x ∈ s := by
intro α x a s simp_all only [Set.mem_insert_iff]



#check SimpleGraph.compl_adj
example: ∀ {V : Type u} (G : SimpleGraph V) (v w : V), SimpleGraph.Adj Gᶜ v w ↔ v ≠ w ∧ ¬SimpleGraph.Adj G v w := by
intro V G v w simp_all only [SimpleGraph.compl_adj, ne_eq]



#check BoxIntegral.TaggedPrepartition.mem_toPrepartition
example: ∀ {ι : Type u_1} {I J : BoxIntegral.Box ι} {π : BoxIntegral.TaggedPrepartition I}, J ∈ π.toPrepartition ↔ J ∈ π := by
intro ι I J π simp_all only [BoxIntegral.TaggedPrepartition.mem_toPrepartition]



#check CategoryTheory.Sieve.union_apply -- not elaborated

#check List.subset_def
example: ∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ ⊆ l₂ ↔ ∀ {a : α}, a ∈ l₁ → a ∈ l₂ := by
intro α l₁ l₂ apply Iff.rfl



#print AddFreimanHom.mk.sizeOf_spec

#print GaloisCoinsertion.mk.sizeOf_spec

#check CategoryTheory.Limits.WidePushoutShape.fintypeHom.proof_7
example: ∀ {J : Type u_1} (j : CategoryTheory.Limits.WidePushoutShape J), j = j := by
intro J j simp_all only



#print Subring.mk_le_mk

#check Convex.starConvex
example: ∀ {𝕜 : Type u_1} {E : Type u_2} [inst : OrderedSemiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : SMul 𝕜 E] {s : Set E}
  {x : E}, Convex 𝕜 s → x ∈ s → StarConvex 𝕜 x s := by
intro 𝕜 E inst inst_1 inst_2 s x hs hx apply hs simp_all only



#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_52
example: ∀ (b : Turing.PartrecToTM2.Λ') (p : Turing.PartrecToTM2.Γ' → Bool) (k : Turing.PartrecToTM2.K')
  (q : Turing.PartrecToTM2.Λ'), b = Turing.PartrecToTM2.Λ'.clear p k q → Turing.PartrecToTM2.Λ'.clear p k q = b := by
intro b p k q h aesop_subst h simp_all only



#check Hyperreal.InfiniteNeg.lt_zero
example: ∀ {x : ℝ*}, Hyperreal.InfiniteNeg x → x < 0 := by
intro x a apply a



#check Set.mapsTo_sInter
example: ∀ {α : Type u_1} {β : Type u_2} {s : Set α} {T : Set (Set β)} {f : α → β},
  (∀ (t : Set β), t ∈ T → Set.MapsTo f s t) → Set.MapsTo f s (⋂₀ T) := by
intro α β s T f H intro x a t a_1 apply H · simp_all only · simp_all only



#print PEquiv.le_def

#check CategoryTheory.finBiconeHom.proof_12
example: ∀ (J : Type u_1) (k : CategoryTheory.Bicone J), k = CategoryTheory.Bicone.right → CategoryTheory.Bicone.right = k := by
intro J k h aesop_subst h simp_all only



#check FirstOrder.Language.DefinableSet.mem_inf
example: ∀ {L : FirstOrder.Language} {M : Type w} [inst : FirstOrder.Language.Structure L M] {A : Set M} {α : Type u₁}
  {s t : FirstOrder.Language.DefinableSet L A α} {x : α → M}, x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := by
intro L M inst A α s t x simp_all only [ge_iff_le, FirstOrder.Language.DefinableSet.mem_inf]



#check FirstOrder.Language.BoundedFormula.realize_bdEqual
example: ∀ {L : FirstOrder.Language} {M : Type w} [inst : FirstOrder.Language.Structure L M] {α : Type u'} {l : ℕ} {v : α → M}
  {xs : Fin l → M} (t₁ t₂ : FirstOrder.Language.Term L (α ⊕ Fin l)),
  FirstOrder.Language.BoundedFormula.Realize (FirstOrder.Language.Term.bdEqual t₁ t₂) v xs ↔
    FirstOrder.Language.Term.realize (Sum.elim v xs) t₁ = FirstOrder.Language.Term.realize (Sum.elim v xs) t₂ := by
intro L M inst α l v xs t₁ t₂ simp_all only [FirstOrder.Language.BoundedFormula.realize_bdEqual]



#check EReal.instSubNegZeroMonoidEReal.proof_1
example: ∀ (a b : EReal), a - b = a - b := by
intro a b simp_all only



#check NonUnitalSubring.mem_toSubsemigroup
example: ∀ {R : Type u} [inst : NonUnitalNonAssocRing R] {s : NonUnitalSubring R} {x : R},
  x ∈ NonUnitalSubring.toSubsemigroup s ↔ x ∈ s := by
intro R inst s x simp_all only [NonUnitalSubring.mem_toSubsemigroup]



#check NonUnitalSubalgebra.star_mono -- not elaborated

#check Set.mem_preimage
example: ∀ {α : Type u_1} {β : Type u_2} {f : α → β} {s : Set β} {a : α}, a ∈ f ⁻¹' s ↔ f a ∈ s := by
intro α β f s a simp_all only [Set.mem_preimage]



#check AddGroupSeminorm.coe_lt_coe
example: ∀ {E : Type u_4} [inst : AddGroup E] {p q : AddGroupSeminorm E}, p < q ↔ p < q := by
intro E inst p q simp_all only



#check CategoryTheory.Limits.WidePushoutShape.struct.proof_4
example: ∀ {J : Type u_1} {Z : CategoryTheory.Limits.WidePushoutShape J} (j : J), Z = some j → some j = Z := by
intro J Z j h aesop_subst h simp_all only



#check RingAut.instGroupRingAut.proof_1
example: ∀ (R : Type u_1) [inst : Mul R] [inst_1 : Add R] (a b c : RingAut R), a * b * c = a * b * c := by
intro R inst inst_1 a b c simp_all only



#check NonUnitalSubalgebra.mem_star_iff
example: ∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : StarRing R] [inst_2 : NonUnitalSemiring A]
  [inst_3 : StarRing A] [inst_4 : Module R A] [inst_5 : StarModule R A] (S : NonUnitalSubalgebra R A) (x : A),
  x ∈ star S ↔ star x ∈ S := by
intro R A inst inst_1 inst_2 inst_3 inst_4 inst_5 S x simp_all only [NonUnitalSubalgebra.mem_star_iff]



#check Computable₂.partrec₂ -- not elaborated

#check CategoryTheory.MorphismProperty.diagonal_iff
example: ∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasPullbacks C]
  {P : CategoryTheory.MorphismProperty C} {X Y : C} {f : X ⟶ Y},
  CategoryTheory.MorphismProperty.diagonal P f ↔ P (CategoryTheory.Limits.pullback.diagonal f) := by
intro C inst inst_1 P X Y f apply Iff.rfl



#print CauSeq.addGroupWithOne.proof_7

#print AffineSubspace.mem_perpBisector_iff_inner_eq_zero'

#check Int.le_def
example: ∀ (a b : ℤ), a ≤ b ↔ Int.NonNeg (b - a) := by
intro a b apply Iff.rfl



#check Iff.mp
example: ∀ {a b : Prop}, (a ↔ b) → a → b := by
intro a b self a_1 aesop_subst self simp_all only



#check Rel.mem_preimage
example: ∀ {α : Type u_1} {β : Type u_2} (r : Rel α β) (x : α) (s : Set β), x ∈ Rel.preimage r s ↔ ∃ y, y ∈ s ∧ r x y := by
intro α β r x s apply Iff.rfl



#check LinearMap.mem_selfAdjointSubmodule
example: ∀ {R : Type u_1} {M : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : Module R M]
  {B : M →ₗ[R] M →ₗ[R] R} (f : Module.End R M), f ∈ LinearMap.selfAdjointSubmodule B ↔ LinearMap.IsSelfAdjoint B f := by
intro R M inst inst_1 inst_2 B f simp_all only [LinearMap.mem_selfAdjointSubmodule]



#check UniformSpace.Completion.instField.proof_8 -- not elaborated

#check BoxIntegral.HasIntegral.tendsto
example: ∀ {ι : Type u} {E : Type v} {F : Type w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
  [inst_2 : NormedAddCommGroup F] [inst_3 : NormedSpace ℝ F] {I : BoxIntegral.Box ι} [inst_4 : Fintype ι]
  {l : BoxIntegral.IntegrationParams} {f : (ι → ℝ) → E} {vol : BoxIntegral.BoxAdditiveMap ι (E →L[ℝ] F) ⊤} {y : F},
  BoxIntegral.HasIntegral I l f vol y →
    Filter.Tendsto (BoxIntegral.integralSum f vol) (BoxIntegral.IntegrationParams.toFilteriUnion l I ⊤) (nhds y) := by
intro ι E F inst inst_1 inst_2 inst_3 I inst_4 l f vol y h exact h



#check ConjClasses.mem_noncenter
example: ∀ {G : Type u_1} [inst : Monoid G] (g : ConjClasses G),
  g ∈ ConjClasses.noncenter G ↔ Set.Nontrivial (ConjClasses.carrier g) := by
intro G inst g simp_all only [ConjClasses.mem_noncenter]



#check mem_idRel -- not elaborated

#print Submonoid.mem_mk

#print Gamma0_mem

#check Int.add_one_le_of_lt
example: ∀ {a b : ℤ}, a < b → a + 1 ≤ b := by
intro a b H exact H



#print OrderDual.le_toDual

#print WithBot.toDual_le_toDual_iff

#check CategoryTheory.Limits.WidePushoutShape.fintypeHom.proof_1
example: ∀ {J : Type u_1} (j' : CategoryTheory.Limits.WidePushoutShape J), j' = none → none = j' := by
intro J j' h aesop_subst h simp_all only



#print SymAlg.mul_def

#check Lists'.nil.sizeOf_spec -- not elaborated


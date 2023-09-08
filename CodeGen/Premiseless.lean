import Mathlib
#check uniformContinuous_def -- not elaborated

#check OrderIso.IicTop.proof_4 -- not elaborated

#print ONote.fundamentalSequenceProp_inl_none

#print BoolRingCat.instParentProjectionTypeCommRingBooleanRingToCommRing.proof_1

#check strictMonoOn_toDual_comp_iff
example: ∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β} {s : Set α},
  StrictMonoOn (↑OrderDual.toDual ∘ f) s ↔ StrictAntiOn f s := by
intro α β inst inst_1 f s 
simp_all only [strictMonoOn_toDual_comp_iff]



#check SubfieldClass.toField.proof_20
example: ∀ {K : Type u_1} [inst : Field K] (S : Type u_2) [inst_1 : SetLike S K] [h : SubfieldClass S K] (s : S)
  (x : { x // x ∈ s }) (n : ℤ), x ^ n = x ^ n := by
intro K inst S inst_1 h s x n 
simp_all only



#print ENorm.mk.sizeOf_spec

#check CategoryTheory.IsSubterminal.def -- not elaborated

#check Filter.mem_rcomap'
example: ∀ {α : Type u} {β : Type v} (r : Rel α β) (l : Filter β) (s : Set α),
  s ∈ Filter.rcomap' r l ↔ ∃ t, t ∈ l ∧ Rel.preimage r t ⊆ s := by
intro α β r l s 
simp_all only [Filter.mem_rcomap']



#check CommRingCat.Colimits.Prequotient.one.sizeOf_spec -- not elaborated

#check Filter.Germ.liftRel_coe -- not elaborated

#print Setoid.inf_iff_and

#check CategoryTheory.Bicone.right.sizeOf_spec -- not elaborated

#check Ordinal.initialSegOut.proof_1
example: ∀ {β : Ordinal.{u_1}} (α : Type u_1) (r : α → α → Prop) (wo : IsWellOrder α r),
  Quotient.out β = { α := α, r := r, wo := wo } → { α := α, r := r, wo := wo } = Quotient.out β := by
intro β α r wo h 
simp_all only



#check CategoryTheory.Limits.isoZeroOfEpiEqZero.proof_1
example: ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
  {X Y : C} {f : X ⟶ Y}, f = 0 → 0 = f := by
intro C inst inst_1 X Y f h 
aesop_subst h 
simp_all only



#check FirstOrder.Language.BoundedFormula.realize_rel
example: ∀ {L : FirstOrder.Language} {M : Type w} [inst : FirstOrder.Language.Structure L M] {α : Type u'} {l : ℕ} {v : α → M}
  {xs : Fin l → M} {k : ℕ} {R : FirstOrder.Language.Relations L k}
  {ts : Fin k → FirstOrder.Language.Term L (α ⊕ Fin l)},
  FirstOrder.Language.BoundedFormula.Realize (FirstOrder.Language.Relations.boundedFormula R ts) v xs ↔
    FirstOrder.Language.Structure.RelMap R fun i => FirstOrder.Language.Term.realize (Sum.elim v xs) (ts i) := by
intro L M inst α l v xs k R ts 
simp_all only [FirstOrder.Language.BoundedFormula.realize_rel]



#check FirstOrder.Language.Sentence.realize_not -- not elaborated

#check AddGroup.fintypeOfKerEqRange.proof_1
example: ∀ {F G H : Type u_1} [inst : AddGroup F] [inst_1 : AddGroup G] [inst_2 : AddGroup H] (f : F →+ G) (g : G →+ H),
  AddMonoidHom.ker g = AddMonoidHom.range f → AddMonoidHom.ker g ≤ AddMonoidHom.range f := by
intro F G H inst inst_1 inst_2 f g h 
simp_all only [le_refl]



#check Ordnode.balanceR.proof_3
example: ∀ {α : Type u_1} (rl : Ordnode α) (size : ℕ) (l : Ordnode α) (rlx : α) (r : Ordnode α),
  rl = Ordnode.node size l rlx r → Ordnode.node size l rlx r = rl := by
intro α rl size l rlx r h 
aesop_subst h 
simp_all only



#check CategoryTheory.Subobject.isoOfEq.proof_2
example: ∀ {C : Type u_1} [inst : CategoryTheory.Category.{u_2, u_1} C] {B : C} (X Y : CategoryTheory.Subobject B), X = Y → Y ≤ X := by
intro C inst B X Y h 
aesop_subst h 
simp_all only [le_refl]



#check Transitive.comap
example: ∀ {α : Type u_1} {β : Type u_2} {r : β → β → Prop}, Transitive r → ∀ (f : α → β), Transitive (r on f) := by
sorry -- could not extract proof



#check WithTop.linearOrderedAddCommGroupWithTop.proof_9
example: ∀ {α : Type u_1} [inst : LinearOrderedAddCommGroup α] (a b : WithTop α), a - b = a - b := by
intro α inst a b 
simp_all only



#check IsInvariant.isFwInvariant
example: ∀ {τ : Type u_1} {α : Type u_2} [inst : Preorder τ] [inst_1 : Zero τ] {ϕ : τ → α → α} {s : Set α},
  IsInvariant ϕ s → IsFwInvariant ϕ s := by
intro τ α inst inst_1 ϕ s h 
intro t a x a_1 
apply h 
simp_all only



#check Set.le_iff_subset
example: ∀ {α : Type u_1} {s t : Set α}, s ≤ t ↔ s ⊆ t := by
intro α s t 
simp_all only [Set.le_eq_subset]



#print LowerSet.mk.sizeOf_spec

#check Algebra.mem_inf
example: ∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {S T : Subalgebra R A}
  {x : A}, x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := by
intro R A inst inst_1 inst_2 S T x 
simp_all only [ge_iff_le, Algebra.mem_inf]



#check Ordnode.balanceR.proof_14
example: ∀ {α : Type u_1} (r : Ordnode α), id r = Ordnode.nil → Ordnode.nil = id r := by
intro α r h 
simp_all only [id_eq]



#check monotone_toDual_comp_iff
example: ∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β},
  Monotone (↑OrderDual.toDual ∘ f) ↔ Antitone f := by
intro α β inst inst_1 f 
simp_all only [monotone_toDual_comp_iff]



#print Sum.Lex.lt_def

#check Algebra.TensorProduct.instRing.proof_1
example: ∀ {R : Type u_3} [inst : CommRing R] {A : Type u_2} [inst_1 : Ring A] [inst_2 : Algebra R A] {B : Type u_1}
  [inst_3 : Ring B] [inst_4 : Algebra R B] (a b : TensorProduct R A B), a - b = a - b := by
intro R inst A inst_1 inst_2 B inst_3 inst_4 a b 
simp_all only



#check UpperSet.mem_compl_iff
example: ∀ {α : Type u_1} [inst : LE α] {s : UpperSet α} {a : α}, a ∈ UpperSet.compl s ↔ ¬a ∈ s := by
intro α inst s a 
simp_all only [UpperSet.mem_compl_iff]



#check FP.ofPosRatDn.proof_4
example: ∀ [C : FP.FloatCfg] (n d : ℕ+) (d₁ n₁ : ℕ),
  Int.shift2 (↑d) (↑n) (↑(Nat.size ↑n) - ↑(Nat.size ↑d) - ↑FP.prec + ↑FP.prec) = (d₁, n₁) →
    (d₁, n₁) = Int.shift2 (↑d) (↑n) (↑(Nat.size ↑n) - ↑(Nat.size ↑d) - ↑FP.prec + ↑FP.prec) := by
intro C n d d₁ n₁ h
simp_all only [sub_add_cancel]



#check isLowerSet_preimage_toDual_iff
example: ∀ {α : Type u_1} [inst : LE α] {s : Set αᵒᵈ}, IsLowerSet (↑OrderDual.toDual ⁻¹' s) ↔ IsUpperSet s := by
intro α inst s
simp_all only [isLowerSet_preimage_toDual_iff]



#print NFA.mem_accepts

#check Function.Semiconj₂.eq
example: ∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α → α} {gb : β → β → β},
  Function.Semiconj₂ f ga gb → ∀ (x y : α), f (ga x y) = gb (f x) (f y) := by
intro α β f ga gb h x y
apply h



#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_112
example: ∀ (b : Turing.PartrecToTM2.Λ') (k : Turing.PartrecToTM2.Cont'),
  b = Turing.PartrecToTM2.Λ'.ret k → Turing.PartrecToTM2.Λ'.ret k = b := by
intro b k h
aesop_subst h
simp_all only



#check ZFSet.mk_mem_iff
example: ∀ {x y : PSet}, ZFSet.mk x ∈ ZFSet.mk y ↔ x ∈ y := by
intro x y
simp_all only [ZFSet.mk_mem_iff]



#check GroupTopology.toTopologicalSpace_le
example: ∀ {α : Type u} [inst : Group α] {x y : GroupTopology α}, x.toTopologicalSpace ≤ y.toTopologicalSpace ↔ x ≤ y := by
intro α inst x y
simp_all only [GroupTopology.toTopologicalSpace_le]



#print Subtype.mk_le_mk

#check Ordnode.balance.proof_31
example: ∀ {α : Type u_1} (lr : Ordnode α) (lrs : ℕ) (lrl : Ordnode α) (lrx : α) (lrr : Ordnode α),
  id lr = Ordnode.node lrs lrl lrx lrr → Ordnode.node lrs lrl lrx lrr = id lr := by
intro α lr lrs lrl lrx lrr h
simp_all only [id_eq]



#check SubfieldClass.toField.proof_18
example: ∀ {K : Type u_1} [inst : Field K] (S : Type u_2) [inst_1 : SetLike S K] [h : SubfieldClass S K] (s : S)
  (x : { x // x ∈ s }) (n : ℚ), n • x = n • x := by
intro K inst S inst_1 h s x n
simp_all only



#print isMax_toDual_iff

#check CategoryTheory.biconeMk.proof_3
example: ∀ (J : Type u_1) {X : CategoryTheory.Bicone J}, X = CategoryTheory.Bicone.left → CategoryTheory.Bicone.left = X := by
intro J X h
aesop_subst h
simp_all only



#print LowerSet.mem_mk

#check ProofWidgets.LayoutKind.block.sizeOf_spec
example: sizeOf ProofWidgets.LayoutKind.block = 1 := by
simp_all only



#check AddAction.mem_fixedPoints
example: ∀ {M : Type u} (α : Type v) [inst : AddMonoid M] [inst_1 : AddAction M α] {a : α},
  a ∈ AddAction.fixedPoints M α ↔ ∀ (m : M), m +ᵥ a = a := by
intro M α inst inst_1 a
simp_all only [AddAction.mem_fixedPoints]



#check SubfieldClass.toField.proof_19
example: ∀ {K : Type u_1} [inst : Field K] (S : Type u_2) [inst_1 : SetLike S K] [h : SubfieldClass S K] (s : S)
  (x : { x // x ∈ s }) (n : ℕ), x ^ n = x ^ n := by
intro K inst S inst_1 h s x n
simp_all only



#check Pmf.mem_support_ofFintype_iff
example: ∀ {α : Type u_1} [inst : Fintype α] {f : α → ENNReal} (h : (Finset.sum Finset.univ fun a => f a) = 1) (a : α),
  a ∈ Pmf.support (Pmf.ofFintype f h) ↔ f a ≠ 0 := by
intro α inst f h a
simp_all only [Pmf.support_ofFintype, Function.mem_support, ne_eq]



#print MeasureTheory.AEDisjoint.eq

#check HahnSeries.instAddGroupHahnSeriesToZeroToNegZeroClassToSubNegZeroMonoidToSubtractionMonoid.proof_12
example: ∀ {Γ : Type u_2} {R : Type u_1} [inst : PartialOrder Γ] [inst_1 : AddGroup R] (a b : HahnSeries Γ R), a - b = a - b := by
intro Γ R inst inst_1 a b
simp_all only



#check Ordinal.principalSegOut.proof_3
example: ∀ {α : Ordinal.{u_1}} (α_1 : Type u_1) (r : α_1 → α_1 → Prop) (wo : IsWellOrder α_1 r),
  Quotient.out α = { α := α_1, r := r, wo := wo } → { α := α_1, r := r, wo := wo } = Quotient.out α := by
intro α α_1 r wo h
simp_all only



#check BilinForm.mem_isPairSelfAdjointSubmodule
example: ∀ {R₂ : Type u_5} {M₂ : Type u_6} [inst : CommSemiring R₂] [inst_1 : AddCommMonoid M₂] [inst_2 : Module R₂ M₂]
  (B₂ F₂ : BilinForm R₂ M₂) (f : Module.End R₂ M₂),
  f ∈ BilinForm.isPairSelfAdjointSubmodule B₂ F₂ ↔ BilinForm.IsPairSelfAdjoint B₂ F₂ f := by
intro R₂ M₂ inst inst_1 inst_2 B₂ F₂ f
simp_all only [BilinForm.mem_isPairSelfAdjointSubmodule]



#check AddGroupSeminorm.le_def
example: ∀ {E : Type u_4} [inst : AddGroup E] {p q : AddGroupSeminorm E}, p ≤ q ↔ p ≤ q := by
intro E inst p q
simp_all only



#check Complex.addCommGroup.proof_6
example: ∀ (a b : ℂ), a - b = a - b := by
intro a b
simp_all only



#check CategoryTheory.BiconeHom.right_id.sizeOf_spec -- not elaborated

#check IsField.toSemifield.proof_8 -- not elaborated

#check Nat.ArithmeticFunction.instCommRingArithmeticFunctionToZeroToCommMonoidWithZeroToCommSemiring.proof_7
example: ∀ {R : Type u_1} [inst : CommRing R] (a b : Nat.ArithmeticFunction R), a - b = a - b := by
intro R inst a b
simp_all only



#print toBoolRing_inj

#check AddAction.orbitRel_apply
example: ∀ {G : Type u} {α : Type v} [inst : AddGroup G] [inst_1 : AddAction G α] {a b : α},
  Setoid.Rel (AddAction.orbitRel G α) a b ↔ a ∈ AddAction.orbit G b := by
intro G α inst inst_1 a b
apply Iff.intro 
· intro a_1
  exact a_1 
· intro a_1
  exact a_1



#check lp.instNormSubtypePreLpMemAddSubgroupToAddGroupInstAddCommGroupPreLpInstMembershipInstSetLikeAddSubgroupLp.proof_2
example: ∀ {p : ENNReal}, p = 0 → 0 = p := by
intro p hp
aesop_subst hp
simp_all only



#check PEquiv.instPartialOrderPEquiv.proof_3
example: ∀ {α : Type u_1} {β : Type u_2} (a b : α ≃. β), a < b ↔ a < b := by
intro α β a b
simp_all only



#check Multiset.mem_of_subset
example: ∀ {α : Type u_1} {s t : Multiset α} {a : α}, s ⊆ t → a ∈ s → a ∈ t := by
intro α s t a h a_1
apply h
simp_all only



#print AddSemigroupCat.instParentProjectionTypeAddAddSemigroupToAdd.proof_1

#print DistLatCat.instParentProjectionTypeLatticeDistribLatticeToLattice.proof_1

#check Multiset.coe_nodup -- not elaborated

#check AddGroupCat.instParentProjectionTypeAddMonoidAddGroupToAddMonoidToSubNegAddMonoid.proof_1 -- not elaborated

#check groupAddGroupEquivalence_inverse_obj_str_div
example: ∀ (X : AddGroupCat) (x y : Multiplicative ↑X), x / y = x / y := by
intro X x y
simp_all only [groupAddGroupEquivalence_inverse_obj_str_div]



#check Matrix.IsHermitian.isSelfAdjoint
example: ∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {A : Matrix n n α}, Matrix.IsHermitian A → IsSelfAdjoint A := by
intro α n inst A h
exact h



#check SmoothBumpCovering.isSubordinate_toBumpCovering -- not elaborated

#check MvFunctor.of_mem_supp
example: ∀ {n : ℕ} {F : TypeVec n → Type v} [inst : MvFunctor F] {α : TypeVec n} {x : F α} {P : ⦃i : Fin2 n⦄ → α i → Prop},
  MvFunctor.LiftP P x → ∀ (i : Fin2 n) (y : α i), y ∈ MvFunctor.supp x i → P y := by
intro n F inst α x P h i y a
apply a
simp_all only



#check specializes_iff_nhds
example: ∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X}, x ⤳ y ↔ nhds x ≤ nhds y := by
intro X inst x y
apply Iff.intro 
· intro a
  exact a 
· intro a
  exact a



#check QuotientAddGroup.equivQuotientAddSubgroupOfOfEq.proof_3
example: ∀ {G : Type u_1} [inst : AddGroup G] {A' B' : AddSubgroup G}, A' = B' → B' ≤ A' := by
intro G inst A' B' h'
aesop_subst h'
simp_all only [le_refl]



#print Ideal.mem_comap

#check Filter.mem_smul -- not elaborated

#check Subgroup.saturated_iff_npow
example: ∀ {G : Type u_1} [inst : Group G] {H : Subgroup G}, Subgroup.Saturated H ↔ ∀ (n : ℕ) (g : G), g ^ n ∈ H → n = 0 ∨ g ∈ H := by
intro G inst H
apply Iff.intro 
· intro a n g a_1
  apply a
  simp_all only 
· intro a
  exact a



#check PosNum.one.sizeOf_spec
example: sizeOf PosNum.one = 1 := by
simp_all only



#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_62
example: ∀ (b q₁ q₂ : Turing.PartrecToTM2.Λ'), b = Turing.PartrecToTM2.Λ'.pred q₁ q₂ → Turing.PartrecToTM2.Λ'.pred q₁ q₂ = b := by
intro b q₁ q₂ h
aesop_subst h
simp_all only



#check FirstOrder.Language.DefinableSet.mem_compl
example: ∀ {L : FirstOrder.Language} {M : Type w} [inst : FirstOrder.Language.Structure L M] {A : Set M} {α : Type u₁}
  {s : FirstOrder.Language.DefinableSet L A α} {x : α → M}, x ∈ sᶜ ↔ ¬x ∈ s := by
intro L M inst A α s x
simp_all only [FirstOrder.Language.DefinableSet.mem_compl]



#check CategoryTheory.Limits.WidePushoutShape.fintypeHom.proof_2
example: ∀ {J : Type u_1} (j' : CategoryTheory.Limits.WidePushoutShape J) (j'_1 : J), j' = some j'_1 → some j'_1 = j' := by
intro J j' j'_1 h
aesop_subst h
simp_all only



#print ProperCone.mem_comap

#check CategoryTheory.Limits.WidePushoutShape.fintypeHom.proof_4
example: ∀ {J : Type u_1} (j : CategoryTheory.Limits.WidePushoutShape J), j = none → none = j := by
intro J j h
aesop_subst h
simp_all only



#check PUnit.addCommGroup.proof_6
example: ∀ (a b : PUnit), a - b = a - b := by
intro a b
simp_all only [sub_self, PUnit.zero_eq]



#check CategoryTheory.ShortComplex.RightHomologyMapData.ofIsLimitKernelFork.proof_3
example: ∀ {C : Type u_2} [inst : CategoryTheory.Category.{u_1, u_2} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
  {S₁ S₂ : CategoryTheory.ShortComplex C} (φ : S₁ ⟶ S₂) (c₁ : CategoryTheory.Limits.KernelFork S₁.g)
  (c₂ : CategoryTheory.Limits.KernelFork S₂.g) (f : c₁.pt ⟶ c₂.pt),
  CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Fork.ι c₁) φ.τ₂ =
      CategoryTheory.CategoryStruct.comp f (CategoryTheory.Limits.Fork.ι c₂) →
    CategoryTheory.CategoryStruct.comp f (CategoryTheory.Limits.Fork.ι c₂) =
      CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Fork.ι c₁) φ.τ₂ := by
intro C inst inst_1 S₁ S₂ φ c₁ c₂ f comm
simp_all only
    [CategoryTheory.Functor.const_obj_obj, CategoryTheory.Limits.parallelPair_obj_zero]



#check ProjectiveSpectrum.as_ideal_le_as_ideal
example: ∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : CommRing A] [inst_2 : Algebra R A]
  (𝒜 : ℕ → Submodule R A) [inst_3 : GradedAlgebra 𝒜] (x y : ProjectiveSpectrum 𝒜),
  x.asHomogeneousIdeal ≤ y.asHomogeneousIdeal ↔ x ≤ y := by
intro R A inst inst_1 inst_2 𝒜 inst_3 x y
simp_all only [ProjectiveSpectrum.as_ideal_le_as_ideal]



#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_2
example: ∀ (b : Turing.PartrecToTM2.Λ') (p : Turing.PartrecToTM2.Γ' → Bool) (k₁ k₂ : Turing.PartrecToTM2.K')
  (q : Turing.PartrecToTM2.Λ'), b = Turing.PartrecToTM2.Λ'.move p k₁ k₂ q → Turing.PartrecToTM2.Λ'.move p k₁ k₂ q = b := by
intro b p k₁ k₂ q h
aesop_subst h
simp_all only



#print GaloisConnection.le_iff_le

#print mem_subalgebraEquivIntermediateField_symm

#check AList.mem_keys
example: ∀ {α : Type u} {β : α → Type v} {a : α} {s : AList β}, a ∈ s ↔ a ∈ AList.keys s := by
intro α β a s
apply Iff.intro 
· intro a_1
  exact a_1 
· intro a_1
  exact a_1



#check SignType.zero.sizeOf_spec
example: sizeOf SignType.zero = 1 := by
simp_all only



#check Ordnode.balance.proof_32
example: ∀ {α : Type u_1} (ll : Ordnode α) (lls : ℕ) (l : Ordnode α) (x : α) (r : Ordnode α),
  id ll = Ordnode.node lls l x r → Ordnode.node lls l x r = id ll := by
intro α ll lls l x r h
simp_all only [id_eq]



#check ne_of_ne_of_eq
example: ∀ {α : Sort u} {a b c : α}, a ≠ b → b = c → a ≠ c := by
intro α a b c h₁ h₂
aesop_subst h₂
simp_all only [ne_eq, not_false_eq_true]



#check Submodule.mem_toConvexCone
example: ∀ {𝕜 : Type u_1} {E : Type u_2} [inst : OrderedSemiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : Module 𝕜 E] {x : E}
  {S : Submodule 𝕜 E}, x ∈ Submodule.toConvexCone S ↔ x ∈ S := by
intro 𝕜 E inst inst_1 inst_2 x S
simp_all only [Submodule.mem_toConvexCone]



#check Filter.mem_sSup
example: ∀ {α : Type u} {x : Set α} {s : Set (Filter α)}, x ∈ sSup s ↔ ∀ (f : Filter α), f ∈ s → x ∈ f := by
intro α x s
simp_all only [Filter.mem_sSup]



#check Subalgebra.mem_carrier
example: ∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {s : Subalgebra R A}
  {x : A}, x ∈ s.carrier ↔ x ∈ s := by
intro R A inst inst_1 inst_2 s x
simp_all only
    [Subsemiring.coe_carrier_toSubmonoid, Subalgebra.coe_toSubsemiring, SetLike.mem_coe]



#check PNat.bit1_le_bit1
example: ∀ (n m : ℕ+), bit1 n ≤ bit1 m ↔ bit1 n ≤ bit1 m := by
intro n m
simp_all only [PNat.bit1_le_bit1, bit1_le_bit1, PNat.coe_le_coe]



#check Function.Commute.semiconj
example: ∀ {α : Type u_1} {f g : α → α}, Function.Commute f g → Function.Semiconj f g g := by
intro α f g h
exact h



#check Nat.Partrec.Code.left.sizeOf_spec
example: sizeOf Nat.Partrec.Code.left = 1 := by
simp_all only



#print Quaternion.instInv_inv

#check AddSubmonoid.toSubmonoid.proof_6 -- not elaborated

#check SubgroupClass.coeSubtype -- not elaborated

#check QuotientGroup.equivQuotientSubgroupOfOfEq.proof_3
example: ∀ {G : Type u_1} [inst : Group G] {A' B' : Subgroup G}, A' = B' → B' ≤ A' := by
intro G inst A' B' h'
aesop_subst h'
simp_all only [le_refl]



#print WithZero.cases_on

#check List.disjoint_symm
example: ∀ {α : Type u_1} {l₁ l₂ : List α}, List.Disjoint l₁ l₂ → List.Disjoint l₂ l₁ := by
sorry -- could not extract proof



#check FP.Float.nan.sizeOf_spec
example: ∀ [C : FP.FloatCfg], sizeOf FP.Float.nan = 1 := by
intro C
simp_all only [FP.Float.nan.sizeOf_spec]



#check OrderIso.Set.univ.proof_1 -- not elaborated

#check Ordnode.balance.proof_10
example: ∀ {α : Type u_1} (r : Ordnode α) (rs : ℕ) (rl : Ordnode α) (rx : α) (rr : Ordnode α),
  id r = Ordnode.node rs rl rx rr → Ordnode.node rs rl rx rr = id r := by
intro α r rs rl rx rr h
simp_all only [id_eq]



#check IsOpen.mono
example: ∀ {α : Type u_1} {t₁ t₂ : TopologicalSpace α} {s : Set α}, IsOpen s → t₁ ≤ t₂ → IsOpen s := by
intro α t₁ t₂ s hs h
simp_all only



#check ONote.lt_def
example: ∀ {x y : ONote}, x < y ↔ ONote.repr x < ONote.repr y := by
intro x y
apply Iff.intro 
· intro a
  exact a 
· intro a
  exact a



#check List.foldrRecOn.proof_1
example: ∀ {α : Type u_1} (l : List α), l = [] → [] = l := by
intro α l h
aesop_subst h
simp_all only



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



#check Function.mem_mulSupport
example: ∀ {α : Type u_1} {M : Type u_5} [inst : One M] {f : α → M} {x : α}, x ∈ Function.mulSupport f ↔ f x ≠ 1 := by
intro α M inst f x
simp_all only [Function.mem_mulSupport, ne_eq]



#check NNReal.coe_pos
example: ∀ {r : NNReal}, 0 < r ↔ 0 < r := by
intro r
simp_all only



#check CompleteLattice.independent_def
example: ∀ {α : Type u_1} {ι : Type u_3} [inst : CompleteLattice α] {t : ι → α},
  CompleteLattice.Independent t ↔ ∀ (i : ι), Disjoint (t i) (⨆ (j : ι) (_ : j ≠ i), t j) := by
intro α ι inst t
simp_all only [ne_eq, not_not]
apply Iff.intro 
· intro a i
  apply a 
· intro a
  exact a



#print MultilinearMap.mk.sizeOf_spec

#print WithBot.ofDual_lt_iff

#check Metric.mem_cthickening_iff
example: ∀ {α : Type u} [inst : PseudoEMetricSpace α] {δ : ℝ} {s : Set α} {x : α},
  x ∈ Metric.cthickening δ s ↔ EMetric.infEdist x s ≤ ENNReal.ofReal δ := by
intro α inst δ s x
simp_all only [Metric.mem_cthickening_iff]



#check AddAction.mem_fixedBy
example: ∀ {M : Type u} (α : Type v) [inst : AddMonoid M] [inst_1 : AddAction M α] {m : M} {a : α},
  a ∈ AddAction.fixedBy M α m ↔ m +ᵥ a = a := by
intro M α inst inst_1 m a
simp_all only [AddAction.mem_fixedBy]



#check Option.mem_iff
example: ∀ {α : Type u_1} {a : α} {b : Option α}, a ∈ b ↔ b = some a := by
intro α a b
simp_all only [Option.mem_def]



#check CategoryTheory.BiconeHom.left_id.sizeOf_spec -- not elaborated

#check AddCon.instPartialOrderCon.proof_3
example: ∀ {M : Type u_1} [inst : Add M] (x x_1 : AddCon M), x < x_1 ↔ x < x_1 := by
intro M inst x x_1
simp_all only



#print CategoryTheory.GradedNatTrans.mk.sizeOf_spec

#check Sym2.gameAdd_mk'_iff
example: ∀ {α : Type u_1} {rα : α → α → Prop} {a₁ a₂ b₁ b₂ : α},
  Sym2.GameAdd rα (Quotient.mk (Sym2.Rel.setoid α) (a₁, b₁)) (Quotient.mk (Sym2.Rel.setoid α) (a₂, b₂)) ↔
    Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ Prod.GameAdd rα rα (b₁, a₁) (a₂, b₂) := by
intro α rα a₁ a₂ b₁ b₂
apply Iff.intro 
· intro a
  exact a 
· intro a
  exact a



#check USize.lt_def
example: ∀ {a b : USize}, a < b ↔ USize.toNat a < USize.toNat b := by
intro a b
simp_all only [USize.lt_def]



#check StrictSeries.le_def
example: ∀ {α : Type u_1} [inst : Preorder α] (x y : StrictSeries α), x ≤ y ↔ x.length ≤ y.length := by
intro α inst x y
apply Iff.intro 
· intro a
  exact a 
· intro a
  exact a



#print NonUnitalSubring.mem_prod

#check CategoryTheory.BiconeHom.decidableEq.proof_21
example: ∀ (J : Type u_1) {j : CategoryTheory.Bicone J}, j = CategoryTheory.Bicone.left → CategoryTheory.Bicone.left = j := by
intro J j h
aesop_subst h
simp_all only



#print Complex.mem_reProdIm

#check ModuleCat.Colimits.Prequotient.zero.sizeOf_spec -- not elaborated

#check LieSubalgebra.mem_toLieSubmodule
example: ∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {K : LieSubalgebra R L}
  (x : L), x ∈ LieSubalgebra.toLieSubmodule K ↔ x ∈ K := by
intro R L inst inst_1 inst_2 K x
simp_all only [LieSubalgebra.mem_toLieSubmodule]



#check ChainComplex.augmentTruncate.proof_4
example: ∀ (i n : ℕ), i = Nat.succ n → Nat.succ n = i := by
intro i n h
aesop_subst h
simp_all only



#check CategoryTheory.Limits.WidePullbackShape.wideCospan.proof_4
example: ∀ {J : Type u_1} {Y : CategoryTheory.Limits.WidePullbackShape J}, Y = none → none = Y := by
intro J Y h
aesop_subst h
simp_all only



#print SModEq.trans

#check Submodule.mem_torsionBy_iff
example: ∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : Module R M] (a : R)
  (x : M), x ∈ Submodule.torsionBy R M a ↔ a • x = 0 := by
intro R M inst inst_1 inst_2 a x
simp_all only [Submodule.mem_torsionBy_iff]



#check LinearMap.mem_range -- not elaborated

#check Subsemiring.mem_carrier
example: ∀ {R : Type u} [inst : NonAssocSemiring R] {s : Subsemiring R} {x : R}, x ∈ s.carrier ↔ x ∈ s := by
intro R inst s x
simp_all only [Subsemiring.coe_carrier_toSubmonoid, SetLike.mem_coe]



#print PSet.nonempty_def

#print Filter.Germ.coe_nonneg

#check Set.mem_prod
example: ∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {p : α × β}, p ∈ s ×ˢ t ↔ p.fst ∈ s ∧ p.snd ∈ t := by
intro α β s t p
simp_all only [Set.mem_prod]



#check CochainComplex.augmentTruncate.proof_4
example: ∀ (i n : ℕ), i = Nat.succ n → Nat.succ n = i := by
intro i n h
aesop_subst h
simp_all only



#check Subalgebra.mem_restrictScalars
example: ∀ (R : Type u) {S : Type v} {A : Type w} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]
  [inst_3 : Algebra R S] [inst_4 : Algebra S A] [inst_5 : Algebra R A] [inst_6 : IsScalarTower R S A]
  {U : Subalgebra S A} {x : A}, x ∈ Subalgebra.restrictScalars R U ↔ x ∈ U := by
intro R S A inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 U x
simp_all only [Subalgebra.mem_restrictScalars]



#print CategoryTheory.GrothendieckTopology.Subpresheaf.mk.sizeOf_spec

#print ConvexCone.mem_mk

#print Seminorm.le_def

#check Finset.subset_iff
example: ∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s₂ ↔ ∀ ⦃x : α⦄, x ∈ s₁ → x ∈ s₂ := by
intro α s₁ s₂
apply Iff.intro 
· intro a x a_1
  apply a
  simp_all only 
· intro a
  exact a



#check RingAut.instGroupRingAut.proof_1
example: ∀ (R : Type u_1) [inst : Mul R] [inst_1 : Add R] (a b c : RingAut R), a * b * c = a * b * c := by
intro R inst inst_1 a b c
simp_all only



-- #check toAntisymmetrization_le_toAntisymmetrization_iff
-- example: ∀ {α : Type u_1} [inst : Preorder α] {a b : α},
--   toAntisymmetrization (fun x x_1 => x ≤ x_1) a ≤ toAntisymmetrization (fun x x_1 => x ≤ x_1) b ↔ a ≤ b := by
-- intro α inst a b
-- simp_all only [toAntisymmetrization_le_toAntisymmetrization_iff]



#check OpenSubgroup.mem_toOpens
example: ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G] {U : OpenSubgroup G} {g : G}, g ∈ U ↔ g ∈ U := by
intro G inst inst_1 U g
simp_all only



#print AddMonoidHom.mem_range

#print Con.rel_mk

#print PartENat.find_dom

#print OrderEmbedding.subtype.proof_1

#check Function.mem_support
example: ∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] {f : α → M} {x : α}, x ∈ Function.support f ↔ f x ≠ 0 := by
intro α M inst f x
simp_all only [Function.mem_support, ne_eq]



#print ofLex_inj

#check ZFSet.subset_def
example: ∀ {x y : ZFSet}, x ⊆ y ↔ ∀ ⦃z : ZFSet⦄, z ∈ x → z ∈ y := by
intro x y
apply Iff.intro 
· intro a z a_1
  apply a
  simp_all only 
· intro a
  exact a



#print equiv_iff_sameRay

#print FirstOrder.Language.Substructure.mk.sizeOf_spec

#check LowerAdjoint.mem_closed_iff
example: ∀ {α : Type u_1} {β : Type u_4} [inst : Preorder α] [inst_1 : Preorder β] {u : β → α} (l : LowerAdjoint u) (x : α),
  x ∈ LowerAdjoint.closed l ↔ u (LowerAdjoint.toFun l x) = x := by
intro α β inst inst_1 u l x
apply Iff.intro 
· intro a
  exact a 
· intro a
  exact a



#check Complementeds.coe_lt_coe
example: ∀ {α : Type u_1} [inst : Lattice α] [inst_1 : BoundedOrder α] {a b : Complementeds α}, a < b ↔ a < b := by
intro α inst inst_1 a b
simp_all only



#print RelIso.refl.proof_1

#print Additive.toMul_le

#check Units.val_lt_val
example: ∀ {α : Type u_1} [inst : Monoid α] [inst_1 : Preorder α] {a b : αˣ}, a < b ↔ a < b := by
intro α inst inst_1 a b
simp_all only



#check Turing.PartrecToTM2.Γ'.bit0.sizeOf_spec
example: sizeOf Turing.PartrecToTM2.Γ'.bit0 = 1 := by
simp_all only



#check AddGroupSeminorm.lt_def
example: ∀ {E : Type u_4} [inst : AddGroup E] {p q : AddGroupSeminorm E}, p < q ↔ p < q := by
intro E inst p q
simp_all only



#check FiberBundleCore.mem_localTrivAsLocalEquiv_source
example: ∀ {ι : Type u_1} {B : Type u_2} {F : Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]
  (Z : FiberBundleCore ι B F) (i : ι) (p : FiberBundleCore.TotalSpace Z),
  p ∈ (FiberBundleCore.localTrivAsLocalEquiv Z i).source ↔ p.proj ∈ FiberBundleCore.baseSet Z i := by
intro ι B F inst inst_1 Z i p
simp_all only
    [FiberBundleCore.localTrivAsLocalEquiv_source, FiberBundleCore.proj, FiberBundleCore.mem_localTriv_source,
      FiberBundleCore.baseSet_at]



#check Filter.eventually_top
example: ∀ {α : Type u} {p : α → Prop}, (∀ᶠ (x : α) in ⊤, p x) ↔ ∀ (x : α), p x := by
intro α p
simp_all only [Filter.eventually_top]



#check ZMod.ringEquivCongr.proof_5
example: ∀ {n : ℕ} (n_1 : ℕ), n = Nat.succ n_1 → Nat.succ n_1 = n := by
intro n n_1 h
aesop_subst h
simp_all only



#print Computable.subtype_mk

#check Ordnode.balanceR.proof_16
example: ∀ {α : Type u_1} (rl : Ordnode α), id rl = Ordnode.nil → Ordnode.nil = id rl := by
intro α rl h
simp_all only [id_eq]



#check LocalRing.mem_maximalIdeal
example: ∀ {R : Type u} [inst : CommSemiring R] [inst_1 : LocalRing R] (x : R), x ∈ LocalRing.maximalIdeal R ↔ x ∈ nonunits R := by
intro R inst inst_1 x
simp_all only [LocalRing.mem_maximalIdeal, mem_nonunits_iff]



#print LinOrdCat.instParentProjectionTypePartialOrderLinearOrderToPartialOrder.proof_1

#print OrderDual.ofDual_lt_ofDual

#check SetTheory.PGame.not_le
example: ∀ {x y : SetTheory.PGame}, ¬x ≤ y ↔ SetTheory.PGame.Lf y x := by
intro x y
simp_all only [SetTheory.PGame.not_le]



#check SubfieldClass.toField.proof_15
example: ∀ {K : Type u_1} [inst : Field K] (S : Type u_2) [inst_1 : SetLike S K] [h : SubfieldClass S K] (s : S)
  (x y : { x // x ∈ s }), x / y = x / y := by
intro K inst S inst_1 h s x y
simp_all only



#check BilinForm.IsAlt.self_eq_zero
example: ∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Module R M]
  {B : BilinForm R M}, BilinForm.IsAlt B → ∀ (x : M), BilinForm.bilin B x x = 0 := by
intro R M inst inst_1 inst_2 B H x
apply H



#check SetLike.le_def
example: ∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {S T : A}, S ≤ T ↔ ∀ ⦃x : B⦄, x ∈ S → x ∈ T := by
intro A B i S T
apply Iff.intro 
· intro a x a_1
  apply a
  simp_all only 
· intro a
  exact a



#print supPrime_ofDual

#print FreimanHom.mk.sizeOf_spec

#check Ordnode.balanceR.proof_21
example: ∀ {α : Type u_1} (r : Ordnode α) (rs : ℕ) (rl : Ordnode α) (rx : α) (rr : Ordnode α),
  id r = Ordnode.node rs rl rx rr → Ordnode.node rs rl rx rr = id r := by
intro α r rs rl rx rr h
simp_all only [id_eq]



#check FirstOrder.Language.DefinableSet.le_iff
example: ∀ {L : FirstOrder.Language} {M : Type w} [inst : FirstOrder.Language.Structure L M] {A : Set M} {α : Type u₁}
  {s t : FirstOrder.Language.DefinableSet L A α}, s ≤ t ↔ s ≤ t := by
intro L M inst A α s t
simp_all only



#check Ordnode.balanceR.proof_22
example: ∀ {α : Type u_1} (l : Ordnode α) (ls : ℕ) (l_1 : Ordnode α) (x : α) (r : Ordnode α),
  id l = Ordnode.node ls l_1 x r → Ordnode.node ls l_1 x r = id l := by
intro α l ls l_1 x r h
simp_all only [id_eq]



#check Option.none.sizeOf_spec -- not elaborated

#print Ordinal.toNatOrdinal_eq_zero

#check BilinForm.mem_selfAdjointSubmodule
example: ∀ {R₂ : Type u_5} {M₂ : Type u_6} [inst : CommSemiring R₂] [inst_1 : AddCommMonoid M₂] [inst_2 : Module R₂ M₂]
  (B₂ : BilinForm R₂ M₂) (f : Module.End R₂ M₂), f ∈ BilinForm.selfAdjointSubmodule B₂ ↔ BilinForm.IsSelfAdjoint B₂ f := by
intro R₂ M₂ inst inst_1 inst_2 B₂ f
simp_all only [BilinForm.mem_selfAdjointSubmodule]



#check Submodule.mem_div_iff_forall_mul_mem
example: ∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [inst_1 : CommSemiring A] [inst_2 : Algebra R A] {x : A}
  {I J : Submodule R A}, x ∈ I / J ↔ ∀ (y : A), y ∈ J → x * y ∈ I := by
intro R inst A inst_1 inst_2 x I J
apply Iff.intro 
· intro a y a_1
  apply a
  simp_all only 
· intro a
  exact a



#check Metric.mem_thickening_iff_infEdist_lt
example: ∀ {α : Type u} [inst : PseudoEMetricSpace α] {δ : ℝ} {s : Set α} {x : α},
  x ∈ Metric.thickening δ s ↔ EMetric.infEdist x s < ENNReal.ofReal δ := by
intro α inst δ s x
apply Iff.intro 
· intro a
  exact a 
· intro a
  exact a



#print CommGroupCat.instParentProjectionTypeGroupCommGroupToGroup.proof_1

#check Filter.ptendsto_def
example: ∀ {α : Type u} {β : Type v} (f : α →. β) (l₁ : Filter α) (l₂ : Filter β),
  Filter.PTendsto f l₁ l₂ ↔ ∀ (s : Set β), s ∈ l₂ → PFun.core f s ∈ l₁ := by
intro α β f l₁ l₂
apply Iff.intro 
· intro a s a_1
  apply a
  simp_all only 
· intro a
  exact a



#check Ordnode.balance.proof_16
example: ∀ {α : Type u_1} (ll : Ordnode α), id ll = Ordnode.nil → Ordnode.nil = id ll := by
intro α ll h
simp_all only [id_eq]



#print WittVector.mk'.sizeOf_spec

#print ValuationSubring.valuation_le_iff

#check groupWithZeroOfIsUnitOrEqZero.proof_5 -- not elaborated

#check EuclideanGeometry.Sphere.mem_coe
example: ∀ {P : Type u_2} [inst : MetricSpace P] {p : P} {s : EuclideanGeometry.Sphere P},
  p ∈ Metric.sphere s.center s.radius ↔ p ∈ s := by
intro P inst p s
simp_all only [Metric.mem_sphere, EuclideanGeometry.Sphere.mem_coe']



#check Subring.mem_carrier
example: ∀ {R : Type u} [inst : Ring R] {s : Subring R} {x : R}, x ∈ s.carrier ↔ x ∈ s := by
intro R inst s x
simp_all only [Subsemiring.coe_carrier_toSubmonoid, Subring.coe_toSubsemiring, SetLike.mem_coe]



#print Order.Cofinal.mk.sizeOf_spec

#print codisjoint_ofDual_iff

#check Bornology.isCobounded_compl_iff
example: ∀ {α : Type u_2} [inst : Bornology α] {s : Set α}, Bornology.IsCobounded sᶜ ↔ Bornology.IsBounded s := by
intro α inst s
simp_all only [Bornology.isCobounded_compl_iff]



#check CategoryTheory.Limits.WalkingParallelPair.one.sizeOf_spec
example: sizeOf CategoryTheory.Limits.WalkingParallelPair.one = 1 := by
simp_all only



#print AddUnits.coe_liftRight

#check CategoryTheory.Limits.WidePullbackShape.struct.proof_6
example: ∀ {J : Type u_1} {Z : CategoryTheory.Limits.WidePullbackShape J}, Z = Z := by
intro J Z
simp_all only



#check Set.subset_singleton_iff
example: ∀ {α : Type u_1} {s : Set α} {x : α}, s ⊆ {x} ↔ ∀ (y : α), y ∈ s → y = x := by
intro α s x
simp_all only [Set.subset_singleton_iff]



#check MeasurableSet.mem_coe
example: ∀ {α : Type u_1} [inst : MeasurableSpace α] (a : α) (s : Subtype MeasurableSet), a ∈ s ↔ a ∈ s := by
intro α inst a s
simp_all only



#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_50
example: ∀ (b : Turing.PartrecToTM2.Λ') (p : Turing.PartrecToTM2.Γ' → Bool) (k₁ k₂ : Turing.PartrecToTM2.K')
  (q : Turing.PartrecToTM2.Λ'), b = Turing.PartrecToTM2.Λ'.move p k₁ k₂ q → Turing.PartrecToTM2.Λ'.move p k₁ k₂ q = b := by
intro b p k₁ k₂ q h
aesop_subst h
simp_all only



#check commGroupAddCommGroupEquivalence_functor_obj_str_add
example: ∀ (X : CommGroupCat) (x x_1 : Additive ↑X), x + x_1 = x + x_1 := by
intro X x x_1
simp_all only [commGroupAddCommGroupEquivalence_functor_obj_str_add]



#check Filter.eventually_sup
example: ∀ {α : Type u} {p : α → Prop} {f g : Filter α},
  (∀ᶠ (x : α) in f ⊔ g, p x) ↔ (∀ᶠ (x : α) in f, p x) ∧ ∀ᶠ (x : α) in g, p x := by
intro α p f g
simp_all only [ge_iff_le, Filter.eventually_sup]



#check NonUnitalSubring.mem_toSubsemigroup
example: ∀ {R : Type u} [inst : NonUnitalNonAssocRing R] {s : NonUnitalSubring R} {x : R},
  x ∈ NonUnitalSubring.toSubsemigroup s ↔ x ∈ s := by
intro R inst s x
simp_all only [NonUnitalSubring.mem_toSubsemigroup]



#check Sym.mem_coe
example: ∀ {α : Type u_1} {n : ℕ} {s : Sym α n} {a : α}, a ∈ s ↔ a ∈ s := by
intro α n s a
simp_all only



#check Subsemiring.mem_inf
example: ∀ {R : Type u} [inst : NonAssocSemiring R] {p p' : Subsemiring R} {x : R}, x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := by
intro R inst p p' x
simp_all only [ge_iff_le, Subsemiring.mem_inf]



#print infIrred_ofDual

#check Set.mem_powerset_iff
example: ∀ {α : Type u} (x s : Set α), x ∈ 𝒫 s ↔ x ⊆ s := by
intro α x s
simp_all only [Set.mem_powerset_iff]



#print Int.ModEq.trans

#check QuotientGroup.equivQuotientSubgroupOfOfEq.proof_2
example: ∀ {G : Type u_1} [inst : Group G] {A B : Subgroup G}, A = B → A ≤ B := by
intro G inst A B h
aesop_subst h
simp_all only [le_refl]



#check CategoryTheory.Subgroupoid.mem_full_iff
example: ∀ {C : Type u} [inst : CategoryTheory.Groupoid C] (D : Set C) {c d : C} {f : c ⟶ d},
  f ∈ CategoryTheory.Subgroupoid.arrows (CategoryTheory.Subgroupoid.full D) c d ↔ c ∈ D ∧ d ∈ D := by
intro C inst D c d f
simp_all only [CategoryTheory.Subgroupoid.mem_full_iff]



#check LazyList.nil.sizeOf_spec -- not elaborated

#check AlgHom.End_toOne_one
example: ∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A], 1 = AlgHom.id R A := by
intro R A inst inst_1 inst_2
apply Eq.refl



#check Turing.PartrecToTM2.Λ'.instDecidableEq.proof_98
example: ∀ (b : Turing.PartrecToTM2.Λ') (p : Turing.PartrecToTM2.Γ' → Bool) (k₁ k₂ : Turing.PartrecToTM2.K')
  (q : Turing.PartrecToTM2.Λ'), b = Turing.PartrecToTM2.Λ'.move p k₁ k₂ q → Turing.PartrecToTM2.Λ'.move p k₁ k₂ q = b := by
intro b p k₁ k₂ q h
aesop_subst h
simp_all only



#check SimpleGraph.inf_adj
example: ∀ {V : Type u} (x y : SimpleGraph V) (v w : V),
  SimpleGraph.Adj (x ⊓ y) v w ↔ SimpleGraph.Adj x v w ∧ SimpleGraph.Adj y v w := by
intro V x y v w
simp_all only [ge_iff_le, SimpleGraph.inf_adj]



#print ONote.fundamentalSequenceProp_inl_some
example : ∀ (o a : ONote),
  ONote.FundamentalSequenceProp o (Sum.inl (some a)) ↔
    ONote.repr o = Order.succ (ONote.repr a) ∧ (ONote.NF o → ONote.NF a) :=by 
    aesop? (add safe apply Iff.rfl)


#check TopCat.Presheaf.stalkCongr.proof_1 -- not elaborated

#check Turing.TM2.Stmt.goto.sizeOf_spec -- not elaborated

#print AddSubgroup.toIntSubmodule.proof_4

#check mem_nilradical
example: ∀ {R : Type u} [inst : CommSemiring R] {x : R}, x ∈ nilradical R ↔ IsNilpotent x := by
intro R inst x
apply Iff.intro 
· intro a
  exact a 
· intro a
  exact a



#print MeasureTheory.mem_ae_iff

#print NonUnitalSubring.mem_comap

#print unitary.mem_iff

#print ValuationSubring.mem_unitGroup_iff

example : ∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul R] {U : R},
  U ∈ unitary R ↔ star U * U = 1 ∧ U * star U = 1:= by 
  aesop (add safe apply Iff.rfl)

#print OrderDual.le_toDual

#check Valuation.IsEquiv.refl
example: ∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀] {v : Valuation R Γ₀},
  Valuation.IsEquiv v v := by
intro R Γ₀ inst inst_1 v 
intro r s
simp_all only



#check Set.mem_smul_set -- not elaborated

#check Seminorm.coe_le_coe
example: ∀ {𝕜 : Type u_3} {E : Type u_7} [inst : SeminormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E]
  {p q : Seminorm 𝕜 E}, p ≤ q ↔ p ≤ q := by
intro 𝕜 E inst inst_1 inst_2 p q
simp_all only



#check Pi.le_def
example: ∀ {ι : Type u} {α : ι → Type v} [inst : (i : ι) → LE (α i)] {x y : (i : ι) → α i}, x ≤ y ↔ ∀ (i : ι), x i ≤ y i := by
intro ι α inst x y
apply Iff.intro 
· intro a i
  apply a 
· intro a
  exact a



#print NatOrdinal.toOrdinal_eq_zero

#check NonUnitalSubalgebra.star_mono -- not elaborated

#print AddSubsemigroup.mk.sizeOf_spec


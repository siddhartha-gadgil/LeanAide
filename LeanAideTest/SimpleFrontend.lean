import LeanAide.SimpleFrontend
import LeanAideCore.Aides
import Mathlib

open LeanAide Lean Meta Elab

open scoped Nat

universe u v w u_1 u_2 u_3 u₁ u₂ u₃

namespace LeanAideTest

/-- info: fun {K} [DivisionSemiring K] {a b} h => Eq.symm (div_add_same h) -/
#guard_msgs in
#eval ppExprM <| elabFrontDefExprM "theorem div_add_one{K : Type u_1} [DivisionSemiring K] {a b : K} (h : b ≠ 0) :
a / b + 1 = (a + b) / b := (div_add_same h).symm" `div_add_one

/--
info: fun R [CommSemiring R] M [AddCommMonoid M] [_root_.Module R M] => LinearMap.BilinMap R M R
-/
#guard_msgs in
#eval ppExprM <| elabFrontDefExprM "{R₁ : Type u_1} →
  [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)" `LinearMap.BilinForm

/--
info: fun V [CategoryTheory.Category.{v, u} V] [CategoryTheory.Limits.HasZeroMorphisms V] α [AddRightCancelSemigroup α]
    [One α] =>
  HomologicalComplex V (ComplexShape.down α)
-/
#guard_msgs in
#eval ppExprM <| elabFrontDefExprM "(C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasCoproducts C] →
      [inst_2 : CategoryTheory.Preadditive C] →
        (R : C) →
          (X : TopCat) →
            [TotallyDisconnectedSpace ↑X] →
              ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
                ChainComplex.alternatingConst.obj (∐ fun x => R)" `ChainComplex

def elabFrontDefTypeValViewM(s: String)(n: Name)(modifyEnv: Bool := false) : MetaM <| String × String := do
  let (type, val) ← elabFrontDefTypeValExprM s n modifyEnv
  let typefmt ←  ppExpr type
  let typeval ←  ppExpr val
  return (typefmt.pretty, typeval.pretty)

/--
info: ("(R : Type u_1) →\n  [inst : CommSemiring R] → (M : Type u_6) → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Type (max u_1 u_6)",
  "fun R [CommSemiring R] M [AddCommMonoid M] [_root_.Module R M] => LinearMap.BilinMap R M R")
-/
#guard_msgs in
#eval elabFrontDefTypeValViewM "{R₁ : Type u_1} →
  [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)" `LinearMap.BilinForm

/--
info: ("∀ {K : Type u_1} [inst : DivisionSemiring K] {a b : K}, b ≠ 0 → a / b + 1 = (a + b) / b",
  "fun {K} [DivisionSemiring K] {a b} h => Eq.symm (div_add_same h)")
-/
#guard_msgs in
#eval elabFrontDefTypeValViewM "theorem div_add_one{K : Type u_1} [DivisionSemiring K] {a b : K} (h : b ≠ 0) :
a / b + 1 = (a + b) / b := (div_add_same h).symm" `div_add_one

/--
info: ("∀ {K : Type u_1} [inst : DivisionSemiring K] {a b : K}, b ≠ 0 → a / b + 1 = (a + b) / b",
  "fun {K} [DivisionSemiring K] {a b} h => Eq.symm (div_add_same h)")
-/
#guard_msgs in
#eval elabFrontDefTypeValViewM "variable {K : Type u_1}
variable [DivisionSemiring K] {a b : K}
theorem div_add_one' (h : b ≠ 0) :
a / b + 1 = (a + b) / b := (div_add_same h).symm" `div_add_one'



/--
info: Messages
---
info: (R : Type u_1) →
  [inst : CommSemiring R] → (M : Type u_6) → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Type (max u_1 u_6)
-/
#guard_msgs in
#eval ppExprM <| elabFrontThmExprM "theorem commutativity (p q : Prop) : p ∧ q → q ∧ p := by
intro h
cases h with
| intro hp hq =>
  constructor
  · exact hq
  · exact hp
"  `LinearMap.BilinForm

/--
info: Messages
---
info: ∀ {K : Type u_1} [inst : DivisionSemiring K] {a b : K}, b ≠ 0 → a / b + 1 = (a + b) / b
-/
#guard_msgs in
#eval ppExprM <| elabFrontThmExprM "theorem div_add_1{K : Type u_1} [DivisionSemiring K] {a b : K} (h : b ≠ 0) :
a / b + 1 = (a + b) / b := (div_add_same h).symm" `div_add_1


elab "#defs" s:str t:ident* : command => Command.liftTermElabM do
  let s := s.getString
  let names := t.map (fun stx => stx.getId)
  let (nameDefs, msgs) ← elabFrontDefsExprM s names.toList
  for (n, v) in nameDefs do
    logInfo s!"Definition: {n} with value {← ppExpr v}"
  for msg in msgs.toList do
    logInfo msg.data

/--
info: Definition: div_add_1 with value fun {K} [DivisionSemiring K] {a b} h => Eq.symm (div_add_same h)
-/
#guard_msgs in
#defs "theorem div_add_1{K : Type u_1} [DivisionSemiring K] {a b : K} (h : b ≠ 0) :
a / b + 1 = (a + b) / b := (div_add_same h).symm" div_add_1 DivisionSemiRing Field

/--
info: Definition: newDef with value fun {𝕜} [NontriviallyNormedField 𝕜] {H} [TopologicalSpace H] {E} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I} {G}
    [TopologicalSpace G] [ChartedSpace H G] [Group G] {a} [LieGroup I ⊤ G] [ENat.LEInfty a] =>
  sorry
---
info: declaration uses 'sorry'
-/
#guard_msgs in
#defs "instance newDef{𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {H : Type u_2} [TopologicalSpace H] {E : Type u_3} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type u_4} [TopologicalSpace G] [ChartedSpace H G] [Group G] {a : WithTop ℕ∞} [LieGroup I (↑⊤) G] [h : ENat.LEInfty a] :
LieGroup I a G := by sorry" ModelWithCorners newDef LieGroup withTop

/--
info: Definition: ChainComplex with value fun V [CategoryTheory.Category.{v, u} V] [CategoryTheory.Limits.HasZeroMorphisms V] α [AddRightCancelSemigroup α]
    [One α] =>
  HomologicalComplex V (ComplexShape.down α)
---
info: Definition: newDef2 with value sorry
---
info: declaration uses 'sorry'
-/
#guard_msgs in
#defs "def newDef2 : ∀ (C : Type u)
  [inst : CategoryTheory.Category.{v, u} C]
    [inst_1 : CategoryTheory.Limits.HasCoproducts C]
      [inst_2 : CategoryTheory.Preadditive C]
        (R : C)
          (X : TopCat)
            [TotallyDisconnectedSpace ↑X],
              ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
                ChainComplex.alternatingConst.obj (∐ fun (_ : X) => R):= by sorry" ChainComplex newDef2

elab "#defs_with_prefix" s:str t:ident : command => Command.liftTermElabM do
  let s := s.getString
  let (nameDefs, msgs) ← elabFrontDefsExprAtM s t.getId
  for (n, v) in nameDefs do
    logInfo s!"Definition: {n} with value {← ppExpr v}"
  for msg in msgs.toList do
    logInfo msg.data

/-- info: ok: ∀ {G : Type u} [inst : Group G] (a : G) (n : ℕ), a ^ n = 1 → ∃ m, n = m * orderOf a -/
#guard_msgs in
#eval ppExprM? <| elabFrontTheoremExprMStrict "∀ {G : Type u} [inst : Group G] (a : G) (n : ℕ), a ^ n = 1 → ∃ m, n = m * orderOf a"

/-- info: ok: ∀ (n : ℕ), n ≤ n + 1 -/
#guard_msgs in
#eval ppExprM? <| elabFrontTheoremExprMStrict "∀ n: Nat, n ≤ n + 1"

/-- info: ok: ∀ {G : Type u} [inst : Group G] (a : G) (n : ℕ), a ^ n = 1 → ∃ m, n = m * orderOf a -/
#guard_msgs in
#eval ppExprM? <| elabFrontTheoremExprM "∀ {G : Type u} [inst : Group G] (a : G) (n : ℕ), a ^ n = 1 → ∃ m, n = m * orderOf a"


/--
info: ok: (C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasCoproducts C] →
      [inst_2 : CategoryTheory.Preadditive C] →
        (R : C) →
          (X : TopCat) →
            [TotallyDisconnectedSpace ↑X] →
              ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
                ChainComplex.alternatingConst.obj (∐ fun x => R)
-/
#guard_msgs in
#eval ppExprM? <| elabFrontTheoremExprM "∀ (C : Type u)
  [inst : CategoryTheory.Category.{v, u} C]
    [inst_1 : CategoryTheory.Limits.HasCoproducts C]
      [inst_2 : CategoryTheory.Preadditive C]
        (R : C)
          (X : TopCat)
            [TotallyDisconnectedSpace ↑X],
              ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
                ChainComplex.alternatingConst.obj (∐ fun (_ : X) => R)"

/-- info: ok: ℕ → ℕ -/
#guard_msgs in
#eval ppExprM? <| elabFrontTypeExprM "Nat → Nat"

/--
info: ok: (C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasCoproducts C] →
      [inst_2 : CategoryTheory.Preadditive C] →
        (R : C) →
          (X : TopCat) →
            [TotallyDisconnectedSpace ↑X] →
              ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
                ChainComplex.alternatingConst.obj (∐ fun x => R)
-/
#guard_msgs in
#eval ppExprM? <| elabFrontTypeExprM "∀ (C : Type u)
  [inst : CategoryTheory.Category.{v, u} C]
    [inst_1 : CategoryTheory.Limits.HasCoproducts C]
      [inst_2 : CategoryTheory.Preadditive C]
        (R : C)
          (X : TopCat)
            [TotallyDisconnectedSpace ↑X],
              ((AlgebraicTopology.singularChainComplexFunctor C).obj R).obj X ≅
                ChainComplex.alternatingConst.obj (∐ fun (_ : X) => R)"

/-- info: [] -/
#guard_msgs in
#eval checkTermElabFrontM "(R : Type u_1) →
  [inst : CommSemiring R] → (M : Type u_6) → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Type (max u_1 u_6)"

/-- info: [] -/
#guard_msgs in
#eval checkTypeElabFrontM "(R : Type u_1) →
  [inst : CommSemiring R] → (M : Type u_6) → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Type (max u_1 u_6)"

/-- info: [] -/
#guard_msgs in
#eval checkTermElabFrontM "∀ {G : Type u} [inst : Group G] (a : G) (n : ℕ), a ^ n = 1 → ∃ m, n = m * orderOf a"

/-- info: [] -/
#guard_msgs in
#eval checkTypeElabFrontM "∀ {G : Type u} [inst : Group G] (a : G) (n : ℕ), a ^ n = 1 → ∃ m, n = m * orderOf a"

/-- info: #[`x] -/
#guard_msgs in
#eval newDeclarations "def x : Nat := 0"

/-- info: #[`newTheorem] -/
#guard_msgs in
#eval newDeclarations "def newTheorem (G : Type u) [Group G] : Type u := G ⧸ commutator G"

/-- info: #[`M, `x, `newTheorem] -/
#guard_msgs in
#eval newDeclarations "def M {R₁ : Type u_1} [CommSemiring R₁] {n : Type u_5} [Fintype n] (M : Matrix n n R₁) : LinearMap.BilinForm R₁ (n → R₁) :=
  Matrix.toLinearMap₂'Aux _ _ M
  def newTheorem (G : Type u) [Group G] : Type u := G ⧸ commutator G
  def x : Nat := 0"

elab "#new_defs" s:str : command => Command.liftTermElabM do
  let s := s.getString
  let (nameDefs, msgs) ← elabFrontDefsNewExprM s
  for (n, v) in nameDefs do
    logInfo s!"New definition: {n} with value {← ppExpr v}"
  for msg in msgs.toList do
    logInfo msg.data

/--
info: New definition: IsContinuous with value fun {X} {Y} [TopologicalSpace X] [TopologicalSpace Y] Φ => ∀ (s : Set Y), IsOpen s → IsOpen (Φ ⁻¹' s)
-/
#guard_msgs in
#new_defs "open Nat def IsContinuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (Φ : X → Y) : Prop := ∀ s : Set Y, IsOpen s → IsOpen (Φ⁻¹' s)"


/-- info: New definition: y with value 1 -/
#guard_msgs in
#new_defs "open Nat def y : Nat := 1"

/--
info: New definition: M with value fun {R₁} [CommSemiring R₁] {n} [Fintype n] M => Matrix.toLinearMap₂'Aux (RingHom.id R₁) (RingHom.id R₁) M
-/
#guard_msgs in
#new_defs "def M {R₁ : Type u_1} [CommSemiring R₁] {n : Type u_5} [Fintype n] (M : Matrix n n R₁) : LinearMap.BilinForm R₁ (n → R₁) :=
  Matrix.toLinearMap₂'Aux _ _ M"


/--
info: New definition: mWCs with value fun 𝕜 [NontriviallyNormedField 𝕜] E [inst_1 : NormedAddCommGroup E] [NormedSpace 𝕜 E] =>
  ModelWithCorners.of_target_univ 𝕜 (PartialEquiv.refl E) (@mWCs._proof_1 E) (@mWCs._proof_2 E)
    (@mWCs._proof_3 E inst_1) (@mWCs._proof_3 E inst_1)
---
info: New definition: MWc with value fun 𝕜 [inst : NontriviallyNormedField 𝕜] {E} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {H}
    [TopologicalSpace H] f hsource htarget hcont hcont_inv =>
  { toPartialEquiv := f, source_eq := hsource,
    convex_range' := @MWc._proof_1 𝕜 inst E inst_1 inst_2 H f hsource htarget,
    nonempty_interior' := @MWc._proof_2 E inst_1 H f hsource htarget, continuous_toFun := hcont,
    continuous_invFun := hcont_inv }
-/
#guard_msgs in
#new_defs "def MWc (𝕜 : Type u_1) [NontriviallyNormedField 𝕜] {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type u_3} [TopologicalSpace H] (f : PartialEquiv H E) (hsource : f.source = Set.univ) (htarget : f.target = Set.univ) (hcont : Continuous ↑f) (hcont_inv : Continuous ↑f.symm) :
ModelWithCorners 𝕜 E H where
  toPartialEquiv := f
  source_eq := hsource
  convex_range' := by
    have : Set.range f = f.target := by rw [← f.image_source_eq_target, hsource, Set.image_univ.symm]
    simp only [this, htarget, dite_else_true]
    intro h
    letI := h.rclike 𝕜
    letI := NormedSpace.restrictScalars ℝ 𝕜 E
    exact convex_univ
  nonempty_interior' := by
    have : Set.range f = f.target := by rw [← f.image_source_eq_target, hsource, Set.image_univ.symm]
    simp [this, htarget]

    def mWCs (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : ModelWithCorners 𝕜 E E :=
  ModelWithCorners.of_target_univ 𝕜 (PartialEquiv.refl E) rfl rfl continuous_id continuous_id
    "
/--
info: New definition: MWCReqT with value fun {𝕜} {E} {H} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] I =>
  Eq.mpr
    (id
      (congrArg (fun _a => Set.range ↑I.toPartialEquiv = _a)
        (Eq.symm (PartialEquiv.image_source_eq_target I.toPartialEquiv))))
    (Eq.mpr (id (congrArg (fun _a => Set.range ↑I.toPartialEquiv = ↑I.toPartialEquiv '' _a) I.source_eq))
      (Eq.mpr (id (congrArg (fun _a => _a = ↑I.toPartialEquiv '' Set.univ) (Eq.symm Set.image_univ)))
        (Eq.refl (↑I.toPartialEquiv '' Set.univ))))
-/
#guard_msgs in
#new_defs "theorem MWCReqT{𝕜 : Type u_1} {E : Type u_2} {H : Type u_3} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) :
Set.range ↑I.toPartialEquiv = I.target := by
  rw [← I.image_source_eq_target, I.source_eq, Set.image_univ.symm]"

/--
info: New definition: CMap with value fun {C} [CategoryTheory.Category.{v₁, u₁} C] {D} [CategoryTheory.Category.{v₂, u₂} D] {E}
    [CategoryTheory.Category.{v₃, u₃} E] F G {X Y} f =>
  rfl
---
info: New definition: CTFC with value fun {C} [CategoryTheory.Category.{v₁, u₁} C] {D} [CategoryTheory.Category.{v₂, u₂} D] F {X Y} {f g} h =>
  Eq.mpr (id (congrArg (fun _a => F.map _a = F.map g) h)) (Eq.refl (F.map g))
-/
#guard_msgs in
#new_defs "open CategoryTheory theorem CTFC {C : Type u₁} [CategoryTheory.Category.{v₁ ,u₁} C] {D : Type u₂} [Category.{v₂, u₂} D] (F : C ⥤ D) {X Y : C} {f g : X ⟶ Y} (h : f = g) :
F.map f = F.map g := by
 rw[h]
theorem CMap {C : Type u₁} [Category.{v₁, u₁} C] {D : Type u₂} [Category.{v₂, u₂} D] {E : Type u₃} [Category.{v₃, u₃} E](F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (F ⋙ G).map f = G.map (F.map f) := rfl"

end LeanAideTest

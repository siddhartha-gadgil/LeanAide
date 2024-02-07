import Mathlib

#check List.sum

#help term

example (l: ∀n : ℕ , n > 10 → n > 5): (∃ (n : ℕ), n > 10) →  ∃n,   n >  5 := by
  intro h
  apply Exists.intro
  let ⟨n, hn⟩ := h
  apply l
  swap


  sorry
  sorry

structure NN where
  n : Nat

structure MM extends NN where
  m : Nat

def getN (n: NN) : Nat := n.n

def m : MM := {n := 3, m := 4}

#eval getN m.toNN

#eval 3 ∣ 4

def listType : Nat → Type
  | 0 => List Unit
  | n + 1 => List (listType n)

def listify : (n : Nat) → listType n
  | 0 => []
  | n + 1 => [listify n]

theorem nat_from_constructors (n: Nat) :
  n = Nat.zero ∨ ∃ m, n = Nat.succ m := by
  cases n with
  | zero => left; rfl
  | succ m => right; use m

#reduce (3: Nat)
set_option pp.all true in
#reduce Nat.succ <| Nat.succ Nat.zero
set_option pp.all true in
#reduce (0 : Nat)
#check String
example (n: Nat): (instOfNatNat n).1 = n := rfl
#check Nat.Linear.Poly.cancel
#check Nat.Linear.ExprCnstr.denote_toNormPoly

#print ULift.up
#print ULift.down
#check ULift.down -- {α : Type s} → ULift.{r, s} α → α
#check ULift
#check ULift.up_down
#check False.elim
#print False.elim
#check @False.rec -- (motive : False → Sort u_1) → (t : False) → motive t
#check False
#check @And.rec
#check @Or.rec
#check PUnit.unit

#check @True.rec

#check Fin.mk -- {n : ℕ} → (val : ℕ) → val < n → Fin n

inductive ArrayTree where
  | leaf (n: Nat) : ArrayTree
  | node (branches: Array ArrayTree) : ArrayTree

#check ArrayTree.rec /- {motive_1 : ArrayTree → Sort u} →
  {motive_2 : Array ArrayTree → Sort u} →
    {motive_3 : List ArrayTree → Sort u} →
      ((n : ℕ) → motive_1 (ArrayTree.leaf n)) →
        ((branches : Array ArrayTree) → motive_2 branches → motive_1 (ArrayTree.node branches)) →
          ((data : List ArrayTree) → motive_3 data → motive_2 { data := data }) →
            motive_3 [] →
              ((head : ArrayTree) → (tail : List ArrayTree) → motive_1 head → motive_3 tail → motive_3 (head :: tail)) →
                (t : ArrayTree) → motive_1 t -/

#check List.rec /- {α : Type u} →
  {motive : List α → Sort u_1} →
    motive [] →
      ((head : α) → (tail : List α) → motive tail → motive (head :: tail)) → (l : List α) → motive l -/

#check Array.rec -- {α : Type u} → {motive : Array α → Sort u_1} → ((data : List α) → motive { data := data }) → (t : Array α) → motive t

structure Gather where
  data : List Nat
  num  : Nat
  rk: String

#check Gather.rec
#check Nat.rec

#check Lean.Syntax.rec /- {motive_1 : Lean.Syntax → Sort u} →
  {motive_2 : Array Lean.Syntax → Sort u} →
    {motive_3 : List Lean.Syntax → Sort u} →
      motive_1 Lean.Syntax.missing →
        ((info : Lean.SourceInfo) →
            (kind : Lean.SyntaxNodeKind) →
              (args : Array Lean.Syntax) → motive_2 args → motive_1 (Lean.Syntax.node info kind args)) →
          ((info : Lean.SourceInfo) → (val : String) → motive_1 (Lean.Syntax.atom info val)) →
            ((info : Lean.SourceInfo) →
                (rawVal : Substring) →
                  (val : Lean.Name) →
                    (preresolved : List Lean.Syntax.Preresolved) →
                      motive_1 (Lean.Syntax.ident info rawVal val preresolved)) →
              ((data : List Lean.Syntax) → motive_3 data → motive_2 { data := data }) →
                motive_3 [] →
                  ((head : Lean.Syntax) →
                      (tail : List Lean.Syntax) → motive_1 head → motive_3 tail → motive_3 (head :: tail)) →
                    (t : Lean.Syntax) → motive_1 t-/

universe l

abbrev recCandidate := ∀ {motive : (∀ (c : @Lean.Syntax) , Sort l)}
  {motive_1 : (∀ (c : @Array.{0} @Lean.Syntax) , Sort l)}
  {motive_2 : (∀ (c : @List.{0} @Lean.Syntax) , Sort l)}
  (h : motive @Lean.Syntax.missing)
  (h_0 :
    (∀ (info : @Lean.SourceInfo) (kind : @Lean.SyntaxNodeKind)
      (args : @Array.{0} @Lean.Syntax) (ih : motive_1 args) , motive
      (@Lean.Syntax.node info kind args)))
  (h_1 :
    (∀ (info : @Lean.SourceInfo) (val : @String) , motive
      (@Lean.Syntax.atom info val)))
  (h_2 :
    (∀ (info : @Lean.SourceInfo) (rawVal : @Substring) (val : @Lean.Name)
      (preresolved : @List.{0} @Lean.Syntax.Preresolved) , motive
      (@Lean.Syntax.ident info rawVal val preresolved)))
  (h_3 :
    (∀ (data : @List.{0} @Lean.Syntax) (ih : motive_2 data) , motive_1
      (@Array.mk.{0} @Lean.Syntax data)))
  (h_4 : motive_2 (@List.nil.{0} @Lean.Syntax))
  (h_5 :
    (∀ (head : @Lean.Syntax) (tail : @List.{0} @Lean.Syntax) (ih : motive head)
      (ih_0 : motive_2 tail) , motive_2
      (@List.cons.{0} @Lean.Syntax head tail))) (x : @Lean.Syntax) , motive x

noncomputable example : recCandidate := Lean.Syntax.rec /- success ⌣ -/

example : @LT.lt.{0} @Nat @instLTNat (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127))
  @UInt32.size := @of_decide_eq_true
  (@LT.lt.{0} @Nat @instLTNat (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127))
    @UInt32.size)
  (@Nat.decLt (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127)) @UInt32.size)
  (@Eq.refl.{1} @Bool @Bool.true)

variable (recEg : recCandidate)

def ltType := (Decidable.decide (LT.lt (OfNat.ofNat 127) UInt32.size))

#reduce ltType - true
def checkLt := Decidable.decide (3 ≤ 5 )
#reduce checkLt -- true
#check Nat.decLt

theorem tt_eq_tt : true = true := rfl
set_option pp.all true in
#reduce tt_eq_tt

#check Nat.le_of_ble_eq_true -- ∀ {n m : ℕ}, Nat.ble n m = true → n ≤ m
#check Nat.not_le_of_not_ble_eq_true -- ∀ {n m : ℕ}, ¬Nat.ble n m = true → ¬n ≤ m

example : 3 ≤ 5  := @Nat.le_of_ble_eq_true 3 5 (@Eq.refl.{1} @Bool @Bool.true)
-- example : ¬6 ≤ 5 := @Nat.not_le_of_not_ble_eq_true 6 5 Bool.ff_ne_tt

example : @Decidable (3 ≤ 5)  :=
  @Decidable.isTrue (3 ≤ 5) <| @Nat.le_of_ble_eq_true 3 5 (@Eq.refl.{1} @Bool @Bool.true)
-- example : @Decidable (6 ≤ 5) :=
--   @Decidable.isFalse (6 ≤ 5) <| @Nat.not_le_of_not_ble_eq_true 6 5 @Bool.ff_ne_tt

#check Nat.Linear.ExprCnstr.denote_toNormPoly
-- set_option maxRecDepth 10000 in
-- #reduce Nat.Linear.ExprCnstr.denote_toNormPoly

#check Nat.Linear.Expr.var
#check Nat.Linear.PolyCnstr.isValid
#check @Bool.rec
#check Nat.Linear.PolyCnstr.eq
#check @Prod.rec
#check Nat.Linear.Poly.cancel


open RealInnerProductSpace
example: ∀ {k : ℕ} (x : EuclideanSpace ℝ (Fin k)), 2 ≤ k → ∃ y : EuclideanSpace ℝ (Fin k), y ≠ 0 ∧ (⟪x, y⟫ = 0) := by sorry

#check RingHom.map_sum

open BigOperators
example: ∀ {C : ℕ → ℝ},
  (∑ i in Finset.range (n + 1), C i / (↑i + 1)) = 0 →
      ∃ x, (Finset.sum (Finset.range (n + 1)) fun i => C i * x ^ i) = 0 := by sorry

#check Finset.sum
#check RingHom.map_sum

set_option pp.all true in
#print Nat.Linear.ExprCnstr.denote_toNormPoly

#check Nat.Linear.ExprCnstr.denote_toNormPoly
#check TopologicalSpace

example : false ≠ true := by
  exact Bool.not_false'

#check Lean.TSyntaxArray.raw
#check Lean.Syntax.mkApp
#check Char.utf8Size.proof_1
#print Char.utf8Size.proof_1
#check UInt32.size
#check Nat.le
#check Decidable.rec /- {p : Prop} →
  {motive : Decidable p → Sort u} →
    ((h : ¬p) → motive (isFalse h)) → ((h : p) → motive (isTrue h)) → (t : Decidable p) → motive t -/

inductive ListTree where
  | leaf (n: Nat) : ListTree
  | node (rec: List ListTree) : ListTree

#check ListTree.rec /- {motive_1 : ListTree → Sort u} →
  {motive_2 : List ListTree → Sort u} →
    ((n : ℕ) → motive_1 (ListTree.leaf n)) →
      ((rec : List ListTree) → motive_2 rec → motive_1 (ListTree.node rec)) →
        motive_2 [] →
          ((head : ListTree) → (tail : List ListTree) → motive_1 head → motive_2 tail → motive_2 (head :: tail)) →
            (t : ListTree) → motive_1 t -/

#print ListTree.rec

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons (n: ℕ)(head : α) (tail : Vec α n) : Vec α  (n + 1)

inductive VectorTree where
  | leaf (n: Nat) : VectorTree
  | node (n: ℕ) (branches: Vec VectorTree n) : VectorTree


#check VectorTree.rec /-
{motive_1 : VectorTree → Sort u} →
  {motive_2 : (a : ℕ) → Vec VectorTree a → Sort u} →
    ((n : ℕ) → motive_1 (VectorTree.leaf n)) →
      ((n : ℕ) → (branches : Vec VectorTree n) → motive_2 n branches → motive_1 (VectorTree.node n branches)) →
        motive_2 0 Vec.nil →
          ((n : ℕ) →
              (head : VectorTree) →
                (tail : Vec VectorTree n) → motive_1 head → motive_2 n tail → motive_2 (n + 1) (Vec.cons n head tail)) →
            (t : VectorTree) → motive_1 t
-/

-- inductive VectorTree where
--   | leaf (n: Nat) : VectorTree
--   | node (n: ℕ) (branches: Vector VectorTree n) : VectorTree


inductive MyList (α : Type u) where
  | nil : MyList α
  | cons (head : α) (tail : MyList α) : MyList α

inductive MyListTree (α : Type u) where
  | leaf (a: α) : MyListTree α
  | node (children: MyList (MyListTree α))(family : Nat → List (MyListTree α )) : MyListTree α

#check MyListTree.rec /- {α : Type u} →
  {motive_1 : MyListTree α → Sort u_1} →
    {motive_2 : MyList (MyListTree α) → Sort u_1} →
      {motive_3 : List (MyListTree α) → Sort u_1} →
        ((a : α) → motive_1 (MyListTree.leaf a)) →
          ((children : MyList (MyListTree α)) →
              (family : ℕ → List (MyListTree α)) →
                motive_2 children → ((a : ℕ) → motive_3 (family a)) → motive_1 (MyListTree.node children family)) →
            motive_2 MyList.nil →
              ((head : MyListTree α) →
                  (tail : MyList (MyListTree α)) → motive_1 head → motive_2 tail → motive_2 (MyList.cons head tail)) →
                motive_3 [] →
                  ((head : MyListTree α) →
                      (tail : List (MyListTree α)) → motive_1 head → motive_3 tail → motive_3 (head :: tail)) →
                    (t : MyListTree α) → motive_1 t
      -/

inductive NatTree where
  | leaf (n: Nat) : NatTree
  | node (rec:  Nat →  NatTree) : NatTree

#check NatTree.rec /- {motive : NatTree → Sort u} →
  ((n : ℕ) → motive (NatTree.leaf n)) →
    ((rec : ℕ → NatTree) → ((a : ℕ) → motive (rec a)) → motive (NatTree.node rec)) → (t : NatTree) → motive t
-/

#check Array.rec

#check Nat.rec

example : forall {a : ℝ} {f : ℝ → ℝ} {M₀ M₁ M₂ : ℝ},  Differentiable ℝ f → Differentiable ℝ (deriv f) →    (∀ x, a < x → abs (f x) ≤ M₀) →      (∀ x, a < x → abs (deriv f x) ≤ M₁) →        (∀ x, a < x → abs (deriv^[2] f x) ≤ M₂) → M₁ ^ 2 ≤ 4 * M₀ * M₂ := by sorry

example : ∀ {M : Type u_1} [inst : MetricSpace M],  ∃ (f : Set M → Set M), (∀ (U : Set M), IsOpen U → IsClosed (f U)) ∧ (∀ (K : Set M), IsClosed K → IsOpen (f K)) ∧    (∀ (U₁ U₂ : Set M), IsOpen U₁ → IsOpen U₂ → f U₁ = f U₂ → U₁ = U₂) ∧    (∀ (K₁ K₂ : Set M), IsClosed K₁ → IsClosed K₂ → f K₁ = f K₂ → K₁ = K₂) := by sorry

example (x : ℝ) : ‖x‖ = 0 := sorry

example (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) : ‖x + y‖^2 + ‖x - y‖^2 = 2*‖x‖ ^2 + 2*‖y‖^2 := by sorry

example : ∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H],  Monoid.IsTorsionFree (G × H) → Monoid.IsTorsionFree G ∧ Monoid.IsTorsionFree H := by sorry

example  (G : Type*) (H : Type*) [Group G] [Group H] (gh_torsion_free : ∀ g : G × H, g ≠ 1 → ∃ n : ℤ, g ^ n ≠ 1) : (∀ (g : G), g ≠ 1 → ∃ n : ℤ, g ^ n ≠ 1) ∧ (∀ (h : H), h ≠ 1 → ∃ n : ℤ, h ^ n ≠ 1) := by sorry

example : PythagoreanTriple 3 4 5 := by sorry

example : ∀ {α : Type u} [t : MetricSpace α] [inst : TopologicalSpace.SeparableSpace α] {s : Set α},  IsClosed s → ∃ t₁ t₂, Perfect t₁ ∧ Set.Countable t₂ ∧ s = t₁ ∪ t₂ := by sorry

example : forall {α : Type u} [inst : PseudoMetricSpace α] [inst_1 : CompleteSpace α] {f : ℕ → Set α},  (∀ n, IsOpen (f n)) → (∀ n, Dense (f n)) → Set.Nonempty (⋂ n, f n)   := by sorry

example : ∀ {Y : Type u_1} [inst : TopologicalSpace Y] [inst_1 : NormalSpace Y] {s : Set Y} (f : C(↑s, ℝ)),  IsClosed s → ∃ g, ContinuousMap.restrict s g = f  := by sorry

example: forall {Y : Type u_1} [inst : TopologicalSpace Y] [inst_1 : NormalSpace Y] {E : Set Y} (f : C(↑E, ℝ)),  IsClosed E → ∃ g, ContinuousMap.restrict E g = f := by sorry

#check Complex.abs

example : ∀ {n : ℕ}, n * n % 2 = 0 → n % 2 = 0 := by sorry

open BigOperators
example (n : ℕ) (f : ℕ → ℂ) : Complex.abs (∑ i in Finset.range n, f i) ≤ ∑ i in Finset.range n, Complex.abs (f i) := by sorry

example : 1 = 1 := by
  let c := 1
  show c = 1
  rfl

example : ∀ x: ℕ, x + 3 = 3 + x := by
  conv =>
    enter [x, 2]
    rw [Nat.add_comm]
  intro _
  rfl

example (f g : ℕ → ℕ): f = g → ∀ x: ℕ, f (x + 3) = g (3 + x) := by
  conv =>
    intro eqn x
    arg 1
    rw [eqn]
    arg 1
    rw [Nat.add_comm]
  simp

example (f g : ℕ → ℕ): f = g → ∀ x: ℕ, f (x + 3) = g (3 + x) := by
  conv =>
    enter [eqn, x, 2]
    rw [← eqn]
  conv =>
    enter [eqn, x, 1]
    rw [Nat.add_comm]
  simp

example (f g : ℕ →   ℕ → ℕ): f = g → ∀ x: ℕ,
    f (x + 3) (4 + x) = g (3 + x) (x + 4) := by
  conv =>
    intro
    enter [x, 1, 2]
    rw [Nat.add_comm]
  conv =>
    intro
    enter [x, 1, 1]
    rw [Nat.add_comm]
  conv =>
    enter [eqn, x, 2]
    rw [← eqn]
  simp

example : 1 = 1 := by
  let _ := 3
  rfl

example : (n: ℕ) → let m := n + 1 ; n + 1 = m := by simp

#check Eq.mp

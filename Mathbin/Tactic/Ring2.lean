/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Tactic.Ring
import Mathbin.Data.Num.Lemmas
import Mathbin.Data.Tree

/-!
# ring2

An experimental variant on the `ring` tactic that uses computational
reflection instead of proof generation. Useful for kernel benchmarking.
-/


namespace Tree

/-- `(reflect' t u α)` quasiquotes a tree `(t: tree expr)` of quoted
values of type `α` at level `u` into an `expr` which reifies to a `tree α`
containing the reifications of the `expr`s from the original `t`. -/
protected unsafe def reflect' (u : level) (α : expr) : Tree expr → expr
  | Tree.nil => (expr.const `` Tree.nil [u] : expr) α
  | Tree.node a t₁ t₂ => (expr.const `` Tree.node [u] : expr) α a t₁.reflect' t₂.reflect'

/-- Returns an element indexed by `n`, or zero if `n` isn't a valid index.
See `tree.get`. -/
protected def getOrZero {α} [Zero α] (t : Tree α) (n : PosNum) : α :=
  t.getOrElse n 0

end Tree

namespace Tactic.Ring2

/-- A reflected/meta representation of an expression in a commutative
semiring. This representation is a direct translation of such
expressions - see `horner_expr` for a normal form. -/
inductive CsringExpr/- (atom n) is an opaque element of the csring. For example,
a local variable in the context. n indexes into a storage
of such atoms - a `tree α`. -/

  | atom : PosNum → csring_expr/- (const n) is technically the csring's one, added n times.
Or the zero if n is 0. -/

  | const : Num → csring_expr
  | add : csring_expr → csring_expr → csring_expr
  | mul : csring_expr → csring_expr → csring_expr
  | pow : csring_expr → Num → csring_expr
  deriving has_reflect

namespace CsringExpr

instance : Inhabited CsringExpr :=
  ⟨const 0⟩

/-- Evaluates a reflected `csring_expr` into an element of the
original `comm_semiring` type `α`, retrieving opaque elements
(atoms) from the tree `t`. -/
def eval {α} [CommSemiringₓ α] (t : Tree α) : CsringExpr → α
  | atom n => t.getOrZero n
  | const n => n
  | add x y => eval x + eval y
  | mul x y => eval x * eval y
  | pow x n => eval x ^ (n : ℕ)

end CsringExpr

/-- An efficient representation of expressions in a commutative
semiring using the sparse Horner normal form. This type admits
non-optimal instantiations (e.g. `P` can be represented as `P+0+0`),
so to get good performance out of it, care must be taken to maintain
an optimal, *canonical* form. -/
inductive HornerExpr/- (const n) is a constant n in the csring, similarly to the same
constructor in `csring_expr`. This one, however, can be negative. -/

  | const : Znum → horner_expr/- (horner a x n b) is a*xⁿ + b, where x is the x-th atom
in the atom tree. -/

  | horner : horner_expr → PosNum → Num → horner_expr → horner_expr
  deriving DecidableEq

namespace HornerExpr

/-- True iff the `horner_expr` argument is a valid `csring_expr`.
For that to be the case, all its constants must be non-negative. -/
def IsCs : HornerExpr → Prop
  | const n => ∃ m : Num, n = m.toZnum
  | horner a x n b => is_cs a ∧ is_cs b

instance : Zero HornerExpr :=
  ⟨const 0⟩

instance : One HornerExpr :=
  ⟨const 1⟩

instance : Inhabited HornerExpr :=
  ⟨0⟩

/-- Represent a `csring_expr.atom` in Horner form. -/
def atom (n : PosNum) : HornerExpr :=
  horner 1 n 1 0

def toString : HornerExpr → Stringₓ
  | const n => reprₓ n
  | horner a x n b => "(" ++ toString a ++ ") * x" ++ reprₓ x ++ "^" ++ reprₓ n ++ " + " ++ toString b

instance : HasToString HornerExpr :=
  ⟨toString⟩

/-- Alternative constructor for (horner a x n b) which maintains canonical
form by simplifying special cases of `a`. -/
def horner' (a : HornerExpr) (x : PosNum) (n : Num) (b : HornerExpr) : HornerExpr :=
  match a with
  | const q => if q = 0 then b else horner a x n b
  | horner a₁ x₁ n₁ b₁ => if x₁ = x ∧ b₁ = 0 then horner a₁ x (n₁ + n) b else horner a x n b

def addConst (k : Znum) (e : HornerExpr) : HornerExpr :=
  if k = 0 then e
  else by
    induction' e with n a x n b A B
    · exact const (k + n)
      
    · exact horner a x n B
      

def addAux (a₁ : HornerExpr) (A₁ : HornerExpr → HornerExpr) (x₁ : PosNum) :
    HornerExpr → Num → HornerExpr → (HornerExpr → HornerExpr) → HornerExpr
  | const n₂, n₁, b₁, B₁ => addConst n₂ (horner a₁ x₁ n₁ b₁)
  | horner a₂ x₂ n₂ b₂, n₁, b₁, B₁ =>
    let e₂ := horner a₂ x₂ n₂ b₂
    match PosNum.cmp x₁ x₂ with
    | Ordering.lt => horner a₁ x₁ n₁ (B₁ e₂)
    | Ordering.gt => horner a₂ x₂ n₂ (add_aux b₂ n₁ b₁ B₁)
    | Ordering.eq =>
      match Num.sub' n₁ n₂ with
      | Znum.zero => horner' (A₁ a₂) x₁ n₁ (B₁ b₂)
      | Znum.pos k => horner (add_aux a₂ k 0 id) x₁ n₂ (B₁ b₂)
      | Znum.neg k => horner (A₁ (horner a₂ x₁ k 0)) x₁ n₁ (B₁ b₂)

def add : HornerExpr → HornerExpr → HornerExpr
  | const n₁, e₂ => addConst n₁ e₂
  | horner a₁ x₁ n₁ b₁, e₂ => addAux a₁ (add a₁) x₁ e₂ n₁ b₁ (add b₁)

/-begin
  induction e₁ with n₁ a₁ x₁ n₁ b₁ A₁ B₁ generalizing e₂,
  { exact add_const n₁ e₂ },
  exact match e₂ with e₂ := begin
    induction e₂ with n₂ a₂ x₂ n₂ b₂ A₂ B₂ generalizing n₁ b₁;
    let e₁ := horner a₁ x₁ n₁ b₁,
    { exact add_const n₂ e₁ },
    let e₂ := horner a₂ x₂ n₂ b₂,
    exact match pos_num.cmp x₁ x₂ with
    | ordering.lt := horner a₁ x₁ n₁ (B₁ e₂)
    | ordering.gt := horner a₂ x₂ n₂ (B₂ n₁ b₁)
    | ordering.eq :=
      match num.sub' n₁ n₂ with
      | znum.zero := horner' (A₁ a₂) x₁ n₁ (B₁ b₂)
      | (znum.pos k) := horner (A₂ k 0) x₁ n₂ (B₁ b₂)
      | (znum.neg k) := horner (A₁ (horner a₂ x₁ k 0)) x₁ n₁ (B₁ b₂)
      end
    end
  end end
end-/
def neg (e : HornerExpr) : HornerExpr := by
  induction' e with n a x n b A B
  · exact const (-n)
    
  · exact horner A x n B
    

def mulConst (k : Znum) (e : HornerExpr) : HornerExpr :=
  if k = 0 then 0
  else
    if k = 1 then e
    else by
      induction' e with n a x n b A B
      · exact const (n * k)
        
      · exact horner A x n B
        

def mulAux (a₁ x₁ n₁ b₁) (A₁ B₁ : HornerExpr → HornerExpr) : HornerExpr → HornerExpr
  | const n₂ => mulConst n₂ (horner a₁ x₁ n₁ b₁)
  | e₂@(horner a₂ x₂ n₂ b₂) =>
    match PosNum.cmp x₁ x₂ with
    | Ordering.lt => horner (A₁ e₂) x₁ n₁ (B₁ e₂)
    | Ordering.gt => horner (mul_aux a₂) x₂ n₂ (mul_aux b₂)
    | Ordering.eq =>
      let haa := horner' (mul_aux a₂) x₁ n₂ 0
      if b₂ = 0 then haa else haa.add (horner (A₁ b₂) x₁ n₁ (B₁ b₂))

def mul : HornerExpr → HornerExpr → HornerExpr
  | const n₁ => mulConst n₁
  | horner a₁ x₁ n₁ b₁ => mulAux a₁ x₁ n₁ b₁ (mul a₁) (mul b₁)

/-begin
  induction e₁ with n₁ a₁ x₁ n₁ b₁ A₁ B₁ generalizing e₂,
  { exact mul_const n₁ e₂ },
  induction e₂ with n₂ a₂ x₂ n₂ b₂ A₂ B₂;
  let e₁ := horner a₁ x₁ n₁ b₁,
  { exact mul_const n₂ e₁ },
  let e₂ := horner a₂ x₂ n₂ b₂,
  cases pos_num.cmp x₁ x₂,
  { exact horner (A₁ e₂) x₁ n₁ (B₁ e₂) },
  { let haa := horner' A₂ x₁ n₂ 0,
    exact if b₂ = 0 then haa else
      haa.add (horner (A₁ b₂) x₁ n₁ (B₁ b₂)) },
  { exact horner A₂ x₂ n₂ B₂ }
end-/
instance : Add HornerExpr :=
  ⟨add⟩

instance : Neg HornerExpr :=
  ⟨neg⟩

instance : Mul HornerExpr :=
  ⟨mul⟩

def pow (e : HornerExpr) : Num → HornerExpr
  | 0 => 1
  | Num.pos p => by
    induction' p with p ep p ep
    · exact e
      
    · exact (ep.mul ep).mul e
      
    · exact ep.mul ep
      

def inv (e : HornerExpr) : HornerExpr :=
  0

/-- Brings expressions into Horner normal form. -/
def ofCsexpr : CsringExpr → HornerExpr
  | csring_expr.atom n => atom n
  | csring_expr.const n => const n.toZnum
  | csring_expr.add x y => (of_csexpr x).add (of_csexpr y)
  | csring_expr.mul x y => (of_csexpr x).mul (of_csexpr y)
  | csring_expr.pow x n => (of_csexpr x).pow n

/-- Evaluates a reflected `horner_expr` - see `csring_expr.eval`. -/
def cseval {α} [CommSemiringₓ α] (t : Tree α) : HornerExpr → α
  | const n => n.abs
  | horner a x n b => Tactic.Ring.hornerₓ (cseval a) (t.getOrZero x) n (cseval b)

theorem cseval_atom {α} [CommSemiringₓ α] (t : Tree α) (n : PosNum) :
    (atom n).IsCs ∧ cseval t (atom n) = t.getOrZero n :=
  ⟨⟨⟨1, rfl⟩, ⟨0, rfl⟩⟩, (Tactic.Ring.horner_atomₓ _).symm⟩

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem cseval_add_const {α} [CommSemiringₓ α] (t : Tree α) (k : Num) {e : HornerExpr} (cs : e.IsCs) :
    (addConst k.toZnum e).IsCs ∧ cseval t (addConst k.toZnum e) = k + cseval t e := by
  simp [← add_const]
  cases k <;> simp [*]
  simp [←
    show Znum.pos k ≠ 0 by
      decide]
  induction' e with n a x n b A B <;> simp [*]
  · rcases cs with ⟨n, rfl⟩
    refine'
      ⟨⟨n + Num.pos k, by
          simp [← add_commₓ] <;> rfl⟩,
        _⟩
    cases n <;> simp
    
  · rcases B cs.2 with ⟨csb, h⟩
    simp [*, ← cs.1]
    rw [← Tactic.Ring.horner_add_constₓ, add_commₓ]
    rw [add_commₓ]
    

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem cseval_horner' {α} [CommSemiringₓ α] (t : Tree α) (a x n b) (h₁ : IsCs a) (h₂ : IsCs b) :
    (horner' a x n b).IsCs ∧
      cseval t (horner' a x n b) = Tactic.Ring.hornerₓ (cseval t a) (t.getOrZero x) n (cseval t b) :=
  by
  cases' a with n₁ a₁ x₁ n₁ b₁ <;> simp [← horner'] <;> split_ifs
  · simp [*, ← Tactic.Ring.hornerₓ]
    
  · exact ⟨⟨h₁, h₂⟩, rfl⟩
    
  · refine' ⟨⟨h₁.1, h₂⟩, Eq.symm _⟩
    simp [*]
    apply Tactic.Ring.horner_hornerₓ
    simp
    
  · exact ⟨⟨h₁, h₂⟩, rfl⟩
    

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem cseval_add {α} [CommSemiringₓ α] (t : Tree α) {e₁ e₂ : HornerExpr} (cs₁ : e₁.IsCs) (cs₂ : e₂.IsCs) :
    (add e₁ e₂).IsCs ∧ cseval t (add e₁ e₂) = cseval t e₁ + cseval t e₂ := by
  induction' e₁ with n₁ a₁ x₁ n₁ b₁ A₁ B₁ generalizing e₂ <;> simp
  · rcases cs₁ with ⟨n₁, rfl⟩
    simpa using cseval_add_const t n₁ cs₂
    
  induction' e₂ with n₂ a₂ x₂ n₂ b₂ A₂ B₂ generalizing n₁ b₁
  · rcases cs₂ with ⟨n₂, rfl⟩
    simp [← cseval_add_const t n₂ cs₁, ← add_commₓ]
    
  cases' cs₁ with csa₁ csb₁
  cases' id cs₂ with csa₂ csb₂
  simp
  have C := PosNum.cmp_to_nat x₁ x₂
  cases PosNum.cmp x₁ x₂ <;> simp
  · rcases B₁ csb₁ cs₂ with ⟨csh, h⟩
    refine' ⟨⟨csa₁, csh⟩, Eq.symm _⟩
    apply Tactic.Ring.horner_add_constₓ
    exact h.symm
    
  · cases C
    have B0 :
      is_cs 0 → ∀ {e₂ : horner_expr}, is_cs e₂ → is_cs (add 0 e₂) ∧ cseval t (add 0 e₂) = cseval t 0 + cseval t e₂ :=
      fun _ e₂ c => ⟨c, (zero_addₓ _).symm⟩
    cases' e : Num.sub' n₁ n₂ with k k <;> simp
    · have : n₁ = n₂ := by
        have := congr_arg (coe : Znum → ℤ) e
        simp at this
        have := sub_eq_zero.1 this
        rw [← Num.to_nat_to_int, ← Num.to_nat_to_int] at this
        exact Num.to_nat_inj.1 (Int.coe_nat_inj this)
      subst n₂
      rcases cseval_horner' _ _ _ _ _ _ _ with ⟨csh, h⟩
      · refine' ⟨csh, h.trans (Eq.symm _)⟩
        simp [*]
        apply Tactic.Ring.horner_add_horner_eqₓ <;>
          try
            rfl
        
      all_goals
        simp [*]
      
    · simp [← B₁ csb₁ csb₂, ← add_commₓ]
      rcases A₂ csa₂ _ _ B0 ⟨csa₁, 0, rfl⟩ with ⟨csh, h⟩
      refine' ⟨csh, Eq.symm _⟩
      rw [show id = add 0 from rfl, h]
      apply Tactic.Ring.horner_add_horner_gtₓ
      · change (_ + k : ℕ) = _
        rw [← Int.coe_nat_inj', Int.coe_nat_add, eq_comm, ← sub_eq_iff_eq_add']
        simpa using congr_arg (coe : Znum → ℤ) e
        
      · rfl
        
      · apply add_commₓ
        
      
    · have : (horner a₂ x₁ (Num.pos k) 0).IsCs := ⟨csa₂, 0, rfl⟩
      simp [← B₁ csb₁ csb₂, ← A₁ csa₁ this]
      symm
      apply Tactic.Ring.horner_add_horner_ltₓ
      · change (_ + k : ℕ) = _
        rw [← Int.coe_nat_inj', Int.coe_nat_add, eq_comm, ← sub_eq_iff_eq_add', ← neg_inj, neg_sub]
        simpa using congr_arg (coe : Znum → ℤ) e
        
      all_goals
        rfl
      
    
  · rcases B₂ csb₂ _ _ B₁ ⟨csa₁, csb₁⟩ with ⟨csh, h⟩
    refine' ⟨⟨csa₂, csh⟩, Eq.symm _⟩
    apply Tactic.Ring.const_add_hornerₓ
    simp [← h]
    

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem cseval_mul_const {α} [CommSemiringₓ α] (t : Tree α) (k : Num) {e : HornerExpr} (cs : e.IsCs) :
    (mulConst k.toZnum e).IsCs ∧ cseval t (mulConst k.toZnum e) = cseval t e * k := by
  simp [← mul_const]
  split_ifs with h h
  · cases (Num.to_znum_inj.1 h : k = 0)
    exact ⟨⟨0, rfl⟩, (mul_zero _).symm⟩
    
  · cases (Num.to_znum_inj.1 h : k = 1)
    exact ⟨cs, (mul_oneₓ _).symm⟩
    
  induction' e with n a x n b A B <;> simp [*]
  · rcases cs with ⟨n, rfl⟩
    suffices
    refine' ⟨⟨n * k, this⟩, _⟩
    swap
    · cases n <;> cases k <;> rfl
      
    rw [show _ from this]
    simp
    
  · cases cs
    simp [*]
    symm
    apply Tactic.Ring.horner_mul_constₓ <;> rfl
    

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem cseval_mul {α} [CommSemiringₓ α] (t : Tree α) {e₁ e₂ : HornerExpr} (cs₁ : e₁.IsCs) (cs₂ : e₂.IsCs) :
    (mul e₁ e₂).IsCs ∧ cseval t (mul e₁ e₂) = cseval t e₁ * cseval t e₂ := by
  induction' e₁ with n₁ a₁ x₁ n₁ b₁ A₁ B₁ generalizing e₂ <;> simp
  · rcases cs₁ with ⟨n₁, rfl⟩
    simpa [← mul_comm] using cseval_mul_const t n₁ cs₂
    
  induction' e₂ with n₂ a₂ x₂ n₂ b₂ A₂ B₂
  · rcases cs₂ with ⟨n₂, rfl⟩
    simpa! using cseval_mul_const t n₂ cs₁
    
  cases' cs₁ with csa₁ csb₁
  cases' id cs₂ with csa₂ csb₂
  simp
  have C := PosNum.cmp_to_nat x₁ x₂
  cases' A₂ csa₂ with csA₂ hA₂
  cases PosNum.cmp x₁ x₂ <;> simp
  · simp [← A₁ csa₁ cs₂, ← B₁ csb₁ cs₂]
    symm
    apply Tactic.Ring.horner_mul_constₓ <;> rfl
    
  · cases' cseval_horner' t _ x₁ n₂ 0 csA₂ ⟨0, rfl⟩ with csh₁ h₁
    cases C
    split_ifs
    · subst b₂
      refine' ⟨csh₁, h₁.trans (Eq.symm _)⟩
      apply Tactic.Ring.horner_mul_horner_zeroₓ <;>
        try
          rfl
      simp [← hA₂]
      
    · cases' A₁ csa₁ csb₂ with csA₁ hA₁
      cases' cseval_add t csh₁ _ with csh₂ h₂
      · refine' ⟨csh₂, h₂.trans (Eq.symm _)⟩
        apply Tactic.Ring.horner_mul_hornerₓ <;>
          try
            rfl
        simp [*]
        
      exact ⟨csA₁, (B₁ csb₁ csb₂).1⟩
      
    
  · simp [← A₂ csa₂, ← B₂ csb₂]
    rw [mul_comm, eq_comm]
    apply Tactic.Ring.horner_const_mulₓ
    · apply mul_comm
      
    · rfl
      
    

theorem cseval_pow {α} [CommSemiringₓ α] (t : Tree α) {x : HornerExpr} (cs : x.IsCs) :
    ∀ n : Num, (pow x n).IsCs ∧ cseval t (pow x n) = cseval t x ^ (n : ℕ)
  | 0 => ⟨⟨1, rfl⟩, (pow_zeroₓ _).symm⟩
  | Num.pos p => by
    simp [← pow]
    induction' p with p ep p ep
    · simp [*]
      
    · simp [← pow_bit1]
      cases' cseval_mul t ep.1 ep.1 with cs₀ h₀
      cases' cseval_mul t cs₀ cs with cs₁ h₁
      simp [*]
      
    · simp [← pow_bit0]
      cases' cseval_mul t ep.1 ep.1 with cs₀ h₀
      simp [*]
      

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
/-- For any given tree `t` of atoms and any reflected expression `r`,
the Horner form of `r` is a valid csring expression, and under `t`,
the Horner form evaluates to the same thing as `r`. -/
theorem cseval_of_csexpr {α} [CommSemiringₓ α] (t : Tree α) :
    ∀ r : CsringExpr, (ofCsexpr r).IsCs ∧ cseval t (ofCsexpr r) = r.eval t
  | csring_expr.atom n => cseval_atom _ _
  | csring_expr.const n =>
    ⟨⟨n, rfl⟩, by
      cases n <;> rfl⟩
  | csring_expr.add x y =>
    let ⟨cs₁, h₁⟩ := cseval_of_csexpr x
    let ⟨cs₂, h₂⟩ := cseval_of_csexpr y
    let ⟨cs, h⟩ := cseval_add t cs₁ cs₂
    ⟨cs, by
      simp [← h, *]⟩
  | csring_expr.mul x y =>
    let ⟨cs₁, h₁⟩ := cseval_of_csexpr x
    let ⟨cs₂, h₂⟩ := cseval_of_csexpr y
    let ⟨cs, h⟩ := cseval_mul t cs₁ cs₂
    ⟨cs, by
      simp [← h, *]⟩
  | csring_expr.pow x n =>
    let ⟨cs, h⟩ := cseval_of_csexpr x
    let ⟨cs, h⟩ := cseval_pow t cs n
    ⟨cs, by
      simp [← h, *]⟩

end HornerExpr

/-- The main proof-by-reflection theorem. Given reflected csring expressions
`r₁` and `r₂` plus a storage `t` of atoms, if both expressions go to the
same Horner normal form, then the original non-reflected expressions are
equal. `H` follows from kernel reduction and is therefore `rfl`. -/
theorem correctness {α} [CommSemiringₓ α] (t : Tree α) (r₁ r₂ : CsringExpr)
    (H : HornerExpr.ofCsexpr r₁ = HornerExpr.ofCsexpr r₂) : r₁.eval t = r₂.eval t := by
  repeat'
      rw [← (horner_expr.cseval_of_csexpr t _).2] <;>
    rw [H]

/-- Reflects a csring expression into a `csring_expr`, together
with a dlist of atoms, i.e. opaque variables over which the
expression is a polynomial. -/
unsafe def reflect_expr : expr → csring_expr × Dlist expr
  | quote.1 ((%%ₓe₁) + %%ₓe₂) =>
    let (r₁, l₁) := reflect_expr e₁
    let (r₂, l₂) := reflect_expr e₂
    (r₁.add r₂, l₁ ++ l₂)
  |/-| `(%%e₁ - %%e₂) :=
        let (r₁, l₁) := reflect_expr e₁, (r₂, l₂) := reflect_expr e₂ in
        (r₁.add r₂.neg, l₁ ++ l₂)
      | `(- %%e) := let (r, l) := reflect_expr e in (r.neg, l)-/
      quote.1
      ((%%ₓe₁) * %%ₓe₂) =>
    let (r₁, l₁) := reflect_expr e₁
    let (r₂, l₂) := reflect_expr e₂
    (r₁.mul r₂, l₁ ++ l₂)
  |/-| `(has_inv.inv %%e) := let (r, l) := reflect_expr e in (r.neg, l)
      | `(%%e₁ / %%e₂) :=
        let (r₁, l₁) := reflect_expr e₁, (r₂, l₂) := reflect_expr e₂ in
        (r₁.mul r₂.inv, l₁ ++ l₂)-/
      e@(quote.1 ((%%ₓe₁) ^ %%ₓe₂)) =>
    match reflect_expr e₁, expr.to_nat e₂ with
    | (r₁, l₁), some n₂ => (r₁.pow (Num.ofNat' n₂), l₁)
    | (r₁, l₁), none => (CsringExpr.atom 1, Dlist.singleton e)
  | e =>
    match expr.to_nat e with
    | some n => (CsringExpr.const (Num.ofNat' n), Dlist.empty)
    | none => (CsringExpr.atom 1, Dlist.singleton e)

/-- In the output of `reflect_expr`, `atom`s are initialized with incorrect indices.
The indices cannot be computed until the whole tree is built, so another pass over
the expressions is needed - this is what `replace` does. The computation (expressed
in the state monad) fixes up `atom`s to match their positions in the atom tree.
The initial state is a list of all atom occurrences in the goal, left-to-right. -/
unsafe def csring_expr.replace (t : Tree expr) : CsringExpr → StateTₓ (List expr) Option CsringExpr
  | csring_expr.atom _ => do
    let e ← get
    let p ← monadLift (t.indexOf (· < ·) e.head)
    put e
    pure (csring_expr.atom p)
  | csring_expr.const n => pure (CsringExpr.const n)
  | csring_expr.add x y => csring_expr.add <$> x.replace <*> y.replace
  | csring_expr.mul x y => csring_expr.mul <$> x.replace <*> y.replace
  | csring_expr.pow x n => (fun x => CsringExpr.pow x n) <$> x.replace

--| (csring_expr.neg x)   := csring_expr.neg <$> x.replace
--| (csring_expr.inv x)   := csring_expr.inv <$> x.replace
end Tactic.Ring2

namespace Tactic

namespace Interactive

open Interactive Interactive.Types Lean.Parser

open Tactic.Ring2

-- mathport name: «expr ?»
local postfix:1024 "?" => optionalₓ

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- `ring2` solves equations in the language of rings.

It supports only the commutative semiring operations, i.e. it does not normalize subtraction or
division.

  This variant on the `ring` tactic uses kernel computation instead
  of proof generation. In general, you should use `ring` instead of `ring2`. -/
unsafe def ring2 : tactic Unit := do
  sorry
  let quote.1 ((%%ₓe₁) = %%ₓe₂) ← target | fail "ring2 tactic failed: the goal is not an equality"
  let α ← infer_type e₁
  let expr.sort (level.succ u) ← infer_type α
  let (r₁, l₁) := reflect_expr e₁
  let (r₂, l₂) := reflect_expr e₂
  let L := (l₁ ++ l₂).toList
  let s := Tree.ofRbnode (rbtreeOf L).1
  let (r₁, L) ← (StateTₓ.run (r₁.replace s) L : Option _)
  let (r₂, _) ← (StateTₓ.run (r₂.replace s) L : Option _)
  let se : expr := s.reflect' u α
  let er₁ : expr := reflect r₁
  let er₂ : expr := reflect r₂
  let cs ← mk_app `` CommSemiringₓ [α] >>= mk_instance
  let e ←
    to_expr (pquote.1 (correctness (%%ₓse) (%%ₓer₁) (%%ₓer₂) rfl)) <|>
        fail
          ("ring2 tactic failed, cannot show equality:\n" ++ toString (HornerExpr.ofCsexpr r₁) ++ "\n  =?=\n" ++
            toString (HornerExpr.ofCsexpr r₂))
  tactic.exact e

add_tactic_doc
  { Name := "ring2", category := DocCategory.tactic, declNames := [`tactic.interactive.ring2],
    tags := ["arithmetic", "simplification", "decision procedure"] }

end Interactive

end Tactic

namespace Conv.Interactive

open Conv

unsafe def ring2 : conv Unit :=
  discharge_eq_lhs tactic.interactive.ring2

end Conv.Interactive


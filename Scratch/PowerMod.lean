import Mathlib
import Lean

def powerModProved (a b m : ℕ)(h: m > 1) :{n: ℕ  // a ^ b % m = n}  :=
  if c:b = 0 then
    ⟨1, by simp [c, Nat.mod_eq_of_lt h]⟩
  else
  let r := b % 2
  if c:r = 0 then
    let ⟨n, pf⟩  := powerModProved a (b/2) m h
    ⟨(n * n) % m, by
      let lem := Nat.div_add_mod b 2
      have : b % 2 = 0 := c
      simp [this] at lem
      rw [mul_comm] at lem
      rw [← lem, Nat.pow_mul, pow_two, Nat.mul_mod, pf]⟩
  else
    let ⟨n, pf⟩ := powerModProved a (b/2) m h
    ⟨(a * n * n) % m, by
      let lem := Nat.div_add_mod b 2
      have : b % 2 = 1 := by
        cases Nat.mod_two_eq_zero_or_one b with
        | inl h => contradiction
        | inr h => assumption
      simp [this] at lem
      rw [mul_comm] at lem
      rw [← lem, Nat.pow_add, Nat.pow_mul, pow_two, Nat.mul_mod, Nat.mul_mod (a^ (b / 2)), pf, pow_one, ← Nat.mul_mod, mul_comm, mul_assoc]
      ⟩
termination_by b

def powerMod (a b m : ℕ) : ℕ   :=
  if b = 0 then 1  % m
  else
  let r := b % 2
  if r = 0 then
    let n := powerMod a (b/2) m
    (n * n) % m
  else
    let n := powerMod a (b/2) m
    (a * n * n) % m
termination_by b

theorem zero_powerMod (a m : ℕ) : powerMod a 0 m = 1 % m :=
  by simp [powerMod]

theorem even_powerMod (a b m n : ℕ) :
  a ^ b % m = n → a ^ (2 * b) % m = (n * n) % m := by
    intro hyp
    rw [Nat.pow_mul, pow_two, mul_pow, Nat.mul_mod, hyp]

theorem odd_powerMod (a b m n : ℕ) :
  a ^ b % m = n → a ^ (2 * b + 1) % m = (n * n * a) % m := by
    intro hyp
    rw [Nat.pow_add, Nat.pow_mul, pow_two, mul_pow, pow_one,
    Nat.mul_mod, Nat.mul_mod (a ^b), hyp, ← Nat.mul_mod]


open Lean Meta Elab Tactic

def simplifyPowMod (a b m n : ℕ): MVarId → MetaM (List (MVarId)) :=
  fun mvarId =>
    mvarId.withContext do
    let rec loop (b n : ℕ)(mvarId : MVarId) :  MetaM Unit := do
      if b = 0 then
        let expr ← (mkAppM ``zero_powerMod #[Expr.lit (Literal.natVal a), Expr.lit (Literal.natVal m),
        Expr.lit (Literal.natVal n)])
        mvarId.assign expr
      else
        if b % 2 = 0 then
          let b' := b/2
          let n' := powerMod a (b/2) m
          let prevGoal ← eqnExpr a b' m n'
          let mvarId' ← mkFreshMVarId
          let mvar' ← mkFreshExprMVarWithId mvarId' (some prevGoal)
          let expr ← (mkAppM ``even_powerMod
            #[Expr.lit (Literal.natVal a), Expr.lit (Literal.natVal b'), Expr.lit (Literal.natVal m),
            Expr.lit (Literal.natVal n'), mvar'])
          mvarId.assign expr
          loop (b/2) n' mvarId'
        else
          let b' := b/2
          let n' := powerMod a (b/2) m
          let prevGoal ← eqnExpr a b' m n'
          let mvarId' ← mkFreshMVarId
          let mvar' ← mkFreshExprMVarWithId mvarId' (some prevGoal)
          let expr ← (mkAppM ``odd_powerMod
            #[Expr.lit (Literal.natVal a), Expr.lit (Literal.natVal b'), Expr.lit (Literal.natVal m),
            Expr.lit (Literal.natVal n'), mvar'])
          mvarId.assign expr
          loop (b/2) n' mvarId'
    loop b n mvarId
    return []
  where eqnExpr (a b m n : ℕ) : MetaM Expr := do
    let aExp := mkNatLit a
    let bExp := mkNatLit b
    let mExp := mkNatLit m
    let nExp := mkNatLit n
    let powExp ←  mkAppM ``HPow.hPow #[aExp, bExp]
    let modExp ← mkAppM ``HMod.hMod #[powExp, mExp]
    mkEq modExp nExp

elab "simplify_power_mod"
    a:num "^" b:num "%" m:num "=" n:num : tactic =>
    liftMetaTactic <|
      simplifyPowMod a.getNat b.getNat m.getNat n.getNat

#check liftMetaTactic
#check Meta.apply
#check mkEq
#check MVarId.assign
#check mkMVar -- `.mvar mvarId`
#check mkFreshExprMVar
#check mkFreshMVarId
#check Syntax.mkNumLit
#check mkFreshExprMVarWithId




#eval powerMod 2232421124 10027676 121

#eval 10027676 / 2 -- 5013838

#eval powerMod 2232421124 5013838 121 -- 23

#eval  2^30485 % 2381 -- 1872

-- example: 2232421124 ^ 10027676 % 121 = 45 := by
--   apply even_powerMod 2232421124 5013838 121 23
--   sorry


#check Nat.div_add_mod
#check Nat.mod_eq_of_lt
#check Nat.pow_two
#check Nat.mod_two_eq_zero_or_one

open Lean Meta Elab

elab "power_mod" a:num "^" b:num "%" m:num : term => do
  let res := powerMod a.getNat b.getNat m.getNat
  return mkNatLit res

#eval power_mod 2232421124 ^ 10027676 % 121

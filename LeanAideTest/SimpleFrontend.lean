import LeanAide.SimpleFrontend
import Mathlib

open LeanAide Lean Meta Elab

open scoped Nat

universe u v w u_1 u_2 u_3 u₁ u₂ u₃

namespace LeanAideTest

/-- info: #[`x] -/
#guard_msgs in
#eval newDeclarations "def x : Nat := 0"

elab "#new_defs" s:str : command => Command.liftTermElabM do
  let s := s.getString
  let (nameDefs, msgs) ← elabFrontDefsNewExprM s
  for (n, v) in nameDefs do
    logInfo s!"New definition: {n} with value {← ppExpr v}"
  for msg in msgs.toList do
    logInfo msg.data

/-- info: New definition: y with value 1 -/
#guard_msgs in
#new_defs "def y : Nat := 1"

/--
info: Except.ok (Lean.Expr.forallE
  `G
  (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u)))
  (Lean.Expr.forallE
    `inst
    (Lean.Expr.app (Lean.Expr.const `Group [Lean.Level.param `u]) (Lean.Expr.bvar 0))
    (Lean.Expr.forallE
      `a
      (Lean.Expr.bvar 1)
      (Lean.Expr.forallE
        `n
        (Lean.Expr.const `Nat [])
        (Lean.Expr.forallE
          (Lean.Name.mkNum `a._@.LeanAideTest.SimpleFrontend._hyg 21)
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.param `u)]) (Lean.Expr.bvar 3))
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `HPow.hPow [Lean.Level.param `u, Lean.Level.zero, Lean.Level.param `u])
                          (Lean.Expr.bvar 3))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `instHPow [Lean.Level.param `u, Lean.Level.zero])
                          (Lean.Expr.bvar 3))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `Monoid.toNatPow [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `DivInvMonoid.toMonoid [Lean.Level.param `u])
                            (Lean.Expr.bvar 3))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.const `Group.toDivInvMonoid [Lean.Level.param `u])
                              (Lean.Expr.bvar 3))
                            (Lean.Expr.bvar 2))))))
                  (Lean.Expr.bvar 1))
                (Lean.Expr.bvar 0)))
            (Lean.Expr.app
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                (Lean.Expr.lit (Lean.Literal.natVal 1)))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `One.toOfNat1 [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `InvOneClass.toOne [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.const `DivInvOneMonoid.toInvOneClass [Lean.Level.param `u])
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.const `DivisionMonoid.toDivInvOneMonoid [Lean.Level.param `u])
                        (Lean.Expr.bvar 3))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `Group.toDivisionMonoid [Lean.Level.param `u])
                          (Lean.Expr.bvar 3))
                        (Lean.Expr.bvar 2))))))))
          (Lean.Expr.app
            (Lean.Expr.app (Lean.Expr.const `Exists [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
            (Lean.Expr.lam
              `m
              (Lean.Expr.const `Nat [])
              (Lean.Expr.app
                (Lean.Expr.app
                  (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Nat []))
                  (Lean.Expr.bvar 2))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `HMul.hMul [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
                            (Lean.Expr.const `Nat []))
                          (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `Nat []))
                      (Lean.Expr.app
                        (Lean.Expr.app (Lean.Expr.const `instHMul [Lean.Level.zero]) (Lean.Expr.const `Nat []))
                        (Lean.Expr.const `instMulNat [])))
                    (Lean.Expr.bvar 0))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app (Lean.Expr.const `orderOf [Lean.Level.param `u]) (Lean.Expr.bvar 5))
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `DivInvMonoid.toMonoid [Lean.Level.param `u])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.const `Group.toDivInvMonoid [Lean.Level.param `u])
                            (Lean.Expr.bvar 5))
                          (Lean.Expr.bvar 4))))
                    (Lean.Expr.bvar 3))))
              (Lean.BinderInfo.default)))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.default))
      (Lean.BinderInfo.default))
    (Lean.BinderInfo.instImplicit))
  (Lean.BinderInfo.implicit))
-/
#guard_msgs in
#eval elabFrontTheoremExprM "∀ {G : Type u} [inst : Group G] (a : G) (n : ℕ), a ^ n = 1 → ∃ m : ℕ, n = m * orderOf a"


end LeanAideTest

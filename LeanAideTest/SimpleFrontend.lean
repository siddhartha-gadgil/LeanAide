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
info: New definition: M with value fun {R₁} [CommSemiring R₁] {n} [Fintype n] M => Matrix.toLinearMap₂'Aux (RingHom.id R₁) (RingHom.id R₁) M
-/
#guard_msgs in
#new_defs "def M {R₁ : Type u_1} [CommSemiring R₁] {n : Type u_5} [Fintype n] (M : Matrix n n R₁) : LinearMap.BilinForm R₁ (n → R₁) :=
  Matrix.toLinearMap₂'Aux _ _ M"

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

/--
info: Expr.lam `R (Expr.sort (Level.param `u_1).succ)
  (Expr.lam `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19322
    ((Expr.const `CommSemiring [Level.param `u_1]).app (Expr.bvar 0))
    (Expr.lam `M (Expr.sort (Level.param `u_6).succ)
      (Expr.lam `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19348
        ((Expr.const `AddCommMonoid [Level.param `u_6]).app (Expr.bvar 0))
        (Expr.lam `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19375
          (((((Expr.const `Module [Level.param `u_1, Level.param `u_6]).app (Expr.bvar 3)).app (Expr.bvar 1)).app
                (((Expr.const `CommSemiring.toSemiring [Level.param `u_1]).app (Expr.bvar 3)).app (Expr.bvar 2))).app
            (Expr.bvar 0))
          (((((((((Expr.const `LinearMap.BilinMap [Level.param `u_1, Level.param `u_6, Level.param `u_1]).app
                                        (Expr.bvar 4)).app
                                    (Expr.bvar 3)).app
                                (Expr.bvar 2)).app
                            (Expr.bvar 4)).app
                        (Expr.bvar 1)).app
                    (((Expr.const `NonUnitalNonAssocSemiring.toAddCommMonoid [Level.param `u_1]).app (Expr.bvar 4)).app
                      (((Expr.const `NonAssocSemiring.toNonUnitalNonAssocSemiring [Level.param `u_1]).app
                            (Expr.bvar 4)).app
                        (((Expr.const `Semiring.toNonAssocSemiring [Level.param `u_1]).app (Expr.bvar 4)).app
                          (((Expr.const `CommSemiring.toSemiring [Level.param `u_1]).app (Expr.bvar 4)).app
                            (Expr.bvar 3)))))).app
                (Expr.bvar 0)).app
            (((Expr.const `Semiring.toModule [Level.param `u_1]).app (Expr.bvar 4)).app
              (((Expr.const `CommSemiring.toSemiring [Level.param `u_1]).app (Expr.bvar 4)).app (Expr.bvar 3))))
          BinderInfo.instImplicit)
        BinderInfo.instImplicit)
      BinderInfo.default)
    BinderInfo.instImplicit)
  BinderInfo.default
-/
#guard_msgs in
#eval elabFrontDefExprM "{R₁ : Type u_1} →
  [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)" `LinearMap.BilinForm

/--
info: (Expr.forallE `R (Expr.sort (Level.param `u_1).succ)
    (Expr.forallE `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19322
      ((Expr.const `CommSemiring [Level.param `u_1]).app (Expr.bvar 0))
      (Expr.forallE `M (Expr.sort (Level.param `u_6).succ)
        (Expr.forallE `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19348
          ((Expr.const `AddCommMonoid [Level.param `u_6]).app (Expr.bvar 0))
          (Expr.forallE `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19375
            (((((Expr.const `Module [Level.param `u_1, Level.param `u_6]).app (Expr.bvar 3)).app (Expr.bvar 1)).app
                  (((Expr.const `CommSemiring.toSemiring [Level.param `u_1]).app (Expr.bvar 3)).app (Expr.bvar 2))).app
              (Expr.bvar 0))
            (Expr.sort ((Level.param `u_1).max (Level.param `u_6)).succ) BinderInfo.instImplicit)
          BinderInfo.instImplicit)
        BinderInfo.default)
      BinderInfo.instImplicit)
    BinderInfo.default,
  Expr.lam `R (Expr.sort (Level.param `u_1).succ)
    (Expr.lam `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19322
      ((Expr.const `CommSemiring [Level.param `u_1]).app (Expr.bvar 0))
      (Expr.lam `M (Expr.sort (Level.param `u_6).succ)
        (Expr.lam `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19348
          ((Expr.const `AddCommMonoid [Level.param `u_6]).app (Expr.bvar 0))
          (Expr.lam `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19375
            (((((Expr.const `Module [Level.param `u_1, Level.param `u_6]).app (Expr.bvar 3)).app (Expr.bvar 1)).app
                  (((Expr.const `CommSemiring.toSemiring [Level.param `u_1]).app (Expr.bvar 3)).app (Expr.bvar 2))).app
              (Expr.bvar 0))
            (((((((((Expr.const `LinearMap.BilinMap [Level.param `u_1, Level.param `u_6, Level.param `u_1]).app
                                          (Expr.bvar 4)).app
                                      (Expr.bvar 3)).app
                                  (Expr.bvar 2)).app
                              (Expr.bvar 4)).app
                          (Expr.bvar 1)).app
                      (((Expr.const `NonUnitalNonAssocSemiring.toAddCommMonoid [Level.param `u_1]).app
                            (Expr.bvar 4)).app
                        (((Expr.const `NonAssocSemiring.toNonUnitalNonAssocSemiring [Level.param `u_1]).app
                              (Expr.bvar 4)).app
                          (((Expr.const `Semiring.toNonAssocSemiring [Level.param `u_1]).app (Expr.bvar 4)).app
                            (((Expr.const `CommSemiring.toSemiring [Level.param `u_1]).app (Expr.bvar 4)).app
                              (Expr.bvar 3)))))).app
                  (Expr.bvar 0)).app
              (((Expr.const `Semiring.toModule [Level.param `u_1]).app (Expr.bvar 4)).app
                (((Expr.const `CommSemiring.toSemiring [Level.param `u_1]).app (Expr.bvar 4)).app (Expr.bvar 3))))
            BinderInfo.instImplicit)
          BinderInfo.instImplicit)
        BinderInfo.default)
      BinderInfo.instImplicit)
    BinderInfo.default)
-/
#guard_msgs in
#eval elabFrontDefTypeValExprM "{R₁ : Type u_1} →
  [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)" `LinearMap.BilinForm


def elabFrontDefTypeValViewM(s: String)(n: Name)(modifyEnv: Bool := false) : MetaM <| String × String := do
  let (type, val) ← elabFrontDefTypeValExprM s n modifyEnv
  let typefmt ←  ppExpr type
  let typeval ←  ppExpr val
  return (typefmt.pretty, typeval.pretty)

/--
info: (Expr.forallE `R (Expr.sort (Level.param `u_1).succ)
    (Expr.forallE `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19322
      ((Expr.const `CommSemiring [Level.param `u_1]).app (Expr.bvar 0))
      (Expr.forallE `M (Expr.sort (Level.param `u_6).succ)
        (Expr.forallE `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19348
          ((Expr.const `AddCommMonoid [Level.param `u_6]).app (Expr.bvar 0))
          (Expr.forallE `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19375
            (((((Expr.const `Module [Level.param `u_1, Level.param `u_6]).app (Expr.bvar 3)).app (Expr.bvar 1)).app
                  (((Expr.const `CommSemiring.toSemiring [Level.param `u_1]).app (Expr.bvar 3)).app (Expr.bvar 2))).app
              (Expr.bvar 0))
            (Expr.sort ((Level.param `u_1).max (Level.param `u_6)).succ) BinderInfo.instImplicit)
          BinderInfo.instImplicit)
        BinderInfo.default)
      BinderInfo.instImplicit)
    BinderInfo.default,
  Expr.lam `R (Expr.sort (Level.param `u_1).succ)
    (Expr.lam `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19322
      ((Expr.const `CommSemiring [Level.param `u_1]).app (Expr.bvar 0))
      (Expr.lam `M (Expr.sort (Level.param `u_6).succ)
        (Expr.lam `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19348
          ((Expr.const `AddCommMonoid [Level.param `u_6]).app (Expr.bvar 0))
          (Expr.lam `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19375
            (((((Expr.const `Module [Level.param `u_1, Level.param `u_6]).app (Expr.bvar 3)).app (Expr.bvar 1)).app
                  (((Expr.const `CommSemiring.toSemiring [Level.param `u_1]).app (Expr.bvar 3)).app (Expr.bvar 2))).app
              (Expr.bvar 0))
            (((((((((Expr.const `LinearMap.BilinMap [Level.param `u_1, Level.param `u_6, Level.param `u_1]).app
                                          (Expr.bvar 4)).app
                                      (Expr.bvar 3)).app
                                  (Expr.bvar 2)).app
                              (Expr.bvar 4)).app
                          (Expr.bvar 1)).app
                      (((Expr.const `NonUnitalNonAssocSemiring.toAddCommMonoid [Level.param `u_1]).app
                            (Expr.bvar 4)).app
                        (((Expr.const `NonAssocSemiring.toNonUnitalNonAssocSemiring [Level.param `u_1]).app
                              (Expr.bvar 4)).app
                          (((Expr.const `Semiring.toNonAssocSemiring [Level.param `u_1]).app (Expr.bvar 4)).app
                            (((Expr.const `CommSemiring.toSemiring [Level.param `u_1]).app (Expr.bvar 4)).app
                              (Expr.bvar 3)))))).app
                  (Expr.bvar 0)).app
              (((Expr.const `Semiring.toModule [Level.param `u_1]).app (Expr.bvar 4)).app
                (((Expr.const `CommSemiring.toSemiring [Level.param `u_1]).app (Expr.bvar 4)).app (Expr.bvar 3))))
            BinderInfo.instImplicit)
          BinderInfo.instImplicit)
        BinderInfo.default)
      BinderInfo.instImplicit)
    BinderInfo.default)
-/
#guard_msgs in
#eval elabFrontDefTypeValExprM "{R₁ : Type u_1} →
  [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)" `LinearMap.BilinForm

/--
info: ("(R : Type u_1) →\n  [inst : CommSemiring R] → (M : Type u_6) → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Type (max u_1 u_6)",
  "fun R [CommSemiring R] M [AddCommMonoid M] [_root_.Module R M] => LinearMap.BilinMap R M R")
-/
#guard_msgs in
#eval elabFrontDefTypeValViewM "{R₁ : Type u_1} →
  [inst : CommSemiring R₁] → {n : Type u_5} → [Fintype n] → Matrix n n R₁ → LinearMap.BilinForm R₁ (n → R₁)" `LinearMap.BilinForm

/--
info: Messages
---
info: Expr.forallE `R (Expr.sort (Level.param `u_1).succ)
  (Expr.forallE `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19322
    ((Expr.const `CommSemiring [Level.param `u_1]).app (Expr.bvar 0))
    (Expr.forallE `M (Expr.sort (Level.param `u_6).succ)
      (Expr.forallE `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19348
        ((Expr.const `AddCommMonoid [Level.param `u_6]).app (Expr.bvar 0))
        (Expr.forallE `inst._@.Mathlib.LinearAlgebra.BilinearMap._hyg.19375
          (((((Expr.const `Module [Level.param `u_1, Level.param `u_6]).app (Expr.bvar 3)).app (Expr.bvar 1)).app
                (((Expr.const `CommSemiring.toSemiring [Level.param `u_1]).app (Expr.bvar 3)).app (Expr.bvar 2))).app
            (Expr.bvar 0))
          (Expr.sort ((Level.param `u_1).max (Level.param `u_6)).succ) BinderInfo.instImplicit)
        BinderInfo.instImplicit)
      BinderInfo.default)
    BinderInfo.instImplicit)
  BinderInfo.default
-/
#guard_msgs in
#eval elabFrontThmExprM "theorem commutativity (p q : Prop) : p ∧ q → q ∧ p := by
intro h
cases h with
| intro hp hq =>
  constructor
  · exact hq
  · exact hp
"  `LinearMap.BilinForm



end LeanAideTest

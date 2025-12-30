import Lean
open Lean Meta Elab Term Parser Tactic

namespace LeanAide

def ppExprM (e: MetaM Expr) : MetaM Format := do
  let expr ← e
  ppExpr expr

def ppExprM? [ToString A](e?: MetaM (Except A Expr)) : MetaM (Except String Format) := do
  match ← e? with
  | Except.error a => return Except.error (toString a)
  | Except.ok expr => return Except.ok (← ppExpr expr)

def ppExprDetailed (e : Expr): MetaM String := do
  let fmtDetailed ← withOptions (fun o₁ =>
                    let o₂ := pp.motives.all.set o₁ true
                    let o₃ := pp.fieldNotation.set o₂ false
                    let o₄ := pp.proofs.set o₃ true
                    let o₅ := pp.deepTerms.set o₄ true
                    let o₆ := pp.funBinderTypes.set o₅ true
                    let o₇ := pp.piBinderTypes.set o₆ true
                    let o₈ := pp.letVarTypes.set o₇ true
                    let o₉ := pp.fullNames.set o₈ true
                    pp.unicode.fun.set o₉ true) do
    ppExpr e
  return fmtDetailed.pretty

def ppExprDetailed' (e : Expr): MetaM String := do
  let fmtDetailed ← withOptions (fun o₁ =>
                    let o₂ := pp.motives.pi.set o₁ true
                    let o₅ := pp.deepTerms.set o₂ true
                    let o₆ := pp.funBinderTypes.set o₅ true
                    let o₇ := pp.piBinderTypes.set o₆ true
                    let o₈ := pp.letVarTypes.set o₇ true
                    let o₉ := pp.fullNames.set o₈ true
                    pp.unicode.fun.set o₉ true) do
    ppExpr e
  return fmtDetailed.pretty

-- test

elab "detailed" t:term : term => do
  let e ← Term.elabTerm t none
  let fmt ← ppExprDetailed e
  logInfo fmt
  logInfo m!"{← ppExpr e}"
  return e

-- #check detailed (fun (n : Nat) => n + 1)

def delabMatchless (e: Expr) : MetaM Syntax := withOptions (fun o₁ =>
                    -- let o₂ := pp.motives.all.set o₁ true
                    let o₃ := pp.fieldNotation.set o₁ false
                    let o₄ := pp.proofs.set o₃ true
                    let o₅ := pp.deepTerms.set o₄ true
                    let o₆ := pp.funBinderTypes.set o₅ true
                    let o₇ := pp.piBinderTypes.set o₆ true
                    let o₈ := pp.letVarTypes.set o₇ true
                    let o₉ := pp.match.set o₈ false
                    let o' := pp.fullNames.set o₉ false
                    pp.unicode.fun.set o' true) do
              PrettyPrinter.delab e

def delabDetailed (e: Expr) : MetaM Syntax.Term := withOptions (fun o₁ =>
                    let o₂ := pp.motives.pi.set o₁ true
                    let o₃ := pp.numericTypes.set o₂ true
                    let o₅ := pp.deepTerms.set o₃ true
                    let o₆ := pp.funBinderTypes.set o₅ true
                    let o₇ := pp.piBinderTypes.set o₆ true
                    let o₈ := pp.letVarTypes.set o₇ true
                    let o₉ := pp.coercions.types.set o₈ true
                    let o' := pp.motives.nonConst.set o₉ true
                    let o'' := pp.fullNames.set o' true
                    pp.unicode.fun.set o'' true) do
              PrettyPrinter.delab e

def delabDetailed' (e: Expr) : MetaM Syntax.Term := withOptions (fun o₁ =>
                    let o₂ := pp.motives.pi.set o₁ true
                    let o₅ := pp.deepTerms.set o₂ true
                    let o₆ := pp.funBinderTypes.set o₅ true
                    let o₇ := pp.piBinderTypes.set o₆ true
                    let o₈ := pp.letVarTypes.set o₇ true
                    let o₉ := pp.fullNames.set o₈ true
                    pp.unicode.fun.set o₉ true) do
              PrettyPrinter.delab e

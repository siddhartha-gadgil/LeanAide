import Lean
import LeanAideCore.Aides

open Lean Meta Elab Term

namespace LeanAide

partial def getSorryTypes (e: Expr) : MetaM (Array Expr) := do
  match e with
  | .app (.const ``sorryAx _) a =>
    match a with
    | .forallE _ (.const ``Name []) body _ =>
      return #[body]
    | _ =>
      logWarning s!"Found sorryAx in app, but not forallE"
      return #[a]
  | Expr.app f a  =>
    return (← getSorryTypes f) ++ (← getSorryTypes a)
  | Expr.lam name type body bi =>
    withLocalDecl name bi type fun x => do
      let body := body.instantiate1 x
      let inner ← getSorryTypes body
      inner.mapM <| mkForallFVars #[x]
  | Expr.letE name type value bdy nondep =>
      let inner ← withLetDecl name type value fun x => do
        let bdy := bdy.instantiate1 x
        let check ←  exprDependsOn bdy x.fvarId!
        logInfo s!"Checking dependence: {check}"
        let inner ← getSorryTypes bdy
        inner.mapM <| fun type => do
          let y ←  mkLetFVars #[x] type
          pure <| .letE name type value y nondep
      let outer ← getSorryTypes value
      return inner ++ outer
  | .proj _ _ s => getSorryTypes s
  | .mdata _ e => getSorryTypes e
  | _ => pure #[]

partial def purgeLets (e: Expr) : MetaM Expr := do
  match e with
  | Expr.app f a  =>
    return .app (← purgeLets f)  (← purgeLets a)
  | Expr.lam name type body bi =>
    withLocalDecl name bi type fun x => do
      let body := body.instantiate1 x
      let inner ← purgeLets body
      mkForallFVars #[x] inner
  | Expr.letE name type value bdy nondep =>
      withLetDecl name type value fun x => do
        let bdy := bdy.instantiate1 x
        if ← exprDependsOn bdy x.fvarId! then
          let inner ← purgeLets bdy
          mkLetFVars #[x] inner nondep
        else
          purgeLets bdy
  | .proj _ _ s => purgeLets s
  | .mdata _ e => purgeLets e
  | e => return e

open Parser.Tactic in
partial def fillSorry (e: Expr) (tac: TSyntax ``tacticSeq) : TermElabM Expr := do
  let goal ← inferType e
  let mvar ← mkFreshExprMVar goal
  let check ← checkTacticSafe mvar.mvarId! tac
  if check then
    let pf ← Term.elabTerm (← `(by $tac)) goal
    Term.synthesizeSyntheticMVarsNoPostponing
    return pf
  else
  match e with
  | Expr.app f a  =>
    return .app (← fillSorry f tac)  (← fillSorry a tac)
  | Expr.lam name type body bi =>
    withLocalDecl name bi type fun x => do
      let body := body.instantiate1 x
      let inner ← fillSorry body tac
      mkForallFVars #[x] inner
  | Expr.letE name type value bdy nondep =>
      withLetDecl name type value fun x => do
        let bdy := bdy.instantiate1 x
        let inner ← fillSorry bdy tac
        mkLetFVars #[x] inner nondep
  | .proj _ _ s => fillSorry s tac
  | .mdata _ e => fillSorry e tac
  | e => return e

def fillSorryWithPf (e: Expr) (pf: String) :
    TermElabM Expr := do
  let .ok term' :=
    Parser.runParserCategory (← getEnv) `term pf
    | throwError "Failed to parse term {pf}"
  let term : Syntax.Term := {raw := term'}
  let tac  := (← `(tacticSeq| apply $term))
  fillSorry e tac

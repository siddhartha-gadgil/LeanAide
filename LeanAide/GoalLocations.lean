import Lean.Meta.ExprLens
import Mathlib.Tactic
import Std

open Lean Meta Expr 

-- TODO Check whether this function already exists
def Lean.Expr.getName! : Expr → Name
  | .lam n _ _ _ => n
  | .letE n _ _ _ _ => n
  | .forallE n _ _ _ => n
  | _               => panic! "Unable to get name for expression."

partial def Lean.Expr.getConvEnters (expr : Expr) (φ : Expr → MetaM α)
    (explicit? : Bool) : MetaM (Array (List String × α)) :=
  match expr with
  | .app _ _ => do
    let fn := expr.getAppFn 
    let args := expr.getAppArgs
    let fnInfo ← getFunInfo fn
    let argsWithBinderInfo := Array.zip args (fnInfo.paramInfo.map (·.isExplicit))
    let args' :=
      argsWithBinderInfo.filterMap <| fun (arg, bi) ↦
        if explicit? || (!explicit? && bi) then
          some arg
        else none
    let enterArgs ← args'.mapIdxM fun idx arg ↦ do
      let argConvEnters ← arg.getConvEnters φ explicit?
      let enterArg := (if explicit? then "@" else "") ++ s!"{idx.val + 1}"
      return updatePaths [enterArg] argConvEnters |>.push ([enterArg], ← φ arg)
    return enterArgs.concatMap id
  | .forallE _ _ _ _ => do
    let binders := expr.getForallBinderNames |>.map (·.getRoot.toString)
    let body := expr.getForallBody
    updatePaths binders <$> body.getConvEnters φ explicit?
  | .lam _ _ _ _ 
  | .letE _ _ _ _ _ =>
    lambdaLetTelescope expr <| fun args body ↦ do
      let binders := args |>.map (·.getName!.toString) |>.toList
      updatePaths binders <$> body.getConvEnters φ explicit?
  | .mdata _ expr => getConvEnters expr φ explicit?
  | .proj _ _ struct => do
    updatePaths ["1"] <$> struct.getConvEnters φ explicit?
  | _ => return #[]
  where updatePaths (pre : List String) (entries : Array (List String × α)) : MetaM <| Array (List String × α) := do
    entries.map <| fun (path, a) ↦ (pre ++ path, a)

open Meta Elab Term in
#eval show TermElabM _ from do
  let stx ← `(term| ∀ x, Nat.succ x = 1) 
  let t ← Term.elabTerm stx none
  let enters ← t.getConvEnters pure (explicit? := false)
  for (path, expr) in enters do
    IO.println path
    let stx ← PrettyPrinter.delab expr
    IO.println stx.raw.reprint.get!

partial def getSubexpressionMatches (d : DiscrTree α s) 
    (e : Expr) (explicit? : Bool) : MetaM (Array (List String × α)) := do sorry

import Lean.Meta.ExprLens
import Mathlib.Tactic
import Std

open Lean Meta Expr 

def Lean.Expr.getConvEnters : Expr → MetaM (Array (List String × Expr))
  | .app _ _ => _
  | .forallE _ _ _ _ => _
  | .lam _ _ _ _ 
  | .letE _ _ _ _ _ => _
  | .mdata _ expr => _
  | .proj _ _ struct => _
  | _ => _


def Lean.SubExpr.extensions (p : SubExpr.Pos) : Expr → MetaM (Array (SubExpr.Pos × Expr))
  | .app fn arg => do
    let fnf ← whnf fn
    if fnf.binderInfoEx == .default then
      if fnf.isApp then
        return #[(p.pushAppFn, fnf), (p.pushAppArg, arg)]
      else
        return #[(p.pushAppArg, arg)]
    else return #[]
  | .lam _ _ body _ => return #[(p.pushBindingBody, body)]
  | .forallE _ _ body _ => return #[(p.pushBindingBody, body)]
  | .letE _ type value body _ => 
    return #[(p.pushLetVarType, type), (p.pushLetValue, value), (p.pushLetBody, body)]
  | .mdata _ expr => extensions p expr
  | .proj _ _ struct => return #[(p.pushProj, struct)]
  |  _ => return #[]

partial def Lean.Expr.allSubExprs (p : SubExpr.Pos) (e : Expr) : MetaM (Array (SubExpr.Pos × Expr)) := do
  let exts ← Lean.SubExpr.extensions p e
  let rexts ← exts.concatMapM fun (pos, subexpr) ↦ allSubExprs pos subexpr 
  return rexts.push (p, e)

def Lean.Expr.allPositions (e : Expr) : MetaM (Array SubExpr.Pos) := do
  let exprs ← e.allSubExprs .root
  return exprs.map Prod.fst

def Lean.Expr.viewPositions (e : Expr) : MetaM (Array (SubExpr.Pos × String)) := do
  let exprs ← e.allSubExprs .root
  exprs.mapM fun (pos, subexpr) ↦ do
    let stx ← PrettyPrinter.delab subexpr
    return (pos, stx.raw.reprint.get!)

open Meta Elab Term in
#eval show TermElabM _ from do
  let stx ← `(term| 1 + 2) 
  let t ← Term.elabTerm stx none
  let t ← reduce t
  return t.allPositions

-- The code below has been modified from `ProofWidgets/Demos/Conv`,
-- copyright of Robin Böhne and Wojciech Nawrocki.

private structure SolveReturn where
  expr : Expr
  val? : Option String
  listRest : List Nat

private def solveLevel (expr : Expr) (path : List Nat) : MetaM SolveReturn := match expr with
  | .app _ _ => do
    let mut descExp := expr
    let mut count := 0
    let mut explicitList := []

    -- we go through the application until we reach the end, counting how many explicit arguments it has and noting whether
    -- they are explicit or implicit
    while descExp.isApp do
      if (←Lean.Meta.inferType descExp.appFn!).bindingInfo!.isExplicit then
        explicitList := true::explicitList
        count := count + 1
      else
        explicitList := false::explicitList
      descExp := descExp.appFn!

    -- we get the correct `enter` command by subtracting the number of `true`s in our list
    let mut mutablePath := path
    let mut length := count
    explicitList := List.reverse explicitList
    while !mutablePath.isEmpty && mutablePath.head! == 0 do
      if explicitList.head! == true then
        count := count - 1
      explicitList := explicitList.tail!
      mutablePath := mutablePath.tail!

    let mut nextExp := expr
    while length > count do
      nextExp := nextExp.appFn!
      length := length - 1
    nextExp := nextExp.appArg!

    let pathRest := if mutablePath.isEmpty then [] else mutablePath.tail!

    return { expr := nextExp, val? := toString count , listRest := pathRest }

  | .lam n _ b _ => pure { expr := b, val? := n.getString!, listRest := path.tail! }
  | .forallE n _ b _ => pure { expr := b, val? := n.getString!, listRest := path.tail! }

  | .mdata _ b => do
    match b with
      | Expr.mdata _ _ => return { expr := b, val? := none, listRest := path }
      | _ => return { expr := b.appFn!.appArg!, val? := none, listRest := path.tail!.tail! }

  | _ => do
    return { expr := ←(Lean.Core.viewSubexpr path.head! expr), val? := toString (path.head! + 1), listRest := path.tail! }

private def solveLevel' (expr : Expr) (path : List Nat) : MetaM SolveReturn := match expr with
  | .app _ _ => do
    let fn := expr.getAppFn 
    let args := expr.getAppArgs
    let fnInfo ← getFunInfo fn
    let explicitArr := fnInfo.paramInfo.map (·.isExplicit) 
    let mut descExp := expr
    let mut count := 0
    let mut explicitList := []

    -- we go through the application until we reach the end, counting how many explicit arguments it has and noting whether
    -- they are explicit or implicit
    while descExp.isApp do
      if (←Lean.Meta.inferType descExp.appFn!).bindingInfo!.isExplicit then
        explicitList := true::explicitList
        count := count + 1
      else
        explicitList := false::explicitList
      descExp := descExp.appFn!

    -- we get the correct `enter` command by subtracting the number of `true`s in our list
    let mut mutablePath := path
    let mut length := count
    explicitList := List.reverse explicitList
    while !mutablePath.isEmpty && mutablePath.head! == 0 do
      if explicitList.head! == true then
        count := count - 1
      explicitList := explicitList.tail!
      mutablePath := mutablePath.tail!

    let mut nextExp := expr
    while length > count do
      nextExp := nextExp.appFn!
      length := length - 1
    nextExp := nextExp.appArg!

    let pathRest := if mutablePath.isEmpty then [] else mutablePath.tail!

    return { expr := nextExp, val? := toString count , listRest := pathRest }

  | .lam n _ b _ => pure { expr := b, val? := n.getString!, listRest := path.tail! }
  | .forallE n _ b _ => pure { expr := b, val? := n.getString!, listRest := path.tail! }

  | .mdata _ b => do
    match b with
      | Expr.mdata _ _ => return { expr := b, val? := none, listRest := path }
      | _ => return { expr := b.appFn!.appArg!, val? := none, listRest := path.tail!.tail! }

  | _ => do
    return { expr := ←(Lean.Core.viewSubexpr path.head! expr), val? := toString (path.head! + 1), listRest := path.tail! }

def Lean.SubExpr.Pos.toConvEnterArg (goalType : Expr) (subexprPos : SubExpr.Pos) : MetaM (List String) := do
  let mut list := subexprPos.toArray.toList
  let mut expr := goalType
  let mut retList := []
  -- generate list of commands for `enter`
  while !list.isEmpty do
    let res ← solveLevel expr list
    expr := res.expr
    retList := match res.val? with
      | none => retList
      | some val => val::retList
    list := res.listRest

  -- build `enter [...]` string
  retList := List.reverse retList
  return retList

def Lean.Expr.allConvEnterArgs (e : Expr) : MetaM <| Array (List String) := do
  (← e.allPositions).filterMapM <| fun pos ↦
    try? do Lean.SubExpr.Pos.toConvEnterArg e pos

open Elab Term

def testExpr := do
  let stx ← `(term| ∀ x, Nat.succ x = 1) 
  Term.elabTerm stx none

-- #eval (SubExpr.Pos.fromString! "/1").toConvEnterArg <$> testExpr

#check FunInfo
#check getFunInfo
#check getAppArgs'

example : ∀ x : 1 + 2 = 3, x = x := by
  conv 
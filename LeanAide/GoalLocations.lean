import Lean.Meta.ExprLens
import Std

open Lean

def Lean.SubExpr.extensions (p : SubExpr.Pos) : Expr → Array (SubExpr.Pos × Expr)
  | .app fn arg => #[(p.pushAppFn, fn), (p.pushAppArg, arg)]
  | .lam _ binderType body _
  | .forallE _ binderType body _ => #[(p.pushBindingDomain, binderType), (p.pushBindingBody, body)]
  | .letE _ type value body _ => #[(p.pushLetVarType, type), (p.pushLetValue, value), (p.pushLetBody, body)]
  | .mdata _ expr => extensions p expr
  | .proj _ _ struct => #[(p.pushProj, struct)]
  |  _ => #[]

partial def Lean.Expr.allSubExprs (p : SubExpr.Pos) (e : Expr) : Array (SubExpr.Pos × Expr) :=
  let exts := Lean.SubExpr.extensions p e |>.concatMap fun (pos, subexpr) ↦ allSubExprs pos subexpr
  exts.push (p, e)

def Lean.Expr.allPositions (e : Expr) : Array SubExpr.Pos := 
  e.allSubExprs .root |>.map Prod.fst

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
  | Expr.app _ _ => do
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

  | Expr.lam n _ b _ => do
    let name := match n with
      | Name.str _ s => s
      | _ => panic! "no name found"
    return { expr := b, val? := name, listRest := path.tail! }

  | Expr.forallE n _ b _ => do
    let name := match n with
      | Name.str _ s => s
      | _ => panic! "no name found"
    return { expr := b, val? := name, listRest := path.tail! }

  | Expr.mdata _ b => do
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

def Lean.Expr.allConvEnterArgs (e : Expr) :=
  e.allPositions.mapM <| Lean.SubExpr.Pos.toConvEnterArg e

open Meta Elab Term in
#eval show TermElabM _ from do
  let stx ← `(term| 1 + 2) 
  let t ← Term.elabTerm stx none
  let t ← reduce t
  t.allConvEnterArgs
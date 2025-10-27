import Lean
import LeanAideCore.Aides.Basic

namespace LeanAide

open Lean Meta Elab Term Parser PrettyPrinter

partial def idents : Syntax → List String
| Syntax.ident _ s .. => [s.toString]
| Syntax.node _ _ ss => ss.toList.flatMap idents
| _ => []

/--
Definitions and theorems in an expression that are both present in its
syntax tree and are *used constants*. Allows for dot notation.
-/
def defsInExpr (expr: Expr) : MetaM <| Array Name := do
  let typeStx ← delab expr
  let defNames := idents typeStx |>.eraseDups |>.map String.toName
  let defNames := defNames.filter fun name =>
    (excludePrefixes.all fun pre => !pre.isPrefixOf name) &&
    (excludeSuffixes.all fun suff => !suff.isSuffixOf name)
  let tails := defNames.filterMap fun n =>
    n.componentsRev.head?
  let constsInType := expr.getUsedConstants
  let dotNames := constsInType.filter fun n =>
    match n.componentsRev.head? with
    | some t => tails.contains t || defNames.contains n
    | none => false
  return dotNames

def defsInTypeRec (name : Name) (type: Expr) (depth:Nat) :
    MetaM <| Array Name := do
  match depth with
  | 0 => if ← isProp type then return #[] else return #[name]
  | k + 1 =>
    let children ← defsInExpr type
    let childrenTypes ← children.filterMapM fun n => do
      let info ← getConstInfo n
      pure <| some (n, info.type)
    let childValueTypes ← children.filterMapM fun n => do
      let info ← getConstInfo n
      match info with
      | ConstantInfo.defnInfo val => pure <| some (n, val.value)
      | _ => return none
    let res ← (childrenTypes ++ childValueTypes).mapM fun (n, t) => defsInTypeRec n t k
    return res.foldl (· ++ ·) children |>.toList |>.eraseDups |>.toArray

def isDefn (name: Name) : MetaM Bool := do
  let info ←  getConstInfo name
  match info with
  | .defnInfo _ => return true
  | _ => return false

open Elab Term
def defsInTypeString? (name: Name)(typeStr: String) (depth: Nat):
    TermElabM <| Option (Array Name) := do
    let typeStx? := Parser.runParserCategory (← getEnv) `term typeStr
    match typeStx? with
    | .error _ => return none
    | .ok stx =>
      try
        let type ← elabType stx
        defsInTypeRec name type depth
      catch _ =>
        return none

def defsInConst (name: Name) (depth: Nat) :
    MetaM <| Array Name := do
  let info ← getConstInfo name
  let base ←  defsInTypeRec name info.type depth
  base.filterM isDefn

def weightedDefsInConsts (names: List Name) (depth: Nat)
  (weight: Float := 1.0) (decay: Float := 0.8) : MetaM (Array (Name × Float)) :=
  match names with
  | [] => return #[]
  | h :: ts => do
    let tailWtdConsts ← weightedDefsInConsts ts depth (weight * decay) decay
    let headConsts ← defsInConst h depth
    let tailConsts := tailWtdConsts.map (fun (x, _) => x)
    let novel := headConsts.filter fun x => !tailConsts.contains x
    let novelWtdConsts :=
      novel.map fun x => (x, weight)
    let unsorted := novelWtdConsts ++ (tailWtdConsts.map fun (x, w) =>
      (x, if headConsts.contains x then w + weight else w))
    return unsorted.qsort fun (_, w₁) (_, w₂) => w₁ > w₂

def bestDefsInConsts (n: Nat) (names: List Name) (depth: Nat)
  (weight: Float := 1.0) (decay: Float := 0.8) : MetaM <| Array Name := do
    let weighted ← weightedDefsInConsts names depth weight decay
    return weighted[0:n] |>.toArray.map fun (n, _) => n

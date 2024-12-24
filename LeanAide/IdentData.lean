import LeanAide.Aides
import Lean
open Lean Meta Elab Term

namespace LeanAide.Meta

def isMatchCase : Name → Bool
| name =>
  let last? := name.components.reverse.head?
  (last?.getD Name.anonymous).toString.startsWith "match_"

partial def identNames : Syntax → MetaM (List Name)
| Syntax.ident _ _ s .. => do
  if (← isWhiteListed s) &&
    !(excludeSuffixes.any fun sfx => sfx.isSuffixOf s) && !(excludePrefixes.any fun pfx => pfx.isPrefixOf s) &&
    !(isMatchCase s)
    then return [s] else return []
| Syntax.node _ _ ss => do
    let groups ← ss.toList.mapM identNames
    return groups.flatten.eraseDup
| _ => return []

partial def propIdents (termExpr : Expr) :
    TermElabM (List (Expr × List Name)) := do
  match termExpr with
  | Expr.letE name type value body _ =>
    withLetDecl name  type value fun x => do
      let body' := body.instantiate1 x
      let ids ← propIdents body'
      let fromBody ← ids.mapM fun (e, ns) => do
        let e' ← mkLetFVars #[x] e
        return (e', ns)
      return fromBody ++ (← propIdents value)
  | Expr.lam name type body bi => do
    withLocalDecl name bi type fun x => do
      let body' := body.instantiate1 x
      let ids ← propIdents body'
      ids.mapM fun (e, ns) => do
        let e' ← mkForallFVars #[x] e
        return (e', ns)
  | _ =>
    let tkds ← termKinds
    let typeExpr ← inferType termExpr
    let typeExpr ← instantiateMVars typeExpr
    let stx ← delabMatchless typeExpr
    match stx with
    | Syntax.node _ _ ss => do
      let termStxs := ss.filter fun s => tkds.contains s.getKind
      let termExprs : Array Expr ← termStxs.filterMapM fun stx =>
        try
          Elab.Term.withoutErrToSorry do
          let t ← elabTerm stx none
          let t ←  instantiateMVars t
          pure t
        catch _ => pure none
      let groups ← termExprs.toList.mapM propIdents
      let children := groups.flatten
      if (← isProof termExpr) && (← termKinds).contains stx.getKind
      then
          let head := (typeExpr, ← identNames stx)
          return head :: children
        else
          return children
    | _ =>
      if (← isProof termExpr) && (← termKinds).contains stx.getKind
      then
        return [(typeExpr, ← identNames stx)]
      else
        return []


end LeanAide.Meta

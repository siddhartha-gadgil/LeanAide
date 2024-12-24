import LeanAide.Aides
import Lean
open Lean Meta Elab Term

namespace LeanAide.Meta

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
  -- logInfo m!"Called propIdents"
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
    let stx ← delabMatchless termExpr
    match stx with
    | `($f:ident $xs*) =>
      let s := f.getId
      let useHead := (← isWhiteListed s) &&
        !(excludeSuffixes.any fun sfx => sfx.isSuffixOf s) && !(excludePrefixes.any fun pfx => pfx.isPrefixOf s) &&
        !(isMatchCase s)
      let termExprs : Array Expr ← xs.filterMapM fun stx =>
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
          let prevNames ← identNames stx
          let names := if useHead then f.getId :: prevNames else prevNames
          let head := (typeExpr, names)
          return head :: children
        else
          return children
    | `($f:term $xs*) =>
      let termStxs := f :: xs.toList |>.map fun stx => stx.raw
      let termExprs : List Expr ← termStxs.filterMapM fun stx =>
        try
          Elab.Term.withoutErrToSorry do
          let t ← elabTerm stx none
          let t ←  instantiateMVars t
          pure <| some t
        catch _ => pure none
      let groups ← termExprs.mapM propIdents
      let children := groups.flatten
      if (← isProof termExpr) && (← termKinds).contains stx.getKind
      then
          let prevNames ← identNames stx
          let head := (typeExpr, prevNames)
          return head :: children
        else
          return children
    | stx =>
      match stx with
    | Syntax.node _ _ ss => do
      let termStxs := ss.filter fun s => tkds.contains s.getKind
      -- logInfo m!"Found {termStxs.size} of {ss.size} in {stx}"
      -- logInfo m!"Kinds: {ss.map Syntax.getKind}"
      -- for stx in ss do
      --   logInfo m!"Node with kind {stx.getKind} : {stx}"
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

structure PropIdentData where
  thm : String
  identifiers : List Name
deriving Inhabited, Repr, FromJson, ToJson

namespace PropIdentData

def fromPair (pair : Expr × List Name) : MetaM PropIdentData := do
  let (expr, idents) := pair
  let idents ← idents.filterM fun n => do
    let info? := (← getEnv).find? n
    pure info?.isSome
  let fmt ← PrettyPrinter.ppExpr expr
  return { thm := fmt.pretty, identifiers := idents }

def fromExpr (expr : Expr) : TermElabM <| List  PropIdentData := do
  let pairs ← propIdents expr
  pairs.mapM fun pair => fromPair pair

def ofName? (name : Name) : TermElabM <| Option (List PropIdentData) := do
  let decl? := (← getEnv).find? name
  let term? ←  decl?.bindM fun decl => do
    pure decl.value?
  let term? := term?.filter fun term => term.approxDepth < 60
  term?.mapM fun term => fromExpr term

def handles : IO <| Std.HashMap String IO.FS.Handle := do
  let handleList ←  ["test", "train", "valid", "all"].mapM fun s => do
    let pieces := ["premises", "identifiers", s ++ ".jsonl"]
    let h ← freshDataHandle pieces
    pure (s, h)
  return Std.HashMap.ofList handleList

def write (data: PropIdentData)(handles: List IO.FS.Handle) : CoreM Unit := do
    let l := (toJson data).compress
    for h in handles do
      h.putStrLn  l


def write' (data: PropIdentData)(group: String)
  (handles: Std.HashMap String IO.FS.Handle) : CoreM Unit := do
    let gh ←  match handles.get? group with
                | some h => pure h
                | none =>
                 IO.throwServerError
                    ("No handle for " ++ group)
    let h ←  match handles.get? "all" with
                | some h => pure h
                | none =>
                    IO.throwServerError "No handle for 'all'"
    data.write [gh, h]

def writeBatchM (batch: List Name)(group: String)
  (handles: Std.HashMap String IO.FS.Handle) (tag: String) : TermElabM Unit := do
    let gh ←  match handles.get? group with
                | some h => pure h
                | none =>
                 IO.throwServerError
                    ("No handle for " ++ group)
    let h ←  match handles.get? "all" with
                | some h => pure h
                | none =>
                    IO.throwServerError "No handle for 'all'"
    let mut count := 0
    for name in batch do
      let propData ← PropIdentData.ofName? name
      let propData := propData.getD []
      count := count + 1
      for data in propData do
        PropIdentData.write data [gh, h]
      if count % 100 == 0 then
        IO.eprintln s!"Wrote {count} names for {tag}"

def writeBatchCore (batch: List Name)(group: String)
  (handles: Std.HashMap String IO.FS.Handle) (tag: String) : CoreM Unit :=
    MetaM.run' do
      TermElabM.run' do
        writeBatchM batch group handles tag

end PropIdentData

def propIdentsFromName (name : Name) : TermElabM (List (Expr × List Name)) := do
  let decl ← getConstInfo name
  let type := decl.value!
  propIdents type

-- #print List.length_concat

-- #print List.of_concat_eq_concat

-- #eval PropIdentData.fromName ``List.length_concat

-- set_option pp.rawOnError true in
-- #eval PropIdentData.fromName ``List.of_concat_eq_concat


end LeanAide.Meta

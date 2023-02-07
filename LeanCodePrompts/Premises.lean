import Lean
import Mathlib
import LeanCodePrompts.ConstDeps

open Lean Meta Elab Parser PrettyPrinter

universe u v w u_1 u_2 u_3 u₁ u₂ u₃

open LeanAide.Meta
    
-- delaborator copied from Lean to modify
open Delaborator SubExpr in
partial def delabVerbose : Delab := do
  checkMaxHeartbeats "delab"
  let e ← getExpr
  let isProof ← (try Meta.isProof e catch _ => pure false)
  -- no need to hide atomic proofs
  let k ← getExprKind
  let stx ← delabFor k <|> (liftM $ show MetaM _ from throwError "don't know how to delaborate '{k}'")
  if isProof || (← getPPOption getPPAnalyzeTypeAscriptions <&&> getPPOption getPPAnalysisNeedsType <&&> pure !e.isMData) then
    let typeStx ← withType delab
    `(($stx : $typeStx)) >>= annotateCurPos
  else
    return stx


partial def Lean.Syntax.kinds (stx: Syntax)(depth?: Option ℕ := none) : List String :=
    if depth? = some 0 then
        []
    else
    match stx with
    | Syntax.node _ k args => 
        let head? : Option String := 
            k.components.head?.map (· |>.toString)
        match head? with
        | some head => head :: (args.map (kinds · (depth?.map (· -1))) |>.toList.join)
        | none => args.map (kinds · (depth?.map (· -1))) |>.toList.join
    | _ => []

partial def Lean.Syntax.idents (stx: Syntax)(depth? : Option ℕ := none) : List <| Name × ℕ  :=
    if depth? = some 0 then
        []
    else
    match stx with
    | Syntax.node _ _ args => 
         args.map (idents · (depth?.map (· -1))) 
            |>.toList.join.map (fun (s, m) => (s, m + 1))
    | Syntax.ident _ _ name .. => 
        if !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf name)) then 
            [(name, 0)]
        else []
    | _ => []

partial def Lean.Syntax.terms (stx: Syntax)(depth?: Option ℕ := none) : List <| String × ℕ × List Name :=
    if depth? = some 0 then
        []
    else
    match stx with
    | Syntax.node _ k args => 
        let head? : Option String := do 
            if 
                (`Lean.Parser.Term).isPrefixOf k ||
                k.components.head!.toString.startsWith "«term_" 
            then
                ← stx.reprint
            else
                none
        match head? with
        | some head => (head.trim, 0, stx.idents.map (·.1)) :: (args.map (terms · (depth?.map (· -1))) |>.toList.join.map (fun (s, m, l) => (s, m + 1, l)))
        | none => args.map (terms · (depth?.map (· -1))) 
            |>.toList.join.map (fun (s, m, l) => (s, m + 1, l))
    | _ => []

namespace LeanAide.Meta

def viewSyntax (s: String) : MetaM <| Syntax × String := do
    let c := runParserCategory (← getEnv) `term s
    match c with
    | Except.error e => throwError e
    | Except.ok s => pure (s, s.reprint.get!)


def nameDefSyntax (name: Name) : MetaM <| Option Syntax := do
    let exp? ← nameExpr? name
    match exp? with
    | none => pure none
    | some exp => do
        let stx ←  delab exp
        pure (some stx)

def nameDefView (name: Name) : MetaM String := do
    let stx? ← nameDefSyntax name
    return (stx?.get!.reprint.get!)

structure Premises where
    type : String
    defTerms : List <| String × ℕ × List Name
    defIdents : List <| Name × ℕ
    typeTerms : List <| String × ℕ × List Name
    typeIdents : List <| Name × ℕ 
deriving Repr, Inhabited

def Premises.defMainTerms (p: Premises) : List <| String × ℕ × List Name  :=
    p.defTerms.filter (
            fun (s, _) => s.1.length < 20)

def Premises.typeMainTerms (p: Premises) : List <| String × ℕ × List Name :=
    p.typeTerms.filter (fun (s, _) => (s.splitOn "=>").length == 1  
                && (s.splitOn "↦").length == 1)

def getPremises (name: Name)(depth? : Option ℕ := none ) : MetaM <| Premises := do
    let termStx? ← nameDefSyntax name
    let term ←  mkConstWithLevelParams name
    let type ← inferType term
    let typeView ← Meta.ppExpr type
    let typeStx ← delab type
    let defTerms := match termStx? with
        | none => []
        | some stx => stx.terms depth?
    let defTerms := defTerms.filter (fun (s, _) => s.1.length < 10000
        && !s.contains '\n')
    let defIdents := match termStx? with
        | none => []
        | some stx => stx.idents depth?
    pure {type := typeView.pretty 10000, defTerms := defTerms, defIdents := defIdents, typeTerms := typeStx.raw |>.terms depth?, typeIdents := typeStx.raw |>.idents depth?}


-- Testing

def showTerms (s: String) : MetaM <| List <| String × ℕ × List Name  := do
    let c := runParserCategory (← getEnv) `term s
    match c with
    | Except.error e => throwError e
    | Except.ok s => pure (s.terms)

def showIdents (s: String) : MetaM <| List <| Name × ℕ := do
    let c := runParserCategory (← getEnv) `term s
    match c with
    | Except.error e => throwError e
    | Except.ok s => pure (s.idents)

def showKinds (s: String) : MetaM <| List String := do
    let c := runParserCategory (← getEnv) `term s
    match c with
    | Except.error e => throwError e
    | Except.ok s => pure (s.kinds)

def nameDefTerms (name: Name)(depth? : Option ℕ := none ) : MetaM <| 
    List <| String × ℕ × List Name  := do
    let stx? ← nameDefSyntax name
    match stx? with
    | none => pure []
    | some stx => pure (stx.terms depth?)

def nameDefIdents (name: Name)(depth? : Option ℕ := none ) : MetaM <| List <| Name × ℕ := do
    let stx? ← nameDefSyntax name
    match stx? with
    | none => pure []
    | some stx => pure (stx.idents depth?)

#check List.join

#eval showTerms "fun n ↦ Nat.succ n"

#eval showIdents "fun n ↦ Nat.succ n"

#eval showTerms "fun n ↦ Nat.succ n = n + 1"

#eval viewSyntax "n = n + 1"

#eval showKinds "n = n + 1"

#eval nameDefSyntax ``List.join

#eval nameDefSyntax ``Nat.le_of_succ_le_succ

#eval nameDefTerms ``Nat.le_of_succ_le_succ


#eval nameDefIdents ``Nat.le_of_succ_le_succ

#eval getPremises ``Nat.le_of_succ_le_succ

#eval getPremises ``Nat.le_of_succ_le_succ (some 7)

#eval getPremises ``Nat.gcd_eq_zero_iff

#eval nameDefSyntax ``Nat.gcd_eq_zero_iff


#eval nameDefView ``Nat.gcd_eq_zero_iff

set_option pp.proofs false in 
#eval nameDefView ``Nat.gcd_eq_zero_iff

set_option pp.proofs.withType true in 
#eval nameDefView ``Nat.gcd_eq_zero_iff




theorem oddExample : ∀ (n : ℕ), ∃ m, m > n ∧ m % 2 = 1 := by
  intro n -- introduce a variable n
  use 2 * n + 1 -- use `m = 2 * n + 1`
  apply And.intro -- apply the constructor of `∧` to split goals
  · linarith -- solve the first goal using `linarith` 
  · simp [Nat.add_mod] -- solve the second goal using `simp` with the lemma `Nat.add_mod`

def egTerms : MetaM <| List <| String × ℕ × List Name := do
    let p ←  getPremises ``oddExample (some 30) 
    return p.defMainTerms

#eval egTerms

def egIdents : MetaM <| List <| Name × ℕ:= do
    let p ←  getPremises ``oddExample (some 30) 
    return p.defIdents

#eval egIdents

#check Linarith.lt_irrefl

#eval nameDefSyntax ``oddExample

def dataSize : MetaM ℕ := do
    let names ← constantNames
    return names.size 

#eval dataSize

def sampleExtract (n: ℕ := 100) : MetaM <|
        List (Name × (List <| String × ℕ × List Name) ×
        (List <| Name × ℕ)) := do
    let names ← constantNames
    let names := names.toList.take n
    names.mapM (fun n => do 
        let p ← nameDefTerms n
        let q ← nameDefIdents n
        pure (n, p, q)
        )

def batchPremiseExtractM (start stop: ℕ) : MetaM ℕ  := do
    let names ← constantNames
    let premisesFile := System.mkFilePath ["rawdata",
    s!"outer-premises.jsonl"]
    let h ← IO.FS.Handle.mk premisesFile IO.FS.Mode.append Bool.false
    let names := names.toList.drop start |>.take (stop - start)
    let mut cursor := start
    IO.println s!"start: {start}, stop: {stop}"
    for name in names do
        IO.println <| s!"starting: {cursor} {name}"
        let premises ← getPremises name (some 30)
        let p := premises.defMainTerms
        let pJson := p.map 
            (fun (s, n, l) => 
                Json.mkObj [
                    ("term", s),
                    ("depth", n),
                    ("local-idents", Json.arr  (
                        l.toArray
                        |>.filter (fun name => !names.contains name)
                        |>.map (fun name : Name =>
                            name.toString)))
                ]
            )
        let q:= premises.defIdents
        let q := q.filter (fun (name, _) => names.contains name)
        let qJson := q.map 
            (fun (name, n) => 
                Json.mkObj [
                    ("name", name.toString),
                    ("depth", n)
                ]
            )
        let js := Json.mkObj [
            ("name", name.toString),
            ("type", premises.type),
            ("terms", Json.arr 
                pJson.toArray),
            ("idents", Json.arr 
                qJson.toArray)
        ]
        let out := js.pretty 10000
        if out.length < 9000 then 
            h.putStrLn <| out
        IO.println <| s!"{cursor}. {name} : {premises.type} ({p.length}, {q.length}, {out.length})"
        cursor := cursor + 1
    return cursor

def batchPremiseExtractCore (start stop: ℕ) : CoreM ℕ := 
    (batchPremiseExtractM start stop).run'

-- #eval sampleExtract

set_option pp.proofs.withType true
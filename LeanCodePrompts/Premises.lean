import Lean
import Mathlib
import LeanCodePrompts.ConstDeps

open Lean Meta Elab Parser PrettyPrinter

def showSyntax (s: String) : MetaM <| Syntax × String := do
    let c := runParserCategory (← getEnv) `term s
    match c with
    | Except.error e => throwError e
    | Except.ok s => pure (s, s.reprint.get!)
    

partial def Lean.Syntax.terms (stx: Syntax) : List String :=
    match stx with
    | Syntax.node _ k args => 
        let head? : Option String := do 
            if (`Lean.Parser.Term).isPrefixOf k then
                ← stx.reprint
            else
                none
        match head? with
        | some head => head :: (args.map (terms) |>.toList.join)
        | none => args.map (terms) |>.toList.join
    | _ => []

partial def Lean.Syntax.idents (stx: Syntax) : List String :=
    match stx with
    | Syntax.node _ _ args => 
         args.map (idents) |>.toList.join
    | Syntax.ident _ _ n .. => [n.toString]
    | _ => []

def nameDefSyntax (name: Name) : MetaM <| Option Syntax := do
    let exp? ← nameExpr? name
    match exp? with
    | none => pure none
    | some exp => do
        let stx ←  delab exp
        pure (some stx)


structure Premises where
    type : String
    defTerms : List String
    defIdents : List String
    typeTerms : List String
    typeIdents : List String
deriving Repr, Inhabited

def Premises.defMainTerms (p: Premises) : List String :=
    p.defTerms.filter (fun s => (s.splitOn "=>").length == 1  
                && (s.splitOn "↦").length == 1)

def Premises.typeMainTerms (p: Premises) : List String :=
    p.typeTerms.filter (fun s => (s.splitOn "=>").length == 1  
                && (s.splitOn "↦").length == 1)

def getPremises (name: Name) : MetaM <| Premises := do
    let termStx? ← nameDefSyntax name
    let term ← mkConstWithFreshMVarLevels name
    let type ← inferType term
    let typeView ← Meta.ppExpr type
    let typeStx ← delab type
    let defTerms := match termStx? with
        | none => []
        | some stx => stx.terms
    let defIdents := match termStx? with
        | none => []
        | some stx => stx.idents
    pure {type := typeView.pretty, defTerms := defTerms, defIdents := defIdents, typeTerms := typeStx.raw.terms, typeIdents := typeStx.raw.idents}


-- Testing

def showTerms (s: String) : MetaM <| List String := do
    let c := runParserCategory (← getEnv) `term s
    match c with
    | Except.error e => throwError e
    | Except.ok s => pure (s.terms)

def showIdents (s: String) : MetaM <| List String := do
    let c := runParserCategory (← getEnv) `term s
    match c with
    | Except.error e => throwError e
    | Except.ok s => pure (s.idents)

def nameDefTerms (name: Name) : MetaM <| List String := do
    let stx? ← nameDefSyntax name
    match stx? with
    | none => pure []
    | some stx => pure (stx.terms)

def nameDefIdents (name: Name) : MetaM <| List String := do
    let stx? ← nameDefSyntax name
    match stx? with
    | none => pure []
    | some stx => pure (stx.idents)

#check List.join

#eval showTerms "fun n ↦ Nat.succ n"

#eval showIdents "fun n ↦ Nat.succ n"

#eval nameDefSyntax ``List.join

#eval nameDefSyntax ``Nat.le_of_succ_le_succ

#eval nameDefTerms ``Nat.le_of_succ_le_succ


#eval nameDefIdents ``Nat.le_of_succ_le_succ

#eval getPremises ``Nat.le_of_succ_le_succ
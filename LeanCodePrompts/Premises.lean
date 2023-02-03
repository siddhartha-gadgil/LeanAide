import Lean
import Mathlib
import LeanCodePrompts.ConstDeps

open Lean Meta Elab Parser PrettyPrinter

def showSyntax (s: String) : MetaM <| Syntax × String := do
    let c := runParserCategory (← getEnv) `term s
    match c with
    | Except.error e => throwError e
    | Except.ok s => pure (s, s.reprint.get!)
    

partial def Lean.Syntax.terms (stx: Syntax)(depth?: Option ℕ := none) : List <| String × ℕ :=
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
        | some head => (head.trim, 0) :: (args.map (terms · (depth?.map (· -1))) |>.toList.join.map (fun (s, m) => (s, m + 1)))
        | none => args.map (terms · (depth?.map (· -1))) 
            |>.toList.join.map (fun (s, m) => (s, m + 1))
    | _ => []

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

def nameDefSyntax (name: Name) : MetaM <| Option Syntax := do
    let exp? ← nameExpr? name
    match exp? with
    | none => pure none
    | some exp => do
        let stx ←  delab exp
        pure (some stx)


structure Premises where
    type : String
    defTerms : List <| String × ℕ 
    defIdents : List <| Name × ℕ
    typeTerms : List <| String × ℕ
    typeIdents : List <| Name × ℕ 
deriving Repr, Inhabited

def Premises.defMainTerms (p: Premises) : List <| String × ℕ  :=
    p.defTerms.filter (
            fun (s, _) => s.1.length < 20 && (s.splitOn "=>").length == 1  
                && (s.splitOn "↦").length == 1)

def Premises.typeMainTerms (p: Premises) : List <| String × ℕ :=
    p.typeTerms.filter (fun (s, _) => (s.splitOn "=>").length == 1  
                && (s.splitOn "↦").length == 1)

def getPremises (name: Name)(depth? : Option ℕ := none ) : MetaM <| Premises := do
    let termStx? ← nameDefSyntax name
    let term ← mkConstWithFreshMVarLevels name
    let type ← inferType term
    let typeView ← Meta.ppExpr type
    let typeStx ← delab type
    let defTerms := match termStx? with
        | none => []
        | some stx => stx.terms depth?
    let defIdents := match termStx? with
        | none => []
        | some stx => stx.idents depth?
    pure {type := typeView.pretty, defTerms := defTerms, defIdents := defIdents, typeTerms := typeStx.raw |>.terms depth?, typeIdents := typeStx.raw |>.idents depth?}


-- Testing

def showTerms (s: String) : MetaM <| List <| String × ℕ  := do
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

def nameDefTerms (name: Name) : MetaM <| 
    List <| String × ℕ  := do
    let stx? ← nameDefSyntax name
    match stx? with
    | none => pure []
    | some stx => pure (stx.terms)

def nameDefIdents (name: Name) : MetaM <| List <| Name × ℕ := do
    let stx? ← nameDefSyntax name
    match stx? with
    | none => pure []
    | some stx => pure (stx.idents)

#check List.join

#eval showTerms "fun n ↦ Nat.succ n"

#eval showIdents "fun n ↦ Nat.succ n"

#eval showTerms "fun n ↦ Nat.succ n = n + 1"

#eval showSyntax "n = n + 1"

#eval showKinds "n = n + 1"

#eval nameDefSyntax ``List.join

#eval nameDefSyntax ``Nat.le_of_succ_le_succ

#eval nameDefTerms ``Nat.le_of_succ_le_succ


#eval nameDefIdents ``Nat.le_of_succ_le_succ

#eval getPremises ``Nat.le_of_succ_le_succ

#eval getPremises ``Nat.le_of_succ_le_succ (some 7)

#eval getPremises ``Nat.gcd_eq_zero_iff


theorem oddExample : ∀ (n : ℕ), ∃ m, m > n ∧ m % 2 = 1 := by
  intro n -- introduce a variable n
  use 2 * n + 1 -- use `m = 2 * n + 1`
  apply And.intro -- apply the constructor of `∧` to split goals
  · linarith -- solve the first goal using `linarith` 
  · simp [Nat.add_mod] -- solve the second goal using `simp` with the lemma `Nat.add_mod`

def egTerms : MetaM <| List <| String × ℕ := do
    let p ←  getPremises ``oddExample (some 20) 
    return p.defMainTerms

#eval egTerms

def egIdents : MetaM <| List <| Name × ℕ:= do
    let p ←  getPremises ``oddExample (some 30) 
    return p.defIdents

#eval egIdents

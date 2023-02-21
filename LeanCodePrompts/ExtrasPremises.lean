import LeanCodePrompts.Premises
open Lean Meta Elab Term Syntax PrettyPrinter Parser

namespace LeanAide.Meta


structure ConstsData where
    definitions : HashMap Name  Syntax
    theorems : HashMap Name  Syntax

def constsData : MetaM ConstsData := do
    let consts ← constantNameTypes
    let mut definitions := HashMap.empty
    let mut theorems := HashMap.empty
    for (c, type) in consts do
        let tstx ← delab type
        let tstx := tstx.raw.purge
        if ← Meta.isProp type then
            theorems := theorems.insert c tstx
        else
            definitions := definitions.insert c tstx
    return { definitions := definitions, theorems := theorems }

end LeanAide.Meta

open LeanAide.Meta

partial def Lean.Syntax.identsM (stx: Syntax)(context: Array Syntax)(maxDepth? : Option ℕ := none) : MetaM <| List <| Name × ℕ  := do
    if maxDepth? = some 0 then
        pure []
    else
    match ← namedArgument? stx with
    | some (arg, _) =>
        -- IO.println s!"Named: {arg}"
        let prev ←  identsM  arg context (maxDepth?.map (· -1))
        return prev.map (fun (s, m) => (s, m + 1))
    | none =>
    match ← proofWithProp? stx with
    | some (proof, _) =>
        -- IO.println s!"Proof: {proof}"
        let prev ←  identsM  proof context (maxDepth?.map (· -1))
        return prev.map (fun (s, m) => (s, m + 1))
    | none =>
    match ← lambdaStx? stx with
    | some (body, args) =>
        -- IO.println s!"Lambda: {args}"
        let prev ←  identsM  body (context ++ args) (maxDepth?.map (· -1))
        return prev.map (fun (s, m) => (s, m + args.size))
    | none =>
        match stx with
        | Syntax.node _ _ args => 
            let prev ← args.mapM (identsM · context (maxDepth?.map (· -1))) 
            return prev.toList.join.map (fun (s, m) => (s, m + 1))
        | Syntax.ident _ _ name .. => 
            let contextVars := context.filterMap getVar
            -- IO.println s!"Context: {contextVars} from {context}"
            if  !(contextVars.contains name) &&
                !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf name)) then 
                pure [(name, 0)]
            else pure []
        | _ => pure []


-- -- #eval termKindList


partial def Lean.Syntax.termsM (context : Array Syntax)(stx: Syntax)(maxDepth? : Option ℕ := none) : MetaM <| List <| TermData × ℕ  := do
    let tks ← termKindList
    let tks := tks.map (·.1)
    if maxDepth? = some 0 then
        pure []
    else
    match ← namedArgument? stx with
    | some (arg, _) =>
        -- IO.println s!"Named: {arg}"
        let prev ←  termsM  context arg (maxDepth?.map (· -1))
        return prev.map (fun (s, m) => (s, m + 1))
    | none =>
    match ← proofWithProp? stx with
    | some (proof, _) =>
        -- IO.println s!"Proof: {proof}"
        let prev ←  termsM context  proof (maxDepth?.map (· -1))
        return prev.map (fun (s, m) => (s, m + 1))
    | none =>
    match ← lambdaStx? stx with
    | some (body, args) =>
        -- IO.println s!"Lambda: {args}"
        let prev ←  termsM (context ++ args) body (maxDepth?.map (· -1))
        return prev.map (fun (s, m) => (s, m + args.size))
    | none =>
        match stx with
        | Syntax.node _ k args => 
            -- IO.println s!"Node: {k}"
            let prev ← args.mapM (termsM context · (maxDepth?.map (· -1)))
            let head : TermData := ⟨context, stx.purge⟩
            if tks.contains k then 
                return (head, 0) :: prev.toList.join.map (fun (s, m) => (s, m + 1))
            else  
            return prev.toList.join.map (fun (s, m) => (s, m + 1))
        | Syntax.ident .. => 
             pure []
        | _ => pure []



partial def Lean.Syntax.proofsM (context : Array Syntax)(stx: Syntax)(maxDepth? : Option ℕ := none) : MetaM <| List <| PropProofData × ℕ  := do
    if maxDepth? = some 0 then
        pure []
    else
    match ← namedArgument? stx with
    | some (arg, _) =>
        -- IO.println s!"Named: {arg}"
        let prev ←  proofsM  context arg (maxDepth?.map (· -1))
        return prev.map (fun (s, m) => (s, m + 1))
    | none =>
    match ← proofWithProp? stx with
    | some (proof, prop) =>
        -- IO.println s!"Proof: {proof}"
        let prev ←  proofsM context  proof (maxDepth?.map (· -1))
        let head : PropProofData := ⟨context, prop, proof⟩
        return  (head, 0) :: prev.map (fun (s, m) => (s, m + 1))
    | none =>
    match ← lambdaStx? stx with
    | some (body, args) =>
        -- IO.println s!"Lambda: {args}"
        let prev ←  proofsM (context ++ args) body (maxDepth?.map (· -1))
        return prev.map (fun (s, m) => (s, m + args.size))
    | none =>
        match stx with
        | Syntax.node _ _ args => 
            -- IO.println s!"Node: {k}"
            let prev ← args.mapM (proofsM context · (maxDepth?.map (· -1)))
            return prev.toList.join.map (fun (s, m) => (s, m + 1))
        | Syntax.ident .. => 
             pure []
        | _ => pure []


def PremiseData.get(ctx : Array Syntax)(name?: Name)(prop pf : Syntax) : MetaM PremiseData := do
    let subProofs: List (PropProofData × ℕ) ←  pf.proofsM ctx
    let subTerms : List (TermData × ℕ)  ← Syntax.termsM ctx pf
    let ids : List (Name  × ℕ) ← pf.identsM ctx 
    return ⟨ctx, name?, prop.purge, subTerms.toArray, subProofs.toArray, ids.toArray⟩

def viewData (name: Name) : MetaM <| String := do
    let (stx, tstx) ← nameDefTypeSyntax name
    -- IO.println s!"{stx.reprint.get!}"
    -- IO.println s!"{← proofWithProp? stx}"
    let data ←  PremiseData.get  #[] name tstx stx 
    data.view

-- #eval viewData ``Nat.succ_le_succ

partial def Lean.Syntax.kinds (stx: Syntax)(maxDepth?: Option ℕ := none) : List String :=
    if maxDepth? = some 0 then
        []
    else
    match stx with
    | Syntax.node _ k args => 
        let head? : Option String := 
            k.components.head?.map (· |>.toString)
        match head? with
        | some head => head :: (args.map (kinds · (maxDepth?.map (· -1))) |>.toList.join)
        | none => args.map (kinds · (maxDepth?.map (· -1))) |>.toList.join
    | _ => []

partial def Lean.Syntax.idents (stx: Syntax)(maxDepth? : Option ℕ := none) : List <| Name × ℕ  :=
    if maxDepth? = some 0 then
        []
    else
    match stx with
    | Syntax.node _ _ args => 
         args.map (idents · (maxDepth?.map (· -1))) 
            |>.toList.join.map (fun (s, m) => (s, m + 1))
    | Syntax.ident _ _ name .. => 
        if !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf name)) then 
            [(name, 0)]
        else []
    | _ => []


partial def Lean.Syntax.terms (stx: Syntax)(maxDepth?: Option ℕ := none) : 
     MetaM <|  List <| String × ℕ × List Name := do
    let tks ← termKindList
    let tks := tks.map (·.1)
    if maxDepth? = some 0 then
        pure []
    else
    match stx with
    | Syntax.node _ k args => 
        match stx with 
        | `(proved_prop| ($pf:term =: $_:term )) =>  
           pf.raw.terms
        | _ =>
        let head? : Option String := do 
            if 
                k ∈ tks 
            then
                ← stx.reprint
            else
                none
        let argTerms ← args.mapM (terms · (maxDepth?.map (· -1))) 
        let argTerms := argTerms.toList.join
        match head? with
        | some head =>             
            return (head.trim, 0, stx.idents.map (·.1)) ::
                 (argTerms.map (fun (s, m, l) => (s, m + 1, l)))
        | none => 
            return (argTerms.map (fun (s, m, l) => (s, m + 1, l)))
    
    | _ => pure []

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



def getPremises (name: Name)(maxDepth? : Option ℕ := none ) : MetaM <| Premises := do
    let termStx? ← nameDefSyntaxVerbose name
    let term ←  mkConstWithLevelParams name
    let type ← inferType term
    let typeView ← Meta.ppExpr type
    let typeStx ← delab type
    let defTerms ←  match termStx? with
        | none => pure []
        | some stx => stx.terms maxDepth?
    let defTerms := defTerms.filter (fun (s, _) => s.1.length < 10000
        && !s.contains '\n')
    let defIdents := match termStx? with
        | none => []
        | some stx => stx.idents maxDepth?
    pure {type := typeView.pretty 10000, defTerms := defTerms, defIdents := defIdents, typeTerms := ←  typeStx.raw |>.terms maxDepth?, typeIdents := typeStx.raw |>.idents maxDepth?}


-- Testing



def showTerms (s: String) : MetaM <| List <| String × ℕ × List Name  := do
    let c := runParserCategory (← getEnv) `term s
    match c with
    | Except.error e => throwError e
    | Except.ok s => (s.terms)

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

def nameDefTerms (name: Name)(maxDepth? : Option ℕ := none ) : MetaM <| 
    List <| String × ℕ × List Name  := do
    let stx? ← nameDefSyntax name
    match stx? with
    | none => pure []
    | some stx => (stx.terms maxDepth?)

def nameDefIdents (name: Name)(maxDepth? : Option ℕ := none ) : MetaM <| List <| Name × ℕ := do
    let stx? ← nameDefSyntax name
    match stx? with
    | none => pure []
    | some stx => pure (stx.idents maxDepth?)

#check List.join

-- #eval showTerms "fun n ↦ Nat.succ n"

-- #eval showIdents "fun n ↦ Nat.succ n"

-- #eval showTerms "fun n ↦ Nat.succ n = n + 1"

-- #eval viewSyntax "n = n + 1"

-- #eval viewSyntax "f (n := m)"

-- #eval nameDefSyntax ``Nat.succ_le_succ

#check Lean.Parser.Term.namedArgument

-- #eval showKinds "n = n + 1"

def egTerms : MetaM <| List <| String × ℕ × List Name := do
    let p ←  getPremises ``oddExample (some 30) 
    return p.defMainTerms

-- #eval egTerms

def egIdents : MetaM <| List <| Name × ℕ:= do
    let p ←  getPremises ``oddExample (some 50) 
    return p.defIdents

-- #eval egIdents

def egGpIdents : MetaM NameGroups := do
    let nd ← egIdents
    return groupedNames nd.toArray

-- #eval egGpIdents

#check Linarith.lt_irrefl

-- -- #eval nameDefSyntax ``oddExample

def dataSize : MetaM ℕ := do
    let names ← constantNames
    return names.size 

-- #eval dataSize

def boundedDataSize (n: ℕ) : MetaM ℕ := do
    let names ← constantNames
    let names ← names.filterM (boundedDef n)
    return names.size

-- #eval boundedDataSize 50

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

-- -- #eval sampleExtract

theorem imo_1964_q1b : ∀ (n : ℕ), (2 ^ n + 1) % 7 ≠ 0
    | 0 | 1 | 2 => by decide
    | n + 3 => by
      rw [pow_add, Nat.add_mod, Nat.mul_mod, show 2 ^ 3 % 7 = 1 from by rfl]
      simp [imo_1964_q1b n]


-- set_option pp.proofs.withType true in
-- -- #eval nameDefView ``imo_1964_q1b

-- #eval nameDefView ``imo_1964_q1b

-- -- #eval nameDefViewVerbose ``imo_1964_q1b
import Lean
import Std.Data.HashMap
import LeanAide.ConstDeps
import LeanAide.VerboseDelabs

/-!
# Premise data

Here we extract premise data from all definitions in the environment. This includes proofs in the environment as well as sub-proofs in proofs/definitions. The main technique for working with subproofs is the use of the custom *verbose* delaborators that rewrite the syntax tree to include the statements of the proof terms, in the syntax `proof =: prop`. 

We are using premises is a broad sense, including:

- identifiers
- propositions that are proved by sub-terms (lemmas)
- terms that are arguments of functions (instantiations)

As theorems are equivalent to others where we trade `∀` with context terms, we associate groups. Further, we exclude statements derived in this way (i.e., by `intro`) from the list of lemmas.
-/

open Lean Meta Elab Parser PrettyPrinter

universe u v w u_1 u_2 u_3 u₁ u₂ u₃

open LeanAide.Meta


def freshDataHandle (fileNamePieces : List String)(clean: Bool := true) : IO IO.FS.Handle := do
    let path := System.mkFilePath <| [".", "rawdata"] ++ fileNamePieces
    let dir := System.mkFilePath <| [".", "rawdata"] ++ 
        fileNamePieces.take (fileNamePieces.length - 1)
    if !(← dir.pathExists) then
        IO.FS.createDirAll dir
    if clean then
        IO.FS.writeFile path "" 
    IO.FS.Handle.mk path IO.FS.Mode.append


def fileNamePieces : HashMap (String × String) (List String) :=
    HashMap.ofList <|
        ["core", "full", "identifiers", "ident_pairs", "ident_strings",
        "term_pairs", "lemma_pairs"].bind fun kind => 
            ("all" :: "extra" :: groups).map fun group => ((kind, group), ["premises", kind, group++".jsonl"])

def mainFileNamePieces : HashMap (String × String) (List String) :=
    HashMap.ofList <|
        ["core",  "identifiers", "ident_pairs", "ident_strings",
        "term_pairs", "lemma_pairs"].bind fun kind => 
            ("all"  :: groups).map fun group => ((kind, group), ["premises", kind, group++".jsonl"])

def fileHandles (clean : Bool := true) : IO (HashMap (String × String) IO.FS.Handle)  := do
    let mut handles := HashMap.empty
    for (k, v) in fileNamePieces.toList do
        handles := handles.insert k <| ← freshDataHandle v clean
    return handles

def mainFileHandles : IO (HashMap (String × String) IO.FS.Handle) := do
    let mut handles := HashMap.empty
    for (k, v) in mainFileNamePieces.toList do
        handles := handles.insert k <| ← freshDataHandle v
    return handles

set_option pp.unicode.fun true
set_option pp.match false

/-- Syntax as json -/
instance : ToJson Syntax := ⟨fun (d: Syntax) ↦ shrink d.reprint.get!.trim⟩

/-- Subterms in a premise -/
structure TermData where
    context : Array Syntax
    value : Syntax
    size : Nat
    depth: Nat
    isProp: Bool
deriving Repr, ToJson, BEq

/-- Increase depth of a subterm (for recursion) -/
def TermData.increaseDepth (d: Nat) : TermData → TermData :=
fun data ↦
    ⟨data.context, data.value, data.size, data.depth + d, data.isProp⟩

/-- Lemma data with proofs -/
structure PropProofData where
    context : Array Syntax
    prop : Syntax
    proof: Syntax
    propSize: Nat 
    proofSize: Nat
    depth: Nat
deriving Repr, ToJson, BEq

/-- Increase depth for a lemma (for recursion) -/
def PropProofData.increaseDepth (d: Nat) : PropProofData → PropProofData :=
fun data ↦
    ⟨data.context, data.prop, data.proof, data.propSize, data.proofSize, data.depth + d⟩

/-- Full premise data for a proposition -/        
structure PremiseData  where 
 context : (Array Syntax) -- variables, types, binders
 name? :       Option Name  -- name
 defnName: Name -- name of definition from which it arose
 type :       Syntax  -- proposition
 typeGroup : Syntax  -- proposition group
 proof: Syntax  -- proof
 typeSize : Nat
 proofSize : Nat
 terms :       Array (TermData)  -- instantiations
 propProofs :       Array (PropProofData)  -- sub-proofs
 ids :       Array (String ×  Nat)  -- proof identifiers used
 deriving Repr, ToJson, BEq

def PremiseData.writeFull (data: PremiseData)(group: String)(handles: HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let l := (toJson data).pretty 10000000
    -- IO.println s!"Handles:  {handles.toList.map (fun (k, _) => k)}"
    let key := ("full", group) 
    -- IO.println s!"Key: {key}, contained in handles: {handles.contains key}"
    let gh ←  match handles.find? key with
                | some h => pure h   
                | none => 
                 IO.throwServerError 
                    ("No handle for " ++ group ++ " in " ++ "full")
    let h ←  match handles.find? ("full", "all") with
                | some h => pure h
                | none => 
                    IO.throwServerError "No handle for 'all' in full"
    if l.length < 9000000 then
                        h.putStrLn  l
                        gh.putStrLn l

structure CoreTermData where
    context : Array String
    value : String
    isProp: Bool
deriving Repr, ToJson, FromJson, BEq

structure CorePropData where
    context : Array String
    prop : String
deriving Repr, ToJson, FromJson, BEq

def CorePropData.ofPropProof (propPf : PropProofData) : CorePropData :=
    ⟨propPf.context.map (fun s => shrink s.reprint.get!.trim),
    shrink propPf.prop.reprint.get!.trim⟩

def CorePropData.thm (data: CorePropData) : String :=
     data.context.foldr (fun s c => s ++ " " ++ c) s!" : {data.prop}"

structure CorePremiseDataDirect where
    context : Array String
    name? :       Option Name  -- name
    type : String
    typeGroup : String
    ids : Array String
    terms : List CoreTermData
    lemmas : Array CorePropData 
deriving Repr, ToJson, FromJson, BEq

def CorePremiseDataDirect.fromPremiseData (pd: PremiseData) : CorePremiseDataDirect := 
    ⟨pd.context.map (fun s => shrink s.reprint.get!.trim), 
    pd.name?,
    shrink pd.type.reprint.get!.trim,
    shrink pd.typeGroup.reprint.get!.trim,
    pd.ids.map (fun (n, _) => shrink n), 
    pd.terms.toList.map (fun td => 
       ⟨td.context.map (fun s => shrink s.reprint.get!.trim),
       shrink td.value.reprint.get!.trim, td.isProp⟩) |>.eraseDups, 
    pd.propProofs.map CorePropData.ofPropProof⟩

structure CorePremiseData extends CorePremiseDataDirect where
    namedLemmas : Array String
    thm: String := context.foldr (fun id s => id ++ s) " : " ++ type
    idString := ids.foldl (fun s id => s ++ id ++ "; ") ""
deriving Repr, ToJson, FromJson

def checkName (name: Name) : MetaM Bool := do
    let l ← resolveGlobalName name
    return l.length > 0 

-- #eval checkName `Or.inl

def getDefn? (name: String)(propMap: HashMap String String) : MetaM <| Option String := do
    match propMap.find? name with
    | some s => return some s
    | none => do
    let l ← resolveGlobalName name
    let names := l.map (fun (n, _) => n.toString)
    return names.findSome? (fun n => propMap.find? n)

namespace CorePremiseData

def fromDirect (direct: CorePremiseDataDirect)(propMap : HashMap String String) : MetaM CorePremiseData := do 
    return {
    context := direct.context,
    name? := direct.name?,
    type := direct.type,
    typeGroup := direct.typeGroup,
    ids := direct.ids
    terms := direct.terms,
    lemmas := direct.lemmas,
    namedLemmas := ←  direct.ids.filterMapM (
        fun id =>  getDefn? id propMap)
    }

def fromPremiseData (pd: PremiseData)(propMap : HashMap String String) : MetaM CorePremiseData := 
    CorePremiseData.fromDirect (CorePremiseDataDirect.fromPremiseData pd) propMap


def write (data: CorePremiseData)(group: String)(handles: HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let l := (toJson data).pretty 10000000
    let gh ← match handles.find? ("core", group) with
                | some h => pure h
                | none => 
                    IO.throwServerError ("No handle for " ++ group ++ " in " ++ "core")                
    let h ←  match handles.find? ("core", "all") with
                | some h => pure h
                | none => 
                    IO.throwServerError "No handle for 'all' in core"
    if l.length < 9000000 then
                        h.putStrLn  l
                        gh.putStrLn l

end CorePremiseData

namespace PremiseData

def filterIds (pd: PremiseData)(p: Name → Bool) : PremiseData := 
    ⟨pd.context, pd.name?, pd.defnName,  pd.type, pd.typeGroup, pd.proof, pd.typeSize, pd.proofSize, pd.terms, pd.propProofs, pd.ids.filter (fun (n, _) => p n)⟩

def increaseDepth (d: Nat) : PremiseData → PremiseData :=  
fun data ↦
    ⟨data.context, data.name?, data.defnName, data.type, data.typeGroup, data.proof, data.typeSize, data.proofSize, (data.terms.map (fun td => td.increaseDepth d)), (data.propProofs.map (fun p => p.increaseDepth d)),
        (data.ids.map (fun (n,  m) => (n,  m + d))) ⟩

def coreData (data: PremiseData)(propMap : HashMap String String) : MetaM CorePremiseData := 
    CorePremiseData.fromPremiseData data propMap

def write (data: PremiseData)(group: String)
    (handles: HashMap (String × String) IO.FS.Handle)
    (propMap : HashMap String String) : MetaM Unit := do 
        data.writeFull group handles
        let coreData ←  CorePremiseData.fromPremiseData data propMap
        coreData.write group handles

end PremiseData

/-- Remove the added `=: prop` from syntax -/
partial def Lean.Syntax.purge: Syntax → Syntax := fun stx ↦
  match stx with
  | Syntax.node info k args =>
    match stx with
    | `(($pf:term =: $_:term)) =>
      pf.raw.purge
    | `(($p : Prop)) => 
        p.raw.purge
    | _ =>
      Syntax.node info k (args.map Syntax.purge) 
  | s => s

def termKinds : MetaM <| SyntaxNodeKindSet :=  do
    let env ← getEnv
    let categories := (parserExtension.getState env).categories
    let termCat? := getCategory categories `term
    return termCat?.get!.kinds    

def termKindList : MetaM <| List (SyntaxNodeKind × Unit) := do
    let s ← termKinds
    pure <| s.toList 

partial def Lean.Syntax.size (stx: Syntax) : Nat := 
    match stx with
    | Syntax.ident _ _ _ _ => 1
    | Syntax.node _ _ args => args.foldl (fun acc x => acc + x.size) 0
    | _ => 1

/-- Compute recursively premise-data of sublemmas as well as the identifiers, instantiations and subproofs. These are used at the top level recursively.

The parameter `isArg` specifies whether the term is an argument of a function. This is used to determine whether to add the term to the list of instantiations. 

The parameter `propHead?` specifies the head of the group of propositions, where groups are related by `intro`, i.e., moving from `∀` to context variables. This is used to determine whether to add the proposition to the list of lemmas.
-/
partial def Lean.Syntax.premiseDataAuxM (context : Array Syntax)(defnName: Name)(stx: Syntax)(propHead? : Option Syntax)(isArg: Bool)(maxDepth? : Option Nat := none) : 
    MetaM (
        Array (TermData) ×
        Array (PropProofData) ×
        Array (String × Nat) ×
        List PremiseData
        )  := do
    if maxDepth? = some 0 then
        pure (#[], #[], #[], [])    
    else
    -- IO.println s!"Recursive call:\n{stx}"
    let tks ← termKindList
    let tks := tks.map (·.1)
    match ← wrappedProp? stx with
    | some prop =>
        let (ts, pfs, ids, ps) ←  prop.premiseDataAuxM context defnName none  false maxDepth?
        if isArg then -- this is an instantiation
            let head : TermData := 
                ⟨context, stx.purge, stx.purge.size, 0, true⟩
            pure <| (ts.push head, pfs, ids, ps)
        else 
            pure (ts, pfs, ids, ps)
    | none =>
    match ← namedArgument? stx with
    | some (arg, _) => -- named argument of a function, name ignored
        arg.premiseDataAuxM context defnName none  isArg (maxDepth?.map (· -1))
    | none =>
    -- the special `proof =: prop` syntax 
    match ← proofWithProp? stx with
    | some (proof, prop) =>
        -- start a group if not in a group
        let newPropHead :=
            match propHead? with
            | some p => p
            | none => prop
        /- compute the data for the subproof; 
        subproof not an instantiation, is part of a new/old group. 
        -/
        let prev ←  
            proof.premiseDataAuxM context defnName (some newPropHead) false (maxDepth?.map (· -1))
        let (ts, pfs, ids, ps) := prev
        let prop := prop.purge
        let proof := proof.purge
        let newPfs :=
            if propHead?.isSome then -- exclude lemma if in prior group
                pfs
            else 
                let headPf : PropProofData := 
                    ⟨context, prop, proof, prop.size, proof.size, 0⟩
                pfs.map (fun s ↦ s.increaseDepth 1) |>.push headPf
        let head : PremiseData := 
            ⟨context, none, defnName, prop, newPropHead, proof, prop.size, proof.size, ts, pfs, ids⟩
        return (ts.map (fun t ↦ t.increaseDepth 1),
                newPfs,
                ids.map (fun (s, m) => (s, m + 1)),
                head :: ps)
    | none =>
    match ← letStx? stx with -- term is a let
    | some (n, type, val, body) =>
        let decl' : Syntax ← `(Lean.Parser.Term.letDecl|$n:ident : $type := $val)
        let decl'' : Syntax ← `(Lean.Parser.Term.funBinder|($n:ident : $type:term))
        let decl : Syntax := 
            if (← proofWithProp? val).isSome then
                decl''
            else  decl' 
        let prev ←   
            body.raw.premiseDataAuxM (context ++ #[decl]) defnName propHead? false (maxDepth?.map (· -1))
        let prev' ←  
            val.raw.premiseDataAuxM (context) defnName propHead? false (maxDepth?.map (· -1))
        let (ts, pfs, ids, ps) := prev
        let (ts', pfs', ids', ps') := prev'
        return (ts.map (fun s => (s.increaseDepth 1)) ++
                ts'.map (fun s => (s.increaseDepth 1)),
                pfs.map (fun s => (s.increaseDepth 1)) ++
                pfs'.map (fun s => (s.increaseDepth 1)),
                ids.map (fun (s, m) => (s, m + 1)) ++
                ids'.map (fun (s, m) => (s, m + 1)),
                ps ++ ps')
    | none =>
    match ← lambdaStx? stx with -- term is a lambda
    | some (body, args) =>
        let prev ←  /- data for subterm; not an instantiation; 
        inherits proposition group: if this is a proof, so would the previous term and hence we will have a group.  -/
            body.premiseDataAuxM (context ++ args) defnName propHead? false (maxDepth?.map (· -1))
        let (ts, pfs, ids, ps) := prev
        -- if ids.size > 0 then
        --             IO.println s!"lambda body ids {ids}"
        return (ts.map (fun s => (s.increaseDepth args.size)),
                pfs.map (fun s => (s.increaseDepth args.size)),
                ids.map (fun (s, m) => (s, m + args.size)),
                ps)
    | none =>
    match ← appStx? stx with
    | some (f, args) =>
        let prev ←  f.premiseDataAuxM context defnName none false (maxDepth?.map (· -1))
        let mut (ts, pfs, ids, ps) := prev
        for arg in args do
            let block ← structuralTerm f
            let prev ←  
                arg.premiseDataAuxM context defnName none (!block) (maxDepth?.map (· -1))
            let (ts', pfs', ids', ps') := prev
            -- if ids'.size > 0 then
            --         IO.println s!"arg ids' {ids'}"
            ts := ts ++ ts'
            pfs := pfs ++ pfs'
            ids := ids ++ ids'
            ps := ps ++ ps'
        if isArg then -- this is an instantiation
            let head : TermData := 
                ⟨context, stx.purge, stx.purge.size, 0, false⟩
            ts := ts.push head
        return (ts.map (fun s => s.increaseDepth 1),
                pfs.map (fun s => s.increaseDepth 1),
                ids.map (fun (s, m) => (s, m + 1)),
                ps) 
    | none =>
        match stx with
        | Syntax.node _ k args => 
            -- IO.println s!"kind {k}; args {args.map (·.reprint.get!)}}"
            let prevs ← args.mapM (
                premiseDataAuxM context defnName · none false (maxDepth?.map (· -1)))
            let mut ts: Array (TermData) := #[]
            let mut pfs: Array (PropProofData) := #[]
            let mut ids: Array (String × Nat) := #[]
            let mut ps: List PremiseData := []
            for prev in prevs do
                let (ts', pfs', ids', ps') := prev
                -- if ids'.size > 0 then
                --     IO.println s!"ids' {ids'}"
                ts := ts ++ ts'.map (fun s => s.increaseDepth 1)
                pfs := pfs ++ pfs'.map (fun s => s.increaseDepth 1)
                ids := ids ++ ids'.map (fun (s, m) => (s, m + 1))
                ps := ps ++ ps'
            if isArg && tks.contains k then 
                let head : TermData := 
                    ⟨context, stx.purge, stx.purge.size, 0, false⟩
                ts := ts.push (head)
            return (ts, pfs, ids, ps)
        | Syntax.ident _ _ name .. => 
            -- IO.println s!"ident {name}"
            let contextVars := context.filterMap getVar?
            if  !(contextVars.contains name) &&
                !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf name)) then 
                pure (#[], #[], #[(stx.reprint.get!.trim, 0)], [])
            else
                -- IO.println s!"skipping {name}" 
                pure (#[], #[], #[], [])
        | _ => pure (#[], #[], #[], [])

def Lean.Syntax.premiseDataM (context : Array Syntax)
    (proof prop: Syntax)(includeHead: Bool)(name? : Option Name)(defnName : Name)(maxDepth? : Option Nat := none) : 
    MetaM (List PremiseData) := do
    let (ts, pfs, ids, ps) ← proof.premiseDataAuxM context defnName (some prop) false maxDepth?
    if includeHead then
        let head : PremiseData := ⟨context, name?, defnName, prop.purge, prop.purge, proof.purge, prop.purge.size, proof.purge.size, ts, pfs, ids⟩
        return head :: ps
    else return ps


structure DefData where
    name : Name
    type : Syntax
    value : Syntax
    isProp : Bool
    typeDepth : Nat
    valueDepth : Nat
    premises : List PremiseData -- empty if depth exceeds bound
    deriving Inhabited, ToJson, Repr

def DefData.getM? (name: Name)(term type: Expr) : MetaM (Option  DefData) :=  withOptions (fun o => 
                    let o' :=  pp.match.set o false
                    pp.unicode.fun.set o' true)
    do
    if term.approxDepth > (← getDelabBound) || type.approxDepth > (← getDelabBound) then return none
    else
    let (stx, _) ←  delabCore term {} (delabVerbose)
    let (tstx, _) ←  delabCore type {} (delabVerbose)
    let isProp ← Meta.isProof term
    let premises ← 
        Lean.Syntax.premiseDataM #[] stx tstx isProp (some name) name
    let typeDepth := type.approxDepth
    let valueDepth := term.approxDepth
    return some {name := name, type := tstx.raw.purge, value := stx.raw.purge, isProp := isProp, typeDepth := typeDepth.toNat, valueDepth := valueDepth.toNat, premises := premises.eraseDups}

def DefData.ofNameM? (name: Name) : MetaM (Option DefData) := do
    let info ←  getConstInfo name
    let type := info.type
    let term? := info.value? 
    match term? with
    | some term => DefData.getM? name term type
    | none => return none

def depths (name: Name) : MetaM (Option (Nat × Nat)) := do
    let info ←  getConstInfo name
    let type := info.type
    let term? := info.value? 
    match term? with
    | some term => return some (term.approxDepth.toNat, type.approxDepth.toNat)
    | none =>
        logInfo m!"no value for {name}" 
        return none

def verboseView? (name: Name) : MetaM (Option String) := 
    withOptions (fun o => 
                    let o' :=  pp.match.set o false
                    pp.unicode.fun.set o' true)
    do
    let info ←  getConstInfo name
    let term? := info.value? 
    match term? with
    | some term => 
        let (stx, _) ←  delabCore term {} (delabVerbose)
        return some <| shrink stx.raw.reprint.get!
    | none => return none

def verboseViewCore? (name: Name) : CoreM (Option String) :=
    (verboseView? name).run' {}

def DefData.ofNameCore? (name: Name) : CoreM (Option DefData) :=
    (DefData.ofNameM? name).run' {}

def PremiseData.ofNames (names: List Name) : MetaM (List PremiseData) := do
    let defs ← names.filterMapM DefData.ofNameM?
    return defs.bind (fun d => d.premises)

structure IdentData where
    context : Array String
    type : String
    ids : Array String
    deriving Inhabited, ToJson, FromJson

structure IdentPair where
    context : Array String
    type : String
    id : String
deriving Inhabited, ToJson

namespace IdentData

def write (data: IdentData)(group: String)(handles: HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let thm := data.context.foldr (fun s c => s ++ c) s!" : {data.type}"
    let js := Json.mkObj [("theorem", thm), ("identifiers", toJson data.ids)]
    let l := js.pretty 10000000
    let gh ← match handles.find? ("identifiers", group) with
                | some h => pure h
                | none => 
                    IO.throwServerError ("No handle for " ++ group ++ " in " ++ "identifiers")                
    let h ←  match handles.find? ("identifiers", "all") with
                | some h => pure h
                | none => 
                    IO.throwServerError "No handle for 'all' in indentifiers"
    if l.length < 9000000 then
                        h.putStrLn  l
                        gh.putStrLn l

def writeString (data: IdentData)(group: String)(handles: HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let thm := data.context.foldr (fun s c => s ++ c) s!" : {data.type}"
    let idString : String := data.ids.foldl (fun s i => s ++ i ++ "; ") ""
    let js := Json.mkObj [("theorem", thm), ("identifiers", idString)]
    let l := js.pretty 10000000
    let gh ← match handles.find? ("ident_strings", group) with
                | some h => pure h
                | none => 
                    IO.throwServerError ("No handle for " ++ group ++ " in " ++ "ident_strings")                
    let h ←  match handles.find? ("ident_strings", "all") with
                | some h => pure h
                | none => 
                    IO.throwServerError "No handle for 'all' in indentifiers"
    if l.length < 9000000 then
                        h.putStrLn  l
                        gh.putStrLn l


def unfold (data: IdentData) : Array IdentPair :=
    data.ids.map (fun id => ⟨data.context, data.type, id⟩)

def ofCorePremiseData (data: CorePremiseData) : IdentData :=
    ⟨data.context, data.type, data.ids⟩

end IdentData

namespace IdentPair

def write (data: IdentPair)(group: String)(handles: HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let thm := data.context.foldr (fun s c => s ++ c) s!" : {data.type}"
    let js := Json.mkObj [("theorem", thm), ("identifier", toJson data.id)]
    let l := js.pretty 10000000
    let gh ← match handles.find? ("ident_pairs", group) with
                | some h => pure h
                | none => 
                    IO.throwServerError ("No handle for " ++ group ++ " in " ++ "ident_pairs")                
    let h ←  match handles.find? ("ident_pairs", "all") with
                | some h => pure h
                | none => 
                    IO.throwServerError "No handle for 'all' in indent_pairs"
    if l.length < 9000000 then
                        h.putStrLn  l
                        gh.putStrLn l

end IdentPair

def contextString (context : Array String) : String := 
    context.foldr (fun s c => s ++ c) ""

structure LemmaPair where
    thmContext : Array String
    thmType : String
    lemmaType : String -- have only this for named lemmas

namespace LemmaPair

def thm (data: LemmaPair) : String := data.thmContext.foldr (fun s c => s ++ c) s!" : {data.thmType}"

def write (data: LemmaPair)(group: String)(handles: HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let js := Json.mkObj [("theorem", data.thm), ("lemma", data.lemmaType)]
    let l := js.pretty 10000000
    let gh ← match handles.find? ("lemma_pairs", group) with
                | some h => pure h
                | none => 
                    IO.throwServerError ("No handle for " ++ group ++ " in " ++ "lemma_pairs")                
    let h ←  match handles.find? ("lemma_pairs", "all") with
                | some h => pure h
                | none => 
                    IO.throwServerError "No handle for 'all' in lemma_pairs"
    if l.length < 9000000 then
                        h.putStrLn  l
                        gh.putStrLn l

def ofCorePremiseData (data: CorePremiseData) : Array LemmaPair :=
    data.lemmas.map (fun l => ⟨data.context, data.type, l.thm⟩) ++
    data.namedLemmas.map (fun l => ⟨data.context, data.type, l⟩)

end LemmaPair

structure TermPair where
    thmContext : Array String
    thmType : String
    termContext : Array String
    term : String
    isProp: Bool
    

namespace TermPair

def thm (data: TermPair) : String := 
    data.thmContext.foldr (fun s c => s ++ c) s!" : {data.thmType}"

def write (data: TermPair)(group: String)(handles: HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let js := Json.mkObj [
        ("theorem", data.thm), 
        ("term_context", contextString data.termContext),
        ("term", data.term),
        ("is_prop", data.isProp)
        ]
    let l := js.pretty 10000000
    let gh ← match handles.find? ("term_pairs", group) with
                | some h => pure h
                | none => 
                    IO.throwServerError ("No handle for " ++ group ++ " in " ++ "term_pairs")                
    let h ←  match handles.find? ("term_pairs", "all") with
                | some h => pure h
                | none => 
                    IO.throwServerError "No handle for 'all' in term_pairs"
    if l.length < 9000000 then
                        h.putStrLn  l
                        gh.putStrLn l

def ofCorePremiseData (data: CorePremiseData) : List TermPair :=
    data.terms.map (fun t => 
        ⟨data.context, data.type, t.context, t.value, t.isProp⟩)

end TermPair

def IdentData.filter (d: IdentData)(p : String → Bool) : IdentData := 
    {context:= d.context, type := d.type, ids := d.ids.filter p}

def DefData.identData (d: DefData) : List IdentData := 
    d.premises.map (fun p => 
        {
                context:= p.context.map (·.reprint.get!)
                type := p.type.reprint.get!
                ids := 
                    p.ids.map (·.1) |>.toList.eraseDups.toArray})


def PremiseData.writeBatch (names: List Name)(group: String)
    (handles: HashMap (String × String) IO.FS.Handle)
    (propMap : HashMap String String)(tag: String := "anonymous")(verbose: Bool := false) : MetaM Nat := do
    let mut count := 0
    let mut premiseCount := 0
    for name in names do
        let dfn ←
            try
                DefData.ofNameM? name
            catch ex =>
                IO.println s!"Error {← ex.toMessageData.toString} writing {name}"
                pure none
        match dfn with
        | none => pure ()
        | some defn =>
            if verbose then
                IO.println s!"Writing {defn.name}"
            for premise in defn.premises do
                premise.write group handles propMap
                let coreData ← premise.coreData propMap 
                let identData := 
                    IdentData.ofCorePremiseData coreData
                identData.write group handles
                let identPairs := identData.unfold
                for identPair in identPairs do
                    identPair.write group handles
                let termPairs := TermPair.ofCorePremiseData coreData 
                for termPair in termPairs do
                    termPair.write group handles
                let lemmaPairs := LemmaPair.ofCorePremiseData coreData
                for lemmaPair in lemmaPairs do
                    lemmaPair.write group handles
                premiseCount := premiseCount + 1
            count := count + 1
            if count % 300 = 0 then
                IO.println s!"Wrote {count} definitions of {names.length} in task {tag}"
    IO.println s!"Wrote {premiseCount} premises from {count} definitions of {names.length} in task {tag}"
    return premiseCount

def PremiseData.writeBatchCore (names: List Name)(group: String)
    (handles: HashMap (String × String) IO.FS.Handle)
    (propMap : HashMap String String)(tag: String := "anonymous")(verbose: Bool := false) : CoreM Nat :=
    PremiseData.writeBatch names group handles propMap tag verbose |>.run'

def CorePremiseData.ofNameM? (name: Name) : 
    MetaM (Option <| List CorePremiseData) := do
    let dfn? ← DefData.ofNameM? name
    let premises := dfn?.map (·.premises)
    let propMap ← getPropMapStr 
    match premises with
    | none => return none
    | some premises => 
        return some <| ←  premises.mapM (fun p =>  p.coreData propMap)

-- #eval CorePremiseData.ofNameM? ``Nat.le_of_succ_le_succ
-- #print Nat.le_of_succ_le_succ

def CorePremiseData.writeTest (names: List Name) : MetaM Unit := do
    let cores ← names.filterMapM CorePremiseData.ofNameM?
    let path := System.mkFilePath ["data", "tests", "premises.json"]
    IO.FS.writeFile path <| (toJson cores).pretty 

def propList : MetaM <| Array (String × String) := do
    let propMap ← getPropMapStr
    return propMap.toArray

-- #eval propList


-- Code below this probably dead

def nameSize : MetaM <| Nat × Nat := do
    let cs ← constantNameValueTypes
    let cs' ← cs.filterM <| fun (_, term, _) => 
        Meta.isProof term
    return (cs.size, cs'.size)

-- #check Json.pretty

-- #eval nameSize

def nameSample (n: Nat) : MetaM (Array Name) := do
    let cs ← constantNameValueTypes 
    let mut out : Array Name := #[]
    let mut count := 0
    for (name, _, _) in cs do
        if count % n = 0 then
            out := out.push name
        count := count + 1    
    return out

-- #eval nameSample 100

def batchDefns (start batch : Nat) : MetaM (Array Json) := do
    let cs ← constantNameValueTypes 
    let mut out : Array Json := #[]
    let mut count := 0
    for (name, term, type, _) in cs do
        if count >= start && count < start + batch then
            let defData? ← DefData.getM? name term type
            match defData? with
            | none => pure ()
            | some defData => out := out.push <| toJson defData
        count := count + 1    
    return out


def writeBatchDefnsM (start batch : Nat) : MetaM Nat  := do
    let cs ← constantNameValueTypes 
    let names := cs.map (·.1)
    IO.println <| s!"{start}; {batch} from {cs.size}"
    let mut count := 0
    let defnsFile := System.mkFilePath ["rawdata", s!"defns.jsonl"]
    let h ← IO.FS.Handle.mk defnsFile IO.FS.Mode.append
    let idsFile := System.mkFilePath ["rawdata", s!"idents.jsonl"]
    let h' ← IO.FS.Handle.mk idsFile IO.FS.Mode.append 
    for (name, term, type, _) in cs do
        if count >= start && count < start + batch then
            IO.println <| s!"{count} {name}"
            let defData? ← DefData.getM? name term type
            match defData? with
            | none => 
                IO.println <| s!"{count} {name} omitted"
                pure ()
            | some defData =>
                IO.println <| s!"{count} {name} written"
                let idData := defData.identData
                let idData := 
                    idData.map (fun d ↦ d.filter 
                        (names.contains · ))
                let l := (toJson defData).pretty 10000000
                if l.length < 9000000 then
                    h.putStrLn  l
                for d in idData do
                    let l := (toJson d).pretty 10000000
                    if l.length < 9000000 then
                    h'.putStrLn l
        count := count + 1    
    return start + batch

def writePremisesM  : MetaM Nat  := do
    let cs ← constantNameValueTypes 
    let names := cs.map (·.1)
    let namesFile := System.mkFilePath ["rawdata", s!"names.txt"]
    IO.FS.writeFile namesFile <| 
        names.map toString |>.foldl (fun a b ↦ a  ++ b ++ "\n") ""
    let defIdsFile := System.mkFilePath ["rawdata", s!"def_ids.jsonl"]
    IO.FS.writeFile defIdsFile ""
    let hId ← IO.FS.Handle.mk defIdsFile IO.FS.Mode.append
    IO.println <| s!"Processing {cs.size} definitions"
    let mut count := 0
    let mut premisesDone : Array <| (Array Syntax) × Syntax := #[]
    let premisesFile := System.mkFilePath ["rawdata", s!"premises.jsonl"]
    IO.FS.writeFile premisesFile ""
    let h ← IO.FS.Handle.mk premisesFile IO.FS.Mode.append
    let trainPremisesFile := System.mkFilePath ["rawdata", s!"train_premises.jsonl"]
    IO.FS.writeFile trainPremisesFile ""
    let hTrain ← IO.FS.Handle.mk trainPremisesFile IO.FS.Mode.append
    let testPremisesFile := System.mkFilePath ["rawdata", s!"test_premises.jsonl"]
    let hTest ← IO.FS.Handle.mk testPremisesFile IO.FS.Mode.append
    let validPremisesFile := System.mkFilePath ["rawdata", s!"valid_premises.jsonl"]
    IO.FS.writeFile validPremisesFile ""
    let hValid ← IO.FS.Handle.mk validPremisesFile IO.FS.Mode.append
    let mut testNum := 0
    let mut validNum := 0
    let mut trainNum := 0
    for (name, term, type, _) in cs do
        IO.println <| s!"{count} {name} (of {cs.size})"
        let defData? ← DefData.getM? name term type
        match defData? with
        | none => 
            IO.println <| s!"{count} {name} omitted"
            pure ()
        | some defData =>
            IO.println <| s!"{count} {name} written"
            let gh ←  match ← IO.rand 0 9 with
                | 0 => do
                    testNum := testNum + 1
                    IO.println s!"writing to test; now :{testNum}" 
                    pure hTest
                | 1 => 
                    validNum := validNum + 1
                    IO.println s!"writing to valid; now :{validNum}"
                    pure hValid
                | _ => 
                    trainNum := trainNum + 1
                    IO.println s!"writing to train; now :{trainNum}"
                    pure hTrain
            let premises := defData.premises
            for premise in premises do
                let premiseHead := (premise.context, premise.type)
                if premisesDone.contains premiseHead then
                    IO.print "premise seen previously; "
                    pure ()
                else
                    premisesDone := premisesDone.push premiseHead
                    IO.print "premise new; "
                    let premise := premise.filterIds (names.contains · )
                    let l := (toJson premise).pretty 10000000
                    if l.length < 9000000 then
                        h.putStrLn  l
                        gh.putStrLn l
            IO.println ""
            let idData := defData.identData.bind (fun d ↦ d.ids.toList)
            let idData ←  idData.filterM 
                (fun n => checkName <| String.toName n) 
            let idData := idData.eraseDups
            let idData := Json.mkObj [
                ("name", toJson defData.name),
                ("ids", toJson idData),
                ("is_prop", toJson defData.isProp),
                ("type", toJson defData.type.purge)
            ]
            let l := idData.pretty 10000000
            if l.length < 9000000 then
                hId.putStrLn l
        count := count + 1    
    return count

def writeBatchDefnsCore (start batch : Nat) : CoreM Nat := 
    (writeBatchDefnsM start batch).run' {} 

def writePremisesCore : CoreM Nat :=
    writePremisesM.run' {}

-- #eval batchDefns 0 5

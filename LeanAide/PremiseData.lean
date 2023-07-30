import Lean
import Std.Data.HashMap
import LeanAide.ConstDeps

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

open LeanAide.Meta

universe u v w u_1 u_2 u_3 u₁ u₂ u₃

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


structure DefData where
    name : Name
    type : Syntax
    value : Syntax
    isProp : Bool
    typeDepth : Nat
    valueDepth : Nat
    premises : List PremiseData -- empty if depth exceeds bound
    deriving Inhabited, ToJson, Repr

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

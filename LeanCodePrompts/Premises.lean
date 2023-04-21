import Lean
import Std.Data.HashMap
import LeanCodePrompts.ConstDeps
import LeanCodePrompts.VerboseDelabs

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


def freshDataHandle (fileNamePieces : List String) : IO IO.FS.Handle := do
    let path := System.mkFilePath <| [".", "rawdata"] ++ fileNamePieces
    IO.FS.writeFile path "" 
    IO.FS.Handle.mk path IO.FS.Mode.append Bool.false


def fileNamePieces : HashMap (String × String) (List String) :=
    HashMap.ofList <|
        ["core", "full"].bind fun kind => 
            ("all" :: groups).map fun group => ((kind, group), ["premises", kind, group++".jsonl"])

def fileHandles : IO (HashMap (String × String) IO.FS.Handle) := do
    let mut handles := HashMap.empty
    for (k, v) in fileNamePieces.toList do
        handles := handles.insert k <| ← freshDataHandle v
    return handles


set_option pp.unicode.fun true
set_option pp.match false

/-- Syntax as json -/
instance : ToJson Syntax := ⟨fun (d: Syntax) ↦ d.reprint.get!.trim⟩

/-- Subterms in a premise -/
structure TermData where
    context : Array Syntax
    value : Syntax
    size : Nat
    depth: Nat
deriving Repr, ToJson

/-- Increase depth of a subterm (for recursion) -/
def TermData.increaseDepth (d: Nat) : TermData → TermData :=
fun data ↦
    ⟨data.context, data.value, data.size, data.depth + d⟩

/-- Lemma data with proofs -/
structure PropProofData where
    context : Array Syntax
    prop : Syntax
    proof: Syntax
    propSize: Nat 
    proofSize: Nat
    depth: Nat
deriving Repr, ToJson

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
 ids :       Array (Name ×  Nat)  -- proof identifiers used
 deriving Repr, ToJson

def PremiseData.writeFull (data: PremiseData)(group: String)(handles: HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let l := (toJson data).pretty 10000000
    let gh := handles.findD ("core", group) 
                (← freshDataHandle ["premises", "core", group++".jsonl"])
    let h := handles.findD ("core", "all") 
                (← freshDataHandle ["premises", "core", "all.jsonl"])
    if l.length < 9000000 then
                        h.putStrLn  l
                        gh.putStrLn l

partial def shrink (s: String) : String := 
    let step := s.replace "  " " " |>.replace "( " "("
                |>.replace " )" ")"
                |>.replace "{ " "{"
                |>.replace " }" "}"
                |>.replace "[ " "["
                |>.replace " ]" "]"
                |>.trim
    if step == s then s else shrink step

structure CorePremiseDataDirect where
    context : Array String
    ids : Array String
    terms : Array <| Array String ×  String
    lemmas : Array String 
deriving Repr, ToJson, FromJson

def CorePremiseDataDirect.fromPremiseData (pd: PremiseData) : CorePremiseDataDirect := 
    ⟨pd.context.map (fun s => shrink s.reprint.get!.trim), pd.ids.map (fun (n, _) => shrink n.toString), pd.terms.map (fun td => 
       (td.context.map (fun s => shrink s.reprint.get!.trim),
       td.value.reprint.get!.trim)), pd.propProofs.map (fun p => p.prop.reprint.get!.trim)⟩

structure CorePremiseData extends CorePremiseDataDirect where
    namedLemmas : Array String
deriving Repr, ToJson, FromJson


namespace CorePremiseData

def fromDirect (direct: CorePremiseDataDirect)(propMap : HashMap String String) : CorePremiseData := {
    context := direct.context,
    ids := direct.ids,
    terms := direct.terms,
    lemmas := direct.lemmas,
    namedLemmas := direct.ids.filterMap (fun id => propMap.find? id)
}

def fromPremiseData (pd: PremiseData)(propMap : HashMap String String) : CorePremiseData := 
    CorePremiseData.fromDirect (CorePremiseDataDirect.fromPremiseData pd) propMap


def write (data: CorePremiseData)(group: String)(handles: HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let l := (toJson data).pretty 10000000
    let gh := handles.findD ("core", group) 
                (← freshDataHandle ["premises", "core", group])
    let h := handles.findD ("core", "all") 
                (← freshDataHandle ["premises", "core", "all"])
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

def write (data: PremiseData)(group: String)
    (handles: HashMap (String × String) IO.FS.Handle)
    (propMap : HashMap String String) : IO Unit := do 
        data.writeFull group handles
        let coreData := CorePremiseData.fromPremiseData data propMap
        coreData.write group handles

end PremiseData

/-- Remove the added `=: prop` from syntax -/
partial def Lean.Syntax.purge: Syntax → Syntax := fun stx ↦
  match stx with
  | Syntax.node info k args =>
    match stx with
    | `(($pf:term =: $_:term)) =>
      pf.raw.purge
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
        Array (Name × Nat) ×
        List PremiseData
        )  := do
    if maxDepth? = some 0 then
        pure (#[], #[], #[], [])    
    else
    let tks ← termKindList
    let tks := tks.map (·.1)
    match ← namedArgument? stx with
    | some (arg, _) => -- named argument of a function, name ignored
        arg.premiseDataAuxM context defnName none  true (maxDepth?.map (· -1))
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
    match ← lambdaStx? stx with -- term is a lambda
    | some (body, args) =>
        let prev ←  /- data for subterm; not an instantiation; 
        inherits proposition group: if this is a proof, so would the previous term and hence we will have a group.  -/
            body.premiseDataAuxM (context ++ args) defnName propHead? false (maxDepth?.map (· -1))
        let (ts, pfs, ids, ps) := prev
        return (ts.map (fun s => (s.increaseDepth args.size)),
                pfs.map (fun s => (s.increaseDepth args.size)),
                ids.map (fun (s, m) => (s, m + args.size)),
                ps)
    | none =>
    match ← appStx? stx with
    | some (f, arg) =>
        let prev ←  f.premiseDataAuxM context defnName none false (maxDepth?.map (· -1))
        let (ts, pfs, ids, ps) := prev
        let prev ←  arg.premiseDataAuxM context defnName none true (maxDepth?.map (· -1))
        let (ts', pfs', ids', ps') := prev
        let ts'' := 
            if isArg then -- this is an instantiation
            let head : TermData := 
                ⟨context, stx.purge, stx.purge.size, 0⟩
            (ts ++ ts').map (fun s => s.increaseDepth 1) |>.push head
            else 
            (ts ++ ts').map (fun s => s.increaseDepth 1)
        return (ts'',
                (pfs ++ pfs').map (fun s => s.increaseDepth 1),
                (ids ++ ids').map (fun (s, m) => (s, m + 1)),
                ps ++ ps')
    | none =>
        match stx with
        | Syntax.node _ k args => 
            let prevs ← args.mapM (
                premiseDataAuxM context defnName · none false (maxDepth?.map (· -1)))
            let mut ts: Array (TermData) := #[]
            let mut pfs: Array (PropProofData) := #[]
            let mut ids: Array (Name × Nat) := #[]
            let mut ps: List PremiseData := []
            for prev in prevs do
                let (ts', pfs', ids', ps') := prev
                ts := ts ++ ts'.map (fun s => s.increaseDepth 1)
                pfs := pfs ++ pfs'.map (fun s => s.increaseDepth 1)
                ids := ids ++ ids'.map (fun (s, m) => (s, m + 1))
                ps := ps ++ ps'
            let head : TermData := 
                ⟨context, stx.purge, stx.purge.size, 0⟩
            if isArg && tks.contains k then 
                ts := ts.push (head)
            return (ts, pfs, ids, ps)
        | Syntax.ident _ _ name .. => 
            let contextVars := context.filterMap getVar
            if  !(contextVars.contains name) &&
                !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf name)) then 
                pure (#[], #[], #[(name, 0)], [])
            else pure (#[], #[], #[], [])
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
    deriving Inhabited, ToJson

def DefData.getM? (name: Name)(term type: Expr) : MetaM (Option  DefData) := do
    if term.approxDepth > (← getDelabBound) || type.approxDepth > (← getDelabBound) then return none
    else
    let (stx, _) ←  delabCore term {} (delabVerbose)
    let (tstx, _) ←  delabCore type {} (delabVerbose)
    let isProp ← Meta.isProof term
    let premises ← 
        Lean.Syntax.premiseDataM #[] stx tstx isProp (some name) name
    let typeDepth := type.approxDepth
    let valueDepth := term.approxDepth
    return some {name := name, type := tstx.raw.purge, value := stx.raw.purge, isProp := isProp, typeDepth := typeDepth.toNat, valueDepth := valueDepth.toNat, premises := premises}

def DefData.ofNameM? (name: Name) : MetaM (Option DefData) := do
    let info ←  getConstInfo name
    let type := info.type
    let term? := info.value? 
    match term? with
    | some term => DefData.getM? name term type
    | none => return none

structure IdentData where
    context : Array Syntax
    type : Syntax
    ids : List Name
    deriving Inhabited, ToJson

def IdentData.filter (d: IdentData)(p : Name → Bool) : IdentData := 
    {context:= d.context, type := d.type, ids := d.ids.filter p}

def DefData.identData (d: DefData) : List IdentData := 
    d.premises.map (fun p => 
        {context:= p.context, type := p.type, ids := p.ids.map (·.1) |>.toList.eraseDups})

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
    let h ← IO.FS.Handle.mk defnsFile IO.FS.Mode.append Bool.false
    let idsFile := System.mkFilePath ["rawdata", s!"idents.jsonl"]
    let h' ← IO.FS.Handle.mk idsFile IO.FS.Mode.append Bool.false
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
    let hId ← IO.FS.Handle.mk defIdsFile IO.FS.Mode.append Bool.false
    IO.println <| s!"Processing {cs.size} definitions"
    let mut count := 0
    let mut premisesDone : Array <| (Array Syntax) × Syntax := #[]
    let premisesFile := System.mkFilePath ["rawdata", s!"premises.jsonl"]
    IO.FS.writeFile premisesFile ""
    let h ← IO.FS.Handle.mk premisesFile IO.FS.Mode.append Bool.false
    let trainPremisesFile := System.mkFilePath ["rawdata", s!"train_premises.jsonl"]
    IO.FS.writeFile trainPremisesFile ""
    let hTrain ← IO.FS.Handle.mk trainPremisesFile IO.FS.Mode.append Bool.false
    let testPremisesFile := System.mkFilePath ["rawdata", s!"test_premises.jsonl"]
    let hTest ← IO.FS.Handle.mk testPremisesFile IO.FS.Mode.append Bool.false
    let validPremisesFile := System.mkFilePath ["rawdata", s!"valid_premises.jsonl"]
    IO.FS.writeFile validPremisesFile ""
    let hValid ← IO.FS.Handle.mk validPremisesFile IO.FS.Mode.append Bool.false
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
            let idData := defData.identData.bind (fun d ↦ d.ids)
            let idData := idData.filter (names.contains · ) |>.eraseDups
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

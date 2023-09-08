import Lean
import Std.Data.HashMap
import LeanAide.ConstDeps
import LeanAide.Using

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

class ToJsonM (α : Type u) where
  toJsonM : α → CoreM Json

instance (α : Type u) [ToJson α] : ToJsonM α where
  toJsonM := pure ∘ toJson

export ToJsonM (toJsonM)

instance [ToJsonM α] : ToJsonM (Array α) where
  toJsonM := fun arr => do
    let as : Array Json ←  arr.mapM fun a => toJsonM a
    return Json.arr as

def termToString : Syntax.Term → CoreM String :=
    fun t => do
        let stx ← ppTerm t
        return stx.pretty.trim

/-- Syntax as json -/
instance : ToJsonM Syntax.Term := ⟨fun (d: Syntax.Term) ↦ do 
    termToString d⟩

abbrev ContextSyn := Array Syntax

open Lean.Parser.Term
def declToString : Syntax → CoreM String := fun d => do
    match d with
    | `(letDecl|$n:ident : $type := $val) => 
        let type := (← ppTerm type).pretty.trim
        let val := (← ppTerm val).pretty.trim
        return s!"{n.getId.toString} : {type} := {val}" 
    | `(funBinder|($n:ident : $type:term)) =>
        let type := (← ppTerm type).pretty.trim
        return s!"({n.getId.toString} : {type})"
    | `(funImplicitBinder|{$n:ident : $type:term}) =>
        let type := (← ppTerm type).pretty.trim
        return "{" ++ s!"{n.getId.toString} : {type}" ++ "}"
    | `(instBinder|[$n:ident : $type:term]) =>
        let type := (← ppTerm type).pretty.trim
        return s!"[{n.getId.toString} : {type}]"
    | `(instBinder|[$type:term]) =>
        let type := (← ppTerm type).pretty.trim
        return s!"[{type}]"
    | `(funStrictImplicitBinder|⦃$n:ident : $type:term⦄) =>
        let type := (← ppTerm type).pretty.trim
        return s!"⦃{n.getId.toString} : {type}⦄"
    | `(funBinder|(_ : $type:term)) =>
        let type := (← ppTerm type).pretty.trim
        return s!"(_ : {type})"
    | `(funImplicitBinder|{_ : $type:term}) =>
        let type := (← ppTerm type).pretty.trim
        return "{" ++ s!"_ : {type}" ++ "}"
    | `(funStrictImplicitBinder|⦃_ : $type:term⦄) =>
        let type := (← ppTerm type).pretty.trim
        return s!"⦃_ : {type}⦄"
    | stx => 
        let fallback := stx.reprint.get!
        IO.println s!"declToString fallback to: {fallback} for {stx}"
        return fallback

def declToThmHead : Syntax → CoreM String := fun d => do
    match d with
    | `(letDecl|$n:ident : $type := $val) => 
        let type := (← ppTerm type).pretty.trim
        let val := (← ppTerm val).pretty.trim
        return s!"let {n.getId.toString} : {type} := {val}; " 
    | `(funBinder|($n:ident : $type:term)) =>
        let type := (← ppTerm type).pretty.trim
        return s!"({n.getId.toString} : {type}) → "
    | `(funImplicitBinder|{$n:ident : $type:term}) =>
        let type := (← ppTerm type).pretty.trim
        return "{" ++ s!"{n.getId.toString} : {type}" ++ "} → "
    | `(instBinder|[$n:ident : $type:term]) =>
        let type := (← ppTerm type).pretty.trim
        return s!"[{n.getId.toString} : {type}] → "
    | `(instBinder|[$type:term]) =>
        let type := (← ppTerm type).pretty.trim
        return s!"[{type}] → "
    | `(funStrictImplicitBinder|⦃$n:ident : $type:term⦄) =>
        let type := (← ppTerm type).pretty.trim
        return s!"⦃{n.getId.toString} : {type}⦄ → "
    | `(funBinder|(_ : $type:term)) =>
        let type := (← ppTerm type).pretty.trim
        return s!"(_ : {type}) → "
    | `(funImplicitBinder|{_ : $type:term}) =>
        let type := (← ppTerm type).pretty.trim
        return "{" ++ s!"_ : {type}" ++ "} → "
    | `(funStrictImplicitBinder|⦃_ : $type:term⦄) =>
        let type := (← ppTerm type).pretty.trim
        return s!"⦃_ : {type}⦄ → "
    | stx => 
        let fallback := stx.reprint.get! ++ " → "
        IO.println s!"declToString fallback to: {fallback} for {stx}"
        return fallback


def declInLctx  (d :Syntax) : TermElabM Bool := do 
    match d with
    | `(letDecl|$n:ident : $type := $val) => 
        let lctx ← getLCtx 
        match lctx.findFromUserName? n.getId with
        | some dcl => do
            let type ←  Term.elabType type
            let dval? := dcl.value? 
            isDefEq dcl.type type <&&> 
                (isProp dcl.type <||>
                match dval? with
                | some dval => do
                    let val ← Term.elabTerm val none
                    isDefEq dval val
                | none => return false)
        | none => return false
    | `(funBinder|($n:ident : $type:term)) =>
        anyWithNameType n type
    | `(funImplicitBinder|{$n:ident : $type:term}) =>
        anyWithNameType n type
    | `(instBinder|[$_:ident : $type:term]) =>
        anyWithType type
    | `(instBinder|[$type:term]) =>
        anyWithType type
    | `(funStrictImplicitBinder|⦃$n:ident : $type:term⦄) =>
        anyWithNameType n type
    | `(funBinder|(_ : $type:term)) =>
        anyWithType type
    | `(funImplicitBinder|{_ : $type:term}) =>
        anyWithType type
    | `(funStrictImplicitBinder|⦃_ : $type:term⦄) =>
        anyWithType type
    | stx => 
        IO.println s!"Expected local declaration syntax; got {stx}"
        return false
    where 
    anyWithNameType (n : TSyntax `ident)(type : Syntax.Term) : 
        TermElabM Bool := do
        let lctx ← getLCtx 
        match lctx.findFromUserName? n.getId with
        | some d => do
            let type ←  Term.elabType type
            isDefEq d.type type
        | none => return false
    anyWithType (type : Syntax.Term) : TermElabM Bool := do
        let lctx ← getLCtx 
        lctx.anyM fun d => do
            let type ←  Term.elabType type
            isDefEq d.type type

partial def runInRelForallCtx (decls: List Syntax)(c: TermElabM Expr) : TermElabM Expr := 
    match decls with
    | [] => c
    | d :: ds => do
    let inCtx ← declInLctx d
    if inCtx then runInRelForallCtx ds c
    else match d with
    | `(letIdDecl|$n:ident : $type := $val) => 
        let name := n.getId
        let type ←  Term.elabType type
        let val ← Term.elabTerm val none
        withLetDecl name type val fun x => do
            let tail ← runInRelForallCtx ds c
            mkLambdaFVars #[x] tail
    | `(funBinder|($n:ident : $type:term)) =>
        forallRec n.getId type BinderInfo.default ds
    | `(funImplicitBinder|{$n:ident : $type:term}) =>
        forallRec n.getId type BinderInfo.implicit ds
    | `(instBinder|[$n:ident : $type:term]) =>
        forallRec n.getId type BinderInfo.instImplicit ds        
    | `(instBinder|[$type:term]) =>
        forallRec Name.anonymous type BinderInfo.instImplicit ds
    | `(funStrictImplicitBinder|⦃$n:ident : $type:term⦄) =>
        forallRec n.getId type BinderInfo.strictImplicit ds
    | `(funBinder|(_ : $type:term)) =>
        forallRec Name.anonymous type BinderInfo.default ds
    | `(funImplicitBinder|{_ : $type:term}) =>
        forallRec Name.anonymous type BinderInfo.implicit ds
    | `(funStrictImplicitBinder|⦃_ : $type:term⦄) =>
        forallRec Name.anonymous type BinderInfo.strictImplicit ds
    | stx => 
        IO.println s!"Expected local declaration syntax; got {stx}"
        c
    where forallRec (name : Name)(type : Syntax.Term)(bi: BinderInfo)
        (ds : List Syntax) : TermElabM Expr := do
        let type ←  Term.elabType type
        withLocalDecl name bi type fun x => do
            let tail ← runInRelForallCtx ds c
            mkForallFVars #[x] tail

def parseContext (s: String) : CoreM <| Except String Syntax := do 
    return parseGroup (← getEnv) s [letDecl, funBinder, funImplicitBinder, funStrictImplicitBinder, instBinder]

-- #eval parseContext "x : Nat := 0"
-- #eval parseContext "(x : Nat)"

def roundTripCtx (s: String) : CoreM String := do
    let stx? ← parseContext s
    declToString stx?.toOption.get!

-- #eval roundTripCtx "x : Nat := 0"
-- #eval roundTripCtx "(x : Nat)"
-- #eval roundTripCtx "{_ : Nat}"

-- #check mkFreshUserName
def egName : MetaM Name :=
    withLocalDecl `n BinderInfo.default (mkConst ``Nat) fun _ => do
    let nn := (← getLCtx).getUnusedName `n
    return nn
-- #eval egName

open Tactic Term
def introInContext (ctx : List String)(term: String) : TacticM Unit := 
    withMainContext do
    for c in ctx do
        let stx? ← parseContext c
        match stx? with
        | Except.error e => throwError s!"Error {e} parsing declaration {c}"
        | Except.ok stx =>
         unless ← declInLctx stx do
            throwError s!"Declaration {c} not in local context"
    let term? := 
     runParserCategory (←getEnv) `term term
    match term? with
    | Except.error e => 
        throwError s!"Error {e} parsing term {term}"
    | Except.ok term =>
        let term' : Syntax.Term := ⟨term⟩ 
        withoutErrToSorry do 
        withSynthesize do
        try
            let term  ←  Term.elabTerm term' none
            let type ← inferType term 
            let name := `θ
            let lctx ← getLCtx
            let name := lctx.getUnusedName name 
            let relGoal ←  (←getMainGoal).define name type term
            replaceMainGoal [relGoal]
        catch e =>
            throwError s!"Error {← e.toMessageData.toString} elaborating term {term}"
    pure ()

elab "intro_in"  ctx:strLit* "!!" t:strLit  : tactic => do
    let dcls := ctx.toList.map (fun s => s.getString)
    introInContext dcls t.getString

example (n m : Nat) : 1 = 1 := by
    let θ := 2 -- name to avoid
    intro_in "(n : Nat)" "{m : Nat}" !! "n + 1 + m"
    rfl

def usingRelContext (ctx : List String)(type: String) : TacticM Unit := 
    withMainContext do
    let mut decls : Array Syntax := #[]
    for c in ctx do
        let stx? ← parseContext c
        match stx? with
        | Except.error e => throwError s!"Error {e} parsing declaration {c}"
        | Except.ok stx =>
         unless ← declInLctx stx do
            decls := decls.push stx
    let type? := 
     runParserCategory (←getEnv) `term type
    match type? with
    | Except.error e => 
        throwError s!"Error {e} parsing type {type}"
    | Except.ok type =>
        let type' : Syntax.Term := ⟨type⟩ 
        let type ←  runInRelForallCtx decls.toList <|
            withoutErrToSorry do 
            withSynthesize do
            Term.elabType type'
        usingM type
    pure ()

elab "using_in"  ctx:strLit* "!!" t:strLit  : tactic => do
    let dcls := ctx.toList.map (fun s => s.getString)
    usingRelContext dcls t.getString

example (n: Nat) : 1 = 1 := by
    using_in "(m : Nat)" "(n: Nat)" !! "n + m = m + n"
    · intro m ; apply Nat.add_comm
    · intros ; rfl

instance : ToJsonM (ContextSyn) := ⟨fun (ds: ContextSyn) => do
let s : Array Json ← ds.mapM fun d => do
    pure <| toJson (← declToString d)
pure <| toJson s⟩

instance : ToJsonM Nat := inferInstance
instance : ToJsonM Bool := inferInstance
instance : ToJsonM String := inferInstance

/-- Subterms in a premise -/
structure TermData where
    context : ContextSyn
    value : Syntax.Term
    size : Nat
    depth: Nat
    isProp: Bool
deriving Repr, BEq

instance : ToJsonM TermData :=
⟨fun (data: TermData) => do
    return Json.mkObj ([
        ("context", ← toJsonM data.context),
        ("value", ← toJsonM data.value),
        ("size", toJson data.size),
        ("depth", toJson data.depth),
        ("isProp", toJson data.isProp) 
        ])⟩

/-- Increase depth of a subterm (for recursion) -/
def TermData.increaseDepth (d: Nat) : TermData → TermData :=
fun data ↦
    ⟨data.context, data.value, data.size, data.depth + d, data.isProp⟩

/-- Lemma data with proofs -/
structure PropProofData where
    context : ContextSyn
    prop : Syntax.Term
    proof: Syntax.Term
    propSize: Nat 
    proofSize: Nat
    depth: Nat
deriving Repr, BEq

instance : ToJsonM PropProofData :=
⟨fun (data: PropProofData) => do
    return Json.mkObj ([
        ("context", ← toJsonM data.context),
        ("prop", ← toJsonM data.prop),
        ("proof", ← toJsonM data.proof),
        ("propSize", toJson data.propSize),
        ("proofSize", toJson data.proofSize),
        ("depth", toJson data.depth) 
        ])⟩

/-- Increase depth for a lemma (for recursion) -/
def PropProofData.increaseDepth (d: Nat) : PropProofData → PropProofData :=
fun data ↦
    ⟨data.context, data.prop, data.proof, data.propSize, data.proofSize, data.depth + d⟩

/-- Full premise data for a proposition -/        
structure PremiseData  where 
 context : ContextSyn -- variables, types, binders
 name? :       Option Name  -- name
 defnName: Name -- name of definition from which it arose
 type :       Syntax.Term  -- proposition
 typeGroup : Syntax.Term  -- proposition group
 proof: Syntax.Term  -- proof
 typeSize : Nat
 proofSize : Nat
 terms :       Array (TermData)  -- instantiations
 propProofs :       Array (PropProofData)  -- sub-proofs
 ids :       Array (String ×  Nat)  -- proof identifiers used
 deriving Repr, BEq

instance : ToJsonM PremiseData :=
⟨fun (data: PremiseData) => do
    return Json.mkObj ([
        ("context", ← toJsonM data.context),
        ("name", toJson data.name?),
        ("defnName", toJson data.defnName.toString),
        ("type", ← toJsonM data.type),
        ("typeGroup", ← toJsonM data.typeGroup),
        ("proof", ← toJsonM data.proof),
        ("typeSize", toJson data.typeSize),
        ("proofSize", toJson data.proofSize),
        ("terms", ← toJsonM data.terms),
        ("propProofs", ← toJsonM data.propProofs),
        ("ids", ← toJsonM data.ids)
        ])⟩

def PremiseData.writeFull (data: PremiseData)(group: String)(handles: HashMap (String × String) IO.FS.Handle) : CoreM Unit := do
    let l := (← toJsonM data).pretty 10000000
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

def CorePropData.ofPropProof (propPf : PropProofData) : CoreM CorePropData := do
    return ⟨← propPf.context.mapM declToString,
    ← termToString propPf.prop⟩

def CorePropData.thm (data: CorePropData) : String :=
     data.context.foldr (fun s c => s ++ " " ++ c) s!" : {data.prop}"

structure CorePremiseDataDirect where
    context : Array String
    name? :       Option Name  -- name
    type : String
    thm: String
    typeGroup : String
    ids : Array String
    terms : List CoreTermData
    lemmas : Array CorePropData 
deriving Repr, ToJson, FromJson, BEq

def CorePremiseDataDirect.fromPremiseData (pd: PremiseData) : CoreM CorePremiseDataDirect := do 
    let heads ←  pd.context.mapM declToThmHead
    let type ← termToString pd.type
    return ⟨← pd.context.mapM declToString, 
        pd.name?,
        type,
        heads.foldr (fun s c => s ++ c) type,
        ← termToString  pd.typeGroup,
        pd.ids.map (fun (n, _) => shrink n), 
        (← pd.terms.toList.mapM (fun td => do 
        pure ⟨← td.context.mapM declToString,
        ← termToString td.value, td.isProp⟩)) |>.eraseDups, 
        ← pd.propProofs.mapM CorePropData.ofPropProof⟩

structure CorePremiseData extends CorePremiseDataDirect where
    namedLemmas : Array String
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
    thm := direct.thm,
    typeGroup := direct.typeGroup,
    ids := direct.ids
    terms := direct.terms,
    lemmas := direct.lemmas,
    namedLemmas := ←  direct.ids.filterMapM (
        fun id =>  getDefn? id propMap)
    }

def fromPremiseData (pd: PremiseData)(propMap : HashMap String String) : MetaM CorePremiseData := do
    CorePremiseData.fromDirect (← CorePremiseDataDirect.fromPremiseData pd) propMap


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
    type : Syntax.Term
    value : Syntax.Term
    isProp : Bool
    typeDepth : Nat
    valueDepth : Nat
    premises : List PremiseData -- empty if depth exceeds bound
    deriving Inhabited,  Repr

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
    let thm := data.context.foldr (fun s c => s ++ " " ++ c) s!" : {data.type}"
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
    let thm := data.context.foldr (fun s c => s ++ " " ++ c) s!" : {data.type}"
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
    context.foldr (fun s c => s ++ " " ++ c) ""

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
    data.thmContext.foldr (fun s c => s ++ " " ++ c) s!" : {data.thmType}"

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

def DefData.identData (d: DefData) : CoreM <| List IdentData := do 
    d.premises.mapM (fun p => do
        pure {
                context:= ← p.context.mapM declToString
                type := ← termToString p.type
                ids := 
                    p.ids.map (·.1) |>.toList.eraseDups.toArray})

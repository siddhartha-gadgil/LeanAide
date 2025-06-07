import Lean
import LeanAide.Aides
import LeanAide.StatementSyntax
import LeanAide.DefData

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

namespace LeanAide
-- open LeanAide.Meta

universe u v w u_1 u_2 u_3 u₁ u₂ u₃

def fileNamePieces : Std.HashMap (String × String) (List String) :=
    Std.HashMap.ofList <|
        ["core", "full", "identifiers", "ident_pairs", "ident_strings",
        "term_pairs", "lemma_pairs"].flatMap fun kind =>
            ("all" :: "extra" :: groups).map fun group => ((kind, group), ["premises", kind, group++".jsonl"])

def mainFileNamePieces : Std.HashMap (String × String) (List String) :=
    Std.HashMap.ofList <|
        ["core",  "identifiers", "ident_pairs", "ident_strings",
        "term_pairs", "lemma_pairs"].flatMap fun kind =>
            ("all"  :: groups).map fun group => ((kind, group), ["premises", kind, group++".jsonl"])

def fileHandles (clean : Bool := true) : IO (Std.HashMap (String × String) IO.FS.Handle)  := do
    let mut handles := Std.HashMap.empty
    for (k, v) in fileNamePieces.toList do
        handles := handles.insert k <| ← freshDataHandle v clean
    return handles

def mainFileHandles : IO (Std.HashMap (String × String) IO.FS.Handle) := do
    let mut handles := Std.HashMap.empty
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


open Lean.Parser.Term


def getBinders : List Syntax → MetaM (Option (List ContextTerm))
| [] => return none
| x :: ys => do
    let tail? ←  getBinders ys
    match tail? with
    | none => return none
    | some t => match x with
        | `(bracketedBinderF|($n:ident : $type:term)) => do
            let s ← `(bracketedBinderF|($n:ident : $type:term))
            return some (s :: t)
        | `(bracketedBinderF|{$n:ident : $type:term}) => do
            let s ← `(bracketedBinderF|{$n:ident : $type:term})
            return some (s :: t)
        | `(bracketedBinderF|(_ : $type:term)) => do
            let s ← `(bracketedBinderF|(_ : $type:term))
            return some (s :: t)
        | `(bracketedBinderF|{_ : $type:term}) => do
            let s ← `(bracketedBinderF|{_ : $type:term})
            return some (s :: t)
        | `(bracketedBinderF|[$n:ident : $type:term]) => do
            let s ← `(bracketedBinderF|[$n:ident : $type:term])
            return some (s :: t)
        | `(bracketedBinderF|[$type:term]) => do
            let s ← `(bracketedBinderF|[$type:term])
            return some (s :: t)
        | `(bracketedBinderF|⦃$n:ident : $type:term⦄) => do
            let s ← `(bracketedBinderF|⦃$n:ident : $type:term⦄)
            return some (s :: t)
        | _ => return none


-- #check Term.explicitBinder

-- #check letDecl

def declToString : Syntax → CoreM String := fun d => do
    match d with
    -- | `(letDecl|$_:ident : $_ := $_) =>
    --     let fmt ← ppCategory `letDecl d
    --     return fmt.pretty.trim
    --     -- let type := (← ppTerm type).pretty.trim
    --     -- let val := (← ppTerm val).pretty.trim
    --     -- -- return s!"{n.getId.toString} : {type} := {val}"
    -- | _ =>
    --     IO.println s!"Trying to show: {d.reprint.get!}"
    --     let fmt ← ppCategory `bracketedBinderF d
    --     return fmt.pretty.trim
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
    -- | `(funStrictImplicitBinder|⦃_ : $type:term⦄) =>
    --     let type := (← ppTerm type).pretty.trim
    --     return s!"⦃_ : {type}⦄"
    | stx =>
        let fallback := stx.reprint.get!
        appendLog "decl" <| Json.str fallback
        -- IO.println s!"declToString fallback to: {fallback} for {stx}"
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
    -- | `(funStrictImplicitBinder|⦃_ : $type:term⦄) =>
    --     let type := (← ppTerm type).pretty.trim
    --     return s!"⦃_ : {type}⦄ → "
    | stx =>
        let fallback := stx.reprint.get! ++ " → "
        appendLog "decl_head" <| Json.str fallback
        -- IO.println s!"declToString fallback to: {fallback} for {stx}"
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
        let type ← instantiateMVars type
        let val ← Term.elabTerm val none
        let val ← instantiateMVars val
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
    {context := data.context, value := data.value, size := data.size, depth := data.depth + d, isProp := data.isProp}

/-- Lemma data with proofs -/
structure PropProofData where
    context : ContextSyn
    prop : Syntax.Term
    proof: Syntax.Term
    propSize: Nat
    proofSize: Nat
    depth: Nat
deriving Repr, BEq

def PropProofData.thm (pd: PropProofData) : CoreM Syntax.Term := do
    foldContext pd.prop pd.context.toList

def PropProofData.statement (pd: PropProofData) : CoreM String := do
    mkStatement none (← pd.thm) none true

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
    {context := data.context, prop := data.prop, proof := data.proof, propSize := data.propSize, proofSize := data.proofSize, depth := data.depth + d}

/-- Full premise data for a proposition -/
structure PremiseData  where
 context : ContextSyn -- variables, types, binders
 name? :       Option Name  -- name
 doc? :      Option String  -- documentation
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

namespace PremiseData

def thm (pd: PremiseData) : CoreM Syntax.Term := do
    foldContext pd.type pd.context.toList

def statement (pd: PremiseData) : CoreM String := do
    mkStatement pd.name? (← pd.thm) none true

def writeFull (data: PremiseData)(group: String)(handles: Std.HashMap (String × String) IO.FS.Handle) : CoreM Unit := do
    let l := (← toJsonM data).compress
    -- IO.println s!"Handles:  {handles.toList.map (fun (k, _) => k)}"
    let key := ("full", group)
    -- IO.println s!"Key: {key}, contained in handles: {handles.contains key}"
    let gh ←  match handles.get? key with
                | some h => pure h
                | none =>
                 IO.throwServerError
                    ("No handle for " ++ group ++ " in " ++ "full")
    let h ←  match handles.get? ("full", "all") with
                | some h => pure h
                | none =>
                    IO.throwServerError "No handle for 'all' in full"
    h.putStrLn  l
    gh.putStrLn l

end PremiseData

structure CoreTermData where
    context : Array String
    value : String
    isProp: Bool
deriving Repr, ToJson, FromJson, BEq

structure CorePropData where
    context : Array String
    prop : String
    thm : String
    statement : String
deriving Repr, ToJson, FromJson, BEq

def CorePropData.ofPropProof (propPf : PropProofData) : CoreM CorePropData := do
    let type ← termToString propPf.prop
    let thm ← foldContext propPf.prop propPf.context.toList
    return {context := ← propPf.context.mapM declToString, prop := type, thm := ← termToString thm, statement := ← propPf.statement}

structure CorePremiseDataDirect where
    context : Array String
    name? :       Option Name  -- name
    doc? :      Option String  -- documentation
    type : String
    thm: String
    statement : String
    typeGroup : String
    ids : Array String
    terms : List CoreTermData
    lemmas : Array CorePropData
deriving Repr, ToJson, FromJson, BEq

def CorePremiseDataDirect.fromPremiseData (pd: PremiseData) : CoreM CorePremiseDataDirect := do
    let thm ← foldContext pd.type pd.context.toList
    let type ← termToString pd.type
    return {context := ← pd.context.mapM declToString, name? := pd.name?, doc? := pd.doc?, type := type, thm := ← termToString thm, statement := ← pd.statement, typeGroup := ← termToString  pd.typeGroup, ids := pd.ids.map (fun (n, _) => shrink n) |>.toList.eraseDups.toArray, terms := (← pd.terms.toList.mapM (fun td => do pure {context := ← td.context.mapM declToString, value := ← termToString td.value, isProp := td.isProp})) |>.eraseDups, lemmas := ← pd.propProofs.mapM CorePropData.ofPropProof}

structure CorePremiseData extends CorePremiseDataDirect where
    namedLemmas : Array (String × String)
    idString := toJson ids |>.compress
deriving Repr, ToJson, FromJson

def checkName (name: Name) : MetaM Bool := do
    let l ← resolveGlobalName name
    return l.length > 0

-- #eval checkName `Or.inl

def getDefn? (name: String)(propMap : Std.HashMap String (String × String)) : MetaM <| Option (String × String) := do
    match propMap.get? name with
    | some ss => return some ss
    | none => do
    let l ← resolveGlobalName name.toName
    let names := l.map (fun (n, _) => n.toString)
    return names.findSome? (fun n =>
        (propMap.get? n))

namespace CorePremiseData

def fromDirect (direct: CorePremiseDataDirect)(propMap : Std.HashMap String (String × String)) : MetaM CorePremiseData := do
    return {direct with namedLemmas := ← direct.ids.toList.eraseDups.toArray.filterMapM (fun id =>  getDefn? id propMap)}

def fromPremiseData (pd: PremiseData)(propMap : Std.HashMap String (String × String)) : MetaM CorePremiseData := do
    CorePremiseData.fromDirect (← CorePremiseDataDirect.fromPremiseData pd) propMap

def write (data: CorePremiseData)(group: String)(handles: Std.HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let l := (toJson data).compress
    let gh ← match handles.get? ("core", group) with
                | some h => pure h
                | none =>
                    IO.throwServerError ("No handle for " ++ group ++ " in " ++ "core")
    let h ←  match handles.get? ("core", "all") with
                | some h => pure h
                | none =>
                    IO.throwServerError "No handle for 'all' in core"
    h.putStrLn  l
    gh.putStrLn l

end CorePremiseData

namespace PremiseData

def filterIds (pd: PremiseData)(p: Name → Bool) : PremiseData :=
    {pd with ids := pd.ids.filter (fun (n, _) => p n.toName)}

def increaseDepth (d: Nat) : PremiseData → PremiseData :=
fun data ↦
    {context := data.context, name? := data.name?, doc? := data.doc?, defnName := data.defnName, type := data.type, typeGroup := data.typeGroup, proof := data.proof, typeSize := data.typeSize, proofSize := data.proofSize, terms := data.terms.map (fun td => td.increaseDepth d), propProofs := data.propProofs.map (fun p => p.increaseDepth d), ids := data.ids.map (fun (n,  m) => (n,  m + d))}

def coreData (data: PremiseData)(propMap : Std.HashMap String (String × String)) : MetaM CorePremiseData :=
    CorePremiseData.fromPremiseData data propMap

def write (data: PremiseData)(group: String)
    (handles: Std.HashMap (String × String) IO.FS.Handle)
    (propMap : Std.HashMap String (String × String)) : MetaM Unit := do
        data.writeFull group handles
        let coreData ←  CorePremiseData.fromPremiseData data propMap
        coreData.write group handles

end PremiseData



structure DefPremiseData extends DefData where
    typeDepth : Option Nat
    valueDepth : Option Nat
    premises : List PremiseData -- empty if depth exceeds bound
    deriving Inhabited,  Repr

def DefPremiseData.ofNameM (name: Name) : MetaM DefPremiseData := do
    let decl ← getConstInfo name
    let type ← instantiateMVars decl.type
    let value ← instantiateMVars decl.value!
    let typeStx ← delab type
    let valueStx ← delab value
    let nc := Lean.isNoncomputable (← getEnv) name
    let isProp := match decl with
    | ConstantInfo.defnInfo _ => false
    | ConstantInfo.thmInfo _ => true
    | _ => false
    let typeDepth := type.approxDepth.toNat
    let valueDepth := value.approxDepth.toNat
    let doc? ← findDocString? (← getEnv) name
    return {name := name, type := typeStx, value := valueStx, isProp := isProp, isNoncomputable := nc, doc? := doc?, typeDepth := typeDepth, valueDepth := valueDepth, premises := []}



structure IdentData where
    context : Array String
    type : String
    thm: String
    name?: Option Name
    doc? : Option String
    statement : String
    ids : Array String
    deriving Inhabited, ToJson, FromJson

structure IdentPair where
    context : Array String
    type : String
    thm: String
    statement: String
    id : String
deriving Inhabited, ToJson

namespace IdentData

def write (data: IdentData)(group: String)(handles: Std.HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let thm := data.thm
    let js := Json.mkObj [("theorem", thm), ("statement", data.statement), ("identifiers", toJson data.ids)]
    let l := js.compress
    let gh ← match handles.get? ("identifiers", group) with
                | some h => pure h
                | none =>
                    IO.throwServerError ("No handle for " ++ group ++ " in " ++ "identifiers")
    let h ←  match handles.get? ("identifiers", "all") with
                | some h => pure h
                | none =>
                    IO.throwServerError "No handle for 'all' in indentifiers"
    h.putStrLn  l
    gh.putStrLn l

def writeString (data: IdentData)(group: String)(handles: Std.HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let thm := data.thm
    let idString : String := toJson data.ids |>.compress
    let js := Json.mkObj [("theorem", thm), ("statement", data.statement), ("identifiers", idString)]
    let l := js.compress
    let gh ← match handles.get? ("ident_strings", group) with
                | some h => pure h
                | none =>
                    IO.throwServerError ("No handle for " ++ group ++ " in " ++ "ident_strings")
    let h ←  match handles.get? ("ident_strings", "all") with
                | some h => pure h
                | none =>
                    IO.throwServerError "No handle for 'all' in indentifiers"
    h.putStrLn  l
    gh.putStrLn l


def unfold (data: IdentData) : Array IdentPair :=
    data.ids.map (fun id => {context := data.context, type := data.type, thm := data.thm, statement := data.statement, id := id})

def ofCorePremiseData (data: CorePremiseData) : IdentData :=
    {context := data.context, type := data.type, thm := data.thm, name? := data.name?, doc? := data.doc?, statement := data.statement, ids := data.ids}

end IdentData

namespace IdentPair

def write (data: IdentPair)(group: String)(handles: Std.HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let thm := data.thm
    let js := Json.mkObj [("theorem", thm), ("statement", data.statement), ("identifier", toJson data.id)]
    let l := js.compress
    let gh ← match handles.get? ("ident_pairs", group) with
                | some h => pure h
                | none =>
                    IO.throwServerError ("No handle for " ++ group ++ " in " ++ "ident_pairs")
    let h ←  match handles.get? ("ident_pairs", "all") with
                | some h => pure h
                | none =>
                    IO.throwServerError "No handle for 'all' in indent_pairs"
    h.putStrLn  l
    gh.putStrLn l

end IdentPair

def contextString (context : Array String) : String :=
    context.foldr (fun s c => s ++ " " ++ c) ""

structure LemmaPair where
    name?: Option Name
    doc? : Option String
    thmContext : Array String
    thmType : String
    thm: String
    statement : String
    lemmaType : String -- have only this for named lemmas
    lemmaStatement : String

namespace LemmaPair

-- def thm (data: LemmaPair) : String := data.thmContext.foldr (fun s c => s ++ c) s!" : {data.thmType}"

def write (data: LemmaPair)(group: String)(handles: Std.HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let d : List (String × Json) := [("theorem", data.statement), ("lemma", data.lemmaStatement), ("theorem-type", data.thmType), ("lemma-type", data.lemmaType)]
    let d := match data.name? with
        | some n => ("name", toJson n.toString) :: d
        | none => d
    let d := match data.doc? with
        | some doc => ("doc_string", toJson doc) :: d
        | none => d
    let js := Json.mkObj d
    let l := js.compress
    let gh ← match handles.get? ("lemma_pairs", group) with
                | some h => pure h
                | none =>
                    IO.throwServerError ("No handle for " ++ group ++ " in " ++ "lemma_pairs")
    let h ←  match handles.get? ("lemma_pairs", "all") with
                | some h => pure h
                | none =>
                    IO.throwServerError "No handle for 'all' in lemma_pairs"

    h.putStrLn  l
    gh.putStrLn l

def ofCorePremiseData (data: CorePremiseData) : Array LemmaPair :=
    data.lemmas.map (fun l =>
        {name? := data.name?, doc? := data.doc?, thmContext := data.context, thmType := data.type, thm := data.thm, statement := data.statement, lemmaType := l.thm, lemmaStatement := l.statement}) ++
    data.namedLemmas.map (fun (type, statement) =>
        {name? := data.name?, doc? := data.doc?, thmContext := data.context, thmType := data.type, thm := data.thm, statement := data.statement, lemmaType := type, lemmaStatement := statement})

end LemmaPair

structure TermPair where
    thmContext : Array String
    thmType : String
    thm: String
    statement: String
    termContext : Array String
    term : String
    isProp: Bool


namespace TermPair

def write (data: TermPair)(group: String)(handles: Std.HashMap (String × String) IO.FS.Handle) : IO Unit := do
    let js := Json.mkObj [
        ("theorem", data.thm),
        ("statement", data.statement),
        ("term_context", contextString data.termContext),
        ("term", data.term),
        ("is_prop", data.isProp)
        ]
    let l := js.compress
    let gh ← match handles.get? ("term_pairs", group) with
                | some h => pure h
                | none =>
                    IO.throwServerError ("No handle for " ++ group ++ " in " ++ "term_pairs")
    let h ←  match handles.get? ("term_pairs", "all") with
                | some h => pure h
                | none =>
                    IO.throwServerError "No handle for 'all' in term_pairs"
    h.putStrLn  l
    gh.putStrLn l

def ofCorePremiseData (data: CorePremiseData) : List TermPair :=
    data.terms.map (fun t =>
        {thmContext := data.context, thmType := data.type, thm := data.thm, statement := data.statement, termContext := t.context, term := t.value, isProp := t.isProp})

end TermPair

def IdentData.filter (d: IdentData)(p : String → Bool) : IdentData :=
    {d with ids := d.ids.filter p}

def DefPremiseData.identData (d: DefPremiseData) : CoreM <| List IdentData := do
    d.premises.mapM (fun p => do
        pure {context := ← p.context.mapM declToString, type := ← termToString p.type, thm := ← termToString p.type, name? := p.name?, doc? := p.doc?, statement := ← p.statement, ids := p.ids.map (·.1) |>.toList.eraseDups.toArray})

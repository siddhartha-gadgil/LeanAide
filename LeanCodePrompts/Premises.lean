import Lean
-- import Mathlib
import Std.Data.HashMap
import LeanCodePrompts.ConstDeps
import LeanCodePrompts.VerboseDelabs

open Lean Meta Elab Parser PrettyPrinter

universe u v w u_1 u_2 u_3 u₁ u₂ u₃

open LeanAide.Meta

def constantNameValueTypes  : MetaM (Array (Name × Expr ×   Expr)) := do
  let env ← getEnv
  let decls := env.constants.map₁.toArray
  let allNames := decls.filterMap <| 
    fun (name, dfn) => dfn.value? |>.map fun t => (name, t, dfn.type) 
  let names ← allNames.filterM (fun (name, _) => isWhiteListed name)
  let names := names.filter <| 
    fun (name, _, _)  ↦ !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf name)) 
  return names

set_option pp.unicode.fun true

class Reprint(a : Type) where
    reprSyn : a → String

instance reprintString : Reprint String where
    reprSyn := id

instance reprintName : Reprint Name where
    reprSyn := toString

instance reprintNat : Reprint Nat where
    reprSyn := toString

instance reprintBool : Reprint Bool where
    reprSyn := toString

instance reprintArray {a : Type} [Reprint a] : Reprint (Array a) where
    reprSyn := fun xs => xs.toList.map Reprint.reprSyn |>.toString

instance reprintList {a : Type} [Reprint a] : Reprint (List a) where
    reprSyn := fun xs => xs.map Reprint.reprSyn |>.toString

instance reprintOption {a : Type} [Reprint a] : Reprint (Option a) where
    reprSyn := fun xs => xs.map Reprint.reprSyn |>.getD ""

instance reprintSyntax : Reprint Syntax where
    reprSyn := fun xs => xs.reprint.get!

def reprint {a : Type}[Reprint a] (x : a) : String := Reprint.reprSyn x

structure TermData where
    context : Array Syntax
    value : Syntax
deriving Repr

structure PropProofData where
    context : Array Syntax
    prop : Syntax
    proof: Syntax
deriving Repr

instance reprintTermData : Reprint TermData where
    reprSyn := fun x => s!"context: {Reprint.reprSyn x.context}; term: {Reprint.reprSyn x.value}"

instance reprintProofData : Reprint PropProofData where
    reprSyn := fun x => s!"context: {Reprint.reprSyn x.context}; prop: {Reprint.reprSyn x.prop}; proof : {Reprint.reprSyn x.proof}"
        
open Reprint 
instance : ToJson TermData := ⟨fun (d: TermData) ↦ 
    Json.mkObj [
        ("context", reprSyn d.context),
        ("term", reprSyn d.value)
    ]⟩

instance : ToJson  PropProofData := ⟨fun (d: PropProofData) ↦  
    Json.mkObj [
        ("context", reprSyn d.context),
        ("prop", reprSyn d.prop),
        ("proof", reprSyn d.proof)
    ]⟩

instance reprintPair {a : Type} {b : Type} [Reprint a] [Reprint b] : Reprint (a × b) where
    reprSyn := fun (x, y) => s!"({Reprint.reprSyn x}, {Reprint.reprSyn y})"

def checkRepr : Repr TermData := inferInstance

example : ToJson Name := inferInstance

instance : ToJson Syntax := ⟨fun (d: Syntax) ↦ d.reprint.get!⟩

structure PremiseData  where 
 context : (Array Syntax)
 name :       Option Name  -- name
 type :       Syntax  -- proposition
 terms :       Array (TermData × Nat)  -- sub-terms
 propProofs :       Array (PropProofData × Nat)  -- sub-terms
 ids :       Array (Name ×  Nat)  -- proof identifiers used
-- deriving Repr

namespace PremiseData

instance premiseToJson : ToJson PremiseData :=⟨
    fun (d: PremiseData) ↦ 
        Json.mkObj [
            ("context", toJson d.context),
            ("name", toJson d.name),
            ("type", toJson d.type),
            ("terms", toJson d.terms),
            ("propProofs", toJson d.propProofs),
            ("ids", toJson d.ids)
    ]⟩


def increaseDepth (d: Nat) : PremiseData → PremiseData :=  
fun data ↦
    ⟨data.context, data.name, data.type, (data.terms.map (fun (p, m) => (p, m + d))), (data.propProofs.map (fun (p, m) => (p, m + d))),
        (data.ids.map (fun (n,  m) => (n,  m + d))) ⟩

open Reprint in
def view : PremiseData → MetaM String := fun data => -- pure "_"
-- | mk ctx name prop subProofs subTerms proofIdents termIdents => do
    return s!"context: {reprSyn data.context}; name: {reprSyn data.name}; type: {reprSyn data.type};  sub-terms: {reprSyn data.terms}; sub-proofs : {reprSyn data.propProofs}  identifiers: {data.ids}"

end PremiseData

partial def Lean.Syntax.purge: Syntax → Syntax := fun stx ↦
  match stx with
  | Syntax.ident _ _ n _ => 
      mkIdent (Name.purgeSuffix n)
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


partial def Lean.Syntax.premiseDataAuxM (context : Array Syntax)(stx: Syntax)(maxDepth? : Option Nat := none) : 
    MetaM (
        Array (TermData × Nat) ×
        Array (PropProofData × Nat) ×
        Array (Name × Nat) ×
        List PremiseData
        )  := do
    if maxDepth? = some 0 then
        pure (#[], #[], #[], [])    
    else
    let tks ← termKindList
    let tks := tks.map (·.1)
    match ← namedArgument? stx with
    | some (arg, _) =>
        arg.premiseDataAuxM context  (maxDepth?.map (· -1))
    | none =>
    match ← proofWithProp? stx with
    | some (proof, prop) =>
        let prev ←  proof.premiseDataAuxM context (maxDepth?.map (· -1))
        let (ts, pfs, ids, ps) := prev
        let headPf : PropProofData := ⟨context, prop.purge, proof.purge⟩
        let head : PremiseData := ⟨context, none, stx.purge, ts, pfs, ids⟩
        return (ts.map (fun (s, m) => (s, m + 1)),
                pfs.map (fun (s, m) => (s, m + 1)) |>.push (headPf, 0),
                ids.map (fun (s, m) => (s, m + 1)),
                head :: ps)
    | none =>
    match ← lambdaStx? stx with
    | some (body, args) =>
        let prev ←  body.premiseDataAuxM (context ++ args) (maxDepth?.map (· -1))
        let (ts, pfs, ids, ps) := prev
        return (ts.map (fun (s, m) => (s, m + args.size)),
                pfs.map (fun (s, m) => (s, m + args.size)),
                ids.map (fun (s, m) => (s, m + args.size)),
                ps)
    | none =>
        match stx with
        | Syntax.node _ k args => 
            let prevs ← args.mapM (premiseDataAuxM context · (maxDepth?.map (· -1)))
            let mut ts: Array (TermData × Nat) := #[]
            let mut pfs: Array (PropProofData × Nat) := #[]
            let mut ids: Array (Name × Nat) := #[]
            let mut ps: List PremiseData := []
            for prev in prevs do
                let (ts', pfs', ids', ps') := prev
                ts := ts ++ ts'.map (fun (s, m) => (s, m + 1))
                pfs := pfs ++ pfs'.map (fun (s, m) => (s, m + 1))
                ids := ids ++ ids'.map (fun (s, m) => (s, m + 1))
                ps := ps ++ ps'
            let head : TermData := ⟨context, stx.purge⟩
            if tks.contains k then 
                ts := ts.push (head, 0)
            return (ts, pfs, ids, ps)
        | Syntax.ident _ _ name .. => 
            let contextVars := context.filterMap getVar
            if  !(contextVars.contains name) &&
                !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf name)) then 
                pure (#[], #[], #[(name, 0)], [])
            else pure (#[], #[], #[], [])
        | _ => pure (#[], #[], #[], [])

def Lean.Syntax.premiseDataM (context : Array Syntax)(proof prop: Syntax)(name? : Option Name)(maxDepth? : Option Nat := none) : 
    MetaM (List PremiseData) := do
    let (ts, pfs, ids, ps) ← proof.premiseDataAuxM context maxDepth?
    let head : PremiseData := ⟨context, name?, prop.purge, ts, pfs, ids⟩
    return head :: ps




namespace LeanAide.Meta

def viewSyntax (s: String) : MetaM <| Syntax × String := do
    let c := runParserCategory (← getEnv) `term s
    match c with
    | Except.error e => throwError e
    | Except.ok s => pure (s, s.reprint.get!)


def nameDefTypeSyntax (name: Name) : MetaM <| Syntax × Syntax := do
    let info? := ((← getEnv).find? name)
    let info := info?.get!
    let exp := info.value?.get!
    let type := info.type
    let (stx, _) ←  delabCore exp {} (delabVerbose)
    let (tstx, _) ←  delabCore type {} (delabVerbose)
    return (stx, tstx)

def nameDefSyntax (name: Name) : MetaM <| Option Syntax := do
    let exp? ← nameExpr? name
    match exp? with
    | none => pure none
    | some exp => do
        let stx ←  delab exp
        pure (some stx)

def premisesFromName (name : Name) : MetaM (List PremiseData) := do
    let (pf, prop) ← nameDefTypeSyntax name
    Lean.Syntax.premiseDataM #[] pf prop name

def premisesViewFromName (name: Name) : MetaM <| List String := do
    let premises ← premisesFromName name
    premises.mapM (fun p => p.view)

def premisesJsonFromName (name: Name) : MetaM <| Json := do
    let premises ← premisesFromName name
    return toJson premises


-- #eval premisesViewFromName ``Nat.pred_le_pred

-- #eval premisesJsonFromName ``Nat.pred_le_pred

-- #eval premisesViewFromName ``Nat.le_of_succ_le_succ


def boundedDef (bound: Nat)(name: Name) : MetaM Bool := do
    let exp? ← nameExpr? name
    match exp? with
    | none => pure false
    | some exp => do
        pure (exp.approxDepth.toNat < bound)

def nameDefView (name: Name) : MetaM String := do
    let stx? ← nameDefSyntax name
    return (stx?.get!.reprint.get!)

def nameDefCleanView (name: Name) : MetaM String := do
    let stx? ← nameDefSyntax name
    return ((stx?.get!.purge).reprint.get!)

def nameDefSyntaxVerbose (name: Name) : MetaM <| Option Syntax := do
    let exp? ← nameExpr? name
    match exp? with
    | none => pure none
    | some exp => do
        let (stx, _) ←  delabCore exp {} (delabVerbose)
        pure (some stx)

def nameDefViewVerbose (name: Name) : MetaM String := do
    let stx? ← nameDefSyntaxVerbose name
    return (stx?.get!.reprint.get!)

-- #eval nameDefSyntax ``List.join

-- #eval nameDefSyntax ``Nat.le_of_succ_le_succ



-- #eval nameDefView ``Nat.gcd_eq_zero_iff

-- #eval nameDefCleanView ``Nat.gcd_eq_zero_iff

-- def egSplit : MetaM <| Option (Syntax × Array Syntax) := do
--     let stx? ← nameDefSyntax ``Nat.gcd_eq_zero_iff
--     lambdaStx? stx?.get!

-- #eval egSplit

-- def egSplitView : MetaM <| Option (String × Array String) := do
--     let stx? ← nameDefSyntax ``Nat.gcd_eq_zero_iff
--     let pair? ← lambdaStx? stx?.get!
--     let (stx, args) := pair?.get!
--     pure (stx.reprint.get!, args.map (fun s => s.reprint.get!))

-- #eval egSplitView

-- set_option pp.proofs false in 
-- #eval nameDefView ``Nat.gcd_eq_zero_iff

-- set_option pp.proofs.withType true in 
-- #eval nameDefView ``Nat.gcd_eq_zero_iff

-- #eval nameDefViewVerbose ``Nat.gcd_eq_zero_iff

-- #eval nameDefSyntaxVerbose ``Nat.gcd_eq_zero_iff

-- #eval nameDefViewVerbose ``Nat.gcd_eq_gcd_ab

-- set_option pp.proofs false in
-- #eval nameDefView ``Nat.gcd_eq_gcd_ab

-- #eval setDelabBound 200

-- #eval nameDefViewVerbose ``Nat.xgcd_aux_P

-- set_option pp.proofs false in
-- #eval nameDefView ``Nat.xgcd_aux_P

-- theorem oddExample : ∀ (n : Nat), ∃ m, m > n ∧ m % 2 = 1 := by
--   intro n -- introduce a variable n
--   use 2 * n + 1 -- use `m = 2 * n + 1`
--   apply And.intro -- apply the constructor of `∧` to split goals
--   · linarith -- solve the first goal using `linarith` 
--   · simp [Nat.add_mod] -- solve the second goal using `simp` with the lemma `Nat.add_mod`

-- -- #eval premisesViewFromName ``oddExample


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
    let premises ← Lean.Syntax.premiseDataM #[] stx tstx name
    let isProp := type.isProp
    let typeDepth := type.approxDepth
    let valueDepth := term.approxDepth
    return some {name := name, type := tstx.raw.purge, value := stx.raw.purge, isProp := isProp, typeDepth := typeDepth.toNat, valueDepth := valueDepth.toNat, premises := premises}

structure IdentData where
    type : Syntax
    ids : List Name
    deriving Inhabited, ToJson

def IdentData.filter (d: IdentData)(p : Name → Bool) : IdentData := 
    {type := d.type, ids := d.ids.filter p}

def DefData.identData (d: DefData) : List IdentData := 
    d.premises.map (fun p => 
        {type := p.type, ids := p.ids.map (·.1) |>.toList.eraseDups})

def nameSize : MetaM Nat := do
    let cs ← constantNameValueTypes 
    return cs.size

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

def batchPremises (start batch : Nat) : MetaM (Array Json) := do
    let cs ← constantNameValueTypes 
    let mut out : Array Json := #[]
    let mut count := 0
    for (name, term, type) in cs do
        if count >= start && count < start + batch then
            let defData? ← DefData.getM? name term type
            match defData? with
            | none => pure ()
            | some defData => out := out.push <| toJson defData
        count := count + 1    
    return out


def writeBatchPremisesM (start batch : Nat) : MetaM Nat  := do
    let cs ← constantNameValueTypes 
    let names := cs.map (·.1)
    IO.println <| s!"{start}; {batch} from {cs.size}"
    let mut count := 0
    let premisesFile := System.mkFilePath ["rawdata", s!"premises.jsonl"]
    let h ← IO.FS.Handle.mk premisesFile IO.FS.Mode.append Bool.false
    let idsFile := System.mkFilePath ["rawdata", s!"idents.jsonl"]
    let h' ← IO.FS.Handle.mk idsFile IO.FS.Mode.append Bool.false
    for (name, term, type) in cs do
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
                h.putStrLn <| (toJson defData).pretty 10000000
                for d in idData do
                    h'.putStrLn <| (toJson d).pretty 10000000
        count := count + 1    
    return start + batch


def writeBatchPremisesCore (start batch : Nat) : CoreM Nat := 
    (writeBatchPremisesM start batch).run' {} 

-- #eval batchPremises 0 5

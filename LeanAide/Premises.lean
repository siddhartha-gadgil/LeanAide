import Lean
import Std.Data.HashMap
import LeanAide.ConstDeps
import LeanAide.VerboseDelabs
import LeanAide.PremiseData

/-!
# Premise data extraction

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

set_option pp.match false

/-- Remove the added `=: prop` from syntax -/
partial def Lean.Syntax.purge: Syntax → MetaM Syntax := fun stx ↦ do
  match stx with
  | Syntax.node info k args =>
    match stx with
    | `(($pf:term =: $_:term)) =>
        padTerm <| ←  pf.raw.purge
    | `(($p : Prop)) => 
        padTerm <| ← p.raw.purge
    | _ => do
     return Syntax.node info k (← args.mapM <| fun arg => do
        Syntax.purge arg
        ) 
  | s => return s
  where padTerm (t : Syntax) : MetaM Syntax := 
    match t with
    | `(($_)) => pure t
    | `($_:ident) => pure t
    | _ =>
        let t : Syntax.Term := TSyntax.mk t 
        `(($t:term))

partial def purgeTerm : Syntax.Term → MetaM Syntax.Term := fun stx ↦ do
  match stx.raw with
  | Syntax.node info k args =>
    match stx with
    | `(($pf:term =: $_:term)) =>
        padTerm <| ←  purgeTerm pf
    | `(($p : Prop)) => 
        padTerm <| ← purgeTerm p
    | _ => do
     return TSyntax.mk <| Syntax.node info k (← args.mapM <| fun arg => do
        Syntax.purge arg
        ) 
  | _ => return stx
  where padTerm (t : Syntax.Term) : MetaM Syntax.Term := 
    match t with
    | `(($_)) => pure t
    | `($_:ident) => pure t
    | _ =>
        let t : Syntax.Term := TSyntax.mk t 
        `(($t:term))

open Lean.Parser.Term in
def purgeContext : Syntax → MetaM Syntax := fun stx => do
    match stx with
    | `(letDecl|$n:ident : $type := $val) => 
        let type  ←purgeTerm type 
        let val ← purgeTerm val
        `(letDecl|$n:ident : $type := $val) 
    | `(funBinder|($n:ident : $type:term)) =>
        let type ← purgeTerm type
        `(funBinder|($n:ident : $type:term))
    | `(funImplicitBinder|{$n:ident : $type:term}) =>
        let type ← purgeTerm type
        `(funImplicitBinder|{$n:ident : $type:term})
    | `(instBinder|[$n:ident : $type:term]) =>
        let type ← purgeTerm type
        `(instBinder|[$n:ident : $type:term])
    | `(instBinder|[$type:term]) =>
        let type ← purgeTerm type
        `(instBinder|[$type:term])
    | `(funStrictImplicitBinder|⦃$n:ident : $type:term⦄) =>
        let type ← purgeTerm type
        `(funStrictImplicitBinder|⦃$n:ident : $type:term⦄)
    | `(funBinder|(_ : $type:term)) =>
        let type ← purgeTerm type
        `(funBinder|(_ : $type:term))
    | `(funImplicitBinder|{_ : $type:term}) =>
        let type ← purgeTerm type
        `(funImplicitBinder|{_ : $type:term})
    | `(funStrictImplicitBinder|⦃_ : $type:term⦄) =>
        let type ← purgeTerm type
        `(funStrictImplicitBinder|⦃_ : $type:term⦄)
    | stx => 
        let fallback := stx.reprint.get!
        IO.println s!"purgeSyntax fallback to: {fallback}, i.e. {stx}"
        return stx


/-- Compute recursively premise-data of sublemmas as well as the identifiers, instantiations and subproofs. These are used at the top level recursively.

The parameter `isArg` specifies whether the term is an argument of a function. This is used to determine whether to add the term to the list of instantiations. 

The parameter `propHead?` specifies the head of the group of propositions, where groups are related by `intro`, i.e., moving from `∀` to context variables. This is used to determine whether to add the proposition to the list of lemmas.
-/
partial def Lean.Syntax.premiseDataAuxM (context : ContextSyn)(defnName: Name)(stx: Syntax.Term)(propHead? : Option Syntax.Term)(isArg: Bool)(maxDepth? : Option Nat := none) : 
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
        let (ts, pfs, ids, ps) ←  
            premiseDataAuxM context defnName prop none  false maxDepth?
        if isArg then -- this is an instantiation
            let head : TermData := 
                ⟨context, ← purgeTerm stx, (← purgeTerm stx).raw.size, 0, true⟩
            pure <| (ts.push head, pfs, ids, ps)
        else 
            pure (ts, pfs, ids, ps)
    | none =>
    match ← namedArgument? stx with
    | some (arg, _) => -- named argument of a function, name ignored
        premiseDataAuxM context defnName arg none  isArg (maxDepth?.map (· -1))
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
            premiseDataAuxM context defnName proof (some newPropHead) false (maxDepth?.map (· -1))
        let (ts, pfs, ids, ps) := prev
        let prop ← purgeTerm prop
        let proof ←  purgeTerm proof
        let newPfs :=
            if propHead?.isSome then -- exclude lemma if in prior group
                pfs
            else 
                let headPf : PropProofData := 
                    ⟨context, prop, proof, prop.raw.size, proof.raw.size, 0⟩
                pfs.map (fun s ↦ s.increaseDepth 1) |>.push headPf
        let head : PremiseData := 
            ⟨context, none, defnName, prop, newPropHead, proof, prop.raw.size, proof.raw.size, ts, pfs, ids⟩
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
        let decl ←purgeContext decl 
        let prev ←   
            premiseDataAuxM (context ++ #[decl]) defnName body propHead? false (maxDepth?.map (· -1))
        let prev' ←  
            premiseDataAuxM (context) defnName val propHead? false (maxDepth?.map (· -1))
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
        let args ← args.mapM (fun arg => purgeContext arg) 
        let prev ←  /- data for subterm; not an instantiation; 
        inherits proposition group: if this is a proof, so would the previous term and hence we will have a group.  -/
            premiseDataAuxM (context ++ args) defnName body propHead? false (maxDepth?.map (· -1))
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
        let prev ←  premiseDataAuxM context defnName f none false (maxDepth?.map (· -1))
        let mut (ts, pfs, ids, ps) := prev
        for arg in args do
            let block ← structuralTerm f
            let prev ←  
                premiseDataAuxM context defnName arg none (!block) (maxDepth?.map (· -1))
            let (ts', pfs', ids', ps') := prev
            -- if ids'.size > 0 then
            --         IO.println s!"arg ids' {ids'}"
            ts := ts ++ ts'
            pfs := pfs ++ pfs'
            ids := ids ++ ids'
            ps := ps ++ ps'
        if isArg then -- this is an instantiation
            let head : TermData := 
                ⟨context, ← purgeTerm stx, (← purgeTerm stx).raw.size, 0, false⟩
            ts := ts.push head
        return (ts.map (fun s => s.increaseDepth 1),
                pfs.map (fun s => s.increaseDepth 1),
                ids.map (fun (s, m) => (s, m + 1)),
                ps) 
    | none =>
        match stx.raw with
        | Syntax.node _ k args => 
            let prevs ← args.mapM (fun arg =>
                match arg with
                | `($arg:term) =>
                premiseDataAuxM context defnName (TSyntax.mk arg) none false (maxDepth?.map (· -1)))
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
                    ⟨context, ← purgeTerm stx, (← purgeTerm stx).raw.size, 0, false⟩
                ts := ts.push (head)
            return (ts, pfs, ids, ps)
        | Syntax.ident _ _ name .. => 
            -- IO.println s!"ident {name}"
            let contextVars := context.filterMap getVar?
            if  !(contextVars.contains name) &&
                !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf name)) then 
                pure (#[], #[], #[(←termToString stx, 0)], [])
            else
                -- IO.println s!"skipping {name}" 
                pure (#[], #[], #[], [])
        | _ => pure (#[], #[], #[], [])

def Lean.Syntax.premiseDataM (context : Array Syntax)
    (proof prop: Syntax.Term)(includeHead: Bool)(name? : Option Name)(defnName : Name)(maxDepth? : Option Nat := none) : 
    MetaM (List PremiseData) := do
    let (ts, pfs, ids, ps) ← 
        premiseDataAuxM context defnName proof (some prop) false maxDepth?
    if includeHead then
        let head : PremiseData := 
            ⟨context, name?, defnName, ← purgeTerm prop, 
            ← purgeTerm prop, ← purgeTerm proof, (← purgeTerm prop).raw.size, 
            (← purgeTerm proof).raw.size, ts, pfs, ids⟩
        return head :: ps
    else return ps


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
    return some {name := name, type := ← purgeTerm tstx, value := ← purgeTerm stx, isProp := isProp, typeDepth := typeDepth.toNat, valueDepth := valueDepth.toNat, premises := premises.eraseDups}

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
        return some <| shrink (← termToString stx) 
    | none => return none



def verboseViewCore? (name: Name) : CoreM (Option String) :=
    (verboseView? name).run' {}

def DefData.ofNameCore? (name: Name) : CoreM (Option DefData) :=
    (DefData.ofNameM? name).run' {}

def PremiseData.ofNames (names: List Name) : MetaM (List PremiseData) := do
    let defs ← names.filterMapM DefData.ofNameM?
    return defs.bind (fun d => d.premises)



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



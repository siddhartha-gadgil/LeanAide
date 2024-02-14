import Lean
import Lean.Meta
import LeanAide.TheoremElab
import LeanAide.TheoremEquality
import LeanAide.Lean4Names

-- import Mathlib.Mathport.Rename

open Lean Meta Elab

partial def camelSplitAux (s : String)(accum: List String) : List String :=
  if s.length == 0 then accum
  else
    let head := s.decapitalize.takeWhile (fun c => 'a' ≤ c)
    if head.length = 0 then accum ++ [s]
    else
      let tail := s.drop (head.length)
      camelSplitAux tail (accum ++ [head])

def camelSplit(s : String) : List String :=
  camelSplitAux s []

-- #eval camelSplit "CamelCaseWord"

def fullSplit (s : String) : List String :=
  let parts := s.splitOn "_"
  parts.bind (fun s => camelSplit s)

-- #eval fullSplit "CamelCaseWord"
-- #eval fullSplit "snake_caseBut_wordWithCamel"

initialize caseNameCache : IO.Ref (HashMap String String)
  ← IO.mkRef (HashMap.empty)

-- initialize xNameCache : IO.Ref (HashMap String String)
--   ← IO.mkRef (HashMap.empty)

-- initialize xxNameCache : IO.Ref (HashMap String String)
--   ← IO.mkRef (HashMap.empty)

initialize dotNameCache : IO.Ref (HashMap String String)
  ← IO.mkRef (HashMap.empty)


initialize binNamesCache : IO.Ref (Array String) ← IO.mkRef (#[])

initialize binNameMapCache : IO.Ref (HashMap (List String) String)
  ← IO.mkRef (HashMap.empty)

initialize binNameNoIsMapCache : IO.Ref (HashMap (List String) String)
  ← IO.mkRef (HashMap.empty)

initialize elabPromptsCache : IO.Ref (HashSet String) ← IO.mkRef (HashSet.empty)

def caseNames : MetaM (HashMap String String) := do
  let cache ← caseNameCache.get
  if cache.isEmpty then
      let jsBlob ←
        IO.FS.readFile (← reroutePath <| System.mkFilePath ["extra_resources", "case_dictionary.json"])
      let json :=
        Lean.Json.parse jsBlob |>.toOption.get!
      match json.getArr? with
      | Except.error e => throwError e
      | Except.ok arr => do
        let mut m : HashMap String String := HashMap.empty
        for js in arr do
          let snakeCase? :=
            (js.getObjVal? "snakecase").toOption.bind (fun s =>
                s.getStr?.toOption)
          let camelCase? :=
            (js.getObjVal? "camelcase").toOption.bind (fun s =>
                s.getStr?.toOption)
          m := match (snakeCase?, camelCase?) with
            | (some sc, some cc) =>  m.insert sc cc
            | _ =>  m
        caseNameCache.set m
        return m
  else return cache

-- def xNames : MetaM (HashMap String String) := do
--   let cache ← xNameCache.get
--   if cache.isEmpty then
--       let lines ←
--         IO.FS.lines (← reroutePath <| System.mkFilePath ["extra_resources", "x_names.txt"])
--       let mut m : HashMap String String := HashMap.empty
--       for xname in lines do
--         m := m.insert (xname.dropRight 1) xname
--       xNameCache.set m
--       return m
--   else return cache

-- def xxNames : MetaM (HashMap String String) := do
--   let cache ← xxNameCache.get
--   if cache.isEmpty then
--       let lines ←
--         IO.FS.lines (← reroutePath <| System.mkFilePath ["extra_resources", "xx_names.txt"])
--       let mut m : HashMap String String := HashMap.empty
--       for xxname in lines do
--         m := m.insert (xxname.dropRight 2) xxname
--       xxNameCache.set m
--       return m
--   else return cache

def dotNames : MetaM (HashMap String String) := do
  let cache ← dotNameCache.get
  if cache.isEmpty then
      let lines ←
        IO.FS.lines (← reroutePath <| System.mkFilePath ["extra_resources", "simple_dot_names.txt"])
      let mut m : HashMap String String := HashMap.empty
      for name in lines do
        m := m.insert (name.toLower) name
      dotNameCache.set m
      return m
  else return cache

def caseName?(s: String) : MetaM (Option String) := do
  let cache ← caseNames
  return cache.find? s

-- def xName?(s: String) : MetaM (Option String) := do
--   let cache ← xNames
--   return cache.find? s

-- def xxName?(s: String) : MetaM (Option String) := do
--   let cache ← xxNames
--   return cache.find? s

def dotName?(s: String) : MetaM (Option String) := do
match s.splitOn "." with
| [head, field] =>
  if head.length ≤ 2 then
    let cache ← dotNames
    return cache.find? field |>.map (fun s => head ++ "." ++ s)
  else return none
| _ => return none

def binNames : IO (Array String) := do
  let cacheStr ← binNamesCache.get
  if cacheStr.size > 0 then
    return cacheStr
  else
    let all ←
      IO.FS.lines (← reroutePath <| System.mkFilePath ["extra_resources", "binport_names.txt"])
    let filtered := all.filter (fun s => s.length > 0)
    let filtered := filtered.toList
    binNamesCache.set filtered.toArray
    return all.filter (fun s => !(s.contains  '.'))

def binNameMap : IO (HashMap (List String) String) := do
  let cacheMap ← binNameMapCache.get
  if cacheMap.isEmpty then
    let names ← binNames
    let res := names.foldl
      (fun m s => m.insert (fullSplit s) s) (HashMap.empty)
    binNameMapCache.set res
    return res
  else
    return cacheMap

def elabPrompts : IO (HashSet String) := do
  let cacheStr ← elabPromptsCache.get
  if !cacheStr.isEmpty then
    return cacheStr
  else
    let arr ←
      IO.FS.lines (←
       reroutePath <| System.mkFilePath ["extra_resources", "elab_thms.txt"])
    return arr.foldl (fun acc n => acc.insert n) HashSet.empty

def isElabPrompt(s: String) : IO Bool := do
  let prompts ← elabPrompts
  return prompts.contains s


def withoutIs? : List String → Option (List String)
| x :: ys =>
  if x = "is" || x = "has" then some ys else none
| [] => none

def binNameNoIsMap : IO (HashMap (List String) String) := do
  let cacheMap ← binNameNoIsMapCache.get
  if cacheMap.isEmpty then
    let names ← binNames
    let res := names.foldl
      (fun m s =>
        match withoutIs? (fullSplit s) with
        | some ys => m.insert ys s
        | none => m
          ) (HashMap.empty)
    binNameNoIsMapCache.set res
    return res
  else
    return cacheMap

def binName?(s : String) : MetaM <| Option String := do
  let map ← binNameMap
  let mapNoIs ← binNameNoIsMap
  let split := fullSplit s
  let splitNoIs? := withoutIs? split
  let res := ((map.find? split).orElse
              (fun _ => mapNoIs.find? split)).orElse
              (fun _ => splitNoIs?.bind (
                  fun splitNoIs => map.find? splitNoIs))
  return res



def caseOrBinName?(s : String) : MetaM (Option String) := do
  match ← lean4Name? s with
  | some name => return some name.toString
  | none => do
    let res ← caseName? s
    if res.isNone then do
      let res ← binName? s
      return res
    else return res

-- #eval lean4Name? "has_abs"


def identErr (err: String) : Option String :=
  let head := "unknown identifier '"
  let tail := "' (during elaboration)"
  if err.startsWith head && err.endsWith tail then
    some <| (err.drop (head.length)).dropRight (tail.length)
  else
    none


def identCorrection(s err: String) : MetaM (Option String) := do
  match identErr err with
  | none => return none
  | some id => match ←  binName? id with
    | none => return none
    | some name => return some (s.replace id name)

/-- identifier substrings -/
partial def identSubs : Syntax → List Substring
| Syntax.ident _ s .. => [s]
| Syntax.node _ _ ss => ss.toList.bind identSubs
| _ => []

partial def extractByteAux (s: String) (start stop : String.Pos) (accum: String)
    := if start ≥  stop then accum else
        let h := s.get start
        extractByteAux s (s.next start) stop (accum ++ h.toString)

def extractBytes (s: String) (start stop : String.Pos) :=
      extractByteAux s start stop ""

def interleaveAux (full: Substring)(cursor: String.Pos)
  (accum: List (Substring × Substring))(idents: List Substring) :
      (List (Substring × Substring)) × Substring :=
  match idents with
  | [] => (accum, full.extract cursor full.stopPos)
  | h :: ts =>
      let pred := full.extract cursor h.startPos
      interleaveAux full (h.stopPos)
          (accum ++ [(pred, h)]) ts

def interLeave(full: Substring)(idents: List Substring) :
      (List (Substring × Substring)) × Substring :=
          interleaveAux full 0 [] idents

/-- given a string expected to be a *theorem statement* such as `{A: Type} (a : A) : P a`, transforms to one of the type `{A: Type} → (a : A) → P a`, parses this as a term and returns segments and a tail, with each segment a pair with the second part an identifier and the first an identifier-free part preceding it. -/
def identThmSegments (s : String)
  : MetaM <| Except String ((Array (String × String)) × String) := do
  let env ← getEnv
  let chk := Lean.Parser.runParserCategory env `theorem_statement  s
  match chk with
  | Except.ok stx  =>
      match stx with
      | `(theorem_statement|$_: docComment $_:theorem_head  $args:bracketedBinder* : $type:term) =>
        identsAux type args
      | `(theorem_statement|$_:theorem_head $_ $args:bracketedBinder* : $type:term) =>
        identsAux type args
      | `(theorem_statement|$args:bracketedBinder* : $type:term) =>
        identsAux type args
      | _ =>
        let err : Except String ((Array (String × String)) × String) := Except.error "not a theorem statement"
        (pure err : MetaM <| Except String ((Array (String × String)) × String))
  | Except.error _  => return Except.error "not a theorem statement"
  where identsAux (type: TSyntax `term)
    (args:  TSyntaxArray `Lean.Parser.Term.bracketedBinder) :
        MetaM <| Except String ((Array (String × String)) × String) := do
        let mut argS := ""
        for arg in args do
          argS := argS ++ (showSyntax arg) ++ " -> "
        let funTypeStr := s!"{argS}{showSyntax type}"
        let mut typeStx : TSyntax `term := type
        for arg in args.reverse do
          let stx ← `(Lean.Parser.Term.depArrow|$arg → $typeStx)
          typeStx := ⟨stx.raw⟩
        match Lean.Parser.runParserCategory (← getEnv) `term funTypeStr with
        | Except.ok termStx =>
              let mut fullString := funTypeStr
              let mut segments : Array (String × String) := #[]
              let mut cursor : String.Pos := 0
              let res := identSubs termStx
              for ss in res do
                fullString := ss.str
                let pred := fullString.extract cursor ss.startPos
                segments := segments.push (pred, ss.toString)
                cursor := ss.stopPos
              let tail := fullString.extract cursor fullString.endPos
              return Except.ok (segments, tail)
        | Except.error e => return Except.error e

def transformBuild (segs: (Array (String × String)) × String)
        (transf : String → MetaM (Option String)) : MetaM (String) := do
        let (pairs, tail) := segs
        let res : Array (String × String) ←
          pairs.mapM (fun (pred, ident) => do
            let ident'? ← transf ident
            let ident' := ident'?.getD ident
            return (pred, ident'))
        let out : String :=
          res.foldr (fun (init, ident) acc => (init ++ ident ++ acc)) tail
        return out

/-- given a string like `{A: Type} → (a : A) → P a` broken up into identifiers and intermediate segments, transforms this by translating identifiers using a given one-one and a given one-many transformation and returns corresponding lists of segments -/
def polyTransform (pairs: (List (String × String)))
        (transf : String → MetaM (Option String))
        (extraTransf : List (String → MetaM (Option String))) :
            MetaM (List (List (String × String))) := do
        match pairs with
        | [] => return [[]]
        | h :: ts =>
          let (pred, ident) := h
          let ident' :=  (← transf ident).getD ident
          let extraIdents ←
              extraTransf.filterMapM (fun f => f ident')
          let h' := (ident' :: extraIdents).map ((pred, .))
          let prev ← polyTransform ts  transf extraTransf
          return h'.bind (fun x => prev.map (x :: .))

/-- given a string like `{A: Type} → (a : A) → P a` broken up into identifiers and intermediate segments, transforms this by translating identifiers using a given one-one and a given one-many transformation and builds strings from the results -/
def polyTransformBuild (segs: (Array (String × String)) × String)
        (transf : String → MetaM (Option String))
        (extraTransf : List (String → MetaM (Option String))) (limit : Option Nat := none) :
        MetaM (List String) := do
        let (pairs, tail) := segs
        if (pairs.size ≥  limit.getD (pairs.size + 1)) then return []
        else
        -- IO.println s!".lake/building {pairs.size} segments"
        let transformed ← polyTransform pairs.toList transf extraTransf
        -- IO.println s!"transformed to {transformed.length} pieces"
        let strings :=
          transformed.map (fun res =>
            res.foldr (fun (init, ident) acc => (init ++ ident ++ acc)) tail)
        -- IO.println "built strings"
        return strings.eraseDups


def identMappedFunStx (s: String)
    (transf : String → MetaM (Option String) := binName?)  : MetaM (Except String String) := do
    let corr?  ← identThmSegments s
    match corr? with
    | Except.ok corr => do
          let t ← transformBuild corr transf
          return Except.ok t
    | Except.error e => return Except.error e

/-- transforms a string expected to be of a form like `{A: Type} → (a : A) → P a` by translating identifiers using a given one-one and a given one-many transformation  -/
def polyIdentMappedFunStx (s: String)
    (transf : String → MetaM (Option String) := caseOrBinName?)
    (extraTransf : List (String → MetaM (Option String))
        := [])
    (limit : Option Nat := none)  : MetaM (Except String (List String)) := do
    let corr?  ← identThmSegments s
    match corr? with
    | Except.ok corr => do
          let t ← polyTransformBuild corr transf extraTransf limit
          return Except.ok t
    | Except.error e => return Except.error e

-- #eval identThmSegments "{K : Type u} [Field K] : is_ring K"

/-- attempts to elaborate a string expected to be of a form like  `{A: Type} → (a : A) → P a` via parsing to a term; in principle any term is parsed -/
def elabFuncTyp (funTypeStr : String) (levelNames : List Lean.Name := levelNames) : TermElabM (Except String <| Syntax ×  Expr) := do
    -- IO.println s!"matching syntax {funTypeStr}"
    match Lean.Parser.runParserCategory (← getEnv) `term funTypeStr with
        | Except.ok termStx => Term.withLevelNames levelNames <|
          try
            -- IO.println "elaborating"
            let expr ← Term.withoutErrToSorry <|
                Term.elabTerm termStx none
            return Except.ok (termStx, expr)
          catch e =>
            return Except.error s!"{← e.toMessageData.toString} for {termStx.reprint} (during elaboration)"
        | Except.error e =>
            return Except.error s!"parsed func-type to {funTypeStr}; error while parsing as theorem: {e}"

/-- elaborates the string with translations and auto-corrections, including the one-to-many compatibility transformations and (optionally) returns a list of translations and translated strings -/
def polyElabThmTrans (s : String)(limit : Option Nat := none)
  (transf : String → MetaM (Option String) := caseOrBinName?)
  (extraTransf : List (String → MetaM (Option String))
        := [])

  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| Except String (List (Expr × Syntax × String)) := do
  match ← polyIdentMappedFunStx s transf extraTransf limit with
  | Except.ok funTypeStrList => do
    -- IO.println s!"elaborating {funTypeStrList.length} strings"
    let pairs: List (Expr × Syntax × String) ←
      funTypeStrList.filterMapM (fun funTypeStr => do
        let expE? ← elabFuncTyp funTypeStr levelNames
        let exp? := expE?.toOption
        return exp?.map <| fun (stx, expr) => (expr, stx , funTypeStr))
    return Except.ok pairs
  | Except.error e => return Except.error e

/-- elaborates the string with translations and auto-corrections, including the one-to-many compatibility transformations and (optionally) returns a  translation and translated string -/
def elabThmTrans? (s : String)(limit : Option Nat := none)
  (transf : String → MetaM (Option String) := caseOrBinName?)
  (extraTransf : List (String → MetaM (Option String))
        := [])

  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| (Option (Expr × Syntax × String)) := do
  match ← polyIdentMappedFunStx s transf extraTransf limit with
  | Except.ok funTypeStrList => do
    -- IO.println s!"elaborating {funTypeStrList.length} strings"
    funTypeStrList.findSomeM? (fun funTypeStr => do
        let expE? ← elabFuncTyp funTypeStr levelNames
        let exp? := expE?.toOption
        return exp?.map <| fun (stx, expr) => (expr, stx , funTypeStr))
  | Except.error _ => return none

def polyStrThmTrans (s : String)
  (transf : String → MetaM (Option String) := caseOrBinName?)
  (extraTransf : List (String → MetaM (Option String))
        := [])

  : TermElabM (List String) := do
  match ← polyIdentMappedFunStx s transf extraTransf with
  | Except.ok funTypeStrList => do
    return funTypeStrList
  | Except.error _ => return [s]

def elabThmTrans (s : String)
  (transf : String → MetaM (Option String) := caseOrBinName?)

  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| Except String (Expr × String) := do
  match ← identMappedFunStx s transf with
  | Except.ok funTypeStr => do
    match (← elabFuncTyp funTypeStr levelNames) with
    | Except.ok (_, expr) => return Except.ok (expr, funTypeStr)
    | Except.error e => return Except.error e
  | Except.error e => return Except.error e

def compareFuncStrs(s₁ s₂ : String)
  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| Except String Bool := do
  let e₁ ← elabFuncTyp s₁  levelNames
  let e₂ ← elabFuncTyp s₂ levelNames
  match e₁ with
  | Except.ok (_, e₁) => match e₂ with
    | Except.ok (_, e₂) =>
        let p ← provedEqual e₁ e₂ <||> provedEquiv e₁ e₂
        return Except.ok p
    | Except.error e₂ => return Except.error e₂
  | Except.error e₁ => return Except.error e₁

def equalFuncStrs(s₁ s₂ : String)
  (levelNames : List Lean.Name := levelNames): TermElabM Bool := do
  match ← compareFuncStrs s₁ s₂  levelNames with
  | Except.ok p => return p
  | Except.error _ => return Bool.false


def groupFuncStrs(ss: Array String)
  (levelNames : List Lean.Name := levelNames)
  : TermElabM (Array (Array String)) := do
    let mut groups: Array (Array String) := Array.empty
    for s in ss do
      match ← groups.findIdxM? (fun g =>
          equalFuncStrs s g[0]!  levelNames) with
      |none  =>
        groups := groups.push #[s]
      | some j =>
        groups := groups.set! j (groups[j]!.push s)
    return groups

def elabCorrected(depth: Nat)(ss : Array String) :
  TermElabM (Array String) := do
  let mut elabs : Array String := #[]
  let mut corrected : Array String := #[]
  for s  in ss do
    match ← elabThm s with
    | Except.ok _ => elabs := elabs.push s
    | Except.error err => do
      logInfo m!"s: {s}, err: {err}"
      match ← identCorrection s err with
      | none => pure ()
      | some s' => corrected := corrected.push s'
  if elabs.isEmpty then
    match depth with
    | 0 => return #[]
    | d + 1 => if corrected.isEmpty then return #[] else do
      elabCorrected d corrected
  else return elabs

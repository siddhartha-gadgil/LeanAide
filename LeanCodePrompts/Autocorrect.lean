import Lean
import Lean.Meta
import LeanCodePrompts.CheckParse
open Lean Std Meta Elab

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

initialize binNamesCache : IO.Ref (Array String) ← IO.mkRef (#[])

initialize binNameMapCache : IO.Ref (HashMap (List String) String) 
  ← IO.mkRef (HashMap.empty)

def binNames : IO (Array String) := do 
  let cacheStr ← binNamesCache.get
  if cacheStr.size > 0 then 
    return cacheStr
  else 
    let all ← 
      IO.FS.lines (System.mkFilePath ["data", "binport_names.txt"])
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

def withoutIs : List String → List String
| x :: ys => if x = "is" || x = "has" then ys else x :: ys
| [] => []

def getBinName(s : String) : IO <| Option String := do
  let all ← binNames
  let split := fullSplit s
  -- let all := #[]
  let res := all.find? (fun s => split = fullSplit s)
  match res with
  | some s => return some s
  | none =>
    match split with
    | x :: ys => 
      if x = "is" || x = "has" 
      then return  all.find? (fun s => ys = withoutIs (fullSplit s))
      else return none
    | _ => return none


def identErr (err: String) : Option String :=
  let head := "unknown identifier '"
  let tail := "' (during elaboration)"
  if err.startsWith head && err.endsWith tail then
    some <| (err.drop (head.length)).dropRight (tail.length)
  else
    none


def identCorrection(s err: String) : IO (Option String) := do
  match identErr err with
  | none => return none 
  | some id => match ←  getBinName id with
    | none => return none
    | some name => return some (s.replace id name)

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


#check Substring.extract

def identsThm (s : String)
  : TermElabM <| Option (List Substring) := do
  let env ← getEnv
  let chk := Lean.Parser.runParserCategory env `thmStat  s
  match chk with
  | Except.ok stx  =>
      match stx with
      | `(thmStat|theorem $_ $args:argument* : $type:term) =>
        identsAux type args
      | `(thmStat|def $_ $args:argument* : $type:term) =>
        identsAux type args
      | `(thmStat|$args:argument* : $type:term) =>
        identsAux type args
      | `(thmStat|$_:ident $args:argument* : $type:term) =>
        identsAux type args
      | _ => return none
  | Except.error _  => return none
  where identsAux (type: Syntax)(args: Array Syntax) : 
        TermElabM <| Option (List Substring) := do
        let header := ""
        let mut argS := ""
        for arg in args do
          argS := argS ++ (showSyntax arg) ++ " -> "
        let funStx := s!"{header}{argS}{showSyntax type}"
        match Lean.Parser.runParserCategory (← getEnv) `term funStx with
        | Except.ok termStx => 
              let res := identSubs termStx
              logInfo m!"{termStx}"
              for ss in res do 
                logInfo m!"{ss}"
                logInfo m!"{ss.str}"
                logInfo m!"{ss.startPos}"
                logInfo m!"{ss.stopPos}"
              return some res
        | Except.error _ => return none

def identsSegments(s : String)
  : TermElabM <| Option ((List (Substring × Substring)) × Substring) := do
      let idents ← identsThm s
      return idents.map (interLeave s.toSubstring)

#eval identsThm "{K : Type u} [Field K] : is_ring K"

#eval identsSegments "{K : Type u} [Field K] : is_ring K"

#check String.endPos

def elabCorrected(depth: Nat)(ss : Array String) : 
  TermElabM (Array String) := do
  let mut elabs : Array String := #[]
  let mut corrected : Array String := #[]
  for s  in ss do
    match ← elabThm s with
    | Except.ok _ => elabs := elabs.push s
    | Except.error err => do
      logInfo m!"s: {s}, err: {err}"
      -- if err.endsWith "(during elaboration)" then
      --     let parsed : Except String Syntax := 
      --         Lean.Parser.runParserCategory (← getEnv) `term s
      --     let p? := parsed.toOption
      --     logInfo m!"identifiers: {p?} in {s}"
      match ← identCorrection s err with
      | none => pure ()
      | some s' => corrected := corrected.push s'
  if elabs.isEmpty then 
    match depth with 
    | 0 => return #[]
    | d + 1 => if corrected.isEmpty then return #[] else do
      elabCorrected d corrected
  else return elabs


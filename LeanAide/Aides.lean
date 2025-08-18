import Lean
import Lean.Meta
import Lean.Elab
import Lean.Parser
import Lean.Parser.Extension
import Batteries.Data.List.Basic
import LeanAide.Config
import Std
import LeanAideCore.Aides

open Lean Meta Elab Parser Tactic System


def leanAidePath : IO System.FilePath := do
  return (← baseDir) / ".lake" /"packages" /"leanaide"

def cachePath : IO System.FilePath := do
  let path : System.FilePath := (← baseDir) /  ".leanaide_cache"
  if ← path.pathExists then
    return path
  else
    return (← leanAidePath) / path

-- #eval cachePath

def reroutePath (fp : System.FilePath) : IO System.FilePath := do
  if ← fp.pathExists then
    return fp
  else
    return (← leanAidePath) / fp


def getDelabBound : MetaM UInt32 := do
   delab_bound.get

def setDelabBound (n: UInt32) : MetaM Unit := do
   delab_bound.set n

def picklePath (descField : String) : IO System.FilePath := do
  let name := if descField == "docString" then "prompts" else descField
  return (← baseDir)/".lake"/ "build" / "lib" /
    s!"mathlib4-{name}-embeddings-{← leanToolchain}.olean"


def appendLog (logFile: String) (content : Json) (force: Bool := false) : CoreM Unit := do
  if force then go logFile content
  else
    match (← leanAideLogging?) with
    | some "0" => return ()
    | some _ => go logFile content
    | none => return ()
  where go (logFile: String) (content: Json) : IO Unit := do
    let dir : FilePath := (← baseDir) / "leanaide_logs"
    if !(← dir.pathExists) then
      IO.FS.createDirAll dir
    let fname : FilePath := dir / (logFile ++ "-" ++ (← showDate) ++ ".jsonl")
    appendFile fname content.compress


def colEqSegments (s: String) : List String :=
  let pieces := s.splitOn ":="
  match pieces with
  | [] => []
  | head :: tail =>
    tail.scanl (fun acc x => acc ++ ":=" ++ x) head |>.map (String.trim)

def splitColEqSegments (ss: Array String) : Array String :=
  ss.toList.flatMap colEqSegments |>.toArray

def trivialEquality : Syntax → CoreM Bool
  | `($a = $b) => return a == b
  | _ => return false



def extractJsonM (s: String) : CoreM Json :=
  let code := codeBlock? "json" s |>.getD s
  let code := code.trim
  match Json.parse code with
  | Except.ok j => do
    -- logInfo s!"parsed JSON: {j}"
    appendLog "json_parsed" j
    return j
  | Except.error e => do
    logWarning  m!"Error parsing JSON: {e}"
    appendLog "json_error" (Json.str code)
    appendLog "json_error" (Json.str e)
    return Json.str code


partial def identNames : Syntax → MetaM (List Name)
| Syntax.ident _ _ s .. => do
  if (← isWhiteListed s) &&
    !(excludeSuffixes.any fun sfx => sfx.isSuffixOf s) && !(excludePrefixes.any fun pfx => pfx.isPrefixOf s)
    then return [s] else return []
| Syntax.node _ _ ss => do
    let groups ← ss.toList.mapM identNames
    return groups.flatten.eraseDup
| _ => return []

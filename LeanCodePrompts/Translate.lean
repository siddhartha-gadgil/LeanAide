import Lean
import Lean.Meta
import Lean.Parser
import Std
import LeanCodePrompts.CheckParse
import LeanCodePrompts.ParseJson
open Std

open Lean Elab Parser Command

def egPrompt:= "Every prime number is either `2` or odd."

def egOut := #["{p : ℕ} (hp : Nat.Prime p) :  p = 2 ∨ p % 2 = 1 ",
   "(p : ℕ) :  Nat.Prime p ↔ p = 2 ∨ p % 2 = 1 ",
   "{p : ℕ} (hp : Nat.Prime p) : p = 2 ∨ p % 2 = 1 ",
   "(n : ℕ) (hp : Nat.Prime n) : n = 2 ∨ n % 2 = 1 ",
   "{p : ℕ} (hp : Nat.Prime p) : p = 2 ∨ p % 2 = 1 ",
   "Nonsense output to test filtering"]

def egBlob := "[\"{p : ℕ} (hp : Nat.Prime p) :  p = 2 ∨ p % 2 = 1 \",
   \"(p : ℕ) :  Nat.Prime p ↔ p = 2 ∨ p % 2 = 1 \",
   \"{p : ℕ} (hp : Nat.Prime p) : p = 2 ∨ p % 2 = 1 \",
   \"(n : ℕ) (hp : Nat.Prime n) : n = 2 ∨ n % 2 = 1 \",
   \"{p : ℕ} (hp : Nat.Prime p) : p = 2 ∨ p % 2 = 1 \",
   \"Nonsense output to test filtering\"]"

def egBlob' := "[{ \"text\" : \"{p : ℕ} (hp : Nat.Prime p) :  p = 2 ∨ p % 2 = 1 \"},
   { \"text\" : \"(p : ℕ) :  Nat.Prime p ↔ p = 2 ∨ p % 2 = 1 \"},
   { \"text\" : \"{p : ℕ} (hp : Nat.Prime p) : p = 2 ∨ p % 2 = 1 \"},
   { \"text\" : \"(n : ℕ) (hp : Nat.Prime n) : n = 2 ∨ n % 2 = 1 \"},
   { \"text\" : \"{p : ℕ} (hp : Nat.Prime p) : p = 2 ∨ p % 2 = 1 \"},
   { \"text\" : \"Nonsense output to test filtering\"}]"

def caseMapProc (s: String) : IO String := do
  let tmpFile := System.mkFilePath ["web_serv/tmp.json"]
  IO.FS.writeFile tmpFile s
  let out ← 
    IO.Process.output {cmd:= "./amm", args := #["scripts/simplemap.sc"]}
  return out.stdout

initialize webCache : IO.Ref (HashMap String String) ← IO.mkRef (HashMap.empty)

def getCached? (s: String) : IO (Option String) := do
  let cache ← webCache.get
  return cache.find? s

def cache (s jsBlob: String)  : IO Unit := do
  let cache ← webCache.get
  webCache.set (cache.insert s jsBlob)
  return ()

def getCodeJson (s: String) : IO String := do
  match ← getCached? s with
  | some s => return s
  | none =>
    let out ←  
      IO.Process.output {cmd:= "curl", args:= 
        #["-X", "POST", "-H", "Content-type: application/json", "-d", s, "localhost:5000/post_json"]}
    let res ← caseMapProc out.stdout
    cache s res
    return res
  -- return out.stdout



def arrayToExpr (output: Array String) : TermElabM Expr := do
  let elaborated ← output.filterM  <| 
      fun s => do
        let chk ← elabThm s
        return chk.toBool
  logInfo m!"elaborated: {elaborated.size} out of {output.size}"
  if elaborated.isEmpty then do
    logWarning m!"No elaborated output found"
    for out in output do
      logWarning m!"{out}"
    throwError "No valid output from codex"  
  let groupSorted ← groupThms elaborated
  let topStr := groupSorted[0]![0]!
  let thmExc ← elabThm topStr
  let thm := thmExc.toOption.get!
  return thm

def textToExpr (s: String) : TermElabM Expr := do
  let json ← readJson s
  let outArr : Array String ← 
    match json.getArr? with
    | Except.ok arr => 
        let parsedArr : Array String ← 
          arr.filterMapM <| fun js =>
          match js.getStr? with
          | Except.ok str => pure (some str)
          | Except.error e => 
            throwError m!"json string expected but got {js}, error: {e}"
        pure parsedArr
    | Except.error e => throwError m!"json parsing error: {e}"
  let output := outArr
  arrayToExpr output

def textToExpr' (s: String) : TermElabM Expr := do
  let json ← readJson s
  let outArr : Array String ← 
    match json.getArr? with
    | Except.ok arr => 
        let parsedArr : Array String ← 
          arr.filterMapM <| fun js =>
            match js.getObjVal? "text" with
              | Except.ok jsstr =>
                match jsstr.getStr? with
                | Except.ok str => pure (some str)
                | Except.error e => 
                  throwError m!"json string expected but got {js}, error: {e}"
              | Except.error _ =>
                throwError m!"no text field"
        pure parsedArr
    | Except.error e => throwError m!"json parsing error: {e}"
  let output := outArr
  arrayToExpr output

def textToExprStx' (s : String) : TermElabM (Expr × TSyntax `term) := do
  let e ← textToExpr' s
  let (stx : Term) ← (PrettyPrinter.delab e)
  return (e, stx)

elab "//-" cb:commentBody "/" : term => do
  let s := cb.raw.getAtomVal!
  let s := (s.dropRight 2).trim  
  let jsBlob ← getCodeJson  s
  let e ← textToExpr' jsBlob
  logInfo m!"{e}"
  return e

elab "#theorem" name:ident " : " stmt:str ":=" prf:term : command => do
  let (fmlstmt, fmlstx) ← liftTermElabM none $ textToExprStx' egBlob' -- stmt.getString
  logInfoAt stmt m!"{fmlstmt}"
  elabCommand $ ← `(theorem $name:ident : $fmlstx:term := $prf:term)

elab "#example" stmt:str ":=" prf:term : command => do
  let (fmlstmt, fmlstx) ← liftTermElabM none $ textToExprStx' egBlob' -- stmt.getString
  logInfoAt stmt m!"{fmlstmt}"
  elabCommand $ ← `(example : $fmlstx:term := $prf:term)

-- #eval getCodeJson egPrompt
import Lean
import Lean.Parser
import LeanCodePrompts.Utils

open Lean Parser


declare_syntax_cat jsonid
syntax ident: jsonid
syntax str: jsonid

declare_syntax_cat json
syntax str : json
syntax num : json
syntax scientific: json
syntax "true" : json
syntax "false" : json
syntax "null" : json
syntax "{" (jsonid ": " json),* "}" : json
syntax "[" json,* "]" : json

#check Json.mkObj

def getJsonSyntax(s: String) : MetaM Syntax := do
  match (runParserCategory (← getEnv) `json s) with
  | Except.ok stx => pure stx
  | Except.error msg => throwError msg

#eval getJsonSyntax "[{hello: 1}, [2, 3]]"

open Json in
partial def parseJsonSyntax (s: Syntax) : MetaM Json := do
  match s with
  | `(json|true) => do
      return Json.bool Bool.true 
  | `(json|false) => do
      return Json.bool Bool.false
  | `(json|null) => do
      return (Json.null)
  | `(json|$s:str) => pure (Syntax.isStrLit? s).get!
  | `(json|$n:num) => pure (Syntax.isNatLit? n).get!
  | `(json|$n:scientific) => 
        return (showSyntax s).trim
  | `(json|{ $[$ns : $js],* }) => do
    let mut fields := #[]
    for n in ns, j in js do
      let name ←  match n with
        | `(jsonid|$s:str) => pure (Syntax.isStrLit? s).get!
        | `(jsonid|$n:ident) => pure n.getId.getString!
        | _ => throwError "invalid json field name" 
       
      let value ←  parseJsonSyntax j
      fields := fields.push (name, value)
    return mkObj fields.toList 
  | `(json|[ $[$js],* ]) => do
    let mut fields := #[]
    for j in js do
      let value ←  parseJsonSyntax j
      fields := fields.push (value)
    return Json.arr fields
  | _ => throwError "invalid json syntax"

def readJson(s: String) : MetaM Json := do
  -- logInfo "parsing json"
  let stx ← getJsonSyntax s
  -- logInfo "got syntax"
  parseJsonSyntax stx

#eval readJson "[{hello: 1}, [2, 3], {\"x\": 3}]"


def checkRead: MetaM Json := do 
  let file := System.mkFilePath ["data/test.json"]
  let s ← IO.FS.readFile file 
  readJson s

#eval checkRead

def readJsonCore(s: String) : CoreM Json :=
    (readJson s).run'

open Lean Parser Command

elab "//--" cb:commentBody : term => do
  let s := cb.raw.getAtomVal
  let s := s.dropRight 2
  logInfo m!"{s}"
  return mkConst ``Unit

#check Parser.ppLine
#check PrettyPrinter.Formatter

-- elab "-#-" cb:commentBody : command => do
--  logInfo m!"{cb.raw.getAtomVal!}"



set_option pp.rawOnError true
#check //-- Every prime is nice -/

def egProc : IO String := do
  let out ←  IO.Process.output {cmd:= "curl", args:= #["example.com"]}
  let key ← IO.getEnv "OPENAI_API_KEY"
  IO.println key
  return out.stdout

#eval egProc

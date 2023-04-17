import Lean
import Lean.Parser
import Lean.Data.Json
import LeanCodePrompts.Utils

open Lean Parser

def readJson(s: String) : MetaM Json := do
  let js? := Lean.Json.parse s
  return js?.toOption.get!

-- #eval readJson "[{hello: 1}, [2, 3], {\"x\": 3}]"


def checkRead: MetaM Json := do 
  let file ← liftM <| reroutePath <| System.mkFilePath ["data/test.json"]
  let s ← IO.FS.readFile file 
  readJson s

-- #eval checkRead

def readJsonCore(s: String) : CoreM Json :=
    (readJson s).run'

open Lean Parser Command

-- #check commentBody

elab "//--" cb:commentBody : term => do
  let s := cb.raw.getAtomVal
  let s := s.dropRight 2
  logInfo m!"{s}"
  return mkConst ``Unit

-- #check Parser.ppLine
-- #check PrettyPrinter.Formatter

-- elab "-#-" cb:commentBody : command => do
--  logInfo m!"{cb.raw.getAtomVal!}"



-- set_option pp.rawOnError true
-- #check //-- Every prime is nice -/

def egProc : IO String := do
  let out ←  IO.Process.output {cmd:= "curl", args:= #["example.com"]}
  let key ← IO.getEnv "OPENAI_API_KEY"
  IO.println key
  return out.stdout

-- #eval egProc

import Lean
import LeanAide.Aides
import LeanAideCore.TheoremElab
import LeanAideCore.Syntax
open Lean Meta Elab Parser  Tactic

/-!
## Parsing and Elaboration of statements

These can be headed with `theorem`, `def`, `example` or nothing and may or may not have a name.
-/
namespace LeanAide


def thmsPrompt : MetaM (Array String) := do
  let file ← reroutePath <| System.mkFilePath ["extra_resources/thms.txt"]
  IO.FS.lines file
open Lean.Parser.Category

/-- check whether a string parses as a theorem -/
def checkThm (s : String) : MetaM Bool := do
  let env ← getEnv
  let chk := Lean.Parser.runParserCategory env ``theorem_statement  s
  match chk with
  | Except.ok stx  =>
      IO.println stx
      pure true
  | Except.error _  => pure false


/-- split prompts into those that parse -/
def promptsThmSplit : MetaM ((Array String) × (Array String)) := do
  let deps ← thmsPrompt
  let mut succ: Array String := Array.empty
  let mut fail: Array String := Array.empty
  for type in deps do
    let chk ←  checkThm type
    if chk then
      succ := succ.push type
    else
      fail := fail.push type
  return (succ, fail)

def promptsThmSplitCore : CoreM ((Array String) × (Array String)) :=
  promptsThmSplit.run'

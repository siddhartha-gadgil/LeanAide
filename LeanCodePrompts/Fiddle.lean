import Lean
import Lean.Parser
open Lean Meta Elab Parser

def runParserCategoryPartial  (catName : Name) (input : String) (fileName := "<input>") : MetaM <| Except String Syntax := do
  let env ← getEnv
  let c := mkParserContext (mkInputContext input fileName) { env := env, options := {} }
  let s := mkParserState input
  let s := whitespace c s
  let parser := categoryParser catName 0
  let parserFn := parser.fn
  let s : ParserState := parserFn c s
  let stack := s.stxStack.filter fun s => !s.hasMissing
  -- let s := categoryParserFnImpl catName c s
  if stack.isEmpty &&  s.hasError then
    return    Except.error (s.toErrorMsg c)
  else 
    IO.println <| input.extract 0 s.pos
    return Except.ok stack.back

def runParserPartial  (parser : Parser) (input : String) (fileName := "<input>") : MetaM <| Except String Syntax := do
  let env ← getEnv
  let c := mkParserContext (mkInputContext input fileName) { env := env, options := {} }
  let s := mkParserState input
  let s := whitespace c s
  let parserFn := parser.fn
  let s : ParserState := parserFn c s
  -- IO.println s.stxStack
  let stack := s.stxStack.filter fun s => !s.hasMissing
  -- let s := categoryParserFnImpl catName c s
  if stack.isEmpty &&  s.hasError then
    return    Except.error (s.toErrorMsg c)
  else 
    IO.println <| input.extract 0 s.pos
    return Except.ok stack.back


#eval runParserCategoryPartial `term "1 + 2  3"

#check Syntax.hasMissing

#eval runParserPartial ident "x y z 3"

#eval runParserCategoryPartial `tactic "repeat (simp [x, Nat]; skip)  1 + 2  3"

open Command

#eval runParserPartial «variable» "variable (x : Nat) [h: Group x] and something else"

variable (x : Nat)

#eval runParserCategoryPartial `tactic "have x : N := 2 := 3 ; simp"

declare_syntax_cat hellotac

declare_syntax_cat defhead
syntax "theorem" : defhead
syntax "def" : defhead
syntax "lemma" : defhead

syntax defhead ident ":" term ":=" "by" tactic : hellotac

#eval runParserCategoryPartial `hellotac "theorem blah : Nat := by let x : N := 2 := 3 ; simp"

def getName (stx: Syntax) : MetaM Name := do
match stx with
| `(hellotac|theorem $name:ident : $_:term := by $_) => pure name.getId
| _ => throwUnsupportedSyntax

def parseName(s: String) : MetaM Name := do
match ← runParserCategoryPartial `hellotac s with
| Except.ok stx => getName stx
| Except.error msg => throwError msg

#eval parseName "theorem blah : Nat := by let x : N := 2 := 3 ; simp"

def getPieces (stx: Syntax) : MetaM (String × String × String) := do
match stx with
| `(hellotac|theorem $name:ident : $t:term := by $tac) => 
    pure (name.raw.reprint.get!, t.raw.reprint.get!, tac.raw.reprint.get!)
| _ => throwUnsupportedSyntax

def parsePieces(s: String) : MetaM (String × String × String) := do
match ← runParserCategoryPartial `hellotac s with
| Except.ok stx => getPieces stx
| Except.error msg => throwError msg

#eval parsePieces "theorem blah : Nat := by let x : N := 2 := 3 ; simp"

#check IO.FS.readFile

#eval (searchPathRef.get : IO _)

def oleanFiles : IO (Array System.FilePath) := do 
  let paths ← searchPathRef.get
  IO.println paths
  Lean.SearchPath.findAllWithExt paths "olean"

#eval oleanFiles

#check System.mkFilePath ["."]

def leanFiles : IO (Array System.FilePath) := do 
  Lean.SearchPath.findAllWithExt [System.mkFilePath ["./LeanCodePrompts"]] "lean"

#eval leanFiles
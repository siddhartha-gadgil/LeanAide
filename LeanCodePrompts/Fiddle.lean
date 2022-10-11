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
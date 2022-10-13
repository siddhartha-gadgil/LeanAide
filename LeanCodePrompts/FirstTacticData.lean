import LeanCodePrompts.CheckParse
import Lean
open Lean Meta Parser Elab Tactic

def contractInductionStx (tac : Syntax) : MetaM Syntax := do
match tac with
| `(tactic| induction $name $_:inductionAlts) => 
  `(tactic| induction $name)
| `(tactic| cases $name $_:inductionAlts) => 
  `(tactic| cases $name)
| _ => return tac

def partialParser  (parser : Parser) (input : String) (fileName := "<input>") : MetaM <| Option (Syntax × String × String) := do
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
    return    none
  else 
    let head := input.extract 0 s.pos
    let stx := stack.back
    return some (stx, head, input.drop head.length)


declare_syntax_cat defHead
syntax "theorem" : defHead
syntax "def" : defHead
syntax "lemma" : defHead
syntax "instance" : defHead

declare_syntax_cat theoremAndTactic

syntax 
  defHead ident (argument)* ":" term ":=" "by" tactic : theoremAndTactic

def egThm1 := "theorem egIsAction: ∀ (x y: Fin 2), 
  (egAction' x) ∘ (egAction' y) = egAction' (x + y) := by 
    decide
    skip"

def tacEg := "
  apply f 
  skip
  decide"

#eval partialParser (categoryParser `tactic 0) tacEg

#eval partialParser (categoryParser `theoremAndTactics 0) egThm1

def getTactics (s : TSyntax ``tacticSeq) : Array Syntax :=
  match s with
  | `(tacticSeq| { $[$t:tactic $[;]?]* }) => t
  | `(tacticSeq| $[$t:tactic $[;]?]*) => t
  | _ => #[]

structure TheoremAndTactic where
  kind: String
  name: String
  args: String 
  type: String
  firstTactic : String
deriving Repr

def parseTheoremAndTactic! (input : Syntax) : 
      MetaM TheoremAndTactic := do
    match input with
    | `(theoremAndTactic|$kind:defHead $name $args : $type := by $tac:tactic) =>
        let tac ← contractInductionStx (tac)
        return ⟨kind.raw.reprint.getD "", name.raw.reprint.getD "", args.raw.reprint.getD "", type.raw.reprint.getD "", tac.reprint.getD ""⟩ 
    | _ =>
      IO.println s!"could not parse theorem ${input.reprint}"
      throwUnsupportedSyntax

partial def getTheoremsTacticsAux (text: String) (vars : Array String)
                        (accum : Array TheoremAndTactic) : MetaM (Array TheoremAndTactic) := do
  if text.isEmpty then 
      return accum
  else
      match (← partialParser (categoryParser `theoremAndTactics 0) text) with
      | none => getTheoremsTacticsAux (text.drop 1) vars accum
      | some (stx, head, tail) => 
          -- IO.println head
          IO.println s!"parsing"
          -- IO.println tail
          try 
            let entry ← parseTheoremAndTactic! stx
            IO.println s!"entry: {entry.firstTactic}"
          catch err => IO.println s!"error: {← err.toMessageData.format}"
          getTheoremsTacticsAux tail vars (accum)

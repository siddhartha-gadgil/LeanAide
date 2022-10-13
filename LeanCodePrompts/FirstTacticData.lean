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
    -- IO.println s!"errors: {s.errorMsg}"
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
  defHead ident (argument)* ":" term ":=" "by" tacticSeq : theoremAndTactic

def ml := "theorem blah : Nat := by 
simp
decide
skip"

-- for testing
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

#eval runParserCategoryPartial `theoremAndTactic ml

def egThm1 := "theorem egIsAction: ∀ (x y: Fin 2), 
  (egAction' x) ∘ (egAction' y) = egAction' (x + y) := by 
    decide
    skip"

def tacEg := 
"apply f
skip
decide"

def mlParse : MetaM <| Except String String := do
  return runParserCategory (← getEnv) `tactic tacEg |>.map 
    fun s => s.reprint.get!

#eval mlParse

#eval partialParser (categoryParser `tactic 0) tacEg

#eval partialParser tacticSeq tacEg

#eval partialParser (categoryParser `theoremAndTactic 0) egThm1

def egThm2 := "theorem unique_morphism_nat (f g : ℤ → A)[AddCommGroup.Homomorphism f]
        [AddCommGroup.Homomorphism g]: 
          f 1 = g 1  → ∀ n: ℕ, f (n + 1) = g (n + 1) := by
          intro hyp
          decide
          intro n
          induction n with
          | zero =>
            simp [hyp]            
          | succ k ih => 
            simp [hyp] at *
            assumption"

#eval partialParser (categoryParser `theoremAndTactic 0) egThm2

#eval partialParser (categoryParser `theoremAndTactic 0) ml

def getTactics (s : Syntax) : Array Syntax :=
  match s with
  | `(tacticSeq| { $[$t:tactic $[;]?]* }) => t
  | `(tacticSeq| $[$t:tactic $[;]?]*) => t
  | _ => #[]

def parseTactics (s: String) : MetaM <| Array Syntax := do
  match ← partialParser tacticSeq s with
  | some (stx, _, _) => 
    let seq := getTactics stx
    IO.println seq[0]!.reprint.get!
    return seq
  | none => return #[]

#eval parseTactics tacEg

structure TheoremAndTactic where
  kind: String
  name: String
  args: String 
  type: String
  firstTactic : String
deriving Repr

def getTheoremAndTactic! (input : Syntax) : 
      MetaM TheoremAndTactic := do
    match input with
    | `(theoremAndTactic|$kind:defHead $name:ident $args:argument* : $type := by $tac:tacticSeq) =>
        let seq := getTactics tac
        let tac ← contractInductionStx (seq[0]!)
        let argString := 
          (args.map fun a => a.raw.reprint.get!).foldl (fun a b => a ++ " " ++ b) ""
        let argString := argString.replace "\n" " " |>.trim
        return ⟨kind.raw.reprint.get!.trim, name.raw.reprint.get!.trim,
        argString, type.raw.reprint.get!.trim, tac.reprint.get!.trim⟩ 
    | _ =>
      IO.println s!"could not parse theorem ${input.reprint}"
      throwUnsupportedSyntax

def parseTheoremAndTactic! (input: String) : MetaM TheoremAndTactic := do
  match ← partialParser (categoryParser `theoremAndTactic 0) input with
  | some (stx, _, _) => 
      getTheoremAndTactic! stx
  | none => 
    IO.println s!"could not parse theorem ${input}"
    throwUnsupportedSyntax

#eval parseTheoremAndTactic! egThm2

partial def getTheoremsTacticsAux (text: String) (vars : Array String)
                        (accum : Array TheoremAndTactic) : MetaM (Array TheoremAndTactic) := do
  if text.isEmpty then 
      return accum
  else
      match (← partialParser (categoryParser `theoremAndTactic 0) text) with
      | none => getTheoremsTacticsAux (text.drop 1) vars accum
      | some (stx, _, tail) => 
          -- IO.println head
          -- IO.println s!"parsing"
          -- IO.println tail
          -- try 
          let entry ← getTheoremAndTactic! stx
            -- IO.println s!"entry: {entry.firstTactic}"
          -- catch err => IO.println s!"error: {← err.toMessageData.format}"
          getTheoremsTacticsAux tail vars (accum.push entry)

def n : Nat := Nat.add 
          3 4
        
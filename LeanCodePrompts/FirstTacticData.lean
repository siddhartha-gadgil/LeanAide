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
syntax "example" : defHead

declare_syntax_cat theoremAndTactic

syntax 
  defHead ident (argument)* ":" term ":=" "by" tacticSeq : theoremAndTactic
syntax 
  "example" (argument)* ":" term ":=" "by" tacticSeq : theoremAndTactic



declare_syntax_cat variableStatement
syntax "variable" (argument)* : variableStatement

declare_syntax_cat sectionHead
syntax "section" (colGt ident)? : sectionHead

declare_syntax_cat sectionEnd
syntax "end" (ident)? : sectionEnd

-- code from Leo de Moura
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


structure TheoremAndTactic where
  kind: String
  name: String
  args: String 
  type: String
  firstTactic : String
deriving Repr

namespace TheoremAndTactic 

def corePrompt (x: TheoremAndTactic) : String := 
  s!"{x.name} : {x.type}"

def tacticPrompt (x: TheoremAndTactic) : String := 
  s!"{x.kind} {x.corePrompt} := by {x.firstTactic}; sorry"

def toJson (x: TheoremAndTactic) : Json := 
  Json.mkObj [
    ("kind", x.kind),
    ("name", x.name),
    ("args", x.args),
    ("type", x.type),
    ("first-tactic", x.firstTactic),
    ("core-promt", x.corePrompt),
    ("tactic-prompt", x.tacticPrompt)
  ]

end TheoremAndTactic

def getTheoremAndTactic! (input : Syntax)(vars : String) : 
      MetaM TheoremAndTactic := do
    match input with
    | `(theoremAndTactic|$kind:defHead $name:ident $args:argument* : $type := by $tac:tacticSeq) =>
        let seq := getTactics tac
        let tac ← contractInductionStx (seq[0]!)
        let argString := 
          (args.map fun a => a.raw.reprint.get!).foldl (fun a b => a ++ " " ++ b) (vars)
        let argString := argString.replace "\n" " " |>.trim
        return ⟨kind.raw.reprint.get!.trim, name.raw.reprint.get!.trim,
        argString, type.raw.reprint.get!.trim, tac.reprint.get!.trim⟩
    | `(theoremAndTactic|example  $args:argument* : $type := by $tac:tacticSeq) =>
        let seq := getTactics tac
        let tac ← contractInductionStx (seq[0]!)
        let argString := 
          (args.map fun a => a.raw.reprint.get!).foldl (fun a b => a ++ " " ++ b) (vars)
        let argString := argString.replace "\n" " " |>.trim
        return ⟨"example","",
        argString, type.raw.reprint.get!.trim, tac.reprint.get!.trim⟩ 
    | _ =>
      IO.println s!"could not parse theorem ${input.reprint}"
      throwUnsupportedSyntax

def parseTheoremAndTactic! (input: String) : MetaM TheoremAndTactic := do
  match ← partialParser (categoryParser `theoremAndTactic 0) input with
  | some (stx, _, _) => 
      getTheoremAndTactic! stx ""
  | none => 
    IO.println s!"could not parse theorem ${input}"
    throwUnsupportedSyntax

def getVariables! (input : Syntax) : 
      MetaM String := do
    match input with
    | `(variableStatement|variable $args:argument*) =>
        let argString := 
          (args.map fun a => a.raw.reprint.get!).foldl (fun a b => a ++ " " ++ b) ""
        return argString.replace "\n" " " |>.trim 
    | _ =>
      IO.println s!"could not parse theorem ${input.reprint}"
      throwUnsupportedSyntax


partial def getTheoremsTacticsAux (text: String) (vars : Array String)
                        (sections : Array String)
                        (accum : Array TheoremAndTactic) : MetaM (Array TheoremAndTactic) := do
  if text.isEmpty then 
      return accum
  else
      match (← partialParser (categoryParser `theoremAndTactic 0) text) with
      | some (stx, _, tail) => 
          let entry ← getTheoremAndTactic! stx (vars.foldl (fun a b => a ++ " " ++ b) "")
          getTheoremsTacticsAux tail vars sections (accum.push entry)
      | none => 
        match 
          (← partialParser (categoryParser `variableStatement 0) text) with
        | some (stx, _, tail) =>
          let newVars ← getVariables! stx
          let innerVars := vars.back
          getTheoremsTacticsAux tail (vars.pop.push (innerVars ++ " " ++ newVars)) sections accum
        | none =>
          match 
            (← partialParser (categoryParser `sectionHead 0) text) with
          | some (stx, _, tail) =>
            match stx with
            | `(sectionHead|section $name) =>
            getTheoremsTacticsAux tail (vars.push "") 
              (sections.push name.raw.reprint.get!.trim) accum
            | _ => 
              getTheoremsTacticsAux tail vars (sections.push "") accum
          | none =>
            match 
              (← partialParser (categoryParser `sectionEnd 0) text) with
            | some (stx, _, tail) =>
              match stx with
              | `(sectionEnd|end $name) =>
                if sections.back? == name.raw.reprint.get!.trim then
                  getTheoremsTacticsAux tail (vars.pop) (sections.pop) accum
                else
                  getTheoremsTacticsAux tail vars sections accum
              | _ => 
                getTheoremsTacticsAux tail (vars.pop) sections accum
            | none =>             
              getTheoremsTacticsAux (text.drop 1) vars sections accum

def getTheoremsTactics (text: String) : MetaM (Array TheoremAndTactic) := do
  getTheoremsTacticsAux text #[""] #[] #[]

def leanFiles (paths: List String) : IO (Array System.FilePath) := do 
  Lean.SearchPath.findAllWithExt [System.mkFilePath paths] "lean"
 
def polyLeanFiles := leanFiles (["/home/gadgil/code/polylean/Polylean"])

def getTheoremsTacticsFromFiles (files: Array System.FilePath) : MetaM (Array TheoremAndTactic) := do
  let mut accum := #[]
  for file in files do
    let text ← IO.FS.readFile file
    let theorems ← getTheoremsTactics text
    accum := accum ++ theorems
  return accum

def getTheoremsTacticsFromPolyLean : MetaM (Array TheoremAndTactic) := do
  let files ← polyLeanFiles
  logInfo m!"found {files.size} files"
  let files := files.toList.take 12 |>.toArray
  getTheoremsTacticsFromFiles files

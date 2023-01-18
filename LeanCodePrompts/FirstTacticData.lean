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

def contractPolyTactic (tac: String): String := 
  if tac.contains ',' then
    let head := tac.splitOn "," |>.head!
    if head.contains '[' 
      then head ++ "]"
      else tac
  else tac


def partialParser  (parser : Parser) (input : String) (fileName := "<input>") : MetaM <| Option (Syntax × String × String) := do
  let env ← getEnv
  -- let c := mkParserContext (mkInputContext input fileName) { env := env, options := {} }
  let p := andthenFn whitespace parser.fn
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  let stack := s.stxStack.toSubarray.as.filter fun s => !s.hasMissing
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
  defHead (ident)? (argument)* ":" term ":=" "by" tacticSeq : theoremAndTactic



declare_syntax_cat variableStatement
syntax "variable" (argument)* : variableStatement

declare_syntax_cat sectionHead
syntax "section" (colGt ident)? : sectionHead

declare_syntax_cat sectionEnd
syntax "end" (ident)? : sectionEnd

-- code from Leo de Moura
def getTactics (s : TSyntax ``tacticSeq) : Array (TSyntax `tactic) :=
  match s with
  | `(tacticSeq| { $[$t]* }) => t
  | `(tacticSeq| $[$t]*) => t
  | _ => #[]


def parseTactics (s: String) : MetaM <| Array Syntax := do
  match ← partialParser tacticSeq s with
  | some (stx, _, _) => 
    let seq := getTactics stx
    IO.println seq[0]!.raw.reprint.get!
    return seq
  | none => return #[]

def parseTactics? (s: String) : MetaM <| Option <| Array Syntax := do
  let parsed? ← partialParser tacticSeq s
  let seq := parsed?.map fun (stx, _, _) => getTactics stx
  return seq

def parseTacticBlocks(s: String) : MetaM <| List <| Array String := do
  let blocks := s.splitOn "by" |>.tailD []
  let stxs ←  blocks.filterMapM fun b => parseTactics? b
  return stxs.map (fun arr => 
    arr.map (fun stx => stx.reprint.getD "" |>.trim))

structure TheoremAndTactic where
  kind: String
  name: String
  args: String 
  type: String
  firstTactic : String
deriving Repr

namespace TheoremAndTactic 

def corePrompt (x: TheoremAndTactic) : String := 
  s!"{x.args} : {x.type}"

def tacticPrompt (x: TheoremAndTactic) : String := 
  s!"{x.kind} {x.corePrompt} := by {x.firstTactic}; sorry"
 
def toJson (x: TheoremAndTactic) : Json := 
  Json.mkObj [
    ("kind", x.kind),
    ("name", x.name),
    ("args", x.args),
    ("type", x.type),
    ("first-tactic", x.firstTactic),
    ("core-prompt", x.corePrompt),
    ("tactic-prompt", x.tacticPrompt)
  ]

end TheoremAndTactic

def getTheoremAndTactic? (input : Syntax)(vars : String) : 
      MetaM <| Option TheoremAndTactic := do
    match input with
    | `(theoremAndTactic|$kind:defHead $name:ident $args:argument* : $type := by $tac:tacticSeq) =>
        let seq := getTactics tac
        let tac ← contractInductionStx (seq[0]!)
        let tac := tac.reprint.get!.splitOn "--" |>.head! |>.trim
        let tac := tac.splitOn "<;>" |>.head! |>.trim
        let tac := contractPolyTactic tac
        let argString := 
          (args.map fun a => a.raw.reprint.get!).foldl (fun a b => a ++ " " ++ b) (vars)
        let argString := argString.replace "\n" " " |>.trim
        return some ⟨kind.raw.reprint.get!.trim, name.raw.reprint.get!.trim,
        argString, type.raw.reprint.get!.trim, tac⟩
    | `(theoremAndTactic|$kind:defHead  $args:argument* : $type := by $tac:tacticSeq) =>
        let seq := getTactics tac
        let tac ← contractInductionStx (seq[0]!)
        let tac := tac.reprint.get!.splitOn "--" |>.head! |>.trim
        let tac := tac.splitOn "<;>" |>.head! |>.trim
        let tac := contractPolyTactic tac
        let argString := 
          (args.map fun a => a.raw.reprint.get!).foldl (fun a b => a ++ " " ++ b) (vars)
        let argString := argString.replace "\n" " " |>.trim
        return some ⟨kind.raw.reprint.get!.trim,"",
        argString, type.raw.reprint.get!.trim, 
        tac⟩ 
    | _ =>
      IO.println s!"could not parse theorem {input.reprint.get!} to get tactic"
      return none

def parseTheoremAndTactic? (input: String) : MetaM <| Option TheoremAndTactic := do
  match ← partialParser (categoryParser `theoremAndTactic 0) input with
  | some (stx, _, _) => 
      getTheoremAndTactic? stx ""
  | none => 
    IO.println s!"could not parse theorem {input}"
    throwUnsupportedSyntax

def getVariables! (input : Syntax) : 
      MetaM String := do
    match input with
    | `(variableStatement|variable $args:argument*) =>
        let argString := 
          (args.map fun a => a.raw.reprint.get!).foldl (fun a b => a ++ " " ++ b) ""
        return argString.replace "\n" " " |>.trim 
    | _ =>
      IO.println s!"could not parse theorem {input.reprint.get!}"
      throwUnsupportedSyntax


partial def getTheoremsTacticsAux (text: String) (vars : Array String)
                        (sections : Array String)
                        (accum : Array TheoremAndTactic) : MetaM (Array TheoremAndTactic) := do
  if text.isEmpty then 
      return accum
  else
      match (← partialParser (categoryParser `theoremAndTactic 0) text) with
      | some (stx, _, tail) => 
          let entry? ← getTheoremAndTactic? stx (vars.foldl (fun a b => a ++ " " ++ b) "")
          let accum := match entry? with
            | some entry => accum.push entry
            | none => accum 
          getTheoremsTacticsAux tail vars sections (accum)
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
            -- IO.println s!"\nsection head found {stx.reprint.get!} followed by {tail.take 30}"
            match stx with
            | `(sectionHead|section $name) =>
            getTheoremsTacticsAux tail (vars.push "") 
              (sections.push name.raw.reprint.get!.trim) accum
            | `(sectionHead|section) => 
              getTheoremsTacticsAux tail (vars.push "") (sections.push "") accum
            | _ => 
              getTheoremsTacticsAux tail vars sections accum
          | none =>
            match 
              (← partialParser (categoryParser `sectionEnd 0) text) with
            | some (stx, _, tail) =>
              -- IO.println s!"\nend found {stx.reprint.get!} with sections {sections} and vars {vars} followed by {tail.take 30}"
              match stx with
              | `(sectionEnd|end $name) =>
                if sections.back? == some name.raw.reprint.get!.trim then
                  getTheoremsTacticsAux tail (vars.pop) (sections.pop) accum
                else
                  getTheoremsTacticsAux tail vars sections accum
              | `(sectionEnd|end) =>
                getTheoremsTacticsAux tail (vars.pop) sections accum
              | _ => 
                getTheoremsTacticsAux tail (vars) sections accum
            | none =>        
              match ← partialParser Command.docComment text with
              | some (_, _, tail) =>
                getTheoremsTacticsAux tail vars sections accum
              | none =>      
                match ← partialParser Command.moduleDoc text with
              | some (_, _, tail) =>
                getTheoremsTacticsAux tail vars sections accum
              | none =>
                let head := text.get 0
                if ('a' ≤ head && head ≤ 'z') || 
                  ('A' ≤ head && head ≤ 'Z') then
                  let tail := text.dropWhile fun c => 
                    ('a' ≤ c && c ≤ 'z') || 
                  ('A' ≤ c && c ≤ 'Z')
                  getTheoremsTacticsAux tail vars sections accum
                else
                  getTheoremsTacticsAux (text.drop 1) vars sections accum

def getTheoremsTactics (text: String) : MetaM (Array TheoremAndTactic) := do
  getTheoremsTacticsAux text #[""] #[] #[]

def leanFiles (paths: List String) : IO (Array System.FilePath) := do 
  Lean.SearchPath.findAllWithExt [System.mkFilePath paths] "lean"
 
def polyLeanFiles := leanFiles (["/home/gadgil/code/polylean/Polylean"])

def getTheoremsTacticsFromFiles (files: Array System.FilePath) : MetaM (Array TheoremAndTactic) := do
  let mut accum := #[]
  IO.println s!"parsing {files.size} lean files"
  let mut parsedCount := 0
  for file in files do
    IO.println s!"parsing {file}"
    let text ← IO.FS.readFile file
    let theorems ← getTheoremsTactics text
    IO.println s!"parsed {theorems.size} theorems with tactics"
    parsedCount := parsedCount + 1
    IO.println s!"parsed {parsedCount} files out of {files.size}"
    accum := accum ++ theorems
  return accum

def readAndSaveTheoremTacticsM (inps: List String ) : MetaM String := do
  let mut files := #[]
  for inp in inps do
    let fs ←  leanFiles [inp]
    files := files ++ fs
  IO.println s!"found {files.size} files"
  let all ← getTheoremsTacticsFromFiles files
  let js := Json.arr <| all.map fun a => a.toJson
  return js.pretty

def readAndSaveTheoremTacticsCore 
  (inps: List String ) : CoreM String :=
  readAndSaveTheoremTacticsM inps |>.run'

-- example
def getTheoremsTacticsFromPolyLean : MetaM (Array TheoremAndTactic) := do
  let files ← polyLeanFiles
  logInfo m!"found {files.size} files"
  let files := files.toList.take 12 |>.toArray
  getTheoremsTacticsFromFiles files

#eval "rw [Subsingleton.elim hd] -- align the Decidable instances implicitly used by `dite`" |>.splitOn "--" |>.head!

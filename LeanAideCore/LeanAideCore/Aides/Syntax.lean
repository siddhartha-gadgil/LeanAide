import Lean

open Lean Meta Elab Term Parser Tactic

def Lean.Expr.view (expr: Expr) : MetaM String := do
  let expr ← instantiateMVars expr
  let fmt ← PrettyPrinter.ppExpr expr
  return fmt.pretty

partial def showSyntax : Syntax → String
| Syntax.node _ _ args =>
  (args.map <| fun s => showSyntax s).foldl (fun acc s => acc ++ " " ++ s) ""
| Lean.Syntax.atom _ val => val
| Lean.Syntax.ident _ _ val _ => val.toString
| _ => ""

syntax (name := showTerm)  "show%" term : term

open Term in
@[term_elab showTerm] def showTermImpl : TermElab :=
   fun stx expectedType =>
   match stx with
  | `(show% $t) => do
    let e ← Term.elabTerm t expectedType
    let v ← mkAppM ``repr #[e]
    let v ← Term.withoutPostponing do
      mkAppM ``toString #[v]
    Term.synthesizeSyntheticMVarsNoPostponing
    let s ← unsafe evalExpr String (mkConst ``String) v
    TryThis.addSuggestion stx s
    return e
  | _ => throwUnsupportedSyntax

-- code from Leo de Moura
def getTactics (s : TSyntax ``tacticSeq) : Array (TSyntax `tactic) :=
  match s with
  | `(tacticSeq| { $[$t]* }) => t
  | `(tacticSeq| $[$t]*) => t
  | _ => #[]

def mkTacticSeq (ts : Array (TSyntax `tactic)) :
  MetaM (TSyntax ``tacticSeq) := do
  `(tacticSeq| $[$ts]*)

def appendTacticSeqSeq (s t : TSyntax ``tacticSeq) :
  MetaM (TSyntax ``tacticSeq) := do
  let ts := getTactics t
  match s with
  | `(tacticSeq| { $[$t]* }) =>
      let ts' := t ++ ts
      `(tacticSeq| { $[$ts']* })
  | `(tacticSeq| $[$t]*) =>
      let ts' := t ++ ts
      `(tacticSeq| $[$ts']*)
  | _ => pure t

def appendTacticArrSeq (ts : Array (TSyntax `tactic))
    (s : TSyntax ``tacticSeq) :
  MetaM (TSyntax ``tacticSeq) := do
  match s with
  | `(tacticSeq| { $[$t]* }) =>
      let ts' := ts ++ t
      `(tacticSeq| { $[$ts']* })
  | `(tacticSeq| $[$t]*) =>
      let ts' := ts ++ t
      `(tacticSeq| $[$ts']*)
  | _ => `(tacticSeq| $[$ts]*)

def consTacticSeq (h: TSyntax `tactic)(s : TSyntax ``tacticSeq):
  MetaM (TSyntax ``tacticSeq) := do
  match s with
  | `(tacticSeq| { $[$t]* }) =>
      let ts' := #[h] ++ t
      `(tacticSeq| { $[$ts']* })
  | `(tacticSeq| $[$t]*) =>
      let ts' := #[h] ++ t
      `(tacticSeq| $[$ts']*)
  | _ => pure s

def endsWithDone (t: TSyntax ``tacticSeq) : MetaM Bool := do
  match getTactics t |>.back? with
  | some t =>
    let fmt ← PrettyPrinter.ppTactic t
    pure <| fmt.pretty.trim.endsWith "done"
  | _ => pure false

declare_syntax_cat tacticSeqCategory
syntax tacticSeq : tacticSeqCategory

def getTacticsFromText? (tacticText: String) : MetaM (Option (TSyntax ``tacticSeq)) := do
  unless (tacticText.splitOn "sorry").length = 1 do
    return none
  let stx? := runParserCategory (← getEnv) `tacticSeqCategory tacticText
  match stx? with
  | Except.ok stx =>
    match stx with
    | `(tacticSeqCategory| $ts:tacticSeq) =>
      return some ts
    | _ =>
      throwError m!"Unexpected syntax format for tactics: {stx}"
      return none
  | Except.error e =>
    throwError m!"Failed to parse tactics; {e}:\n{tacticText}"
    return none



syntax commandSeq := sepBy1IndentSemicolon(command)

def getCommands : TSyntax `commandSeq → Array (TSyntax `command)
  | `(commandSeq| $cs*) => cs
  | _ => #[]

def mkCommandSeq : Array (TSyntax `command) → CoreM (TSyntax `commandSeq)
  | cs => `(commandSeq| $cs*)

def flattenCommandSeq (cs: Array <| TSyntax `commandSeq) :
  CoreM (TSyntax `commandSeq) :=
  mkCommandSeq (cs.map getCommands |>.flatten)

def flattenTacticSeq (tacs: Array <| TSyntax ``tacticSeq) :
  CoreM (TSyntax ``tacticSeq) := do
  let tacs := tacs.map getTactics |>.flatten
  `(tacticSeq| $tacs*)

partial def Lean.Expr.hasUnassignedExprMVar (e: Expr) : MetaM Bool := do
  let deps ← getMVars e
  for m in deps do
    match (← getExprMVarAssignment? m) with
    | some e  =>
      if ←  e.hasUnassignedExprMVar then
        return true
    | none => return true
  return false

-- def checkNoLoop : MetaM Bool := do
--   let mvar ← mkFreshExprMVar (mkConst ``Nat)
--   mvar.hasUnassignedExprMVar

-- #eval checkNoLoop

def getCommandName (stx: TSyntax `command) : Option Name :=
  match stx with
      | `(command| theorem $id:ident $_:declSig $_:declVal) => some id.getId
      | `(command| def $id:ident $_* : $_ := $_) => some id.getId
      | `(command| noncomputable def $id:ident $_* : $_ := $_) => some id.getId
      | _ => none

declare_syntax_cat commandSeqWrap

syntax commandSeq : commandSeqWrap

def getNamesFromCode (s: String) : MetaM (Array Name) := do
  let env ← getEnv
  let res := Parser.runParserCategory env `commandSeqWrap s
  match res with
  | .ok stx =>
    let stx'' := match stx with
      | `(commandSeqWrap| $cs:commandSeq) => cs
      | _ => panic! "Expected commandSeqWrap syntax"
    let stx' : TSyntax `commandSeq := ⟨ stx'' ⟩
    let cmds := getCommands stx'
    logInfo m!"Parsed commandSeq: {stx}"
    logInfo m!"Commands: {cmds}"
    return cmds.filterMap getCommandName
  | .error err =>
    logError m!"Error parsing commandSeq: {err}"
    return #[]

def parseCommandSeq (s: String) : CoreM (TSyntax ``commandSeq) := do
  let env ← getEnv
  let res := Parser.runParserCategory env `commandSeqWrap s
  match res with
  | .ok stx =>
    match stx with
      | `(commandSeqWrap| $cs:commandSeq) => return cs
      | _ => throwError "Expected commandSeqWrap syntax"
  | .error err =>
    throwError m!"Error parsing commandSeq: {err}"

def showCommandSeq (cs: TSyntax `commandSeq) : CoreM String := do
  let cmds := getCommands cs
  let fmtCmds ← cmds.mapM fun c => PrettyPrinter.ppCommand c
  return fmtCmds.foldl (fun acc f => acc ++ f.pretty ++ "\n\n") ""

declare_syntax_cat tacticSeqWrap
syntax tacticSeq : tacticSeqWrap

def parseTacticSeq (s: String) : CoreM <| TSyntax ``tacticSeq := do
  let env ← getEnv
  let res := Parser.runParserCategory env `tacticSeqWrap s
  match res with
  | .ok stx =>
    match stx with
      | `(tacticSeqWrap| $ts:tacticSeq) => return ts
      | _ => throwError "Expected tacticSeqWrap syntax"
  | .error err =>
    logError m!"Error parsing tacticSeq: {err}"
    throwError s!"Failed to parse tacticSeq : {err}"

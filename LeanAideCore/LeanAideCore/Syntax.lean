import Lake.Toml.ParserUtil
import Lean

open Lean Meta Elab Term PrettyPrinter Tactic Command Parser

namespace LeanAide.Meta

syntax (name := thmCommand) "#theorem" (ident)? (":")? str : command
syntax (name := defCommand) "#def"  str : command
open Lake.Toml
def proofFn : ParserFn := takeWhile1Fn fun c => c != '∎'

def proofBodyInit : Parser :=
  { fn := rawFn proofFn}

def proofBody : Parser := andthen proofBodyInit "∎"

@[combinator_parenthesizer proofBodyInit] def proofBodyInit.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter proofBodyInit] def proofBodyInit.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

/-!
# Proof Syntax
-/
syntax (name := proofCmd) withPosition("#proof" ppLine (colGt (str <|> proofBody) )) : command

def mkProofStx (s: String) : Syntax :=
  mkNode ``proofCmd #[mkAtom "#proof", mkAtom s, mkAtom "∎"]

@[command_elab proofCmd] def elabProofCmd : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #proof $t:proofBodyInit ∎) =>
    let s := stx.getArgs[1]!.reprint.get!.trim
    logInfo m!"Syntax: {stx}"
    let stx' := mkProofStx "Some proof."
    logInfo m!"Extract: {s}"
    logInfo m!"Details: {repr stx}"
    logInfo m!"{stx'}"
  | _ => throwUnsupportedSyntax


syntax (name := textCmd) withPosition("#text" ppLine (colGt (str <|> proofBody) )) : command

syntax (name:= whyTac) "why" : tactic

syntax (name:= textProof) withPosition("#proof" ppLine (str <|> proofBody)) : tactic


syntax (name:= addDocs) "#doc" command : command

syntax (name := askCommand) "#ask" (num)? str : command





def mkTextStx (s: String) : Syntax :=
  mkNode ``textCmd #[mkAtom "#text", mkAtom s, mkAtom "∎"]

@[command_elab textCmd] def elabTextCmd : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #text $t:proofBodyInit ∎) =>
    -- let s := stx.getArgs[1]!.reprint.get!.trim
    return
  | _ => throwUnsupportedSyntax

/-!
# From Descriptions
-/


open Tactic
@[tactic textProof] def textProofImpl : Tactic :=
  fun _ => withMainContext do
  evalTactic (← `(tactic|sorry))

-- example : True := by
--   #proof "trivial"

open Lean.Parser.Command

@[command_parser]
def proofComment := leading_parser
  ppDedent <| "/proof" >> ppSpace >> commentBody >> ppLine

def getProofStringText [Monad m] [MonadError m] (stx : TSyntax ``proofComment) : m String :=
  match stx.raw[1] with
  | Lean.Syntax.atom _ val => return val.extract 0 (val.endPos - ⟨2⟩)
  | _                 => throwErrorAt stx "unexpected doc string{indentD stx.raw[1]}"

@[command_elab proofComment] def elabProofComment : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command|$doc:proofComment) =>
    let view ← getProofStringText doc
    logInfo m!"Proof comment: {view}"
  | _ => throwUnsupportedSyntax

-- /proof Hello there -/

end LeanAide.Meta

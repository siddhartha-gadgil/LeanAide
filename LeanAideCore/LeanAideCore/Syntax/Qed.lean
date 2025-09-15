import Lake.Toml.ParserUtil
import Lean


open Lean Meta Elab Term PrettyPrinter Tactic Command Parser

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


syntax (name := quoteCmd) withPosition("#quote" ppLine (colGt (str <|> proofBody) )) : command

syntax (name:= whyTac) "why" : tactic

syntax (name:= textProof) withPosition("#proof" ppLine (str <|> proofBody)) : tactic




def mkQuoteStx (s: String) : Syntax.Command :=
  ⟨mkNode ``quoteCmd #[mkAtom "#quote", mkAtom s, mkAtom "∎"]⟩

@[command_elab quoteCmd] def elabQuoteCmd : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #quote $t:proofBodyInit ∎) =>
    -- let s := stx.getArgs[1]!.reprint.get!.trim
    return
  | _ => throwUnsupportedSyntax

open Tactic
@[tactic textProof] def textProofImpl : Tactic :=
  fun _ => withMainContext do
  evalTactic (← `(tactic|sorry))

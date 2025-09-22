import Lean
import LeanAideCore.Kernel
import LeanAideCore.Discussion
import LeanAideCore.KernelGenerators
import LeanAideCore.Syntax.Basic

open Lean Meta Elab Term PrettyPrinter Tactic Command Parser

namespace LeanAide
open Meta

def pruneName (n : Name) : Name :=
  let cs := n.componentsRev
  let cs := cs.tail.reverse
  cs.foldl (fun acc c => if c == Name.anonymous then acc else acc.append c) Name.anonymous

macro "#start_chat" n:ident : command =>
  `(command| def $n := Discussion.start none)

macro "#start_chat" n:ident s:term : command =>
  `(command| def $n := Discussion.start $s)

#start_chat chat1

#start_chat chat2 "Prove that 2 + 2 = 4."

macro doc:docComment "#query" ppSpace n:ident : command =>
  let text := doc.raw.reprint.get!
  let text := text.drop 4 |>.dropRight 4
  let textStx := Syntax.mkStrLit text
  `(command| def $n : Query := { message := $textStx} )

def mkQueryCmd (s: String) (name: Name)  : CoreM Syntax.Command :=
  let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom ("\n" ++ s ++ "\n" ++ " -/")]
  let nameStx := mkIdent name
  `(command | $docs:docComment #query $nameStx)

macro doc:docComment "#response" ppSpace name:ident : command =>
  let text := doc.raw.reprint.get!
  let text := text.drop 4 |>.dropRight 4
  let textStx := Syntax.mkStrLit text
  let name := name.getId
  let nameStx := mkIdent name
  `(command| def $nameStx : Response := { message := $textStx} )

def mkResponseCmd (s: String) (name: Name)  : CoreM Syntax.Command :=
  let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom ("\n" ++ s ++ "\n" ++ " -/")]
  let nameStx := mkIdent name
  `(command | $docs:docComment #response $nameStx)

macro doc:docComment "#proof_document" ppSpace n:ident : command =>
  let text := doc.raw.reprint.get!
  let text := text.drop 4 |>.dropRight 4
  let textStx := Syntax.mkStrLit text
  let name := n.getId
  let nameStx := mkIdent name
  let docName := pruneName name
  `(command| def $nameStx : ProofDocument := { name := $(quote docName), content := $(textStx) } )

instance documentCommand : DefinitionCommand ProofDocument where
  cmd d  := do
    let name := d.name ++ "proof_doc".toName
    let nameStx := Lean.mkIdent (d.name ++ "proof_doc".toName)
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom ( d.content ++ " -/")]

    return (← `(command| $docs:docComment #proof_document $nameStx), name)


instance structuredDocumentCommand : DefinitionCommand StructuredProof where
  cmd s := do
    let name := s.name ++ "struct_proof".toName
    let nameStx := Lean.mkIdent name
    let jsStx ← getJsonSyntax s.json
    let typeId := Lean.mkIdent ``StructuredProof
    return (← `(command| def $nameStx : $typeId := ⟨ $(quote s.name),  json% $jsStx ⟩), name)

-- #consider ({name := `hello, json := json% {a : {b : 1}} }: StructuredProof)

macro doc:docComment "#conjecture" ppSpace n:ident ppSpace ":" ppSpace t:term : command => do
  let name := n.getId
  let nameStx := mkIdent name
  `(command| $doc:docComment def $nameStx : Prop := $t )

/--
Just a test
-/
#conjecture easy : 2 + 2 = 4

-- #check easy

#check ppTerm

elab doc:docComment "#theorem_code" ppSpace n:ident ppSpace ":" ppSpace t:term : command => do
  let name := n.getId
  let nameStx := mkIdent name
  let termName := pruneName name
  let termNameStx := Syntax.mkStrLit (toString termName)
  let text ← getDocStringText doc
  let textStx := Syntax.mkStrLit text
  let typeFmt ← Command.liftTermElabM do
    ppTerm t
  let typeStx := Syntax.mkStrLit typeFmt.pretty
  let propName := termName ++ "prop".toName
  let propId := mkIdent propName
  let statement ← Command.liftTermElabM do
    let cmd ← `(command| def $propId : Prop := $t )
    ppCommand cmd
  let statementStx := Syntax.mkStrLit statement.pretty
  let stx ←  `(command| $doc:docComment def $nameStx : TheoremCode := {name := $termNameStx |>.toName, text := $textStx, type := $typeStx, statement := $statementStx} )
  elabCommand stx

/--
Just a test
-/
#theorem_code easy₁.theorem_code : 2 + 2 = 4

#eval easy₁.theorem_code

#eval unproxy easy₁.theorem_code

instance : DefinitionCommand Conjecture where
  cmd c := do
    let name := c.name ++ "conj".toName
    let nameStx := Lean.mkIdent name
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom ( c.text ++ " -/")]
    let typeStx ← delab c.type
    return (← `(command| $docs:docComment #conjecture $nameStx : $typeStx), name)

instance : DefinitionCommand TheoremCode where
  cmd c := do
    let name := c.name ++ "theorem_code".toName
    let nameStx := Lean.mkIdent name
    let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom ( c.text ++ " -/")]
    let .ok typeStx := runParserCategory (← getEnv) `term c.type | throwError "Failed to parse type"
    let typeStx : Syntax.Term := ⟨typeStx⟩
    return (← `(command| $docs:docComment #theorem_code $nameStx : $typeStx), name)

instance : DefinitionCommand DefinitionCodeM where
  cmd d := return (d.statement, d.name)

instance : DefinitionCommand TheoremText where
  cmd t := do
    let name := t.name? |>.getD ("theorem_" ++ toString (hash t.text)).toName
    return (← mkQuoteCmd t.text name, name)

instance : TermCommands ProofCode where
  commandArray pc := return commands pc.code

instance [inst: TermCommands α] : TermCommands (Discussion α) where
  commandArray dc := do
    let dc := dc.last
    inst.commandArray dc

instance : DefinitionCommand Query where
  cmd q := do
    let name := s!"query_{hash q.message}".toName
    return (← mkQueryCmd q.message name, name)

instance : DefinitionCommand Response where
  cmd r := do
    let name := s!"response_{hash r.message}".toName
    return (← mkResponseCmd r.message name, name)

instance : DefinitionCommand DefinitionCodeM where
  cmd d := return (d.statement, d.name)

instance : DefinitionCommand DefinitionText where
  cmd t := do
    let name := ("definition_" ++ toString (hash t.text)).toName
    return (← mkQuoteCmd t.text name, name)

instance : DefinitionCommand Comment where
  cmd c := do
    let name := ("comment_" ++ toString (hash c.message)).toName
    return (← mkQuoteCmd c.message name, name)

open Discussion in
def definitionCommandsAux [DefinitionCommand α] (prevName : Syntax.Term) (d : α) : TermElabM (List Syntax.Command  × Name) := do
  let (elemDef, name) ← definitionCommandPair d
  let descName := name ++ "chat".toName
  let appendIdent := mkIdent ``append
  let descId := mkIdent descName
  let nameIdent := mkIdent name
  let stx := prevName
  let cmd ← `(command| def $descId := $appendIdent $stx $nameIdent)
  return ([elemDef, cmd], descName)

def definitionCommands (disc: Discussion α)  (chatName : Syntax.Term) (prevLength : Nat := 0) : TermElabM (List Syntax.Command  × Syntax.Term) := do
  if disc.length <= prevLength then
    return ([], chatName)
  else
  match disc with
  | .start q =>
    return ([], chatName)
  | .query init d =>
      let (prevcmds, prevname) ← definitionCommands init chatName prevLength
      let (cmds, name) ← definitionCommandsAux prevname d
      return (prevcmds ++ cmds, mkIdent name)
  | .response init d =>
      let (prevcmds, prevname) ← definitionCommands init chatName prevLength
      let (cmds, name) ← definitionCommandsAux prevname d
      return (prevcmds ++ cmds, mkIdent name)
  | .translateTheoremQuery init d =>
      let (prevcmds, prevname) ← definitionCommands init chatName prevLength
      let (cmds, name) ← definitionCommandsAux prevname d
      return (prevcmds ++ cmds, mkIdent name)
  | .theoremTranslation init d =>
      let (prevcmds, prevname) ← definitionCommands init chatName prevLength
      let (cmds, name) ← definitionCommandsAux prevname d
      return (prevcmds ++ cmds, mkIdent name)
  | .translateDefinitionQuery init d =>
      let (prevcmds, prevname) ← definitionCommands init chatName prevLength
      let (cmds, name) ← definitionCommandsAux prevname d
      return (prevcmds ++ cmds, mkIdent name)
  | .definitionTranslation init d =>
      let (prevcmds, prevname) ← definitionCommands init chatName prevLength
      let (cmds, name) ← definitionCommandsAux prevname d
      return (prevcmds ++ cmds, mkIdent name)
  | .comment init d =>
      let (prevcmds, prevname) ← definitionCommands init chatName prevLength
      let (cmds, name) ← definitionCommandsAux prevname d
      return (prevcmds ++ cmds, mkIdent name)
  | .proveTheoremQuery init d =>
      let (prevcmds, prevname) ← definitionCommands init chatName prevLength
      let (cmds, name) ← definitionCommandsAux prevname d
      return (prevcmds ++ cmds, mkIdent name)
  | .proofDocument init d _ =>
      let (prevcmds, prevname) ← definitionCommands init chatName prevLength
      let (cmds, name) ← definitionCommandsAux prevname d
      return (prevcmds ++ cmds, mkIdent name)
  | .proofStructuredDocument init d _ _ =>
      let (prevcmds, prevname) ← definitionCommands init chatName prevLength
      let (cmds, name) ← definitionCommandsAux prevname d
      return (prevcmds ++ cmds, mkIdent name)
  | .proofCode init d =>
      let (prevcmds, prevname) ← definitionCommands init chatName prevLength
      let cmds := commands d.code
      return (prevcmds ++ cmds.toList, prevname)
  | .rewrittenDocument init d _ =>
      let (prevcmds, prevname) ← definitionCommands init chatName prevLength
      let (cmds, name) ← definitionCommandsAux prevname d
      return (prevcmds ++ cmds, mkIdent name)
  | .edit _ init  =>
      definitionCommands init chatName prevLength

def relDefinitionCommands (disc: Discussion α) (prevDisc : Discussion β) : Syntax.Term → TermElabM (List Syntax.Command) := fun stx => do
  let prevLength := prevDisc.length
  let (cmds, _) ← definitionCommands disc stx prevLength
  return cmds

def relDefinitionCommandsM (discM: TermElabM (Discussion α)) (prevDisc : Discussion β) : TermElabM (Syntax.Term → TermElabM (List Syntax.Command)) := do
  return relDefinitionCommands (← discM) prevDisc

def discEg := (Discussion.start none) |>.mkQuery (⟨"Prove that 2 + 2 = 4.", Json.null⟩) |>.response (⟨"Sure, here's a proof: /-- 2 + 2 = 4 -/ theorem two_plus_two : 2 + 2 = 4 := by norm_num", Json.null⟩)

elab "#disc_eg_cmds" : command => Command.liftTermElabM do
  let (cmds, name) ← definitionCommands discEg (mkIdent `chat_eg)
  logInfo s!"Final name: {name}"
  for c in cmds do
    logInfo c

-- #disc_eg_cmds

syntax (name:= proofGenCmd) "#prove" ppSpace term (">>" ppSpace term)? : command

@[command_elab proofGenCmd] def elabProofGenCmd : CommandElab
  | stx@`(command| #prove $t:term >> $out:term) =>
    Command.liftTermElabM do
    let type ← elabType out
    let init ← Term.elabTerm t none
    let discussion ←
      Discussion.isDiscussionType <| ← inferType init
    let type ← if discussion && !(← Discussion.isDiscussionType type) then
      mkAppM ``Discussion #[type]
    else
      pure type
    let result ← mkAppM ``generateM #[type, init]
    if discussion then
      let cmdsMapExpr ← mkAppM ``relDefinitionCommandsM #[result, init]
      let cmdsMapType' ← mkArrow (mkConst ``Syntax.Term) (← mkAppM ``TermElabM #[(← mkAppM ``List #[mkConst ``Syntax.Command])])
      let cmdsMapType ← mkAppM ``TermElabM #[cmdsMapType']
      let cmdsMapM ← unsafe evalExpr (TermElabM (Syntax.Term → TermElabM (List Syntax.Command))) cmdsMapType cmdsMapExpr
      let cmdsMap ← cmdsMapM
      let cmds ← cmdsMap t
      let cmds := cmds.toArray
      let s ← printCommands (← `(commandSeq | $cmds*))
      TryThis.addSuggestion stx s (header := "Generated commands:")
    else
      let SideEffect' ← mkAppM ``TermElabM #[mkConst ``Unit]
      let SideEffect ← mkArrow (mkConst ``Syntax) SideEffect'
      let resultEffectExpr ← mkAppM ``replaceCommandM #[result]
      let resultEffect ← unsafe evalExpr (Syntax → (TermElabM Unit)) SideEffect resultEffectExpr
      resultEffect stx
  | stx@`(command| #prove $t:term ) => Command.liftTermElabM do
    let tc := mkIdent ``Conjecture
    let pd := mkIdent ``ProofDocument
    let sp := mkIdent ``StructuredProof
    let pc := mkIdent ``ProofCode
    TryThis.addSuggestions stx #[(← `(command| #prove $t:term >> $tc)), (← `(command| #prove $t:term >> $pd)), (← `(command| #prove $t:term >> $sp)), (← `(command| #prove $t:term >> $pc))] (header := "Specify output type with >>")
  | _ => throwUnsupportedSyntax

syntax (name:= askCommand) (docComment)? "#ask" (ppSpace str)? ppSpace "<<" ppSpace term : command

@[command_elab askCommand] def elabAskCmd : CommandElab
  | stx@`(command| #ask $s:str << $t:term) =>
    Command.liftTermElabM do
    let text := s.getString
    go text stx t
  | stx@`(command| $doc:docComment #ask << $t:term) =>
    Command.liftTermElabM do
    let text ← getDocStringText doc
    go text stx t
  | _ => throwUnsupportedSyntax
  where go (text: String) (stx : Syntax) (t: Syntax.Term) : TermElabM Unit := do
    let textExpr := mkStrLit text
    let init ← Term.elabTerm t none
    let init' ← mkAppM ``Discussion.addQuery #[init, textExpr]
    let type ← mkAppM ``Discussion #[mkConst ``Response]
    let result ← mkAppM ``generateM #[type, init']
    let cmdsMapExpr ← mkAppM ``relDefinitionCommandsM #[result, init]
    let cmdsMapType' ← mkArrow (mkConst ``Syntax.Term) (← mkAppM ``TermElabM #[(← mkAppM ``List #[mkConst ``Syntax.Command])])
    let cmdsMapType ← mkAppM ``TermElabM #[cmdsMapType']
    let cmdsMapM ← unsafe evalExpr (TermElabM (Syntax.Term → TermElabM (List Syntax.Command))) cmdsMapType cmdsMapExpr
    let cmdsMap ← cmdsMapM
    let cmds ← cmdsMap t
    let cmds := cmds.toArray
    let s ← printCommands (← `(commandSeq | $cmds*))
    TryThis.addSuggestion stx s (header := "Generated commands:")

@[command_elab llmQueryCommand] def llmQueryCommandImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #llm_query  $_:str) =>
    logWarning "Follow ask command with 'following <term>' or 'initiate' to continue/start a discussion."
  | `(command| #llm_query $_:num $_:str) =>
    logWarning "Follow ask command with 'following <term>' or 'initiate' to continue/start a discussion."
  | `(command| #llm_query $s:str following $p:term) =>
    let s := s.getString
    let _p ← Term.elabTerm p none
    go s none stx
  | `(command| #llm_query $n:num $s:str following $p:term) =>
    let s := s.getString
    let _p ← Term.elabTerm p none
    let n := n.getNat
    go s (some n) stx
  | `(command| #llm_query $s:str initiate) =>
    let s := s.getString
    go s none stx
  | `(command| #llm_query $n:num $s:str initiate) =>
    let s := s.getString
    let n := n.getNat
    go s (some n) stx
  | _ => throwUnsupportedSyntax
  where go (s: String) (n?: Option Nat)(stx: Syntax) : TermElabM Unit := do
      -- let server ← chatServer
      let n := n?.getD 3
      let responses ← KernelM.mathQuery s [] n
      for r in responses do
        logInfo r
      let stxs : List TryThis.Suggestion ← responses.mapM fun res => do
        let name := s!"query_{hash res}".toName
        let stxQ ← mkQueryCmd s name
        let name := s!"response_{hash res}".toName
        let stxR ←  mkResponseCmd res name
        printCommands <| ←  toCommandSeq #[stxQ, stxR]
      TryThis.addSuggestions stx <| stxs.toArray


end LeanAide

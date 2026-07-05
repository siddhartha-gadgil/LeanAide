import LeanAideCore.CodegenCore
import LeanAideCore.Translate
/-!
# Code generation for LeanAide "PaperStructure" schema

This module provides code generation for the LeanAide "PaperStructure" schema, which includes sections, theorems, definitions, logical steps, proofs, and other elements of a mathematical document.

Each function corresponds to a specific JSON schema element and generates the appropriate Lean code. The tag `codegen` is used to mark these functions for code generation with argument the key.
-/
open Lean Meta Elab Term

namespace LeanAide

open Codegen Translate

#logIO leanaide.papercodes.info


/--
Translating to a proposition in Lean, using the `translateToProp?` method of the `Translator`. Various checks are performed to ensure the type is valid and does not contain `sorry` or metavariables. An error is thrown if the translation fails or if the type is not valid.
-/


def Translator.translateToPropStrictAux
    (claim: String)(translator : Translator)
    : TranslateM Expr := do
  try
    let leanClaim ← withVarPreludes claim
    let .ok stx := Parser.runParserCategory (← getEnv) `term leanClaim |
      throwError s!"codegen: failed to parse '{claim}' as a term"
    withoutErrToSorry do
      let prop ← elabType stx
      let prop ← instantiateMVars prop
      Term.synthesizeSyntheticMVarsNoPostponing
      if prop.hasSorry || (← prop.hasUnassignedExprMVar) then
        traceAide `leanaide.papercodes.error s!"codegen: failed to infer type {prop} has sorry or mvar when translating assertion '{claim}'"
      if prop.hasSorry || (← prop.hasUnassignedExprMVar) then
        throwError s!"codegen: failed to infer type {prop} has sorry or mvar when translating assertion '{claim}'"
      traceAide `leanaide.papercodes.info s!"Obtained type: {← ppExpr prop}"
      let prop ← dropLocalContext prop
      traceAide `leanaide.papercodes.info s!"Obtained type in local context: {← ppExpr prop}"
      return prop
  catch _ =>
  let thm ← withPreludes claim
  traceAide `leanaide.papercodes.info s!"Translating to proposition: {claim}, full statement: {thm}"
  let (js, _, _) ← translator.getLeanCodeJson claim
  let output ← getMessageContents js
  for out in output do
    let el? ← elabThm4 out
    match el? with
    | Except.error _ =>
      continue
    | Except.ok type =>
      let type ← instantiateMVars type
      Term.synthesizeSyntheticMVarsNoPostponing
      if type.hasSorry || (← type.hasUnassignedExprMVar) then
        throwError s!"Failed to infer type {type} has sorry or mvar when translating assertion '{claim}', full statement {thm}"
      try
        let univ ←
          Term.withoutErrToSorry do
            inferType type
        if univ.isSort then
          traceAide `leanaide.papercodes.info s!"Obtained type: {← ppExpr type}"
          Translate.addRecentTranslation thm out
          let type ← dropLocalContext type
          traceAide `leanaide.papercodes.info s!"Obtained type in local context: {← ppExpr type}"
          return type
      catch _ =>
        continue
  throwError s!"codegen: no valid type found for assertion '{claim}', full statement {thm}; all translations:\n{output.foldl (init := "") (· ++ "\n" ++ ·)}"

/--
Translating to a proposition in Lean, using the `translateToProp?` method of the `Translator`. Various checks are performed to ensure the type is valid and does not contain `sorry` or metavariables. An error is thrown if the translation fails or if the type is not valid.
-/
def Translator.translateToPropStrict
    (claim: String)(translator : Translator)
    : TranslateM Expr := do
    try
      Translator.translateToPropStrictAux claim translator
    catch e =>
      let fullClaim ← translator.server.fullStatement claim
      try
        Translator.translateToPropStrictAux fullClaim translator
      catch e' =>
        -- If the translation fails, we throw an error with the original claim and the error message.
        -- This is useful for debugging and understanding what went wrong.
        throwError s!"codegen: failed to translate '{claim}' to a proposition even with 'full statement', error: {← e.toMessageData.format}; full claim: {fullClaim}, error: {← e'.toMessageData.format}"

def translateToDef (statement: String) (translator : Translator) : TranslateM <| Except (Array CmdElabError) Syntax.Command := do
  try
    let .ok stx := Parser.runParserCategory (← getEnv) `command statement | throwError
      s!"codegen: failed to parse '{statement}' as a command"
    let checks ← checkElabFrontM statement
    unless checks.isEmpty do
      throwError s!"codegen: failed to elaborate '{statement}' as a command, errors: {checks}"
    return .ok ⟨stx⟩
  catch _ =>
    translator.translateDefCmdM? statement

def translateToTermAux (term: String)(translator: Translator) : TranslateM Syntax.Term := do
  let termStat := s!"Let my_new_term := {term}"
  let termCmd ← translator.translateDefCmdM? termStat
  match termCmd with
  | .ok cmd =>
    let term ← commandToTerm cmd
    match term with
    | `(term| fun $_args* => $value) => pure value
    | _ => pure term
  | .error errs =>
    throwError s!"codegen: failed to translate '{term}' to a term, errors: {errs.map (·.text)}"

def Translator.translateToTerm (term: String)(translator: Translator) : TranslateM Syntax.Term := do
  try
    withoutErrToSorry do
     let .ok finalTerm := Parser.runParserCategory (← getEnv) `term term | throwError s!"codegen: failed to parse the term: {term}"
     let expr ← elabTerm finalTerm none
     Term.synthesizeSyntheticMVarsNoPostponing
     delabDetailed expr
  catch _ =>
    translateToTermAux term translator
/--
If the goal is a ∀, function etc., this function intros the variables and returns the goal with the names of the variables introduced. Further, corresponding prelude commands are added to the context.
-/
def consumeIntros (goal: MVarId) (maxDepth : Nat)
    (accum: List Name) : TranslateM <| MVarId × List Name := goal.withContext do
  match maxDepth, ← goal.getType with
  | 0, _ =>
    return (goal, accum)
  | k + 1, Expr.forallE n type _ _ => do
    let hash := (← PrettyPrinter.ppExpr type).pretty.hash
    let n := if n.isInternal then s!"{n.components[0]!}_{hash}".toName else n
    addPrelude s!"Fix {n} : {← ppExpr type}"
    let (_, goal') ← goal.intro n
    goal'.withContext do
      consumeIntros goal' k (accum ++ [n])
  | k + 1, Expr.letE n type value _ _ => do
    let hash := (← PrettyPrinter.ppExpr type).pretty.hash
    let n := if n.isInternal then s!"{n.components[0]!}_{hash}".toName else n
    addPrelude s!"Fix {n} : {← ppExpr type} := {← ppExpr value}"
    let (_, goal') ← goal.intro n
    goal'.withContext do
      consumeIntros goal' k (accum ++ [n])
  | _, _ => do
    return (goal, accum)

open Lean.Parser.Tactic

def resolveIntros (goal: MVarId) (names: List Name) : TranslateM <| MVarId × (Array Syntax.Tactic)  := goal.withContext do
  let mut goal := goal
  let mut tacs := #[]
  for n in names do
    let introTerm ← elabTerm (mkIdent n) none
    let introType ← inferType introTerm
    let introTypeStx ← delabDetailed introType
    let resolved ← resolveExistsHave introTypeStx (mkIdent n)
    tacs := tacs ++ resolved
  return (goal, tacs)

def recallTheoremsAux : List DefData → TranslateM (Array Syntax.Tactic)
| [] => return #[]
| head :: tail => do
  let name := head.name
  let type ← elabType head.type
  let value ← elabTerm head.value type
  withLetDecl name type value fun x => do
    let tailTacs ← recallTheoremsAux tail
    let topTacs ←  if head.isProp then
      let thm ← fillLocalContext x
      let quotName := "quot" ++ name.toString |>.toName
      let quotId := mkIdent quotName
      let thmType ← inferType thm
      let typeStx ← delabDetailed thmType
      let thmStx ← delabDetailed thm
      let head ← `(tactic| have $quotId : $typeStx := $thmStx)
      let exs ← resolveExistsHave typeStx
      pure <| #[head] ++ exs
      else pure #[]
    return topTacs ++ tailTacs

def recallTheorems : TranslateM <| Array Syntax.Tactic := do
  recallTheoremsAux (← getDefs).toList

/--
Extract the `ResultUsed` from the JSON object. It tries to find either a `target_identifier` or a `mathlib_identifier`. If both are missing, it translates the `statement` to a proposition and returns it as a term. If `mathlib_identifier` is present, it returns an identifier for it. If `target_identifier` is present, it looks for the theorem with that identifier and returns its name.
-/
def getResultUsed? (translator: Translator) (js: Json) : TranslateM (Option Syntax.Term) := do
  let targetIdentifier? := js.getObjValAs? String "target_identifier"
  let mathlibIdentifier? := js.getObjValAs? String "mathlib_identifier"
  match targetIdentifier?, mathlibIdentifier? with
  | .error _, .error _ =>
    let .ok statement := js.getObjValAs? String "statement" | throwError "'ResultUsed' must have 'statement'"
    let type ← translator.translateToPropStrict statement
    getExactTerm? type
  | _, .ok mathlibIdentifier =>
    return mkIdent mathlibIdentifier.toName
  | .ok targetIdentifier, _ =>
    let l? ← findTheorem? targetIdentifier
    return l?.map fun l =>
      mkIdent l.name

/--
Extracts the `results_used` from the JSON object and returns an array of `Syntax.Term` representing the results used. It uses `getResultUsed?` to extract each result.
-/
def getResultsUsed (translator: Translator) (js: Json) : TranslateM (Array Syntax.Term) := do
  match js.getObjValAs? (Array Json) "results_used" with
  | .error _ => return #[]
  | .ok resultsUsed =>
    resultsUsed.filterMapM fun js =>
      getResultUsed? translator js

/--
Deals with an error where the full JSON is an `object` instead of a `document` or theorem-proof etc, with `properties` containing the actual content.
-/
@[codegen "object"]
def objectBypassCode (translator : CodeGenerator := {})
    (goal? :Option MVarId) (kind: SyntaxNodeKinds) : Json → TranslateM (Option (TSyntax kind))
| js => do
  traceAide `leanaide.papercodes.info s!"bypassing 'object"
  let .ok properties :=
    js.getObjVal? "properties" | throwError "'object' must have 'properties'"
  getCode translator goal? kind properties

/--
Wrapping proofs that are single assertions.
-/
def getProof (translator: CodeGenerator)(goal: MVarId) (js: Json) : TranslateM (Option (TSyntax ``tacticSeq)) := do
  match js.getObjVal? "type" with
  | .ok "assert_statement" => getCodeTactics translator goal [js]
  | _ => getCode translator (some goal) ``tacticSeq js

/--
Generic parser for Lean code. We write an object with a single key value of the form:
`{"lean": "<lean code>"}`
-/
@[codegen "lean"]
def leanCode (_ : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, ``tacticSeq, js => do
  let .ok code := js.getStr? | throwError "'lean' must have 'lean' field"
  let code := if code.startsWith "\"" then code.drop 1 else code
  let code := if code.endsWith "\"" then code.dropEnd 1 else code
  parseTacticSeq code.toString
| _, ``commandSeq, js => do
  let .ok code := js.getStr? | throwError "'lean' must have 'lean' field"
  let code := if code.startsWith "\"" then code.drop 1 else code
  let code := if code.endsWith "\"" then code.dropEnd 1 else code
  let cmdSeq ← parseCommandSeq code.toString
  let cmds := getCommands  cmdSeq
  for cmd in cmds do
    runCommand cmd
  return some cmdSeq
| _, kind, _ => throwError
    s!"codegen: 'lean' does not work for kind {kind}"

/--
Checks the value of a declaration and returns a trace.
-/
@[codegen "check"]
def checkCode (_ : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, ``commandSeq, js => do
  let .ok (name : Name) := fromJson? js | throwError "'check' must be a key-value pair with value a name"
  match (← getEnv).find? name with
  | none => throwError s!"codegen: 'check' cannot find declaration '{name}'"
  | some decl =>
    let typeStr ← ppExprDetailed decl.type
    let valueStr? ←
      decl.value?.mapM fun value => do
        let valueStr ← ppExprDetailed value
        return s!" with value `{valueStr}`"
    let valueStr := valueStr?.getD ""
    let typeLit := Syntax.mkStrLit s!"{name} has type {typeStr}{valueStr}"
    -- TODO: Avoid emitting diagnostic `#check` commands into generated code or
    -- into command preludes when a check/failure is only for codegen tracing.
    let stx : TSyntax ``commandSeq ←  `(commandSeq| #check $typeLit)
    return some stx
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok (name : Name) := fromJson? js | throwError "'check' must be a key-value pair with value a name"
  match (← getEnv).find? name with
  | none =>
    let lctx ← getLCtx
    match lctx.findFromUserName? name with
    | none => throwError s!"codegen: 'check' cannot find declaration '{name}'"
    | some decl =>
      let typeStr ← ppExprDetailed decl.type
      let typeLit := Syntax.mkStrLit s!"{name} has (local declaration with) type {typeStr}"
      let stx : TSyntax ``tacticSeq ←  `(tacticSeq| trace $typeLit)
      return some stx
  | some decl =>
    let typeStr ← ppExprDetailed decl.type
    let valueStr? ←
      decl.value?.mapM fun value => do
        let valueStr ← ppExprDetailed value
        return s!" with value {valueStr}"
    let typeLit := Syntax.mkStrLit s!"{name} has type {typeStr} {valueStr?}"
    let stx : TSyntax ``tacticSeq ←  `(tacticSeq| trace $typeLit)
    return some stx
| _, kind, _ => throwError
    s!"codegen: 'check' does not work for kind {kind}"


/--
Gets a sequence of commands or tactics from a JSON "document". There are two options for compatibility with the old schema.
-/
@[codegen "document"]
def documentCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, ``commandSeq, js => do
  let some content := js.getArr?.toOption.orElse
    (fun _ =>js.getObjValAs? (Array Json) "body" |>.toOption) | throwError "'document' must have body or be a JSON array"
  getCodeCommands translator none  content.toList
| some goal, ``tacticSeq, js => goal.withContext do
  let some content := js.getArr?.toOption.orElse
    (fun _ =>js.getObjValAs? (Array Json) "body" |>.toOption) | throwError "'document' must have body or be a JSON array"
  getCodeTactics translator goal  content.toList
| _, kind, _ => throwError
    s!"codegen: 'document' does not work for kind {kind}"

/--
A bunch of cases that do not generate any code. This is used to mark elements that are not expected to generate code, such as titles, abstracts, remarks, metadata, authors, bibliography, citations, internal references, paragraphs, figures, tables, and images.
-/
@[codegen "title","abstract", "remark", "metadata", "author", "bibliography", "citation", "internalreference", "paragraph", "figure", "table", "image"]
def noGenCode := noCode

/--
Generate commands or tactics for a section of the document. It processes the `content` array and generates the appropriate code based on the kind of content.
-/
@[codegen "section"]
def sectionCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => do
  let .ok content := js.getObjValAs? (List Json) "content" | throwError "'section' must have 'content'"
  getCodeCommands translator none  content
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok content := js.getObjValAs? (List Json) "content" | throwError "'section' must have 'content'"
  getCodeTactics translator goal  content
| _, kind, _ => throwError
    s!"codegen: 'section' does not work for kind {kind}"



/--
Generate code for a theorem, lemma, proposition, corollary, or claim. It processes the `hypothesis`, `claim`, and `proof` fields to generate the appropriate Lean code. If the proof is absent a definition is generated instead, which is the statement of the theorem and with name `{name}.prop`.

Should perhaps try to use automation if there is no proof.
-/
@[codegen "theorem"]
def theoremCodeCore (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `command, js => do
  let (stx, name, pf?, isProp) ← thmStxParts js
  match pf? with
  | some pf =>
    let n := mkIdent name
    if isProp then
      `(command| theorem $n : $stx := by $pf)
    else
      `(command| noncomputable def $n : $stx := by $pf)
  | none =>
    let n := mkIdent (name ++ `prop)
    let propExpr := mkSort Level.zero
    let propIdent ← delabDetailed propExpr
    `(command| abbrev $n : $propIdent:term := $stx)
| _, `commandSeq, js => do
  let (stx, name, pf?, isProp) ← thmStxParts js
  match pf? with
  | some pf =>
    let n := mkIdent name
    let defn : DefData := {
      name := n.getId,
      type := stx,
      value := ← `(by $pf),
      isProp := isProp,
      isNoncomputable := true,
      doc? := none
    }
    addDefn defn
    traceAide `leanaide.papercodes.info s!"Added theorem definition: {defn.name}"
    if isProp then
      `(commandSeq| theorem $n : $stx := by $pf)
    else
      `(commandSeq| noncomputable def $n : $stx := by $pf)
  | none =>
    throwError s!"codegen: 'theorem' without proof is not supported in command sequences; found theorem {name} with statement {stx}"
| some goal, ``tacticSeq, js => goal.withContext do
  let (stx, name, pf?, _) ← thmStxParts js
  match pf? with
  | some pf =>
    let n := mkIdent name
    `(tacticSeq| have $n : $stx := by $pf)
  | none =>
    let n := mkIdent (name ++ `prop)
    let propExpr := mkSort Level.zero
    let propIdent ← delabDetailed propExpr
    `(tacticSeq| have $n : $propIdent := $stx)
| some _, `tactic, js => do
  let (stx, name, pf?, _) ← thmStxParts js
  match pf? with
  | some pf =>
    let n := mkIdent name
    `(tactic| have $n : $stx := by $pf)
  | none =>
    let n := mkIdent (name ++ `prop)
    let propExpr := mkSort Level.zero
    let propIdent ← delabDetailed propExpr
    `(tactic| let $n : $propIdent := $stx)
| goal?, kind, _ => throwError
    s!"codegen: 'theorem' does not work for kind {kind}where goal present: {goal?.isSome}"
where
  thmStxParts (js: Json)  :
    TranslateM <| Syntax.Term × Name × Option (TSyntax ``tacticSeq) × Bool  := withoutModifyingState do
    match js.getObjVal?  "hypothesis" with
      | Except.ok h => contextRun translator none ``tacticSeq h
      | Except.error _ => pure ()
    let .ok  claim := js.getObjValAs? String "claim" | throwError
      s!"codegen: no 'claim' found in 'theorem'"
    traceAide `leanaide.papercodes.info s!"Translating claim: {claim}"
    let type ← translator.translateToPropStrict claim
    traceAide `leanaide.papercodes.info s!"Obtained type from translation: {← ppExpr type}"
    let proof? :=
      js.getObjVal? "proof" |>.toOption
    let hypSize ←
      match js.getObjValAs? (Array Json)  "hypothesis" with
      | Except.ok h =>
        traceAide `leanaide.papercodes.info s!"hypothesis: {h} in proof"
        contextRun translator none ``tacticSeq (.arr h)
        traceAide `leanaide.papercodes.info s!"Preludes added:\n {(← withPreludes "")}"
        pure h.size
      | Except.error _ => pure 0
    traceAide `leanaide.papercodes.info s!"hypothesis size: {hypSize} in proof"
    let thm ← withPreludes claim
    let name := (js.getObjValAs? Name "name").toOption.getD <| ← translator.server.theoremName thm
    traceAide `leanaide.papercodes.info s!"Theorem name from server: {name} for {thm}"
    let name :=
      if name.toString = "[anonymous]" then

        let hash := thm.hash
        let name := s!"thm_{hash}"
        name.toName
      else
        name
    traceAide `leanaide.papercodes.info s!"Theorem name: {name} for {thm}"
    let typeStx ← delabDetailed type
    let proofStx? ← proof?.mapM fun
      pf => withoutModifyingState do
      -- Adding dummy statement for prompt, will be rolled back
      let nameIdent := mkIdent name
      let dummyCmd ← `(command| theorem $nameIdent : $typeStx := by sorry)
      Translate.addCommand dummyCmd
      -- Finding proof
      let pfGoal ← mkFreshExprMVar type
      let (pfGoal', names') ← extractIntros pfGoal.mvarId! hypSize
      traceAide `leanaide.papercodes.debug s!"Extracted intros, names: {names'}"
      let (pfGoal'', names) ← consumeIntros pfGoal' 10 names'
      traceAide `leanaide.papercodes.debug s!"Consumed intros, names: {names}"
      let (pfGoal, resTacs) ← resolveIntros pfGoal'' names
      let pfStx ←
        withoutModifyingState do
        pfGoal.withContext do
        match ←
        getProof translator pfGoal pf with
      | some pfStx =>
        let pfStx ←  if names.isEmpty then
            pure pfStx
          else
            let namesStx : List <| TSyntax `term ←
              names.mapM fun n =>
                if n.isInaccessibleUserName || n.isInternal then
                  `(_)
                else do
                  traceAide `leanaide.papercodes.info s!"Adding intro for {n}, not inaccessible"
                  let n' := mkIdent n
                  `($n':ident)
            let namesStx := namesStx.toArray
            let introTac ←
              `(tacticSeq| intro $namesStx*; $resTacs*)
            appendTacticSeqSeq introTac pfStx
        pure pfStx
      | none => throwError
        s!"codegen: no proof translation found for {pf}"
      pure pfStx
    traceAide `leanaide.papercodes.info s!"Obtained or skipped proof; obtained: {proofStx?.isSome}"
    let label := js.getObjValAs? String "label" |>.toOption.getD name.toString
    Translate.addTheorem <| {name := name, type := type, label := label, isProved := proof?.isSome, source:= js}
    logInfo m!"All theorems : {← allLabels}"
    return (typeStx, name, proofStx?, ← isProp type)

/--
Generate code for a definition. It processes the `definition` field to generate the appropriate Lean code.
-/
@[codegen "definition"]
def defCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => do
  let stx ← defCmdStx js
  `(commandSeq | $stx)
| _, ``tacticSeq, js => do
  let stx ← defCmdStx js
  let tac ← commandSeqToTacticSeq stx
  `(tacticSeq| $tac)
| _, kind, _ => throwError
    s!"codegen: 'definition' does not work for kind {kind}"
where
  defCmdStx (js: Json) :
    TranslateM <| TSyntax ``commandSeq :=
    withoutModifyingState do
    let .ok statement :=
      js.getObjValAs? String "definition" | throwError
        s!"codegen: no 'definition' found in 'definition'"
    let .ok name :=
      js.getObjValAs? Name "name" | throwError
        s!"codegen: no 'name' found in 'definition'"
    let nameStx := mkIdent name
    match
      ← translator.translateDefCmdM? statement with
      | .ok cmd =>
        match cmd with
        | `(command| def $_defName:ident $args:bracketedBinder* : $type := $value) =>
            `(command| def $nameStx $args* : $type := $value)
        | `(command| def $_defName:ident $args:bracketedBinder* := $value) =>
            `(command| def $nameStx $args*  := $value)
        | `(command| noncomputable def $_defName:ident $args:bracketedBinder* : $type := $value) =>
            `(command| noncomputable def $nameStx  $args* : $type := $value)
        | `(command| noncomputable def $_defName:ident $args:bracketedBinder* := $value) =>
            `(command| noncomputable def $nameStx $args*:= $value)
        | _ => throwError s!"commandToTerm: unsupported command {cmd}"
        let cmds := #[cmd]
        `(commandSeq| $cmds*)
      | .error errs =>
        try
          -- TODO: Avoid this fallback for ordinary definitions. Predicate and
          -- type-valued definitions should remain `def`/`abbrev` declarations,
          -- not be converted into existential theorem declarations.
          let claim := s!"There exists {name} such that:\n{statement}"
          let type ←
            translator.translateToPropStrict claim
          let typeStx ← delabDetailed type
          let mvar ← mkFreshExprMVar type
          let proof ←
            findTacticsI mvar.mvarId!
          let proofStx ←
            `(tacticSeq| $proof*)
          let thm ← withPreludes claim
          let name ← translator.server.theoremName thm
          let name :=
            if name.toString = "[anonymous]" then
              let hash := type.hash
              let name := s!"thm_{hash}"
              name.toName
            else
              name
          let name := mkIdent name
          let head ←
            `(command| theorem $name : $typeStx := by $proofStx)
          let resolvedCmds ←
            cmdResolveExistsHave typeStx
          mkCommandSeq <| #[head] ++ resolvedCmds
        catch e =>
          let innerMsg ←  e.toMessageData.format
          let outputs := errs.map (·.text)
          throwError s!"codegen: no definition translation found for {statement}; outputs: {outputs}\nError when trying existential definition:\n{innerMsg}"


/- LogicalStepSequence
{
  "type": "array",
  "description": "A sequence of structured logical steps, typically used within a proof or derivation, consisting of statements like 'let', 'assert', 'assume', etc.",
  "items": {
    "anyOf": [
      {
        "$ref": "#/$defs/let_statement"
      },
      {
        "$ref": "#/$defs/assert_statement"
      },
      {
        "$ref": "#/$defs/assume_statement"
      },
      {
        "$ref": "#/$defs/some_statement"
      },
      {
        "$ref": "#/$defs/cases_proof"
      },
      {
        "$ref": "#/$defs/induction_proof"
      },
      {
        "$ref": "#/$defs/calculate_statement"
      },
      {
        "$ref": "#/$defs/contradiction_statement"
      },
      {
        "$ref": "#/$defs/conclude_statement"
      }
    ]
  }
}
-/
/--
Generate code for a sequence of logical steps. It processes the items in the sequence and generates the appropriate Lean code, either as commands or tactics.
-/
@[codegen "logicalstepsequence"]
def logicalStepCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => do
  let .ok content := js.getObjValAs? (Array Json) "items" | throwError "logicalStepSequence must have an `items` field that is a JSON array"
  getCodeCommands translator none  content.toList
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok content := js.getObjValAs? (Array Json) "items" | throwError "logicalStepSequence must have an `items` field that is a JSON array"
  getCodeTactics translator goal  content.toList
| goal?, kind, _ => throwError
    s!"codegen: logicalStepSequence does not work for kind {kind}where goal present: {goal?.isSome}"

/--
Generate code for a proof environment, either a sequence of tactics or a command sequence. To generate a command sequence, it requires a `claim_label` to find the theorem being proved. It intros the variables of the theorem and generates the proof steps as tactics.
-/
@[codegen "proof"]
def proofCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => withoutModifyingState do
  let .ok content := js.getObjValAs? (List Json) "proof_steps" | throwError "missing or invalid 'proof_steps' in 'proof'"
  let .ok claimLabel := js.getObjValAs? String "claim_label" | throwError
    s!"codegen: no 'claim_label' found in standalone 'proof'"
  let some labelledTheorem ← findTheorem? claimLabel | throwError
    s!"codegen: no theorem found with label {claimLabel}; all labels {← allLabels}"
  let goalType := labelledTheorem.type
  let goalExpr ← mkFreshExprMVar goalType
  let goal := goalExpr.mvarId!
  traceAide `leanaide.papercodes.info s!"number of proof steps: {content.length}"
  let hypSize ←
    match labelledTheorem.source.getObjValAs? (Array Json)  "hypothesis" with
      | Except.ok h =>
        traceAide `leanaide.papercodes.info s!"hypothesis: {h} in proof"
        contextRun translator none ``tacticSeq (.arr h)
        traceAide `leanaide.papercodes.info s!"Ran hypothesis context"
        traceAide `leanaide.papercodes.info s!"Preludes added:\n {(← withPreludes "")}"
        pure h.size
      | Except.error _ => pure 0
  traceAide `leanaide.papercodes.info s!"hypothesis size: {hypSize} in proof"
  let (goal', names') ← extractIntros goal hypSize
  traceAide `leanaide.papercodes.info s!"Extracted intros: {names'}"
  let (goal'', names) ← consumeIntros goal' 10 names'
  let (goal, resTacs) ← resolveIntros goal'' names
  traceAide `leanaide.papercodes.info s!"Consumed intros: {names}"
  let pfStx ←
    withoutModifyingState do
    goal.withContext do
    getCodeTactics translator goal content
  let pfStx ←  if names.isEmpty then
      pure pfStx
    else
      let namesStx : List <| TSyntax `term ←
        names.mapM fun n =>
          if n.isInaccessibleUserName || n.isInternal then
            `(_)
          else do
            traceAide `leanaide.papercodes.info s!"Adding intro for {n}, not inaccessible"
            let n' := mkIdent n
            `($n':ident)
      let namesStx := namesStx.toArray
      let introTac ←
        `(tacticSeq| intro $namesStx*; $resTacs*)
      appendTacticSeqSeq introTac pfStx
  traceAide `leanaide.papercodes.info s!"Proof steps: {← PrettyPrinter.ppCategory ``tacticSeq pfStx}"
  let n := mkIdent labelledTheorem.name
  let typeStx ← delabDetailed goalType
  updateToProved labelledTheorem.label
  `(commandSeq| theorem $n : $typeStx := by $pfStx)
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok content := js.getObjValAs? (List Json) "proof_steps" | throwError "missing or invalid 'proof_steps' in 'proof'"
  withoutModifyingState do
  getCodeTactics translator goal  content
| goal?, kind, _ => throwError
    s!"codegen: proof does not work for kind {kind}where goal present: {goal?.isSome}"

/--
Generate code for a `let_statement`. If the let statement has a value, it generates a command or tactic that defines the variable with the given value. If there is no value, it simply adds a prelude statement.
If goal is a `there exists` statement and binderName matches variable_name, it returns `use` tactic.
-/
@[codegen "let_statement"]
def letCodeCore (translator : CodeGenerator := {})(goal? : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind)) := fun s js => do
  match s, js with
  | ``tacticSeq, js => do
    let statement := statement js
    match js.getObjValAs? String "value" with
    | .error _ =>
      -- If there is no value, we do not need to return a value
      traceAide `leanaide.papercodes.info s!"codegen: No value in 'let_statement' for {js.getObjValAs? String "variable_name" |>.toOption.getD ""}"
      addPrelude statement
      return none
    | .ok value =>
      match goal? with
      | some goal =>
        match (← goal.getType).app2? ``Exists with
        | some (_, .lam _ _ _ _) =>
            traceAide `leanaide.papercodes.info s!"goal is a there exists statement, not in leanaide-core"
            throwError s!"codegen: 'let_statement' with exists goal is not supported in leanaide-core; goal type: {← ppExpr (← goal.getType)}"
        | _ => pure ()
      | none => pure ()
      let letStx ←
        commandToTactic
          (← defStx translator js statement value)
      let stxs := #[letStx]
      addPrelude statement
      return some <| ← `(tacticSeq| $stxs*)
  | ``commandSeq, js => do
    let statement := statement js
    match js.getObjValAs? String "value" with
    | .error _ =>
      -- If there is no value, we do not need to return a value
      traceAide `leanaide.papercodes.info s!"codegen: No value in 'let_statement' for {js.getObjValAs? String "variable_name" |>.toOption.getD ""}"
      addPrelude statement
      return none
    | .ok value =>
      let defStx ←
          defStx translator js statement value
      let stxs := #[defStx]
      match ← DefData.ofSyntax? defStx with
      | some data =>
        -- If we have a definition, we add it to the definitions
        -- and return the command
        addDefn data
      | none =>
        traceAide `leanaide.papercodes.info s!"codegen: No definition found for 'let_statement' {statement} with value {value}"
      addPrelude statement
      return some <| ← `(commandSeq| $stxs*)

  | _, js =>
      addPrelude <| statement js
      return none
  where
    statement (js: Json) : String :=
      match js.getObjValAs? String "statement" with
      | Except.ok s => s
      | Except.error _ =>
        let varSegment := match js.getObjValAs? String "variable_name" with
        | .ok "<anonymous>" => "We have "
        | .ok v => s!"Let {v} be"
        | .error _ => "We have "
        let kindSegment := match js.getObjValAs? String "variable_type" with
          | .ok k => s!"a {k}"
          | .error _ => s!""
        let valueSegment := match js.getObjValAs? String "value" with
          | .ok v => s!"{v}"
          | .error _ => ""
        let propertySegment := match js.getObjValAs? String "properties", js.getObjValAs? String "variable_name" with
          | .ok p, .ok v =>
            if v != "<anonymous>"
              then s!"(such that) ({v} is) {p}"
              else s!"(such that) {p}"
          | _, _ => ""
        s!"{varSegment} {kindSegment} {valueSegment} {propertySegment}".trimAscii.toString ++ "."
    defStx (translator: CodeGenerator) (js: Json) (statement: String)  (value: String) : TranslateM Syntax.Command :=
      withoutModifyingState do
        let statement' ← withPreludes statement
        let varName ← match js.getObjValAs? String "variable_name" with
        | .ok "<anonymous>" => pure "_"
        | .ok v => pure v
        | .error _ => throwError s!"codegen: no 'variable_name' found in 'let_statement' for {js}"
        let statement' := statement'.trimAscii.toString ++ "\n" ++ s!"Define ONLY the term {varName} with value {value}. Other terms have been defined already."

        let stx? ← translator.translateDefCmdM? statement'
        match stx? with
        | .ok stx =>
          traceAide `leanaide.papercodes.info s!"codegen: 'let_statement' {statement'} translated to command:\n{← PrettyPrinter.ppCommand stx}"
          return stx
        | .error es =>
          let fallback ← try
            CmdElabError.fallback es
          catch _ =>
            traceAide `leanaide.papercodes.info s!"codegen: 'let_statement' {statement'} fallback failed"
            let output := es.map fun e => e.text
            throwError
              s!"codegen: no fallback for 'let_statement' {statement'}; output: {output} "
          match Parser.runParserCategory (← getEnv) `command fallback with
          | .ok stx =>
            let stx: Syntax.Command := ⟨stx⟩
            return stx
          |.error er =>
            traceAide `leanaide.papercodes.info s!"codegen: 'let_statement' {statement'} translation failed with error:\n{er} and fallback:\n{fallback}"
            traceAide `leanaide.papercodes.info s!"codegen: 'let_statement' {statement'} translation attempts:\n"
            for e in es do
              traceAide `leanaide.papercodes.info s!"codegen: not a command:\n{e.text}"
            throwError
              s!"codegen: no definition translation found for {statement'}"

/--
Add code for a "some" statement. This is used to introduce a variable with some properties, such as "there exists an integer `n` such that ...". The code is generated as an assertion statement, which is a claim that the variable exists with the given properties.
-/
@[codegen "some_statement"]
def someCode (translator : CodeGenerator := {})(goal : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| kind, js => do
  let statement :=
    match js.getObjValAs? String "statement" with
    | Except.ok s => s
    | Except.error _ =>
      let varSegment := match js.getObjValAs? String "variable_name" with
      | .ok "<anonymous>" => "We have "
      | .ok v => s!"Let {v} be"
      | .error _ => "We have "
    let kindSegment := match js.getObjValAs? String "variable_kind" with
      | .ok k => s!"a {k}"
      | .error _ => s!""
    let propertySegment := match js.getObjValAs? String "properties" with
      | .ok p => s!"(such that) {p}"
      | .error _ => ""
    s!"{varSegment} {kindSegment} {propertySegment}".trimAscii.toString ++ "."
  let assJs := Json.mkObj [
    ("type", "assert_statement"),
    ("claim", .str statement)
  ]
  addPrelude statement
  getCode translator goal kind assJs


/--
Generate code for an `assume_statement`. This is used to add an assumption to the proof or logical context. It simply adds a prelude statement with the assumption text.
-/
@[codegen "assume_statement"]
def assumeCode (_ : CodeGenerator := {})(_ : Option (MVarId)) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, js => do
  let .ok statement :=
      js.getObjValAs? String "assumption" | throwError "No 'assumption' found in 'assume_statement'"
  addPrelude <| "Assume that: " ++ statement
  addVarPrelude statement
  return none


/--
Code generation for an `assert_statement`. This is used to assert a mathematical claim that follows from known results. It can generate a command, command sequence, or tactic sequence depending on the kind specified.

If the assertion involves existential quantification, additional handling is done to introduce the variable and its properties.
-/
@[codegen "assert_statement"]
def assertionCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `command, js => do
  let (stx, tac, _) ← typeStx js
  `(command| example : $stx := by $tac)
| _, `commandSeq, js => do
  let (stx, tac, isProp) ← typeStx js
  let hash₀ := hash ((← ppTerm {env := ← getEnv} stx).pretty)
  let name := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
  let head ← `(command| theorem $name : $stx := by $tac)
  let dfn: DefData :=
    { name := "assert_{hash₀}".toName, type := stx, value := stx, isProp := isProp, isNoncomputable := true, doc? := none}
  addDefn dfn
  let resolvedCmds ←
    cmdResolveExistsHave stx
  mkCommandSeq <| #[head] ++ resolvedCmds
| _, ``tacticSeq, js => do
  let (stx, tac, _) ← typeStx js
  let hash₀ := hash ((← ppTerm {env := ← getEnv} stx).pretty)
  let name := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
  let headTac ← `(tactic| have $name : $stx := by $tac)
  traceAide `leanaide.papercodes.info s!"codegen: assertionCode: headTac: {← PrettyPrinter.ppTactic headTac}"
  let resTacs ← resolveExistsHave stx
  traceAide `leanaide.papercodes.info s!"codegen: assertionCode: resolved exists have tactics (size {resTacs.size})"
  let tacSeq := #[headTac] ++ resTacs
  `(tacticSeq| $tacSeq*)
| _, `tactic, js => do
  let (stx, tac, _) ← typeStx js
  `(tactic| have : $stx := by $tac)
| _, kind, _ => throwError
    s!"codegen: test does not work for kind {kind}"
where typeStx (js: Json) :
    TranslateM <| Syntax.Term × (TSyntax ``tacticSeq) × Bool :=
      withoutModifyingState do
  let .ok  claim := js.getObjValAs? String "claim" | throwError
    s!"codegen: no claim found in 'assertion_statement'"
  let deducedFrom? := js.getObjValAs? (Array Json) "deduced_from_theorem" |>.toOption
  let mut deductionHaves : Array Syntax.Tactic := #[]
  match deducedFrom? with
  | .some deducedFrom =>
    for data in deducedFrom do
      let thmLabel := data.getObjValAs? String "name" |>.toOption.getD "thm_used"
      let leanTerm? := match data.getObjValAs? String "lean_term" with
      | .ok t => some t
      | .error _ =>
        match data.getObjValAs? String "lean_name" with
        | .ok n => some n
        | .error _ => none
      match leanTerm? with
      | some leanTerm =>
        let termStx := Parser.runParserCategory (← getEnv) `term leanTerm
        match termStx with
        | .ok stx =>
          try
            let stx : TSyntax `term := ⟨stx⟩
            withoutErrToSorry do
              let _ ← elabTerm stx none
              Term.synthesizeSyntheticMVarsNoPostponing
            let haveTac ←
            match data.getObjValAs? String "name" with
            | .ok name =>
              let nameStx := mkIdent name.toName
              `(tactic| have $nameStx : $stx := by apply $stx)
            | .error _ =>
              `(tactic| have : $stx := by apply $stx)
            deductionHaves := deductionHaves.push haveTac
          catch e =>
            traceAide `leanaide.papercodes.info s!"codegen: failed to create have tactic for 'lean_term' {leanTerm} for theorem {thmLabel} with error:\n{← e.toMessageData.format}"
        | .error er =>
          traceAide `leanaide.papercodes.info s!"codegen: failed to parse 'lean_term' {leanTerm} for theorem {thmLabel} with error:\n{er}"
      | none =>
        traceAide `leanaide.papercodes.info s!"codegen: no 'lean_term' or 'lean_name' found for theorem {thmLabel} used in deduction of assertion"
  | none => pure ()
  let type ← translator.translateToPropStrict claim
  let mvar ← mkFreshExprMVar type
  let some mvarId ← runForSingleGoal mvar.mvarId! (← `(tacticSeq| $deductionHaves*)) | throwError
    s!"codegen: failed to apply deduction theorems for assertion; deduction tactics:\n{deductionHaves}"
  let tacs ← findTacticsI mvarId
  addPrelude <| "Assume: " ++ claim
  return (← delabDetailed type, ← `(tacticSeq| $tacs*), ← isProp type)

/--
Generate code for a non-destructive specialization of an already proved claim.
This creates a new local lemma with `have name := lean_term`, keeping the
original general claim available in the local context.
-/
@[codegen "specialize"]
def specializeCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, ``tacticSeq, js => do
  let tac ← specializeTactic js
  let tacs := #[tac]
  `(tacticSeq| $tacs*)
| _, `tactic, js => do
  specializeTactic js
| _, kind, _ => throwError
    s!"codegen: specialize does not work for kind {kind}; it must be used inside a proof"
where
  specializeTactic (js: Json) : TranslateM (TSyntax `tactic) := do
    let .ok name := js.getObjValAs? Name "name" | throwError
      s!"codegen: no 'name' found in 'specialize'"
    let .ok leanTerm := js.getObjValAs? String "lean_term" | throwError
      s!"codegen: no 'lean_term' found in 'specialize'"
    let .ok termStx := Parser.runParserCategory (← getEnv) `term leanTerm |
      throwError s!"codegen: failed to parse 'lean_term' as a term: {leanTerm}"
    let termStx : TSyntax `term := ⟨termStx⟩
    let nameStx := mkIdent name
    match js.getObjValAs? String "claim" with
    | .ok claim =>
        let type ← translator.translateToPropStrict claim
        let typeStx ← delabDetailed type
        `(tactic| have $nameStx : $typeStx := $termStx)
    | .error _ =>
        `(tactic| have $nameStx := $termStx)

/--
Generate code for a `calculation` step. This can either be a single inline calculation or a sequence of calculations. If the `inline_calculation` is provided, it generates a tactic that asserts the calculation. If `calculation_sequence` is provided, it generates a sequence of tactics for each step in the calculation.
-/
@[codegen "calculation"]
def calculationCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, ``tacticSeq, js => do
  let tac ← `(tacticSeq | first | grind | simp | rfl)
  match js.getObjVal? "inline_calculation" with
  | Except.ok <| .str inline =>
    let stx ← typeStx inline
    let hash₀ := hash ((← ppTerm {env := ← getEnv} stx).pretty)
    let name := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
    let headTac ← `(tactic| have $name : $stx := by $tac)
    let tacSeq := #[headTac]
    `(tacticSeq| $tacSeq*)
  | Except.ok js =>
    throwError
      s!"codegen: 'calculation' must have 'inline_calculation' as a string, got {js}"
  | Except.error _ =>
    let .ok steps := js.getObjValAs? (Array String) "calculation_sequence" | throwError
      s!"codegen: no 'calculation_sequence' found in 'calculation'"
    let mut tacs : Array <| Syntax.Tactic := #[]
    for step in steps do
      let stx ← typeStx step
      let hash₀ := hash ((← ppTerm {env := ← getEnv} stx).pretty)
      let name := mkIdent <| Name.mkSimple s!"assert_{hash₀}"
      let headTac ← `(tactic| have $name : $stx := by $tac)
      tacs := tacs.push headTac
    `(tacticSeq| $tacs*)
| _, kind, _ => throwError
    s!"codegen: test does not work for kind {kind}"
where typeStx (eqn: String) :
    TranslateM <| Syntax.Term  := do
  let claim := "Have " ++ eqn ++ "."
  let type ← translator.translateToPropStrict claim
  delabDetailed type


open Lean.Parser.Term CodeGenerator Parser
/--
Generate code for a `pattern_cases_proof`. This is used to perform a proof by cases based on matching patterns against a given expression. It generates a `match` tactic with the specified patterns and their corresponding proofs.
-/
@[codegen "pattern_cases_proof"]
def patternCasesCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok discr := js.getObjValAs? String "on" | throwError
    s!"codegen: no 'on' found in 'pattern_cases_proof'"
  let .ok patternCases := js.getObjValAs? (Array Json) "proof_cases" | throwError
    s!"codegen: no 'proof_cases' found in 'pattern_cases_proof'"
  let pats := patternCases.filterMap fun
    case =>
      case.getObjValAs? String "pattern" |>.toOption
  let proofData := patternCases.filterMap fun
    case =>
      case.getObjValAs? Json "proof" |>.toOption
  let mut alts : Array <| TSyntax ``matchAltTac := #[]
  let mut patTerms : Array Syntax.Term := #[]
  for pat in pats do
    let patTerm :=
      runParserCategory (← getEnv) `term pat |>.toOption.getD (← `(_))
    let patTerm' : Syntax.Term := ⟨patTerm⟩
    patTerms := patTerms.push patTerm'
    let m ← `(matchAltTac| | $patTerm' => _)
    alts := alts.push m
  let alts' : Array <| TSyntax ``matchAlt := alts.map fun alt => ⟨alt⟩
  let discrTerm :=
    runParserCategory (← getEnv) `term discr |>.toOption.getD (← `(_))
  let discrTerm' : Syntax.Term := ⟨discrTerm⟩
  let hash := hash discrTerm.reprint
  let c := mkIdent <| ("c" ++ s!"_{hash}").toName
  let tac ← `(tactic| match $c:ident : $discrTerm':term with $alts':matchAlt*)
  let newGoals ←
    runAndGetMVars goal #[tac] proofData.size
  let proofStxs ← proofData.zip newGoals.toArray |>.mapM fun (proof, newGoal) => do
    let some proofStx ← withoutModifyingState do
      newGoal.withContext do
      getProof translator newGoal proof |
      throwError s!"codegen: no translation found for {proof}"
    return proofStx
  let mut provedAlts : Array <| TSyntax ``matchAltTac := #[]
  for (patTerm, pf) in patTerms.zip proofStxs do
    let m ← `(matchAltTac| | $patTerm => $pf)
    provedAlts := provedAlts.push m
  let alts' : Array <| TSyntax ``matchAlt := provedAlts.map fun alt => ⟨alt⟩
  let c := mkIdent <| ("c" ++ s!"_{hash}").toName
  `(tacticSeq| match $c:ident : $discrTerm':term with $alts':matchAlt*)

| goal?, kind ,_ => throwError
    s!"codegen: biequivalenceCode does not work for kind {kind} with goal present: {goal?.isSome}"

@[codegen "pattern_cases_proof"]
def patternCasesViaMulti (translator : CodeGenerator := {}) (goal : Option MVarId) : (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| kind, js => do
  let .ok on := js.getObjValAs? String "on" | throwError
    s!"codegen: no 'on' found in 'pattern_cases_proof'"
  let .ok patternCases := js.getObjValAs? (Array Json) "proof_cases" | throwError
    s!"codegen: no 'proof_cases' found in 'pattern_cases_proof'"
  -- convert each `pattern_case` into `condition_case`
  let conditionCasesArray ← patternCases.mapM fun
    pattern_case_js => do
      let .ok pattern := pattern_case_js.getObjValAs? String "pattern" | throwError
        s!"codegen : no 'pattern' found in 'pattern_case'"
      let .ok proof := pattern_case_js.getObjValAs? Json "proof" | throwError
        s!"codegen : no 'proof' found in 'pattern_case'"
      pure (pattern, proof)
  let conditionCases := conditionCasesArray.map fun
    (pattern, proof) =>
      Json.mkObj [
        ("type", "condition_case"),
        ("condition", .str s!"{on} = {pattern}"),
        ("proof", proof)
      ]
  let multicondJs := Json.mkObj [
    ("type", "multi-condition_cases_proof"),
    ("proof_cases", .arr conditionCases)
  ]
  getCode translator goal kind multicondJs

/--
Generate code for a `bi-implication_cases_proof`. This is used to prove a bi-implication `P ↔ Q` by proving both directions: `P → Q` and `Q → P`. It recursively generates a sequence of tactics that handle both implications.
-/
@[codegen "bi-implication_cases_proof"]
def biequivalenceCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok ifProof := js.getObjValAs? Json "if_proof" | throwError
    s!"codegen: no 'if_proof' found in 'bi-implication_cases_proof'"
  let .ok onlyIfProof := js.getObjValAs? Json "only_if_proof" | throwError
    s!"codegen: no 'only_if_proof' found in 'bi-implication_cases_proof'"
  let tac ← `(tactic|constructor)
  let [ifGoal, onlyIfGoal] ←
    runAndGetMVars goal #[tac] 2 | throwError "codegen: in 'biequivalenceCode' `constructor` failed to get two goals; goal: {← ppExpr <| ← goal.getType}"
  let some ifProofStx ← withoutModifyingState do getProof translator ifGoal ifProof | throwError
    s!"codegen: no translation found for if_proof {ifProof}"
  let some onlyIfProofStx ← withoutModifyingState do getProof translator onlyIfGoal onlyIfProof | throwError
    s!"codegen: no translation found for only_if_proof {onlyIfProof}"
  let tacs := #[tac, ← `(tactic| · $ifProofStx), ← `(tactic| · $onlyIfProofStx)]
  `(tacticSeq| $tacs*)
| goal?, kind ,_ => throwError
    s!"codegen: biequivalenceCode does not work for kind {kind} with goal present: {goal?.isSome}"

/--
Generate code for a `condition_cases_proof`. This is used to prove a statement by splitting into two cases based on a condition. It generates an `if ... then ... else ...` tactic with the provided proofs for each case.
-/
@[codegen "condition_cases_proof"]
def conditionCasesCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok condition := js.getObjValAs? String "condition" | throwError
    s!"codegen: no 'condition' found in 'condition_cases_proof'"
  let conditionType ← translator.translateToPropStrict condition
  let conditionStx ← delabDetailed conditionType
  let fmt ← ppTerm {env := ← getEnv} conditionStx
  let hash₀ := hash (fmt.pretty)
  let conditionId := mkIdent <| Name.mkSimple s!"condition_{hash₀}"
  let conditionBinder ←
    `(Lean.binderIdent| $conditionId:ident)
  let tac ← `(tactic|if $conditionBinder:binderIdent : $conditionStx then ?_ else ?_)
  let [thenGoal, elseGoal] ←
    runAndGetMVars goal #[tac] 2 | throwError "codegen:  `if _ then _ else _` failed to get two goals, goal: {← ppExpr <| ← goal.getType}"
  let resolution ←
    resolveExistsHave conditionStx conditionId
  let .ok trueCaseProof := js.getObjValAs? Json "true_case_proof" | throwError
    s!"codegen: no 'true_case_proof' found in 'condition_cases_proof'"
  let .ok falseCaseProof := js.getObjValAs? Json "false_case_proof" | throwError
    s!"codegen: no 'false_case_proof' found in 'condition_cases_proof'"
  let thenGoal ← if resolution.isEmpty then
    pure thenGoal
  else
    let [goal] ← runAndGetMVars thenGoal resolution 1 | throwError
      s!"codegen: have tactics resolving exact failed to get one goal, goal: {← ppExpr <| ← thenGoal.getType}"
    pure goal
  let some trueCaseProofStx ← withoutModifyingState do getProof translator thenGoal trueCaseProof | throwError
    s!"codegen: no translation found for true_case_proof {trueCaseProof}"
  let trueCaseProofStx ← if resolution.isEmpty then
    pure trueCaseProofStx
  else
    appendTacticSeqSeq
      (← `(tacticSeq| $resolution*)) trueCaseProofStx
  let some falseCaseProofStx ← withoutModifyingState do getProof translator elseGoal falseCaseProof | throwError
    s!"codegen: no translation found for false_case_proof {falseCaseProof}"
  let fmt ← ppTerm {env := ← getEnv} conditionStx
  let hash := hash fmt.pretty
  let conditionId := mkIdent <| ("condition" ++ s!"_{hash}").toName
  let conditionBinder ←
    `(Lean.binderIdent| $conditionId:ident)
  let tacs := #[← `(tactic| if $conditionBinder :  $conditionStx then $trueCaseProofStx else $falseCaseProofStx), ← `(tactic| done)]
  `(tacticSeq| $tacs*)
| goal?, kind ,_ => throwError
    s!"codegen: conditionCasesCode does not work for kind {kind} with goal present: {goal?.isSome}"

/--
Generate code for a multi-condition cases statement. This is used to handle proofs that involve multiple conditions, where each condition leads to a different case in the proof. It recursively generates tactics for each condition and its corresponding proof.
-/
def multiConditionCasesAux (translator : CodeGenerator := {}) (goal: MVarId) (cases : List (Expr ×Json)) (exhaustiveness: Option <| Syntax.Tactic) : TranslateM (TSyntax ``tacticSeq) := match cases with
  | [] => goal.withContext do
    let pf ← findTacticsI goal
    let pf := match exhaustiveness with
      | some e => #[e] ++ pf
      | none => pf
    `(tacticSeq| $pf*)
  | (conditionType, trueCaseProof) :: tail => goal.withContext do
    traceAide `leanaide.papercodes.info s!"number of cases (remaining): {tail.length + 1}"
    let conditionStx ← delabDetailed conditionType
    let fmt ← ppTerm {env := ← getEnv} conditionStx
    let hash₀ := hash fmt.pretty
    let conditionId := mkIdent <| Name.mkSimple s!"condition_{hash₀}"
    let conditionBinder ←
      `(Lean.binderIdent| $conditionId:ident)
    let tac ← `(tactic|if $conditionBinder : $conditionStx then ?_ else ?_)
    let [thenGoal, elseGoal] ←
      runAndGetMVars goal #[tac] 2 | throwError "codegen:  `if _ then _ else _` failed to get two goals, goal: {← ppExpr <| ← goal.getType}"
    let resolution ←
      resolveExistsHave conditionStx conditionId
    let thenGoal ← if resolution.isEmpty then
      pure thenGoal
    else
      let [goal] ← runAndGetMVars thenGoal resolution 1 | throwError
        s!"codegen: have tactics resolving exact failed to get one goal, goal: {← ppExpr <| ← thenGoal.getType}"
      pure goal
    let some trueCaseProofStx ← withoutModifyingState do getProof translator thenGoal trueCaseProof | throwError
      s!"codegen: no translation found for true_case_proof {trueCaseProof}"
    traceAide `leanaide.papercodes.info s!"true case proof tactics: {← PrettyPrinter.ppTerm <| ←  `(by $trueCaseProofStx)}"
    let trueCaseProofStx ← if resolution.isEmpty then
      pure trueCaseProofStx
    else
      appendTacticSeqSeq
        (← `(tacticSeq| $resolution*)) trueCaseProofStx
    traceAide `leanaide.papercodes.info s!"true case proof tactics: {← PrettyPrinter.ppTerm <| ←  `(by $trueCaseProofStx)}"
    let falseCaseProofStx ←
      multiConditionCasesAux translator elseGoal tail exhaustiveness
    let fmt ← ppTerm {env := ← getEnv} conditionStx
    let hash := hash fmt.pretty
    let conditionId := mkIdent <| ("condition" ++ s!"_{hash}").toName
    let conditionBinder ←
      `(Lean.binderIdent| $conditionId:ident)
    let tacs := #[← `(tactic| if $conditionBinder :  $conditionStx then $trueCaseProofStx else $falseCaseProofStx)]
    `(tacticSeq| $tacs*)

/--
Generate code for a multi-condition cases statement. This is used to handle proofs that involve multiple conditions, where each condition leads to a different case in the proof. It recursively generates tactics for each condition and its corresponding proof.
-/
@[codegen "multi-condition_cases_proof"]
def multiConditionCasesCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok proofCases := js.getObjValAs? (List Json) "proof_cases" | throwError
    s!"codegen: no 'proof_cases' found in 'multi-condition_cases_proof'"
  let exhaustiveness? := js.getObjValAs? Json "exhaustiveness" |>.toOption
  let exhaustiveness? := exhaustiveness?.filter fun js => js != .null
  let cases ←  proofCases.mapM fun
    c => do
      let .ok condition := c.getObjValAs? String "condition" | throwError
        s!"codegen: no 'condition' found in 'condition_case'"
      let conditionType ← translator.translateToPropStrict condition
      let .ok proof := c.getObjValAs? Json "proof" | throwError
        s!"codegen: no 'proof' found in 'condition_case'"
      pure (conditionType, proof)
  let exhaustiveTac : Option <| Syntax.Tactic ←
    exhaustiveness?.mapM fun
      e => do
        let conds := cases.map (·.1)
        let exhaustGoalType ←
          orAllWithGoal conds (← goal.getType)
        let exhaustGoalStx ← delabDetailed exhaustGoalType
        let fmt ← ppTerm {env := ← getEnv} exhaustGoalStx
        let hash := hash fmt.pretty
        let exhaustId := mkIdent <| ("exhaust" ++ s!"_{hash}").toName
        let exhaustGoalExpr ← mkFreshExprMVar
          exhaustGoalType
        let exhaustGoal := exhaustGoalExpr.mvarId!
        let some pfStx ← withoutModifyingState do getProof translator exhaustGoal e | throwError
          s!"codegen: no translation found for exhaustiveness {e}"
        `(tactic| have $exhaustId : $exhaustGoalStx := by $pfStx)
  traceAide `leanaide.papercodes.info s!"number of cases (after exhaustiveness): {cases.length}"
  let tacs ← multiConditionCasesAux translator goal cases exhaustiveTac
  appendTacticSeqSeq tacs <| ← `(tacticSeq| done)
| goal?, kind ,_ => throwError
    s!"codegen: conditionCasesCode does not work for kind {kind} with goal present: {goal?.isSome}"

/--
Generate code for an `induction_proof`. This is used to perform a proof by induction on a variable or expression. It generates an `induction` tactic with the specified base case and induction step proofs.
-/
@[codegen "induction_proof"]
def inductionCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok discr := js.getObjValAs? String "on" | throwError
    s!"codegen: no 'on' found in 'induction_proof'"
  let discrTerm' :=
    runParserCategory (← getEnv) `term discr |>.toOption.getD (← `(sorry))
        let succId := mkIdent `succ
  let ihId := mkIdent `ih
  let discrTerm : Syntax.Term := ⟨discrTerm'⟩
  let discrTerm' ← `(elimTarget| $discrTerm:term)
  let discrTerm'' : TSyntax ``elimTarget := ⟨discrTerm'⟩
  let zeroId := mkIdent `zero
  let prevVar := js.getObjValAs? String "prev_var" |>.toOption |>.getD discr
  let prevVarId :=  mkIdent <| prevVar.toName
  let tac ← `(tactic|
    induction $discrTerm'' with
    | $zeroId => _
    | $succId:ident $prevVarId:ident $ihId:ident => _)

  let [baseGoal, stepGoal] ←
    runAndGetMVars goal #[tac] 2 | throwError s!"codegen: induction failed to get two goals, goal: {← ppExpr <| ← goal.getType}"
  let .ok baseCaseProof := js.getObjVal? "base_case_proof" | throwError
    s!"codegen: no true_case_proof found in {js}"
  let .ok inductionStepProof := js.getObjValAs? Json "induction_step_proof" | throwError
    s!"codegen: no false_case_proof found in {js}"
  let some baseCaseProofStx ←
    withoutModifyingState do
    baseGoal.withContext do
    getProof translator baseGoal baseCaseProof | throwError
    s!"codegen: no translation found for base_case_proof {baseCaseProof}"
  traceAide `leanaide.papercodes.info s!"codegen: base case proof tactics: {← PrettyPrinter.ppTerm <| ←  `(by $baseCaseProofStx)}"
  let some inductionStepProofStx ←
    withoutModifyingState do
    stepGoal.withContext do
    getProof translator stepGoal inductionStepProof | throwError
    s!"codegen: no translation found for induction_step_proof {inductionStepProof}"
  let tacs := #[← `(tactic|
    induction $discrTerm'' with
    | $zeroId => $baseCaseProofStx
    | $succId:ident $prevVarId:ident $ihId:ident => $inductionStepProofStx), ← `(tactic| done)]
  `(tacticSeq| $tacs*)
| goal?, kind ,_ => throwError
    s!"codegen: induction does not work for kind {kind} with goal present: {goal?.isSome}"

/--
Generate code for a `contradiction_statement`. This is used to prove a statement by contradiction, where an assumption leads to a contradiction. It generates a tactic that introduces the assumption and then provides the proof of the contradiction.
-/
@[codegen "contradiction_statement"]
def contradictCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, ``tacticSeq, js => do
  let .ok assumptionText := js.getObjValAs? String "assumption" | throwError
    s!"codegen: no 'assumption' found in 'contradiction_statement'"
  let assumptionType ← translator.translateToPropStrict assumptionText
  let goalType ← mkArrow assumptionType (mkConst ``False)
  let goalExpr ←  mkFreshExprMVar goalType
  let fullGoal := goalExpr.mvarId!
  let contraId := mkIdent `contraHyp
  let [goal] ← runAndGetMVars fullGoal #[← `(tactic| intro $contraId:term)] 1 | throwError
    s!"codegen: contradiction_statement failed to get goal, goalType: {← ppExpr <| goalType}"
  let .ok proof := js.getObjValAs? Json "proof" | throwError
    s!"codegen: no 'proof' found in 'contradiction_statement'"
  let some tacs ← withoutModifyingState do getProof translator goal proof | throwError
    s!"codegen: no tactics found for proof {proof}"
  let fullTacs ←  appendTacticSeqSeq (← `(tacticSeq| intro $contraId:term)) tacs
  let stx ← delabDetailed goalType
  `(tacticSeq| have : $stx := by $fullTacs)
| _, kind, _ => throwError
    s!"codegen: conclude_statement does not work for kind {kind}"

/- contrapositive_proof
{
  "type": "object",
  "description": "A proof by contrapositive.",
  "properties": {
    "type": {
      "type": "string",
      "const": "contrapositive_proof",
      "description": "The type of this logical step."
    },
    "assumption": {
      "type": "string",
      "description": "The negated conclusion or contrapositive assumption."
    },
    "proof": {
      "$ref": "#/$defs/Proof",
      "description": "The proof deriving the negated hypothesis from the contrapositive assumption."
    },
    "conclusion": {
      "type": "string",
      "description": "(OPTIONAL) The final contrapositive conclusion, usually the negated hypothesis."
    }
  },
  "required": [
    "type",
    "assumption",
    "proof"
  ],
  "additionalProperties": false
}
-/

/--
Generate code for a `contrapositive_proof`. If the JSON contains a
`conclusion`, this first proves the contrapositive implication
`assumption → conclusion`, then lets automation close the original goal from
that contrapositive form. Without `conclusion`, it falls back to a direct
`Classical.byContradiction` proof of the current goal.
-/
@[codegen "contrapositive_proof"]
def contrapositiveProofCode (translator : CodeGenerator := {}) :
    Option MVarId → (kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok assumptionText := js.getObjValAs? String "assumption" | throwError
    s!"codegen: no 'assumption' found in 'contrapositive_proof'"
  let .ok proof := js.getObjValAs? Json "proof" | throwError
    s!"codegen: no 'proof' found in 'contrapositive_proof'"
  let assumptionType ← translator.translateToPropStrict assumptionText
  let contraId := mkIdent `contraHyp
  match js.getObjValAs? String "conclusion" with
  | .ok conclusionText =>
      let conclusionType ← translator.translateToPropStrict conclusionText
      let contraType ← mkArrow assumptionType conclusionType
      let contraGoalExpr ← mkFreshExprMVar contraType
      let contraGoal := contraGoalExpr.mvarId!
      let [proofGoal] ← runAndGetMVars contraGoal #[← `(tactic| intro $contraId:term)] 1 | throwError
        s!"codegen: contrapositive_proof failed to introduce assumption; contrapositive type: {← ppExpr contraType}"
      let some proofStx ← withoutModifyingState do
        getProof translator proofGoal proof | throwError
        s!"codegen: no tactics found for contrapositive proof {proof}"
      let fullProof ← appendTacticSeqSeq (← `(tacticSeq| intro $contraId:term)) proofStx
      let contraTypeStx ← delabDetailed contraType
      let contraName := mkIdent `contrapositiveHyp
      `(tacticSeq|
        have $contraName : $contraTypeStx := by
          $fullProof
        grind)
  | .error _ =>
      let contraTacs ← `(tacticSeq|
        apply Classical.byContradiction
        intro $contraId:term)
      let [proofGoal] ← runAndGetMVars goal #[← `(tactic| apply Classical.byContradiction), ← `(tactic| intro $contraId:term)] 1 | throwError
        s!"codegen: contrapositive_proof failed to introduce contrapositive assumption; goal: {← ppExpr <| ← goal.getType}"
      let some proofStx ← withoutModifyingState do
        getProof translator proofGoal proof | throwError
        s!"codegen: no tactics found for contrapositive proof {proof}"
      appendTacticSeqSeq contraTacs proofStx
| goal?, kind, _ => throwError
    s!"codegen: contrapositive_proof does not work for kind {kind} where goal present: {goal?.isSome}"


/--
Generate code for a `conclude_statement`. This is used to conclude a proof with a final claim. It generates a tactic that asserts the claim as a theorem or lemma.
-/
@[codegen "conclude_statement"]
def concludeCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, ``tacticSeq, js => do
  let type ←
    match js.getObjValAs? String "claim" with
    | .ok claim =>
      let claim := "We have: " ++ claim
      translator.translateToPropStrict claim
    | .error _ =>
      goal.getType
  let stx ← delabDetailed type
  let mvar ← mkFreshExprMVar type
  let pf ← findTacticsI mvar.mvarId!
  `(tacticSeq| have : $stx := by $pf*)
| none, ``tacticSeq, _ => do return none
| _, kind, _ => throwError
    s!"codegen: conclude_statement does not work for kind {kind}"

/--
Generate code for a `general_induction_proof`. This is used to perform a proof by induction with multiple conditions, where each condition leads to a different case in the proof. It recursively generates tactics for each condition and its corresponding proof.
-/
def generalInductionAux (translator : CodeGenerator := {}) (goal: MVarId) (cases : List (Expr ×Json × (Array String))) (inductionNames: Array Name)  : TranslateM (TSyntax ``tacticSeq) := match cases with
  | [] => goal.withContext do
    let pf ← findTacticsI goal
    `(tacticSeq| $pf*)
  | (conditionType, trueCaseProof, inductionHyps) :: tail => goal.withContext do
    traceAide `leanaide.papercodes.info s!"number of cases (remaining): {tail.length + 1}"
    for hyp in inductionHyps do
      addPrelude <| s!"Assume (inductively): {hyp}"
    let conditionStx ← delabDetailed conditionType
    let fmt ← ppTerm {env := ← getEnv} conditionStx
    let hash₀ := hash fmt.pretty
    let conditionId := mkIdent <| Name.mkSimple s!"condition_{hash₀}"
    let conditionBinder ←
      `(Lean.binderIdent| $conditionId:ident)
    let tac ← `(tactic|if $conditionBinder : $conditionStx then ?_ else ?_)
    let [thenGoal, elseGoal] ←
      runAndGetMVars goal #[tac] 2 | throwError "codegen:  `if _ then _ else _` failed to get two goals, goal: {← ppExpr <| ← goal.getType}"
    let resolution ←
      resolveExistsHave conditionStx conditionId
    let thenGoal ← if resolution.isEmpty then
      pure thenGoal
    else
      let [goal] ← runAndGetMVars thenGoal resolution 1 | throwError
        s!"codegen: have tactics resolving exact failed to get one goal, goal: {← ppExpr <| ← thenGoal.getType}"
      pure goal
    let some trueCaseProofStx ← withoutModifyingState do getProof translator thenGoal trueCaseProof | throwError
      s!"codegen: no translation found for true_case_proof {trueCaseProof}"
    let trueCaseProofStx ← if resolution.isEmpty then
      pure trueCaseProofStx
    else
      appendTacticSeqSeq
        (← `(tacticSeq| $resolution*)) trueCaseProofStx
    let falseCaseProofStx ←
      generalInductionAux translator elseGoal tail inductionNames
    let fmt ← ppTerm {env := ← getEnv} conditionStx
    let hash := hash fmt.pretty
    let conditionId := mkIdent <| ("condition" ++ s!"_{hash}").toName
    let conditionBinder ←
      `(Lean.binderIdent| $conditionId:ident)
    let tacs := #[← `(tactic| if $conditionBinder :  $conditionStx then $trueCaseProofStx else $falseCaseProofStx)]
    `(tacticSeq| $tacs*)

/--
Generate code for a `general_induction_proof`. This is used to perform a proof by induction with multiple conditions, where each condition leads to a different case in the proof. It recursively generates tactics for each condition and its corresponding proof.
-/
@[codegen "general_induction_proof"]
def generalInductionCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal, ``tacticSeq, js => goal.withContext do
  let .ok proofCases := js.getObjValAs? (List Json) "proof_cases" | throwError
    s!"codegen: no 'proof_cases' found in 'multi-condition_cases_proof'"
  let .ok inductionPrinciple :=  js.getObjValAs? String "induction_principle" | throwError
    s!"codegen: no 'induction_principle' found in 'general_induction_proof'"
  let inductionPrincipleNames ← Translator.matchingTheorems inductionPrinciple (qp := translator)
  let cases ←  proofCases.mapM fun
    c => do
      let .ok condition := c.getObjValAs? String "condition" | throwError
        s!"codegen: no 'condition' found in 'condition_case'"
      let conditionType ← translator.translateToPropStrict condition
      let .ok proof := c.getObjValAs? Json "proof" | throwError
        s!"codegen: no 'proof' found in 'condition_case'"
      let inductionHyps := (c.getObjValAs? (Array String) "induction_hyps" |>.toOption |>.orElse fun _ =>  c.getObjValAs? (Array String) "induction_hypotheses" |>.toOption).getD #[]
      pure (conditionType, proof, inductionHyps)
  let tacs ← generalInductionAux translator goal cases inductionPrincipleNames.toArray
  appendTacticSeqSeq tacs <| ← `(tacticSeq| done)
| goal?, kind ,_ => throwError
    s!"codegen: conditionCasesCode does not work for kind {kind} with goal present: {goal?.isSome}"


#notImplementedCode "Figure"

#notImplementedCode "Table"

/-!
### `reduction_proof`

JSON type to match: `reduction_proof`.

Fields:

- `claim`: current claim being reduced.
- `reduced_to`: target result or previously proved theorem.
- `proof_of_reduction`: proof object showing that `claim` follows from, or is
  reduced to, `reduced_to`.
- `proof`: proof object for the reduced goal `reduced_to`.

Expected Lean behavior: first prove the reduction from `claim` to `reduced_to`,
then prove the reduced goal. This avoids separating "reduction steps" from
"result used"; the result/theorem being used should appear inside either
`proof_of_reduction` or `proof` as an ordinary proof reference.
-/

@[codegen "reduction_proof"]
def reductionProofCode(translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| some goal , ``tacticSeq, js => goal.withContext do
    let .ok claim := js.getObjValAs? String "claim" | throwError s!"codegen: no 'claim' found in 'reduction_proof'"
    let .ok reducedTo := js.getObjValAs? String "reduced_to"| throwError s!"codegen: no 'reduced_to' found in 'reduction_proof"
    let .ok proofOfReduction := js.getObjVal? "proof_of_reduction"| throwError s!"codegen: no 'proof_of_reduction' found in 'reductionn_proof'"
    let .ok proof := js.getObjVal? "proof" | throwError s!"codegen: no 'proof' found in 'reduction_proof'"

    -- proving the reduction
    let claim ← translator.translateToPropStrict claim
    let reducedProp ← translator.translateToPropStrict reducedTo
    let reductionStep ← mkArrow reducedProp claim
    let reductionStepExpr ← mkFreshExprMVar reductionStep
    let reductionGoal := reductionStepExpr.mvarId!
    let some tacs ← withoutModifyingState do getProof translator reductionGoal proofOfReduction | throwError
    s!"codegen: no tactics found for proof {proofOfReduction}"
    let reduction ← delabDetailed reductionStep
    let hash₀ := hash ((← ppTerm {env := ← getEnv} reduction).pretty)
    let name := mkIdent <| Name.mkSimple s!"reduction_{hash₀}"
    let tacReduction ← `(tactic| have $name : $reduction := by $tacs)

    -- proving the reduced statement
    let reducedPropExpr ← mkFreshExprMVar reducedProp
    let reducedPropGoal := reducedPropExpr.mvarId!
    let some reducedProof ← withoutModifyingState do getProof translator reducedPropGoal proof | throwError
    s!"codegen: no tactics found for proof {proof}"
    let reduced ← delabDetailed reducedProp
    let hash₁ := hash ((← ppTerm {env := ← getEnv} reduced).pretty)
    let name' := mkIdent <| Name.mkSimple s!"reduced_{hash₁}"
    let tacReduced ← `(tactic| have $name' : $reduced := by $reducedProof)
    let [remGoals] ← runAndGetMVars goal #[tacReduction,tacReduced] 1 | throwError s!"codegen: reduction proof failed to get goal, goal: {← ppExpr <| ← reductionGoal.getType}"
    let finalpf ← findTacticsI remGoals
    `(tacticSeq| $tacReduction; $tacReduced; $finalpf*)
| goal?, kind, _ => throwError s!"codegen: reductionProofCode does not work for kind {kind} with goal present : {goal?.isSome}"

/-
### `epsilon_delta_proof`

JSON type to match: `epsilon_delta_proof`.

Fields:

- `epsilon_var`: epsilon variable name.
- `epsilon_positive`: positivity hypothesis for epsilon.
- `delta`: chosen delta expression.
- `delta_positive_proof`: proof that delta is positive.
- `bound_claim`: bound or implication to prove after the delta is chosen.
- `bound_proof`: proof of the required bound.

Expected Lean behavior: introduce epsilon and its positivity hypothesis, use
the proposed delta, prove positivity, then prove the implication/bound.
-/

@[codegen "epsilon_delta_proof"]
def epsilonDeltaProof(translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
|some goal, ``tacticSeq, js => goal.withContext do
    let .ok epsilonVar := js.getObjValAs? String "epsilon_var" | throwError s!"codegen: no 'epsilon_var' found in 'epsilon_delta_proof'"
    let .ok delta := js.getObjValAs? String "delta" | throwError s!"codegen : no 'delta' found in 'epsilon_delta_proof'"
    let .ok deltaPosProof := js.getObjVal? "delta_positive_proof" | throwError s!"codegen : no 'delta_positive_proof' found in 'epsilon_delta_proof'"
    let .ok boundClaim := js.getObjValAs? String "bound_claim" | throwError s!"codegen: no 'bound_claim' found in 'epsilon_delta_proof'"
    let .ok boundProof := js.getObjVal? "bound_proof" | throwError s!"codegen: no 'bound_proof' found in 'epsilon_delta_proof'"

    let epsilon := mkIdent epsilonVar.toName
    let hyp := mkIdent ("h"++epsilonVar).toName
    let epsilonPosStx ← `($epsilon > 0)
    let epsilonPosExpr ← `(tactic| have $hyp : $epsilonPosStx := by assumption)

    let .ok deltaStxRaw := Parser.runParserCategory (← getEnv) `term delta
      | throwError s!"could not parse delta term: {delta}"
    let deltaStx : TSyntax `term := ⟨deltaStxRaw⟩
    let deltaIdent := mkIdent `delta
    let deltaExpr ← `(tactic| let $deltaIdent := $deltaStx)
    addPrelude s!"Let delta := {delta}"

    let deltaPosStat := "For all ε > 0, delta > 0"
    let deltaPosExpr ← translator.translateToPropStrict deltaPosStat
    let deltaPosStx ← delabDetailed deltaPosExpr
    let deltaPosMVar ← mkFreshExprMVar deltaPosExpr
    let deltaPosGoal := deltaPosMVar.mvarId!
    let some deltaPosProof ← getProof translator deltaPosGoal deltaPosProof
        | throwError "no proof found for epsilon-delta bound claim"
    Term.synthesizeSyntheticMVarsNoPostponing
    let hash₀ := hash ((← ppTerm {env := ← getEnv} deltaStx).pretty)
    let name := mkIdent <| Name.mkSimple s!"δ_pos_{hash₀}"
    let deltaTac ← `(tactic|
      have $name : $deltaPosStx := by
        $deltaPosProof)
    try
      let boundClaim ← translator.translateToPropStrict ("For all ε > 0"++boundClaim)
      traceAide `leanaide.papercodes.info s!"The bound claim: {← ppExpr boundClaim}"
      let boundClaimMVar ← mkFreshExprMVar boundClaim
      let boundClaimGoalExpr := boundClaimMVar.mvarId!
      let some boundClaimProof ← getProof translator boundClaimGoalExpr boundProof
        | throwError "no proof found for epsilon-delta bound claim"
      let boundClaimName := mkIdent <| Name.mkSimple s!"claim_{hash₀}"
      let boundClaimStx ← delabDetailed boundClaim
      let boundProofTacs ← `(tactic| have $boundClaimName : $boundClaimStx := by $boundClaimProof)
      let [remGoals] ← runAndGetMVars goal #[deltaTac, boundProofTacs] 1 | throwError
        s!"codegen: epsilon_delta_proof failed to get goal, goal: {← ppExpr <| ← goal.getType}"
      let finalpf ← findTacticsI remGoals
      `(tacticSeq| $deltaTac; $boundProofTacs; $finalpf*)
    catch e =>
      traceAide `leanaide.papercodes.info
        s!"could not translate epsilon_delta_proof bound claim, using sorry; error: {← e.toMessageData.toString}"
      `(tacticSeq| sorry)
| _, _, _ => throwError s!"Wrong Case"

/-!
### `structure-definition`

JSON type to match: `structure-definition`.

Fields:

- `name`: Lean declaration name.
- `is_class`: whether to emit `class` instead of `structure`.
- `parameters`: optional array of binders, e.g. `["α : Type", "le : α → α → Prop"]`.
- `extends`: optional array of parent structures/classes.
- `fields`: array of field objects:
  - `name`: field name.
  - `type`: field type.
  - `default`: optional default value.
- `text`: source prose for comments or repair prompts.

Expected Lean behavior:

- If `is_class = false`, emit:

  ```lean
  structure SortedList (α : Type) (le : α → α → Prop) where
    xs : List α
    sorted : List.Pairwise le xs
  ```

- If `is_class = true`, emit:

  ```lean
  class Magma where
    carrier : Type
    mul : carrier → carrier → carrier
  ```

- If `extends` is nonempty, emit `structure Name ... extends Parent₁, Parent₂ where`
  or `class Name ... extends Parent₁, Parent₂ where`.
- If a field has `default`, emit `field_name : field_type := default`.
- For "data and property" structures, both data fields and proof/property fields
  are plain structure fields. Example: `BoundedNat` has data `n : Nat` and
  property `bound : n ≤ b`.

Implementation notes:

- Add a `@[codegen]` handler for `structure-definition`.
- Add a parser helper for optional arrays of strings (`parameters`, `extends`).
- Add a parser helper for field objects with required `type` and optional
  `name`/`default`.
- The field name should be required for generated Lean. If omitted, either infer
  a stable name such as `field1` or emit a TODO comment.

-/

open Lean Syntax Parser Command

def getNameAndBinders (name: String)(parameters: Array String) : MetaM (Syntax.Ident × Array (TSyntax ``bracketedBinder)) := do
  let mut paramString := ""
  for param in parameters do
    paramString := paramString ++ "(" ++ param ++ ") "
  let defString := s!"def {name} {paramString} : Unit := sorry"
  let .ok stx := runParserCategory (← getEnv) `command defString | throwError
    s!"codegen: failed to parse structure definition header: {defString}"
  match stx with
    | `(command| def $name:ident $params:bracketedBinder* : $_ := $_) =>
      return (name, params)
    | `(command| def $name:ident : $_ := $_) =>
      return (name, #[])
    | _ => throwError s!"codegen: unexpected syntax for structure definition header: {stx}"

def getBracketedBinders (translator: CodeGenerator)  (parameters: Array (String × String × Option String)) : TranslateM (Array (TSyntax ``bracketedBinder)) := do
  parameters.mapM fun (nameStr, type, biStr) => do
    let nameId := mkIdent nameStr.toName
    let typeStx ← translator.translateToTerm type
    match biStr with
      | "default" => `(bracketedBinder| ($nameId:ident : $typeStx:term))
      | "implicit" => `(bracketedBinder| {$nameId:ident : $typeStx:term})
      | "typeclass" => `(bracketedBinder| [$nameId:ident : $typeStx:term])
      | _ => `(bracketedBinder| ($nameId:ident : $typeStx:term))

def getBinderInfo (os : Option String) : BinderInfo :=
  match os with
  | none => BinderInfo.default
  | some s =>
    if s == "implicit" then BinderInfo.implicit
    else if s == "typeclass" then BinderInfo.instImplicit
    else BinderInfo.default

def withParamsLocalDecl {α} (translator : CodeGenerator := {}) (parameters : List (String × String × Option String)) (k : List Expr → TranslateM α) (l : List Expr := []) : TranslateM α :=
  match parameters with
  | [] => k l
  | p :: rest => do
    withLocalDecl (p.1.toName) (getBinderInfo p.2.2) (← elabTerm (← translator.translateToTerm p.2.1).raw none) fun expr =>
      withParamsLocalDecl translator rest k (l++[expr])

def withTypeLocalDecl {α} (translator : CodeGenerator := {}) (name : String) (isProp : Bool) (parameters : List (String × String × Option String)) (k : Expr → TranslateM α) : TranslateM α :=
  withoutModifyingState <| withParamsLocalDecl translator parameters fun l => do
    let lastType := if isProp then mkSort levelZero else mkSort levelOne
    let fullType ← mkForallFVars l.toArray lastType
    withLocalDecl name.toName (BinderInfo.default) fullType fun expr =>
      k expr

def structureCommand (translator : CodeGenerator := {}) (name: String) (parameters: Array (String × String × Option String)) (inputFieldsRaw : Array (String × String × Option String)) (isClass: Bool) (isProp : Bool) :
  TranslateM (TSyntax `commandSeq) := do
  let structIdent := mkIdent name.toName
  let inputFields : Array (Syntax.Ident × Syntax.Term × Option Syntax.Term) ←  inputFieldsRaw.mapM fun (fieldName, fieldType, default?) => do
    withTypeLocalDecl translator name isProp parameters.toList fun _ => do
    let fieldIdent := mkIdent fieldName.toName
    let fieldType ← translator.translateToTerm fieldType
    let defaultStx? : Option (Syntax.Term) ← match default? with
      | some defaultStr =>
        let defaultStx ← translator.translateToTerm defaultStr
        pure <| some defaultStx
      | none =>
        traceAide `leanaide.papercodes.info s!"No default value for {fieldName}"
        pure none
    pure (fieldIdent, fieldType, defaultStx?)
  let ps : Array (TSyntax ``structSimpleBinder) ←
    inputFields.mapM fun (fieldIdent, fieldType, defaultStx?) => do
      match defaultStx? with
        | some defaultStx =>
          `(structSimpleBinder| $fieldIdent:ident : $fieldType:term := $defaultStx:term)
        | none =>
          `(structSimpleBinder| $fieldIdent:ident : $fieldType:term)
  if isClass then
    if isProp then
      if parameters.isEmpty then
        `(commandSeq| class $structIdent:ident : Prop where
          $ps:structSimpleBinder*)
      else
        let params ← getBracketedBinders translator parameters
        `(commandSeq| class $structIdent:ident $params* : Prop where
            $ps:structSimpleBinder*)
    else
      if parameters.isEmpty then
        `(commandSeq| class $structIdent:ident where
          $ps:structSimpleBinder*)
      else
        let params ← getBracketedBinders translator parameters
        `(commandSeq| class $structIdent:ident $params* where
            $ps:structSimpleBinder*)
  else
    if isProp then
      if parameters.isEmpty then
        `(commandSeq| structure $structIdent:ident : Prop where
          $ps:structSimpleBinder*)
      else
        let params ← getBracketedBinders translator parameters
        `(commandSeq| structure $structIdent:ident $params* : Prop where
            $ps:structSimpleBinder*)
    else
      if parameters.isEmpty then
        `(commandSeq| structure $structIdent:ident where
          $ps:structSimpleBinder*)
      else
        let params ← getBracketedBinders translator parameters
        `(commandSeq| structure $structIdent:ident $params* where
            $ps:structSimpleBinder*)

@[codegen "structure-definition"]
def structureDefinitionCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => do
  let .ok name := js.getObjValAs? String "name" | throwError
    s!"codegen: no 'name' found in 'structure_definition'"
  let parameters := js.getObjValAs? (Array Json) "parameters" |>.toOption.getD #[]
  let parametersRaw ← parameters.mapM fun paramJson => do
    let .ok paramName := paramJson.getObjValAs? String "name" | throwError
      s!"codegen: no 'name' found in structure field definition {paramJson}"
    let .ok paramType := paramJson.getObjValAs? String "type" | throwError
      s!"codegen: no 'type' found in structure field definition {paramJson}"
    let binder := paramJson.getObjValAs? String "binder" |>.toOption
    pure (paramName, paramType, binder)
  let .ok fields := js.getObjValAs? (Array Json) "fields" | throwError
    s!"codegen: no 'fields' found in 'structure_definition'"
  let isClass := js.getObjValAs? Bool "is_class" |>.toOption.getD false
  let isProp := js.getObjValAs? Bool "isProp" |>.toOption.getD false
  let inputFieldsRaw ← fields.mapM fun fieldJson => do
    let .ok fieldName := fieldJson.getObjValAs? String "name" | throwError
      s!"codegen: no 'name' found in structure field definition {fieldJson}"
    let .ok fieldType := fieldJson.getObjValAs? String "type" | throwError
      s!"codegen: no 'type' found in structure field definition {fieldJson}"
    let default := fieldJson.getObjValAs? String "default" |>.toOption
    pure (fieldName, fieldType, default)
-- structureCommand name parameters inputFieldsRaw isClass
  structureCommand translator name parametersRaw inputFieldsRaw isClass isProp
| _, kind, _ => throwError
    s!"codegen: structure_definition does not work for kind {kind}"

/-!
### `instance-definition`

JSON type to match: `instance-definition`.

Fields:

- `name`: optional instance declaration name.
- `class_name`: class being instantiated.
- `target`: target type or target expression.
- `parameters`: optional array of binders.
- `fields`: object mapping field names to implementation expressions.
- `value`: optional raw instance expression or prose summary.
- `text`: source prose for comments or repair prompts.

Expected Lean behavior:

- If `fields` is present, emit a structure-style instance body:

  ```lean
  instance natAddMagma : Magma where
    carrier := Nat
    mul := Nat.add
  ```

- If `class_name` and `target` should be combined into an applied class, emit
  `: ClassName Target` only when the class expects a target argument. For the
  current `Magma` example, the target is metadata and `: Magma` is enough because
  `carrier` is a field.
- If `value` is a usable Lean expression and `fields` is absent, emit:

  ```lean
  instance name : ClassName Target := value
  ```

- If `name` is absent, emit an anonymous instance:

  ```lean
  instance : ClassName Target where
    ...
  ```

Implementation notes:

- Add a `@[codegen]` handler for `instance-definition`.
- Be conservative about the instance type: classes vary between bundled
  structures (`Magma`) and typeclass-on-carrier shapes (`Group G`). If both
  `class_name` and `target` are present, a first heuristic is:
  - if `fields` contains `carrier`, use `: class_name`;
  - otherwise use `: class_name target`.
- Long term, add a repair pass that tries both instance signatures when Lean
  elaboration fails.
-/
@[codegen "instance-definition"]
def instanceDefinitionCode (_ : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => do
  let .ok className := js.getObjValAs? String "class_name" | throwError
    s!"codegen: no 'class_name' found in 'instance_definition'"
  let target? := js.getObjValAs? String "target" |>.toOption
  let type : Syntax.Term ← match target? with
    | some target =>
      let .ok targetStx := Parser.runParserCategory (← getEnv) `term target | throwError
        s!"codegen: failed to parse instance target expression: {target}"
      let targetTerm := ⟨targetStx⟩
      let classIdent := mkIdent className.toName
      `(term| $classIdent $targetTerm)
    | none =>
      let classIdent := mkIdent className.toName
      `(term| $classIdent)
  let .ok fields := js.getObjValAs? (Array Json) "fields" | throwError
    s!"codegen: no 'fields' found in 'instance_definition'"
  let name? := js.getObjValAs? String "name" |>.toOption
  let parameters := js.getObjValAs? (Array String) "parameters" |>.toOption.getD #[]
  let mut paramString := ""
  for param in parameters do
    paramString := paramString ++ " " ++ param
  let (_, params) ← getNameAndBinders "dummy" parameters
  let fieldList ← fields.mapM fun (fieldJson) => do
    let .ok fieldName := fieldJson.getObjValAs? String "name" | throwError
      s!"codegen: no 'name' found in instance field"
    let .ok fieldVal := fieldJson.getObjValAs? String "value" | throwError
      s!"codegen: no 'value' found in instance field"
    let .ok val := Parser.runParserCategory (← getEnv) `term fieldVal | throwError
      s!"codegen: failed to parse instance field implementation expression: {fieldVal}"
    let valTerm : Syntax.Term := ⟨val⟩
    let fieldIdent := mkIdent fieldName.toName
    `(structInstField| $fieldIdent:ident := $valTerm:term)
  match name?, params with
  | some name, #[] =>
    let nameIdent := mkIdent name.toName
    `(commandSeq| instance $nameIdent:ident : $type := {
      $fieldList:structInstField,* })
  | some name, ps =>
    let nameIdent := mkIdent name.toName
    `(commandSeq | instance $nameIdent:ident $ps*  : $type := {
    $fieldList:structInstField,* })
  | none, _ =>
    `(commandSeq| instance : $type := {
      $fieldList:structInstField,* })
| _, kind, _ => throwError
    s!"codegen: instance_definition does not work for kind {kind}"

/-!
### `inductive-type-definition`

JSON type to match: `inductive-type-definition`.

Fields:

- `name`: Lean inductive declaration name.
- `is_prop`: whether the inductive family lives in `Prop`; otherwise emit a
  normal `Type` inductive.
- `parameters`: optional array of declaration binder objects with `name`,
  `type`, and optional `binder`.
- `indices`: optional array of index binder objects with the same shape as
  `parameters`. These describe the indexed family arguments, e.g. `n : Nat` in
  `Even : Nat → Prop`.
- `constructors`: array of constructor objects:
  - `name`: constructor name.
  - `arguments`: array of JSON objects with string fields `name` and `type`,
    e.g. `[{"name": "n", "type": "Nat"}, {"name": "h", "type": "Even n"}]`.
  - `index_args`: optional array of strings giving the index values for this
    constructor. For `Even : Nat → Prop`, `step_even` has
    `"index_args": ["n + 2"]`.
- `text`: source prose for comments or repair prompts.

Expected Lean behavior:

- For propositions, emit an inductive proposition:

  ```lean
  inductive Even : Nat → Prop where
    | zero_even : Even 0
    | step_even (n : Nat) (h : Even n) : Even (n + 2)
  ```

  Example input:

  ```json
  {
    "type": "inductive-type-definition",
    "name": "Even",
    "is_prop": true,
    "indices": [
      {"name": "n", "type": "Nat", "binder": "default"}
    ],
    "constructors": [
      {"name": "zero_even", "arguments": []},
      {
        "name": "step_even",
        "arguments": [
          {"name": "n", "type": "Nat"},
          {"name": "h", "type": "Even n"}
        ],
        "index_args": ["n + 2"]
      }
    ]
  }
  ```

- For types, emit an inductive type:

  ```lean
  inductive BinaryTree (α : Type) : Type where
    | leaf : BinaryTree α
    | node (left : BinaryTree α) (label : α) (right : BinaryTree α) : BinaryTree α
  ```

Index/result information:

- The Python schema now records constructor index values using optional
  `index_args`. For indexed families, Lean codegen should combine the inductive
  declaration name, parameters, and `index_args` to form constructor result
  targets. For example, for `Even` with one index, `index_args = ["n + 2"]`
  means the constructor target is `Even (n + 2)`.
- If `index_args` is absent for an indexed family, codegen should not invent a
  target silently. Use `text` plus constructor arguments to prompt/repair the
  full declaration, or emit a commented TODO if the target cannot be inferred.
- For non-indexed inductive types, constructor targets are usually the family
  applied to parameters, e.g. `BinaryTree α`.

Implementation notes:

- Add a `@[codegen]` handler for `inductive-type-definition`.
- Add binder parsers for both `parameters` and `indices`; for compatibility,
  allow old raw string binders and normalize them to default binder objects.
- Add a constructor parser for `name`, structured `arguments`, and optional
  `index_args`. For compatibility with old hand-written JSON, it is acceptable
  to normalize legacy string arguments such as `"n : Nat"` to
  `{"name": "n", "type": "Nat"}` before codegen.
- For `is_prop = true`, the declaration result should usually be `... → Prop`.
  The `indices` array gives the family domain part, so an inductive with
  `indices = [{"name": "n", "type": "Nat"}]` should at least target
  `: Nat → Prop`. Constructor `index_args` should provide the constructor
  result indices needed for precise constructor types.
- For `is_prop = false`, default to `: Type` when no result universe is
  specified.
-/

def getFullType (translator : CodeGenerator := {}) (isProp : Bool) (parameters : List (String × String × Option String)) : TranslateM Expr :=
  withoutModifyingState <| withParamsLocalDecl translator parameters fun l => do
    let lastType := if isProp then mkSort levelZero else mkSort levelOne
    let fullType ← mkForallFVars l.toArray lastType
    return fullType

def inductiveCommand (translator : CodeGenerator := {}) (name: String) (parametersRaw : Array (String × String × Option String))
  (indicesRaw : Array (String × String × Option String)) (constructorsRaw : Array (String × Array (String × String × Option String) × Array String)) (isProp : Bool) :
    TranslateM (TSyntax `commandSeq) := do
  let inductiveIdent := mkIdent name.toName
  let typeExprWithoutParams ← withoutModifyingState <| withParamsLocalDecl translator parametersRaw.toList fun _ => getFullType translator isProp indicesRaw.toList
  let typeStxWithoutParams ← delabDetailed typeExprWithoutParams
  let fullTypeExpr ← withTypeLocalDecl translator name isProp (parametersRaw.toList ++ indicesRaw.toList) fun expr => return expr
  let explicitParamsIdents : Array Ident := parametersRaw.filterMap fun (name, _, binder) =>
    match getBinderInfo binder with
    | BinderInfo.default => some (mkIdent name.toName)
    | _ => none
  let ctorFields : Array (Syntax.Ident × Array (TSyntax ``bracketedBinder) × Array Term) ← constructorsRaw.mapM
    fun (ctorName, ctorArgs, index_args) => do
      withParamsLocalDecl translator parametersRaw.toList fun _ =>
        withLocalDecl name.toName BinderInfo.default fullTypeExpr fun _ => do
          let ctorIdent := mkIdent ctorName.toName
          --let ctorArgsWithBinderInfo := ctorArgs.map fun (name, type) => (name, type, some "default")
          let ctorParamsStx ← getBracketedBinders translator ctorArgs
          withParamsLocalDecl translator ctorArgs.toList fun _ => do
            let indexArgsStx ← index_args.mapM fun index_arg => do
              let index_term ← translator.translateToTerm index_arg
              pure index_term
            pure (ctorIdent, ctorParamsStx, indexArgsStx)
  let ctors : Array (TSyntax ``ctor) ←
    ctorFields.mapM fun (ctorIdent, ctorParams, index_args) => do
      `(ctor| | $ctorIdent:ident $ctorParams* : $inductiveIdent $explicitParamsIdents* $index_args*)
  if parametersRaw.isEmpty then
    `(commandSeq| inductive $inductiveIdent:ident : $typeStxWithoutParams where
      $ctors:ctor*)
  else
    let params ← getBracketedBinders translator parametersRaw
    `(commandSeq| inductive $inductiveIdent:ident $params* : $typeStxWithoutParams where
        $ctors:ctor*)

@[codegen "inductive-type-definition"]
def inductiveDefinitionCode (translator : CodeGenerator := {}) : Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, `commandSeq, js => do
  let .ok name := js.getObjValAs? String "name" | throwError
    s!"codegen: no 'name' found in 'inductive-type-definition'"
  let isProp := js.getObjValAs? Bool "is_prop" |>.toOption.getD false
  let parameters := js.getObjValAs? (Array Json) "parameters" |>.toOption.getD #[]
  let parametersRaw ← parameters.mapM fun paramJson => do
    let .ok paramName := paramJson.getObjValAs? String "name" | throwError
      s!"codegen: no 'name' found in inductive field definition {paramJson}"
    let .ok paramType := paramJson.getObjValAs? String "type" | throwError
      s!"codegen: no 'type' found in inductive field definition {paramJson}"
    let binder := paramJson.getObjValAs? String "binder" |>.toOption
    pure (paramName, paramType, binder)
  let indices := js.getObjValAs? (Array Json) "indices" |>.toOption.getD #[]
  let indicesRaw ← indices.mapM fun indexJson => do
    let .ok indexName := indexJson.getObjValAs? String "name" | throwError
      s!"codegen: no 'name' found in inductive index definition {indexJson}"
    let .ok indexType := indexJson.getObjValAs? String "type" | throwError
      s!"codegen: no 'type' found in inductive index definition {indexJson}"
    let binder := indexJson.getObjValAs? String "binder" |>.toOption
    pure (indexName, indexType, binder)
  let .ok constructors := js.getObjValAs? (Array Json) "constructors" | throwError
    s!"codegen: no 'constructors' found in 'inductive-type-definition'"
  let constructorsRaw ← constructors.mapM fun constructorJson => do
    let .ok constructorName := constructorJson.getObjValAs? String "name" | throwError
      s!"codegen: no 'name' found in inductive constructor definition {constructorJson}"
    let .ok constructorArgs := constructorJson.getObjValAs? (Array Json) "arguments" | throwError
      s!"codegen: no 'arguments' found in inductive constructor definition {constructorJson}"
    let constructorArgsRaw ← constructorArgs.mapM fun ctorArgJson => do
      let .ok ctorArgName := ctorArgJson.getObjValAs? String "name" | throwError
        s!"codegen: no 'name' found in inductive constructor argument {ctorArgJson}"
      let .ok ctorArgType := ctorArgJson.getObjValAs? String "type" | throwError
        s!"codegen: no 'type' found in inductive constructor argument {ctorArgJson}"
      let ctorArgDefault := ctorArgJson.getObjValAs? String "binder" |>.toOption
      pure (ctorArgName, ctorArgType, ctorArgDefault)
    let indexArgs := constructorJson.getObjValAs? (Array String) "index_args" |>.toOption.getD #[]
    pure (constructorName, constructorArgsRaw, indexArgs)
  inductiveCommand translator name parametersRaw indicesRaw constructorsRaw isProp
| _, kind, _ => throwError
    s!"codegen: inductive_type_definition does not work for kind {kind}"

/-
- `name`: Lean inductive declaration name.
- `is_prop`: whether the inductive family lives in `Prop`; otherwise emit a
  normal `Type` inductive.
- `parameters`: optional array of declaration binder objects with `name`,
  `type`, and optional `binder`.
- `indices`: optional array of index binder objects with the same shape as
  `parameters`. These describe the indexed family arguments, e.g. `n : Nat` in
  `Even : Nat → Prop`.
- `constructors`: array of constructor objects:
  - `name`: constructor name.
  - `arguments`: array of JSON objects with string fields `name` and `type`,
    e.g. `[{"name": "n", "type": "Nat"}, {"name": "h", "type": "Even n"}]`.
  - `index_args`: optional array of strings giving the index values for this
    constructor. For `Even : Nat → Prop`, `step_even` has
    `"index_args": ["n + 2"]`.
- `text`: source prose for comments or repair prompts.
-/

/-!
## Adding handlers for different schema elements

The following functions are helpers that one can use.
-/

/--
info: LeanAide.runForSingleGoal (mvarId : MVarId) (tacticCode : TSyntax `Lean.Parser.Tactic.tacticSeq) :
  TermElabM (Option MVarId)
-/
#guard_msgs in
#check runForSingleGoal


/--
info: LeanAide.Translator.translateToPropStrict (claim : String) (translator : Translator) : TranslateM Expr
-/
#guard_msgs in
#check Translator.translateToPropStrict

/--
info: LeanAide.Translator.translateDefCmdM? (s : String) (translator : Translator) (isProp : Bool := false) :
  TranslateM (Except (Array CmdElabError) Command)
-/
#guard_msgs in
#check Translator.translateDefCmdM?

/--
info: LeanAide.getProof (translator : CodeGenerator) (goal : MVarId) (js : Json) :
  TranslateM (Option (TSyntax `Lean.Parser.Tactic.tacticSeq))
-/
#guard_msgs in
#check getProof

/--
info: LeanAide.Codegen.getCode (translator : CodeGenerator) (goal? : Option MVarId) (kind : SyntaxNodeKinds) (source : Json) :
  TranslateM (Option (TSyntax kind))
-/
#guard_msgs in
#check getCode

/--
info: LeanAide.Codegen.getCodeTactics (translator : CodeGenerator) (goal : MVarId) (sources : List Json) :
  TranslateM (TSyntax `Lean.Parser.Tactic.tacticSeq)
-/
#guard_msgs in
#check getCodeTactics

/--
info: LeanAide.Codegen.commandSeqToTacticSeq (cmdSeq : TSyntax `commandSeq) :
  TermElabM (TSyntax `Lean.Parser.Tactic.tacticSeq)
-/
#guard_msgs in
#check commandSeqToTacticSeq

/-- info: LeanAide.Codegen.commandToTactic (cmd : Command) : TermElabM Syntax.Tactic -/
#guard_msgs in
#check commandToTactic

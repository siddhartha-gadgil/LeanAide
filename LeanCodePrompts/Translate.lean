import Lean
import Lean.Meta
import Lean.Parser
import LeanAide.TheoremElab
import LeanAide.TheoremElabCheck
import LeanAide.TheoremEquality
import LeanAide.IP
import LeanAide.PromptBuilder
import LeanCodePrompts.SpawnNearestEmbeddings
import Lean.Meta.Tactic.TryThis
import Batteries.Util.Pickle
import LeanCodePrompts.ChatClient
import LeanAide.StatementSyntax
import LeanAide.TranslateM
import LeanAide.PromptBuilder
import LeanAide.SimpleFrontend
import LeanAide.Descriptions

open Lean Meta Elab Parser Command
open LeanAide.Meta

namespace LeanAide
open Translate

#logIO leanaide.elaboration.info
-- #logIO leanaide.translate.debug

@[default_instance]
instance : Add ℤ := inferInstance
@[default_instance]
instance : Semiring ℤ := inferInstance

-- example : {n | Odd n}.Infinite := by sorry



/-!
Caching, polling etc to avoid repeatedly calling servers
-/

initialize webCacheJson : IO.Ref (Std.HashMap String (Json × Json × Array (String × Json))) ← IO.mkRef (Std.HashMap.emptyWithCapacity)

initialize pendingJsonQueries : IO.Ref (Std.HashSet String)
    ← IO.mkRef (Std.HashSet.emptyWithCapacity)

def getCachedJson? (s: String) : IO (Option (Json × Json × Array (String × Json))) := do
  let cache ← webCacheJson.get
  return cache.get? s

def cacheJson (s: String)(js: Json × Json × Array (String × Json))  : IO Unit := do
  let cache ← webCacheJson.get
  webCacheJson.set (cache.insert s js)
  return ()

partial def pollCacheJson (s : String) : IO <| Json × Json × Array (String × Json) := do
  let cache ← webCacheJson.get
  match cache.get? s with
  | some jsBlob => return jsBlob
  | none => do
    IO.sleep 200
    pollCacheJson s

/-- check if there is a valid elaboration after translation, autocorrection -/
def hasElab (s: String) : TranslateM Bool := do
  let elab? ← elabThm4 s
  return elab?.toOption.isSome

/-- prompts generated from the declarations in the current file. -/
def getEnvPrompts (moduleNames : Array Name := .empty) (useMain? : Bool := true) : MetaM <| Array (String × String):= do
  if moduleNames.isEmpty && !useMain? then
    return #[]
  let env ← getEnv
  let moduleNames :=
    if useMain? then
      moduleNames.push env.mainModule
    else moduleNames
  let moduleIdxs := moduleNames.filterMap env.getModuleIdx?

  List.toArray <$> env.constants.toList.filterMapM fun ⟨nm, ci⟩ ↦ do
    let some _ := moduleIdxs.contains <$> env.getModuleIdxFor? nm  | pure none
    let some docstring ← findDocString? env nm | pure none
    let some kind := (
      match ci with
        | .defnInfo _ => some "def"
        | .thmInfo _  => some "theorem"
        |     _       => none
    ) | pure none
    let some type ← try? (Format.pretty <$> PrettyPrinter.ppExpr ci.type) | pure none
    return some ⟨docstring, s!"{kind} : {type} :="⟩


def Translator.getMessages (s: String) (translator : Translator)
    (header: String := "Theorem") (useInstructions := translator.useInstructions) :
      TranslateM <| Json × Array (String × Json):= do
  let docPairs ← translator.pb.getPromptPairs s
  let dfns ← translator.relDefs.blob s docPairs
  let promptPairs := if useInstructions then translatePromptPairs docPairs else docPairs
  trace[Translate.info] m!"prompt pairs: \n{promptPairs}"
  let messages ←
    translateMessages s promptPairs header dfns translator.toChat translator.messageBuilder
  trace[Translate.info] m!"prompt: \n{messages.pretty}"
  return (messages, docPairs)

/-- given string to translate, build prompt and query OpenAI; returns JSON response
-/
def Translator.getLeanCodeJson (s: String)
    (translator : Translator)(header: String := "Theorem") : TranslateM <| Json × Json × Array (String × Json) := do
  traceAide `leanaide.translate.debug  s!"translating string `{s}` with  examples"
  -- IO.eprintln s!"translating string `{s}` with  examples"
  let s ← withPreludes s
  setContext s
  match ← getCachedJson? s with
  | some js =>
    -- IO.eprintln s!"cached json found"
    return js
  | none =>
    let pending ←  pendingJsonQueries.get
    if pending.contains s then pollCacheJson s
    else
      let pending ←  pendingJsonQueries.get
      pendingJsonQueries.set (pending.insert s)
      -- work starts here; before this was caching, polling etc
      let (messages, docPairs) ← translator.getMessages s header
      trace[Translate.info] m!"prompt: \n{messages.pretty}"
      traceAide `leanaide.translate.debug  "querying server"
      -- IO.eprintln s!"querying server"
      let fullJson ← translator.server.query messages translator.params
      let outJson :=
        (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
      traceAide `leanaide.translate.debug  "obtained llm response"
      let pending ←  pendingJsonQueries.get
      pendingJsonQueries.set (pending.erase s)
      cacheJson s (outJson, messages, docPairs)
      return (outJson, messages, docPairs)

/-- Given an array of outputs, tries to elaborate them with translation and autocorrection and returns the best choice, throwing an error if nothing elaborates.  -/
def bestElab (output: Array String) : TranslateM Expr := do
  trace[Translate.info] m!"output:\n{output}"
  let mut elabStrs : Array String := Array.empty
  let mut elaborated : Array Expr := Array.empty
  let mut fullElaborated : Array Expr := Array.empty
  let mut cache : Std.HashMap String (Except ElabError Expr) :=
    Std.HashMap.emptyWithCapacity output.size
  for out in output do
    -- IO.println s!"elaboration called: {out}"
    let elab? ←
      match cache.get? out with
      | some elab? =>
        pure elab?
      | none =>
        let res ← elabThm4 out
        cache := cache.insert out res
        pure res
    match elab? with
      | Except.error _ => pure ()
      | Except.ok expr =>
          elaborated := elaborated.push expr
          elabStrs := elabStrs.push out
          trace[Translate.info] m!"elaborated: {out}"
          if !( ← (← whnf expr).hasUnassignedExprMVar) then
            fullElaborated := fullElaborated.push expr
  if elaborated.isEmpty then
    let mut errors : Array Json := #[]
    for out in output do
      let stx ← parseThm4 out
      match stx with
      | Except.error err =>
          errors := errors.push <|
            Json.mkObj [("parsed", false),
              ("error", Json.str err), ("output", Json.str out)]
          pure ()
      | Except.ok stx => do
        errors := errors.push <|
            Json.mkObj [("parsed", true),
              ("syntax", stx.reprint.get!), ("output", Json.str out)]
    let errorJson := Json.arr errors
    appendLog "translate_fail_error" errorJson
    mkAppM ``sorryAx #[(mkSort levelZero), mkConst ``true]
  else
    traceAide `leanaide.translate.debug  "elaborated outputs, starting majority voting"
    let priority :=
        if fullElaborated.isEmpty then elaborated else fullElaborated
    let groupSorted ← groupThmExprsSorted priority
    traceAide `leanaide.translate.debug  "finished majority voting"
    return (groupSorted[0]!)[0]!

/-- Given an array of outputs, tries to elaborate them with translation and autocorrection and optionally returns the best choice as well as all elaborated terms (used for batch processing, interactive code uses `bestElab` instead)  -/
def bestElab? (output: Array String)(maxVoting: Nat := 5) : TranslateM (Except (Array ElabError) ElabSuccessResult) := do
  -- IO.println s!"arrayToExpr? called with {output.size} outputs"
  let mut elabStrs : Array String := Array.empty
  let mut elaborated : Array Expr := Array.empty
  let mut fullElaborated : Array Expr := Array.empty
  let mut cache : Std.HashMap String (Except ElabError Expr) :=
    Std.HashMap.emptyWithCapacity output.size
  traceAide `leanaide.translate.debug  "elaborating outputs"
  let mut errors : Array ElabError := #[]

  for out in output do
    -- IO.println s!"elaboration called: {out}"
    let elab? ←
      match cache.get? out with
      | some elab? => pure elab?
      | none =>
        let res ← elabThm4 out
        cache := cache.insert out res
        pure res

    match elab? with
      | Except.error e =>
        errors := errors.push e
        pure ()
      | Except.ok expr =>
          elaborated := elaborated.push expr
          elabStrs := elabStrs.push out
          if !( ← (← whnf expr).hasUnassignedExprMVar) then
            fullElaborated := fullElaborated.push expr
  if elaborated.isEmpty then
    return Except.error errors
  else
    traceAide `leanaide.translate.debug  "elaborated outputs, starting majority voting"
    -- let priority :=
    --     if fullElaborated.isEmpty then elaborated else fullElaborated
    -- IO.eprintln s!"grouping priority: {priority.size}"
    let groupSorted ← groupThmExprsSorted (elaborated.toList.take maxVoting).toArray -- priority
    let thm := (groupSorted[0]!)[0]!
    let gpView ←  groupSorted.mapM (fun gp => gp.mapM (fun e => e.view))
    traceAide `leanaide.translate.debug  "obtained majority vote"
    return Except.ok {term := thm, allElaborated := elabStrs, groups := gpView, allElaboratedExprs := elaborated, groupsExprs := groupSorted, typeView := (← ppExpr thm).pretty}
    -- {⟨thm, elabStrs, gpView⟩}

/--
Pick the first elaboration that succeeds.
-/
def greedyBestExpr? (output: Array String) : TranslateM (Option Expr) := do
    output.findSomeM? <| fun out => do
      let el? ← elabThm4 out
      pure el?.toOption

/--
Pick the first elaboration that succeeds, accumulating errors.
-/
def greedyBestExprWithErr? (output: Array String) :
    TranslateM (Except (Array ElabError) Expr) := do
  let mut errs : Array ElabError := #[]
  for out in output do
    let el? ← elabThm4 out
    match el? with
    | Except.error e =>
      errs := errs.push e
    | Except.ok e => return Except.ok e
  return Except.error errs


def matchElab? (output: Array String)(defs : Array <| Name × String):
  TranslateM (Option Name) := do
  let elabDefs : Array (Name × Expr) ←  defs.filterMapM (fun (nm, s) => do
    let el? ← elabThm4 s
    let el? := el?.toOption
    pure <| el?.map (fun e => (nm, e)))
  output.findSomeM? (fun out => do
    let el? ← elabThm4Aux out
    match el? with
    | Except.error _ => pure none
    | Except.ok e₁ =>
      let pair? ← elabDefs.findM? (fun (_, e₂) => do
        provedEquiv e₁ e₂)
      pure <| pair?.map (fun (nm, _) => nm))

def matchElabs (output: Array String)(defs : Array <| Name × String):
  TranslateM (List Name) := do
  let elabDefs : Array (Name × Expr) ←  defs.filterMapM (fun (nm, s) => do
    let el? ← elabThm4 s
    let el? := el?.toOption
    pure <| el?.map (fun e => (nm, e)))
  output.toList.filterMapM (fun out => do
    let el? ← elabThm4Aux out
    match el? with
    | Except.error _ => pure none
    | Except.ok e₁ =>
      let pair? ← elabDefs.findM? (fun (_, e₂) => do
        provedEquiv e₁ e₂)
      pure <| pair?.map (fun (nm, _) => nm))

def sufficientElab? (output: Array String)(defs : Array <| Name × String):
  TranslateM (Option Name) := do
  let elabDefs : Array (Name × Expr) ←  defs.filterMapM (fun (nm, s) => do
    let el? ← elabThm4 s
    let el? := el?.toOption
    pure <| el?.map (fun e => (nm, e)))
  output.findSomeM? (fun out => do
    let el? ← elabThm4Aux out
    match el? with
    | Except.error _ => pure none
    | Except.ok e₁ =>
      let pair? ← elabDefs.findM? (fun (_, e₂) => do
        provedSufficient e₁ e₂)
      pure <| pair?.map (fun (nm, _) => nm))



def egThm := "theorem eg_thm : ∀ n: Nat, ∃ m : Nat, m > n ∧ m % 2 = 0"


-- #eval egPrompt

-- #eval statementToDoc egThm 5 0


/-- array of outputs extracted from OpenAI Json -/
def exprStrsFromJson (json: Json) : TranslateM (Array String) := do
  let outArr : Array String ←
    match json.getArr? with
    | Except.ok arr =>
        let parsedArr : Array String ←
          arr.filterMapM <| fun js =>
            match js.getObjVal? "text" with
              | Except.ok jsstr =>
                match jsstr.getStr? with
                | Except.ok str => pure (some str)
                | Except.error e =>
                  throwError m!"json string expected but got {js}, error: {e}"
              | Except.error _ =>
                throwError m!"no text field"
        pure parsedArr
    | Except.error e =>
      IO.eprintln s!"json parsing error: {e}"
      pure #[]
  return outArr

/-- array of outputs extracted from Json Array -/
def exprStrsFromJsonStr (jsString: String) : TranslateM (Array String) := do
  try
  let json := Lean.Json.parse  jsString |>.toOption.get!
  let outArr : Array String ←
    match json.getArr? with
    | Except.ok arr =>
        let parsedArr : Array String ←
          arr.filterMapM <| fun js =>
            match js.getStr? with
            | Except.ok str => pure (some str)
            | Except.error e =>
              throwError m!"json string expected but got {js}, error: {e}"
        pure parsedArr
    | Except.error _ => pure #[jsString]
  return outArr
  catch _ =>
    pure #[jsString]

-- #eval jsonStringToExprStrArray "simple"
-- #eval jsonStringToExprStrArray "[\"simple\", \"simple2\"]"


/-- given json returned by open-ai obtain the best translation -/
def jsonToExpr' (json: Json)(greedy: Bool)(splitOutput := false) : TranslateM Expr := do
  let output ← getMessageContents json
  let output := if splitOutput
    then
      splitColEqSegments output
    else output
  if greedy then
    match ← greedyBestExpr? output with
    | some e => return e
    | none => throwError "no elaboration found"
  else
    bestElab output


/-- given json returned by open-ai obtain the best translation -/
def jsonToExprFallback (json: Json)(greedy: Bool)(splitOutput := false) : TranslateM <|Except String Expr := do
  let output ← getMessageContents json
  let output := if splitOutput
    then
      splitColEqSegments output
    else output
  let res? ← if greedy then
    greedyBestExprWithErr? output
    else
    match ← bestElab? output with
    | Except.ok res => pure <| .ok res.term
    | Except.error e => pure <| Except.error e
  match res? with
  | Except.ok e => return .ok e
  | Except.error e => return .error (←  ElabError.fallback e)


/-- translation from a comment-like syntax to a theorem statement -/
elab "//-" cb:commentBody  : term => do
  let s := cb.raw.getAtomVal
  let s := (s.dropRight 2).trim
  -- querying codex
  let (js, _) ←
    Translator.getLeanCodeJson  s {} |>.run' {}
  -- filtering, autocorrection and selection
  let e ←
    jsonToExpr' js true !(← chatParams).stopColEq |>.run' {}
  trace[Translate.info] m!"{e}"
  return e

/--
Write a theorem in the form `(a : A) ... : type` instead of `(a : A) → ... → type`
-/
def uncurriedView(numArgs: Nat)(e: Expr) : MetaM String :=
  match numArgs with
  | 0 => do return " : " ++ (← e.view)
  | k +1 =>
    match e with
    | Expr.forallE n t _ bi => do
      let core := s!"{n.eraseMacroScopes} : {← t.view}"
      let typeString :=s!"{← t.view}"
      let argString := match bi with
      | BinderInfo.implicit => "{"++ core ++ "}"
      | BinderInfo.strictImplicit => "{{ "++ core ++ "}}"
      | BinderInfo.instImplicit =>
        if (`inst).isPrefixOf n then s!"[{typeString}]"
          else s!"[{core}]"
      | BinderInfo.default => s!"({core})"
      let tail : String ←
        withLocalDecl `func BinderInfo.default e fun func =>
          withLocalDecl n bi t fun arg => do
            let fx := mkAppN func #[arg]
            let newType ← inferType fx
            uncurriedView k newType
      return " " ++ argString ++ tail
    | _ => do return " : " ++ (← e.view)

/--
Write a theorem in the form `(a : A) ... : type` instead of `(a : A) → ... → type`
-/
elab "uncurry2" e:term : term => do
  let e ← Term.elabTerm e none
  let e ← uncurriedView 2 e
  return mkStrLit e

universe u

namespace Translator
/--
Translate a string and output as a string.
-/
def translateViewM (s: String)(translator : Translator := {}) : TranslateM String := do
  traceAide `leanaide.translate.debug  "starting translation"
  let (js, _) ← translator.getLeanCodeJson  s
  let output ← getMessageContents js
  trace[Translate.info] m!"{output}"
  -- let output := params.splitOutputs output
  let e? ← bestElab? output
  match e? with
  | Except.ok res => do
    res.view
  | Except.error _ => do
    let view? ← output.findSomeM? <| fun s => do
      let elab? ← elabThm4 s
      match elab? with
      | Except.ok expr =>
        trace[Translate.info] m!"elaborated: {expr}"
        pure <| some (← expr.view)
      | Except.error e =>
        trace[Translate.warning] m!"elaboration failed: {e} for {s}"
        pure none
    return view?.getD "False"

def translateToProp? (s: String)(translator : Translator)
   : TranslateM (Except (Array ElabError) Expr) := do
  traceAide `leanaide.translate.debug  "starting translation"
  let (js, prompt, _) ← translator.getLeanCodeJson  s
  let output ← getMessageContents js
  trace[Translate.info] m!"{output}"
  -- let output := params.splitOutputs output
  match ← greedyBestExprWithErr? output with
  | Except.ok res => return Except.ok res
  | Except.error e =>
    logError s prompt e
    return Except.error e

/--
Translating a definition greedily by parsing as a command
-/
def translateDefCmdM? (s: String) (translator : Translator)
  (isProp: Bool := false): TranslateM <| Except (Array CmdElabError) Syntax.Command := do
  traceAide `leanaide.translate.debug  "starting translation"
  let header := if isProp then "Theorem" else "Definition"
  let (js, _) ← translator.forDef.getLeanCodeJson  s (header:= header)
  let output ← getMessageContents js
  trace[Translate.info] m!"{output}"
  let context? ← getContext
  let mut checks : Array (CmdElabError) := #[]
  for s in output do
    let s := extractLean s
    -- let s := s.replace "\n" " "
    let s := if s.startsWith "definition " then s.replace "definition " "def " else s
    let cmd? := runParserCategory (← getEnv) `command s
    match cmd? with
    | Except.error e =>
      checks := checks.push <| .unparsed s e context?
    | Except.ok cmd =>
      let check ← checkElabFrontM s
      if check.isEmpty then return .ok ⟨ cmd ⟩
      checks := checks.push (.parsed s check context?)
      trace[Translate.info] s!"Not a valid command:\n{s}"
      for chk in check do
        trace[Translate.info] chk
  return .error checks

def translateDefData? (s: String)
 (translator : Translator) (isProp: Bool := false)
   : TranslateM <| Except (Array CmdElabError) DefData := do
  let cmd? ← translator.translateDefCmdM? s isProp
  match cmd? with
  | Except.error e => return .error e
  | Except.ok cmd =>
    match ← DefData.ofSyntax? cmd with
    | none =>
      return .error #[.unparsed s s!"{← PrettyPrinter.ppCommand cmd} not a command def/theorem" (← getContext)]
    | some dd => return .ok dd

def translateDefViewM? (s: String)
  (translator : Translator) (isProp: Bool := false)
   : TranslateM <| Option String := do
  let cmd? ← translator.translateDefCmdM? s  isProp
  let fmt? ← cmd?.toOption.mapM fun cmd =>
    PrettyPrinter.ppCommand cmd
  return fmt?.map (·.pretty)

def translateDefList (dfns : List DefSource)
 (translator : Translator) (progress : Array DefData := #[]) (initial : Bool := true): TranslateM DefTranslateResult := do
  if initial then clearDefs
  match dfns with
  | [] => return .success progress
  | x :: ys =>
    let head? ← translator.translateDefData? x.doc x.isProp
    match head? with
    | Except.error e => do
      return .failure (progress : Array DefData) e
    | Except.ok dd => do
      let progress :=
        progress.push <| {dd with doc? := x.doc, isProp := x.isProp}
      let progBlob ← progress.mapM <|
        fun dfn => do pure (dfn.name, ← dfn.statement)
      let relDefs := translator.relDefs ++ progBlob
      let translator : Translator :=
        {translator with relDefs := relDefs}
      translator.translateDefList ys  progress false


syntax (name := ltrans) "l!" str : term

open PrettyPrinter Tactic

@[term_elab ltrans] def ltransImpl : Term.TermElab :=
  fun stx _ => do
  match stx with
  | `(l! $s:str) =>
  let s := s.getString
  let embedUrl := lean_aide.translate.examples_url?.get (← getOptions)
  let embedUrl? := if embedUrl.isEmpty then none else some embedUrl
  let translator : Translator := {server := ← chatServer, pb := PromptExampleBuilder.mkEmbedBuilder embedUrl? (← promptSize) (← conciseDescSize) (← descSize), params := ← chatParams}
  let (js, _) ←
    translator.getLeanCodeJson  s |>.run' {}
  let e ← jsonToExpr' js (← greedy) !(← chatParams).stopColEq |>.run' {}
  traceAide `leanaide.translate.debug  "obtained expression"
  let stx' ← delab e
  traceAide `leanaide.translate.debug  "obtained syntax"
  TryThis.addSuggestion stx stx'
  traceAide `leanaide.translate.debug  "added suggestion"
  return e
  | _ => throwUnsupportedSyntax

def findTheorem? (s: String)(translator: Translator := {}) : TranslateM (Option Name) := do
  let (js, _, prompts) ← translator.getLeanCodeJson s
  let output ← getMessageContents js
  trace[Translate.info] m!"thmPairs: {prompts}"
  let thmPairs := prompts.reverse.map (fun (_, js) =>
    (js.getObjValAs? String "name" |>.toOption.get! |>.toName,
    js.getObjValAs? String "type" |>.toOption.get!))
  matchElab? output thmPairs

def findTheorems (s: String)(numLeanSearch : ℕ := 8)
  (numMoogle : ℕ := 0) : TranslateM (List Name) := do
  let translator : Translator := {pb := PromptExampleBuilder.searchBuilder numLeanSearch numMoogle}
  let (js, _, prompts) ← translator.getLeanCodeJson s
  let output ← getMessageContents js
  trace[Translate.info] m!"thmPairs: {prompts}"
  let thmPairs := prompts.reverse.map (fun (_, js) =>
    (js.getObjValAs? String "name" |>.toOption.get! |>.toName,
    js.getObjValAs? String "type" |>.toOption.get!))
  matchElabs output thmPairs

def nearbyTheoremsChunk (s: String)
  (numLeanSearch : Nat := 8) (numMoogle: Nat := 0)  : TranslateM String := do
    let pb : PromptExampleBuilder :=
      PromptExampleBuilder.searchBuilder numLeanSearch numMoogle
    let pairs ← pb.getPromptPairs s
    let statements : Array String ← pairs.filterMapM (fun (doc, js) => do
      let name? := js.getObjValAs? String "name" |>.toOption
      let thm? := js.getObjValAs? String "type" |>.toOption
      let prop? := js.getObjValAs? Bool "isProp" |>.toOption
      match name?, thm?, prop? with
      | some name, some thm, some true =>
        mkTheoremWithDoc name.toName thm doc
      | _, _,_ => pure <| none
    )
    return statements.foldl (fun acc s => acc ++ s ++ "\n\n") ""

def nearbyDefs
    (numClosure: Nat := 4) (pairs : Array (String × Json)) : TranslateM (Array Name) := do
    let searchNames : Array Name := pairs.filterMap (fun (_, js) => do
      js.getObjValAs? Name "name" |>.toOption
    )
    let defNames : Array Name := pairs.filterMap (fun (_, js) => do
      let prop := js.getObjValAs? Bool "isProp" |>.toOption |>.getD true
      if prop then none else js.getObjValAs? Name "name" |>.toOption
    )
    let closureNames ←  bestDefsInConsts numClosure searchNames.toList 1
    return defNames ++ closureNames

def matchingTheoremsAI (s: String)(n: ℕ := 3)(qp: CodeGenerator) : TranslateM (List Name) := do
    let chunk ← nearbyTheoremsChunk s qp.numLeanSearch qp.numMoogle
    let prompt := s!"The following are some theorems in Lean with informal statements as documentation strings\n\n{chunk}\n\n---\n¬List the names of theorems that are equivalent to the following informal statement:\n\n{s}.\n\nOutput ONLY a (possibly empty) list of names."
    let completions ← qp.server.completions prompt (← sysPrompt) n qp.params
    let entries : Array (Array String) := completions.filterMap fun s =>
      let js? := Json.parse s |>.toOption
      match js? with
      | some js =>
        fromJson? js |>.toOption
      | none => none
    let checked := entries.flatten.toList.map (·.toName)
    let pb : PromptExampleBuilder :=
      PromptExampleBuilder.searchBuilder qp.numLeanSearchDirect qp.numMoogleDirect
    let pairs ← pb.getPromptPairs s
    let names : Array Name ← pairs.filterMapM fun (_, js) => do
      pure <| js.getObjValAs? String "name" |>.toOption |>.map (·.toName)
    return checked ++ names.toList

def matchingTheorems (s: String)(n: ℕ := 3)(qp: CodeGenerator)  : TranslateM (List Name) := do
  let elabMatch ← findTheorems s qp.numLeanSearch qp.numMoogle
  if elabMatch.isEmpty then
    matchingTheoremsAI  s n qp
  else
    pure elabMatch

/--
Translate a string to a Lean expression using the GPT model, returning three componenst:
* The expression, all elaborated expressions, grouped expressions
* All outputs from the LLM
* The prompt used for the LLM.
-/
def translateViewVerboseM (s: String)(translator : Translator) :   TranslateM ((Option TranslateSuccessResult) × Array String × Json) := do
  -- let dataMap ← getEmbedMap
  -- IO.eprintln s!"dataMap keys: {dataMap.toList.map Prod.fst}"
  let (js,prompt, _) ←
    translator.getLeanCodeJson s
  let output ← getMessageContents js
  if output.isEmpty then
    IO.eprintln "no output"
    return (none, output, prompt)
  else
    let res? ← bestElab? output
    match res? with
    | Except.error err =>
      appendLog "translate_fail" <| toJson err
      logError s prompt err
      return (none, output, prompt)
    | Except.ok res =>
      let view ←  res.withView
      return (some view, output, prompt)

def translateM (s: String)(translator: Translator)  :
  TranslateM ((Except (Array ElabError) (ElabSuccessResult))  × ( Json)) := do
  let (js,prompt, _) ← translator.getLeanCodeJson s
  let output ← getMessageContents js
  let res? ← bestElab? output
  match res? with
  | Except.error err =>
    appendLog "translate_fail" <| toJson err
    return (Except.error err,  prompt)
  | Except.ok res =>
    if translator.roundTripSelect then
      let res ←  translator.roundTripRefinedM s res
      return (Except.ok res,  prompt)
    else
      if translator.roundTrip then
        let pair? ←  checkTranslationM s res.term translator
        match pair? with
        | none =>
          let res := {res with roundTripCheck? := some false}
          return (Except.ok res, prompt)
        | some (_, checkStrings) =>
          let checks := checkStrings.map (fun (b, _) => b)
          if checks.any id then
            let res := {res with roundTripCheck? := some true}
            return (Except.ok res,  prompt)
          else
            let res := {res with roundTripCheck? := some false, roundTripFailures := #[(s, checkStrings)]}
            return (Except.ok res,  prompt)
      else
        return (Except.ok res, prompt)

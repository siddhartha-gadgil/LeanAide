import LeanAideCore.PromptExampleBuilder
import LeanAideCore.ChatClient
import LeanAideCore.TranslateM
import Lean
open Lean

namespace LeanAide
variable [LeanAideBaseDir]

open Translate
inductive RelevantDefs where
  | select (bound? : Option Nat) : RelevantDefs
  | closure (num : Nat)(depth: Nat := 1) : RelevantDefs
  | env : RelevantDefs
  | data (d: Array (Name × String)) : RelevantDefs
  | seq : List RelevantDefs → RelevantDefs
  deriving Repr, FromJson, ToJson

instance : Append RelevantDefs where
  append := fun x y =>
    match x, y with
    | RelevantDefs.seq xs, RelevantDefs.seq ys => RelevantDefs.seq <| xs ++ ys
    | RelevantDefs.seq xs, y => RelevantDefs.seq <| xs ++ [y]
    | x, RelevantDefs.seq ys => RelevantDefs.seq <|  x :: ys
    | x, y => RelevantDefs.seq [x, y]

instance : HAppend RelevantDefs (Array (Name × String)) RelevantDefs where
  hAppend x y := x ++ RelevantDefs.data y

def RelevantDefs.empty := RelevantDefs.seq []

def RelevantDefs.base := RelevantDefs.env

def RelevantDefs.addDefs (nbs: Array (Name × String)) (nbd: RelevantDefs) : RelevantDefs :=
  nbd ++ nbs

open LeanAide

partial def RelevantDefs.names (nbd: RelevantDefs)(s: String) (pairs : Array (String × Json)) : TranslateM (Array Name) := do
  match nbd with
  | RelevantDefs.select bound? =>
    let pairs := pairs.filter fun (doc, _) => match bound? with
      | some bound => doc.length < bound
      | none => true
    return pairs.filterMap fun (_, js) => do
      js.getObjValAs? Name "name" |>.toOption
  | RelevantDefs.closure num depth =>
    let searchNames : Array Name := pairs.filterMap (fun (_, js) => do
      js.getObjValAs? Name "name" |>.toOption
    )
    bestDefsInConsts num searchNames.toList depth
  | RelevantDefs.env => do
    let env ← get
    return env.defs.map (·.name)
  | .data d => return d.map (·.1)
  | RelevantDefs.seq nbs => do
    let names ← nbs.mapM fun nb => nb.names s pairs
    return names.toArray.flatten

partial def RelevantDefs.blob (nbd: RelevantDefs)(s: String) (pairs : Array (String × Json)) : TranslateM (Array String) := do
  match nbd with
  | RelevantDefs.select bound? =>
    let pairs := pairs.filter fun (doc, _) => match bound? with
      | some bound => doc.length < bound
      | none => true
    return pairs.filterMap fun (doc, js) =>
      fullStatement? js |>.map fun s => s!"/-- {doc} -/" ++ "\n" ++ s
  | RelevantDefs.closure num depth =>
    let searchNames : Array Name := pairs.filterMap (fun (_, js) => do
      js.getObjValAs? Name "name" |>.toOption
    )
    let names ← bestDefsInConsts num searchNames.toList depth
    names.filterMapM fun n => do
      let info ← getConstInfo n
      let doc? ← findDocString? (← getEnv) n
      match doc? with
      | some doc =>
        let value? ← info.value?.mapM fun e => PrettyPrinter.delab e
        mkStatementWithDoc n
          (← PrettyPrinter.delab info.type) value? false (doc := doc) (isNoncomputable := Lean.isNoncomputable (← getEnv) n)
      | none =>
        mkStatement n (← PrettyPrinter.delab info.type) none false (isNoncomputable := Lean.isNoncomputable (← getEnv) n)
  | RelevantDefs.env => do
    defsBlob
  | .data d => return d.map (·.2)
  | RelevantDefs.seq nbs => do
    let names ← nbs.mapM fun nb => nb.blob s pairs
    return names.toArray.flatten


def translatePromptPairs (docPairs: Array (String × Json))
      : Array (String × Json) :=
  docPairs.map fun (doc, thm) =>
    let isThm :=
      thm.getObjValAs? Bool "isProp" |>.toOption |>.getD true
    let head := if isThm then "Theorem" else "Definition"
    (s!"Translate the following statement into Lean 4:\n## {head}: " ++ doc ++ "\n\nGive ONLY the Lean code", thm)


def translateMessages (s: String)(promptPairs: Array (String × Json))
      (header: String) (dfns: Array String) (toChat : ChatExampleType)
      (msg: MessageBuilder) : TranslateM Json := do
  let examples ←  promptPairs.filterMapM fun pair =>
    toChat.map? pair
  let examples :=
    examples ++ (← getRecentTranslations)
  let preludeCode :=
    if dfns.isEmpty then ""
    else
        let defsBlob := dfns.foldr (fun acc df => acc ++ "\n\n" ++ df) ""
        s!"Your goal is to translate from natural language to Lean. The following are some definitions that may be relevant:\n\n{defsBlob}"

  trace[Translate.info] m!"examples: \n{(examples).size}"
  let s' := preludeCode ++ s!"Translate the following statement into Lean 4:\n## {header}: " ++ s ++ "\n\nGive ONLY the Lean code"
  mkMessages s' examples (← transPrompt) msg

/--
Structure collecting together parameters used in translation.
-/
structure Translator where
  /-- The LLM server being used. -/
  server : ChatServer := .default
  /-- Parameters for the LLM server called. -/
  params : ChatParams := {n := 8}
  /-- Builder for prompt examples given sentence. -/
  pb : PromptExampleBuilder := .default
  /-- Chat examples, i.e., the dialogues of `user` and `assistant`, from the examples. -/
  toChat : ChatExampleType := .simple
  /-- Relevant definitions to include in the prompt -/
  messageBuilder : MessageBuilder := server.messageBuilder
  useInstructions : Bool := messageBuilder.useInstructions
  relDefs : RelevantDefs := .empty
  /-- Whether to do a roundtrip test -/
  roundTrip : Bool := false
  /-- Whether to select the first elaboration that passes a roundtrip-/
  roundTripSelect : Bool := false -- selecting first to pass roundtrip
  reasoningServer : ChatServer := .openAI "o3-mini"
deriving Repr, FromJson, ToJson

def Translator.forDef (t: Translator)  : Translator :=
  let chat : ChatExampleType := match t.toChat with
  | .simple => .doc
  | .detailed => .detailedDoc
  | x => x
  {t with toChat := chat}

def Translator.reasoning (t: Translator) : Translator :=
  {t with params := {t.params with n := 1, temp := 1.0}}

/--
Structure collecting together parameters used in code generation.
-/
structure CodeGenerator extends Translator where
  numLeanSearch : Nat := 6
  numMoogle : Nat := 6
  numLeanSearchDirect : Nat := 2
  numMoogleDirect : Nat := 2
deriving Repr, FromJson, ToJson

def Translator.codeGenerator (t: Translator) : CodeGenerator := {t with}

def CodeGenerator.default : CodeGenerator :=
  {}
-- #eval toJson <| ({} : CodeGenerator)
-- #eval (fromJson? (toJson <| ({} : CodeGenerator)) : Except _ Translator)

register_option lean_aide.translate.prompt_size : Nat :=
  { defValue := 8
    group := "lean_aide.translate"
    descr := "Number of document strings in a prompt (default 8)" }

register_option lean_aide.translate.concise_desc_size : Nat :=
  { defValue := 0
    group := "lean_aide.translate"
    descr := "Number of concise descriptions in a prompt (default 0)" }

register_option lean_aide.translate.desc_size : Nat :=
  { defValue := 0
    group := "lean_aide.translate"
    descr := "Number of descriptions in a prompt (default 0)" }


register_option lean_aide.translate.choices : Nat :=
  { defValue := 8
    group := "lean_aide.translate"
    descr := "Number of outputs to request in a query (default 8)." }

register_option lean_aide.translate.use_defintions : Bool :=
  { defValue := true
    group := "lean_aide.translate"
    descr := "Whether to use docstrings of definitions (in addition to theorems)." }

register_option lean_aide.translate.definition_penalty : Nat :=
  { defValue := 20
    group := "lean_aide.translate"
    descr := "Penalty for a prompt being from a definition scaled by 10" }

register_option lean_aide.translate.model : String :=
  { defValue := "gpt-5"
    group := "lean_aide.translate"
    descr := "Model to use (gpt-5.1)." }

register_option lean_aide.translate.azure : Bool :=
  { defValue := false
    group := "lean_aide.translate"
    descr := "Whether to use Azure OpenAI." }

register_option lean_aide.translate.url? : String :=
  { defValue := ""
    group := "lean_aide.translate"
    descr := "Local or generic url to query. Empty string for none" }

register_option lean_aide.translate.authkey? : String :=
  { defValue := ""
    group := "lean_aide.translate"
    descr := "Authentication key for OpenAI or generic model" }

register_option lean_aide.translate.examples_url? : String :=
  { defValue := ""
    group := "lean_aide.translate"
    descr := "Local or generic url to query for embeddings. Empty string for none" }

register_option lean_aide.translate.greedy : Bool :=
  { defValue := false
    group := "lean_aide.translate"
    descr := "Whether to choose the first elaboration." }

register_option lean_aide.translate.has_sysprompt : Bool :=
  { defValue := true
    group := "lean_aide.translate"
    descr := "Whether the server has a system prompt." }

register_option lean_aide.translate.temperature10 : Int :=
  { defValue := 10
    group := "lean_aide.translate"
    descr := "temperature * 10." }

/--
Number of similar sentences to query in interactive mode
-/
def promptSize : CoreM Nat := do
  return  lean_aide.translate.prompt_size.get (← getOptions)

/--
Number of similar concise descriptions to query in interactive mode
-/
def conciseDescSize : CoreM Nat := do
  return  lean_aide.translate.concise_desc_size.get (← getOptions)

def descSize : CoreM Nat := do
  return  lean_aide.translate.desc_size.get (← getOptions)

/--
Parameters for a chat query in interactive mode
-/
def chatParams : CoreM ChatParams := do
  let opts ← getOptions
  return {
    n := lean_aide.translate.choices.get opts,
    temp := {mantissa:= lean_aide.translate.temperature10.get opts, exponent :=1}
  }

def greedy : CoreM Bool := do
  return lean_aide.translate.greedy.get (← getOptions)

def hasSysPrompt : CoreM Bool := do
  return lean_aide.translate.has_sysprompt.get (← getOptions)

/--
Chat server to use in interactive mode
-/
def chatServer : CoreM ChatServer := do
  let opts ← getOptions
  let model := lean_aide.translate.model.get opts
  if lean_aide.translate.azure.get opts then
    return ChatServer.azure
  else
    let authkeyString := lean_aide.translate.authkey?.get opts
    let authKey? :=
      if authkeyString = "" then none else some authkeyString
    let url := lean_aide.translate.url?.get opts
    if url.isEmpty then
      return ChatServer.openAI model |>.addKeyOpt authKey?
    else
      return ChatServer.generic model url none (← hasSysPrompt)

def Translator.defaultM : CoreM Translator := do
  return {server := ← chatServer, pb := PromptExampleBuilder.similarBuilder (← promptSize) (← conciseDescSize) 0, params := ← chatParams, toChat := .simple}

def Translator.defaultDefM : CoreM Translator := do
  let t ← defaultM
  return t.forDef

def ElabError.fallback (errs : Array ElabError) :
    TranslateM String := do
  let bestParsed? := errs.findSome? (fun e => do
    match e with
    | ElabError.parsed e .. => some e
    | _ => none)
  match bestParsed? with
  | some e => return e
  | none => match errs[0]? with
    | some e => return e.text
    | _ => throwError "no outputs found"

def ElabError.fallback? (errs : Array ElabError) :
    TranslateM (Except (Array ElabError) String) := do
  let bestParsed? := errs.findSome? (fun e => do
    match e with
    | ElabError.parsed e .. => return .ok e
    | _ => none)
  match bestParsed? with
  | some e => return e
  | none => match errs[0]? with
    | some e => return .ok e.text
    | _ => return .error errs


end LeanAide

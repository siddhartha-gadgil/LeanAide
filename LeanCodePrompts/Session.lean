import LeanCodePrompts.BatchTranslate
import LeanAide.Aides
import LeanAide.Descriptions
import LeanAide.PutnamBench
/-!
# Translation Session

This is a session for translating Lean code interactively to natural language. The goal is to allow experimentation similar to the tactics mode in Lean, but for translation. Caching should ensure that if the same query is recomputed, there is no cost.

A session is a term of type `SessionM Unit`. The state keeps track of the history and various settings. We have commands for modifying the settings and for translating and related tasks. Some of the commands are:

* `translate`: translating a string literal that is given or from the context.
* `consider`: add a string literal to the context.
* `translateDef`: translate a definition.
* `promptExamples`: generate a prompt for a string literal.
* `message`: the message to be sent to the chat server.
* `roundtrip` for testing and selecting the first translation that passes roundtrip.
* `add_prompt`: add a fixed prompt to the context to be used.
* `add_definition`: add a definition to the context to be used.
* `set` and `get` for the prompt builder, server, and other settings.

Commands need to be designed for more complex tasks:

* Given the name of something in Mathlib, add the corresponding definition or prompt to the context.
* On locating a missing definition, translate it and add it to the context.
-/

open Lean Meta Elab
open LeanAide.Meta
namespace LeanAide.Translate

structure SessionM.State where
  server : ChatServer := ChatServer.default
  params : ChatParams := {n := 10, temp := ⟨8, 1⟩}
  pb : PromptExampleBuilder := PromptExampleBuilder.classicDefault
  toChat : ChatExampleType := .simple
  relDefs : RelevantDefs := .empty
  roundTrip : Bool := false
  roundTripSelect : Bool := false -- selecting first to pass roundtrip

  contextStatements : Array String := #[]
  translationStack: Array (Name × TranslateResult) := #[]
  defTranslationStack: Array <| Name × (Except (Array CmdElabError) DefData) := #[]
  logs : Array Json := #[]

  descFields: List String := ["concise-description", "description"]
  preferDocs : Bool := true

abbrev SessionM := StateT  SessionM.State TranslateM

abbrev Session := SessionM Unit

def sessionLogs (sess: Session) : TranslateM (Format) := do
  let (_, s) ←  sess.run {logs := #[]}
  let logs := s.logs.foldl (init := "") fun acc s => acc ++ s.pretty ++ "\n"
  return logs

namespace Session

def getParams : SessionM ChatParams := do
  return (← get).params

def setParams (params : ChatParams) : SessionM Unit := do
  modify fun s => {s with params := params}

def getServer : SessionM (Option ChatServer) := do
  return (← get).server

def setServer (server : ChatServer) : SessionM Unit := do
  modify fun s => {s with server := server}

def getPromptBuilder : SessionM PromptExampleBuilder := do
  return (← get).pb

def setPromptBuilder (pb : PromptExampleBuilder) : SessionM Unit := do
  modify fun s => {s with pb := pb}

def getRoundTrip : SessionM Bool := do
  return (← get).roundTrip

def setRoundTrip (value : Bool) : SessionM Unit := do
  modify fun s => {s with roundTrip := value}

def getRoundTripSelect : SessionM Bool := do
  return (← get).roundTripSelect

def setRoundTripSelect (value : Bool) : SessionM Unit := do
  modify fun s => {s with roundTripSelect := value}

def getToChat : SessionM ChatExampleType := do
  return (← get).toChat

def setToChat (value : ChatExampleType) : SessionM Unit := do
  modify fun s => {s with toChat := value}

def detailedPrompt : SessionM Unit := do
  setToChat .detailed

def simplePrompt : SessionM Unit := do
  setToChat .simple

def docPrompt : SessionM Unit := do
  setToChat .doc

def getRelDefs : SessionM RelevantDefs := do
  return (← get).relDefs

def setRelDefs (value : RelevantDefs) : SessionM Unit := do
  modify fun s => {s with relDefs := value}

def useEnvDefs : SessionM Unit := do
  modify fun s => {s with relDefs := s.relDefs ++ .env}

def getTranslator : SessionM Translator := do
  let s ← get
  return {server := s.server, params := s.params, pb := s.pb, toChat := s.toChat, relDefs := s.relDefs, roundTrip := s.roundTrip, roundTripSelect := s.roundTripSelect}

def addTranslation (name : Name := Name.anonymous) (result : TranslateResult) : SessionM Unit := do
  modify fun s => {s with translationStack := s.translationStack.push (name, result)}

def addDefTranslation (name : Name := Name.anonymous) (result : Except (Array CmdElabError) DefData) : SessionM Unit := do
  modify fun s => {s with defTranslationStack := s.defTranslationStack.push (name, result)}

def findTranslationByName? (name : Name) : SessionM (Option TranslateResult) := do
  let stack := (← get).translationStack
  return stack.find? (fun (n, _) => n == name) |>.map Prod.snd

def getLastTranslation? : SessionM (Option (Name × TranslateResult)) := do
  let stack := (← get).translationStack
  return stack.back?

-- Simple commands to be used in the session.


def say [ToJson α] (msg : α) (name: Name := `say): SessionM Unit := do
  let msg := Json.mkObj [("cmd", toJson name), ("res", toJson msg)]
  modify fun s => {s with logs := s.logs.push msg}

def sayM [ToJson α] (msg : SessionM α) (name: Name := `sayM) : SessionM Unit := do
  let msg ← msg
  say msg name


def showLastText : SessionM Unit := do
  match (← get).contextStatements.back? with
  | some s => say s
  | none => say "No text in context"

def consider (statement: String) : SessionM Unit := do
  say statement `consider
  modify fun s =>
    {s with contextStatements := s.contextStatements.push statement}

def considerAll (statements: Array String) : SessionM Unit := do
  say statements `considerAll
  modify fun s =>
    {s with contextStatements := s.contextStatements ++ statements}
  showLastText

def text : SessionM String := do
  match (← get).contextStatements.back? with
  | some s => return s
  | none =>
      throwError "ERROR: No text in context"

def skipText : SessionM Unit := do
  modify fun s =>
    {s with contextStatements := s.contextStatements.pop}
  showLastText


def translate (s : String) (name: Name := Name.anonymous) : SessionM Unit := do
  let translator ← getTranslator
  say ("Translating: " ++ s) `translate
  let (res, prompt) ← translator.translateM s
  match res with
  | Except.ok res => do
    say "Success in translation" `translate
    say res.toElabSuccessBase `translate
  | Except.error err =>
    say "Error in translation" `translate
    say "Prompt:" `translate
    say prompt `translate
    for e in err do
      say e `translate
  let result : TranslateResult :=
    match res with
    | Except.ok res => do
      Except.ok res
    | Except.error err =>
      Except.error {source := s, prompt? := prompt, elabErrors := err}
  addTranslation name result

def translateText (name: Name := Name.anonymous) : SessionM Unit := do
  let s ← text
  translate s name

def translateDef (s: String)(n: Name)(add : Bool := true) : SessionM Unit := do
  let translator ← getTranslator
  let res ← translator.translateDefData? s
  addDefTranslation n res
  match res with
  | Except.ok res => do
    say "Success in translation" `translateDef
    sayM res.jsonView `translateDef
    if add then
      let dd : DefWithDoc := {res with doc := s}
      addDefn dd
  | Except.error err =>
    say "Error in translation"
    for e in err do
      say e `translateDef

def docs (s: String) : SessionM (Array (String × Json)) := do
  let translator ← getTranslator
  let docs ← translator.pb.getPromptPairs s
  say docs `docs
  return docs

def docsText : SessionM (Array (String × Json)) := do
  let s ← text
  docs s

def messages (s: String) (header: String := "theorem") : SessionM Json := do
  let translator ← getTranslator
  let docPairs ← docs s
  let dfns ← translator.relDefs.blob s docPairs
  let promptPairs := translatePromptPairs docPairs dfns
  let messages ←
    translateMessages s promptPairs header translator.toChat translator.server.hasSysPrompt
  say messages `messages
  return messages

def messagesText (header: String := "theorem") : SessionM Json := do
  let s ← text
  messages s header

def add_prompt (name: Name)(type? : Option String := none) (docString?: Option String := none) : SessionM Unit := do
  let sr : SearchResult := {name := name.toString, type? := type?, docString? := docString?, doc_url? := none, kind? := none}
  let state ← get
  let pair? ← sr.withDoc? state.descFields state.preferDocs
  match pair? with
  | some pair => do
    let pb ← getPromptBuilder
    let pb := pb.prependFixed #[pair]
    setPromptBuilder pb
  | none => throwError "No prompt found"

def add_defs (nbs: Array (Name × String)) : SessionM Unit := do
  let state ← get
  let rds := state.relDefs
  let rds := rds ++ nbs
  set {state with relDefs := rds}

def save (name?: Option Name := none) : SessionM Unit := do
  let state ← get
  let logs := state.logs
  let name := name?.map (·.toString) |>.getD s!"session_{hash logs}"
  let path := System.mkFilePath ["sessions", s!"{name}.json"]
  let json := Json.arr logs
  IO.FS.writeFile path json.pretty

end Session

open Session

def eg : Session := do
  consider "Let $n$ be a natural number."
  let t ← text
  say t ; #eval sessionLogs eg

macro "#session" n:ident ":=" t:term : command => do
  withRef t (
    `(def $n : Session := $t
    #eval sessionLogs $n))

#session eg' := do
  consider "There are infinitely many odd numbers"
  setRoundTrip true
  translateText
  save `small
  consider (← putnamProblem 57)
  -- discard docsText

/-
def LeanAide.Translate.eg' : Session :=
do
  consider "There are infinitely many odd numbers"
  setRoundTrip true
  translateText
-/
#print eg'

#session putnam_eg := do
  for i in [15:45] do
    consider (← putnamProblem i)
    -- translateText

#session def_eg := do
  translateDef "Let \\( \\delta(x) \\) be the greatest odd divisor of the positive integer \\( x \\)" `δ

end LeanAide.Translate

#check ExistsUnique

#check {n | Odd n}.Infinite

-- #leansearch "Topological Circle; Unit Circle."

-- #moogle "Topological Circle; Unit Circle."

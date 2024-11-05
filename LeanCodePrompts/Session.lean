import LeanCodePrompts.BatchTranslate
import LeanAide.Aides
import LeanAide.Descriptions
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
  params : ChatParams := {}
  pb : PromptExampleBuilder := PromptExampleBuilder.default
  toChat : ChatExampleType := .simple
  relDefs : RelevantDefs := .empty
  roundTrip : Bool := false
  roundTripSelect : Bool := false -- selecting first to pass roundtrip

  contextStatement? : Option String := none
  translationStack: Array (Name × TranslateResult) := #[]
  logs : Array MessageData := #[]

abbrev SessionM := StateT  SessionM.State TranslateM

abbrev Session := SessionM Unit

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


def getTranslator : SessionM Translator := do
  let s ← get
  return {server := s.server, params := s.params, pb := s.pb, toChat := s.toChat, relDefs := s.relDefs}

def addTranslation (name : Name := Name.anonymous) (result : TranslateResult) : SessionM Unit := do
  modify fun s => {s with translationStack := s.translationStack.push (name, result)}

def findTranslationByName? (name : Name) : SessionM (Option TranslateResult) := do
  let stack := (← get).translationStack
  return stack.find? (fun (n, _) => n == name) |>.map Prod.snd

def getLastTranslation? : SessionM (Option (Name × TranslateResult)) := do
  let stack := (← get).translationStack
  return stack.back?

-- Simple commands to be used in the session.

def consider (statement: String) : SessionM Unit := do
  logInfo s!"Consider: {statement}"
  modify fun s => {s with contextStatement? := some statement}

def text : SessionM String := do
  match (← get).contextStatement? with
  | some s => return s
  | none => throwError "No text in context"

def nil : Session := pure ()

end Session




open Session

def eg : Session := do
  consider "Let $n$ be a natural number."
  let t ← text

#check eg

end LeanAide.Translate

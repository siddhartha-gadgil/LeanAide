import LeanCodePrompts.BatchTranslate
import LeanAide.Aides
import LeanAide.Descriptions
import LeanAide.PutnamBench
-- import LeanAide.Premises
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

def checkElab (s: String) : SessionM Unit := do
  let stx? := Parser.runParserCategory (← getEnv) `term s
  match stx? with
  | Except.ok stx =>
    try
      let e ← Term.withoutErrToSorry do
         Term.elabTerm stx none
      say "Elaborated" `checkEl
      let v ← ppExpr e
      say v.pretty `checkElab
      pure ()
    catch ex =>
      say "Failed to elaborate" `checkElab
      let m := ex.toMessageData
      say (← m.format).pretty `checkElab
      pure ()
  | Except.error e =>
    say "Error in parsing" `checkElab
    say e `checkElab

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
  let (messages, _) ← translator.getMessages s header
  return messages

def messagesText (header: String := "theorem") : SessionM Json := do
  let s ← text
  messages s header

def addPromptByName (name: Name)(type? : Option String := none) (docString?: Option String := none) : SessionM Unit := do
  let sr : SearchResult := {name := name.toString, type? := type?, docString? := docString?, doc_url? := none, kind? := none}
  let state ← get
  let pair? ← sr.withDoc? state.descFields state.preferDocs
  match pair? with
  | some pair => do
    let pb ← getPromptBuilder
    let pb := pb.prependFixed #[pair]
    setPromptBuilder pb
  | none => throwError "No prompt found"

def addPromptByDef (sd: SimpleDef) : SessionM Unit := do
    let pb ← getPromptBuilder
    let pb := pb.prependSimpleDef sd
    setPromptBuilder pb

def addDefsRaw (nbs: Array (Name × String)) : SessionM Unit := do
  let state ← get
  let rds := state.relDefs
  let rds := rds ++ nbs
  set {state with relDefs := rds}

def addDefRaw (name: Name)(s: String) : SessionM Unit := do
  addDefsRaw #[(name, s)]

def null : SessionM Unit := do
  return ()

syntax (name := add_def)
  withPosition("add_def%" (colGt str command)) : term

open Lean.Elab.Term
@[term_elab add_def] def addDefImpl : TermElab :=
  fun stx _ =>
    match stx with
    | `(add_def% $s $cmd) => do
      let s := s.getString
      let dfn? ←  DefData.ofSyntax? cmd
      let dfn ← match dfn? with
        | some dfn => pure dfn
        | none => throwError "Error in parsing definition"
      dfn.addDeclaration
      let dfnStatement ←  dfn.statementWithDoc s
      let name := dfn.name
      mkAppM ``addDefRaw #[toExpr name, toExpr dfnStatement]
    | _ => throwUnsupportedSyntax

def addDefByName (name: Name)(doc? : Option String := none) : SessionM Unit := do
  let dfn ← DefData.ofNameM name
  let envdoc?  ← findDocString? (← getEnv) name
  let doc? := doc?.orElse fun _ => envdoc?
  let some doc := doc? | throwError "No docstring found or specified"
  let dfnStatement ← dfn.statementWithDoc doc
  addDefRaw name dfnStatement

def chatQuery (queryString: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]) : SessionM (Array String) := do
  unless queryString.endsWith "." || queryString.endsWith "?" do
    say "Query should end with a full stop or question mark" `chatQuery
    return #[]
  let translator ← getTranslator
  let server := translator.server
  let res ← server.mathCompletions queryString n params examples
  say "Chat Query responses" `chatQuery
  say res `chatQuery
  return res

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
  discard <|  chatQuery "Are there infinitely many odd numbers?"
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


#session translate_def_eg := do
  translateDef "Let
𝛿
(
𝑥
)
δ(x) for a positive integer
𝑥
x be the odd positive integer
𝑑
d such that
𝑑
d divides
𝑥
x and, for every odd positive integer
𝑑
′
d
′
 , if
𝑑
′
d
′
  divides
𝑥
x, then
𝑑
′
≤
𝑑
d
′
 ≤d." `δ

#session eg_add_def := do
  sayM getRelDefs
  checkElab "(0 : Nat) = 1"
  checkElab "eg = 1"
  add_def%
    "Hello"
    def egg : Nat := Nat.zero
  sayM getRelDefs
  checkElab "egg"
  sayM <| messages "scrambled egg"

def quas : (N : Nat) → Prop :=
  fun N => N > 0 ∧ (Finset.sum (Nat.divisors N) id = 2 * N + 1)

#session quasi_add_def := do
  sayM getRelDefs
  add_def%
    "Definition of quasiperfect"
    def quas : (N : ℕ) → Prop := fun N => N > 0 ∧ (Finset.sum (Nat.divisors N) id = 2 * N + 1)
  sayM getRelDefs
  checkElab "quas"

#session translate_def := do
  translateDef "Let $c$ be a real number such that $n^c$ is an integer for every positive integer $n$." `c

#session putnam_eg' := do
    consider (← putnamProblem 247)

#session translatee := do
  translateDef "Let $s_k (a_1, a_2, \\dots, a_n)$ denote the sum of all $k$-fold products of the $a_i$. For example, $s_1 (a_1, \\dots, a_n) = \\sum_{i=1}^{n} a_i$, and $s_2 (a_1, a_2, a_3) = a_1a_2 + a_2a_3 + a_1a_3$." `ex


#session env_add_def := do
  consider "Let $a_1, a_2, \\dots, a_n$ be real numbers, and let $b_1, b_2, \\dots, b_n$ be distinct positive integers. Suppose that there is a polynomial $f(x)$ satisfying the identity\n\\[\n(1-x)^n f(x) = 1 + \\sum_{i=1}^n a_i x^{b_i}.] Show that $f(1) = b_1 b_2 \\dots b_n / n!$."
  setRoundTrip true
  translateText

#session exp := do
  sayM getRelDefs
  add_def%
    "Def of del"
    def del : (x : ℕ) → ℕ := fun x => if x = 0 then 0 else Nat.findGreatest (fun d => d ∣ x ∧ d % 2 = 1) x
  sayM getRelDefs
  checkElab "del"
  consider "Using the delta definition from above show that $|\\sum_{n = 1}^x \\delta(n)/n - 2x/3| < 1$ for all positive integers $x$."
  setRoundTrip true
  translateText

#session tri := do
consider "Let $z_i$ be complex numbers for $i = 1, 2, \\dots, n$. Show that\n\\[\n\\left \\lvert \\mathrm{Re} \\, [(z_1^2 + z_2^2 + \\dots + z_n^2)^{1/2} ] \\right \\rvert \\leq \\lvert \\mathrm{Re} \\, z_1 \\rvert + \\lvert \\mathrm{Re} \\, z_2 \\rvert + \\dots + \\lvert \\mathrm{Re} \\, z_n \\rvert.\n\\]"
setRoundTrip true
translateText

#check Nat.add

-- Avoid this
#session egP := do
  addPromptByDef {name := "δ", type := "ℕ → ℕ", docString := "The greatest odd divisor of a positive integer.", isProp := false}
  discard <|  docs "There are infinitely many odd numbers"

end LeanAide.Translate

#check ExistsUnique

#check {n | Odd n}.Infinite

-- #leansearch "Topological Circle; Unit Circle."

-- #moogle "Topological Circle; Unit Circle."

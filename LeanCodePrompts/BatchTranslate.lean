import LeanCodePrompts.Translate
import LeanAide.Aides
import LeanAide.Descriptions

open Lean Meta Elab
open LeanAide.Meta
namespace LeanAide.Translator
open Translate

/--
Translate a string to a Lean expression using the GPT model, returning the expression, all outputs and the prompt used.
-/
def translateWithDataM (s: String)(translator: Translator)  (repeats: Nat := 0)(sleepTime : Nat := 1)
  (queryData? : Option <| (Std.HashMap String Json) := none ) :
  TranslateM ((Except (Array ElabError) (ElabSuccessResult)) × Array String × (Option Json)) := do
  let (output, prompt?) ←  match queryData? with
  | none =>
    let (js,prompt, _) ← translator.getLeanCodeJson s
    pure (← getMessageContents js, some prompt)
  | some f =>
    let res? := f.get? s.trim
    match res? with
    | none =>
      throwError s!"no data for {s}"
    | some js =>
      let arr := js.getArr? |>.toOption.get!
      pure (arr.map fun js => js.getStr!, none)
  if output.isEmpty then
  match repeats with
  | 0 => return (Except.error #[], output, prompt?)
  | k + 1 =>
    logToStdErr `leanaide.translate.info s!"No outputs; repeating ({k} left)"
    IO.sleep (sleepTime * 1000).toUInt32
    translator.translateWithDataM s
       k
      (sleepTime * 2) queryData?
  else
    -- let output := params.splitOutputs output
    let res? ← bestElab? output
    match res? with
    | Except.error err =>
      appendLog "translate_fail" <| toJson err
      return (Except.error err, output, prompt?)
    | Except.ok res =>
      return (Except.ok res, output, prompt?)



/--
Translate theorems in a given file and record results in a JSON file.
-/
def checkTranslatedThmsM(inputFile: String := "thm")(translator: Translator)
  (delay: Nat := 20)(repeats: Nat := 0)(queryData? : Option <| (Std.HashMap String Json) )(tag: Bool := false) : TranslateM Json := do
  logToStdErr `leanaide.translate.info s!"Writing to file: {inputFile}-elab-{translator.pb.signature}-{translator.params.n}-{translator.params.temp.mantissa}.json"
  let promptsFile := System.mkFilePath ["data",
    s!"prompts-{inputFile}-{translator.pb.signature}-{translator.params.n}-{translator.params.temp.mantissa}.jsonl"]
  let gitHash ← gitHash
  let outFile :=
      if tag then
      System.mkFilePath
      ["results", translator.server.model,gitHash,
      s!"{inputFile}-elab-{translator.pb.signature}-{translator.params.n}-{translator.params.temp.mantissa}.jsonl"]
      else
      System.mkFilePath
      ["results", translator.server.model,
      s!"{inputFile}-elab-{translator.pb.signature}-{translator.params.n}-{translator.params.temp.mantissa}.jsonl"]
  IO.println s!"Writing to {outFile}"
  IO.FS.writeFile outFile ""
  let outHandle ← IO.FS.Handle.mk outFile IO.FS.Mode.append
  let h ← IO.FS.Handle.mk promptsFile IO.FS.Mode.append
  let file := System.mkFilePath [s!"data/{inputFile}-prompts.txt"]
  let statements ←  IO.FS.lines file
  let statements :=
      statements.map <| fun s => s.replace "<br>" "\n" |>.replace "\\n" "\n"
  let mut count := 0
  let mut elaborated := 0
  let mut roundTripError := 0
  let mut elabData: Array Json := #[]
  let mut failed : Array (ElabErrorData) := #[]
  for statement in statements do
    trace[Translate.info] m!"{statement}"
    IO.println ""
    IO.println statement
    let (res?, _, prompt?) ←
        translator.translateWithDataM statement  repeats 0 queryData?
    let fullPrompt := prompt?.getD "No prompt (maybe using cached data)"
    let js := Json.mkObj [("text", Json.str statement),
       ("fullPrompt", fullPrompt)]
    h.putStrLn <| js.compress
    count := count + 1
    match res? with
    | Except.ok res =>
      let v ← res.view
      logToStdErr `leanaide.translate.info s!"theorem {v}"
      elaborated := elaborated + 1
      let js := Json.mkObj [("text", Json.str statement),
       ("prompt", toJson prompt?),
       ("result-obtained", true),
       ("theorem", v),
       ("all-elaborations", Json.arr <| res.allElaborated.map Json.str),
       ("elaboration-groups", Json.arr <| res.groups.map (Json.arr ∘ Array.map Json.str))]

      let (js, rt) ←  if translator.roundTrip then
          let pair? ←  checkTranslationM statement res.term translator
          let translateBackResult : TranslateBackResult := match pair? with
          | none => .failure
          | some (translation, check') =>
            let check := check'.map (·.1)
            let checkData := check'.map (·.2)
            .success statement translation check checkData
          pure <| (js.mergeObj (toJson translateBackResult), translateBackResult.checkFailed)
        else
          pure (js, true)
      unless rt do
        roundTripError := roundTripError + 1
      outHandle.putStrLn <| js.compress
      elabData := elabData.push js
    | .error err =>
      logToStdErr `leanaide.translate.info "failed to elaborate"
      failed := failed.push ⟨statement, prompt?, err⟩
    logToStdErr `leanaide.translate.info s!"total : {count}"
    logToStdErr `leanaide.translate.info s!"elaborated: {elaborated}"
    logToStdErr `leanaide.translate.info s!"roundtrip errors: {roundTripError}"
    IO.sleep <| (delay * 1000).toUInt32

  let js :=
    Json.mkObj
      [("total-prompts", count),
        ("elaborated", elaborated),
        ("number-similar-sentences", translator.pb.signature),
        ("prompt-examples", toJson translator.pb),
       ("query-number", translator.params.n),
       ("temperature", Json.num translator.params.temp),
       ("elaborated-prompts", Json.arr elabData),
        ("roundtrip-errors", roundTripError),
        ("failures", Json.arr <| failed.map (toJson))
            ]
  return js


def parsedThmsPrompt : IO (Array String) := do
  let file := System.mkFilePath ["data/parsed_thms.txt"]
  IO.FS.lines file

/--
Split theorems based on whether they elaborate
-/
def elabThmSplit(start? size?: Option Nat := none) : TranslateM ((Array String) × (Array String)) := do
  let deps ← parsedThmsPrompt
  let deps := deps.toList.drop (start?.getD 0)
  let deps := deps.take (size?.getD (deps.length))
  let deps := deps.toArray
  let mut succ: Array String := Array.empty
  let mut fail: Array String := Array.empty
  let mut count := start?.getD 0
  let succFile := System.mkFilePath ["extra_resources", "elab_thms.txt"]
  let h ← IO.FS.Handle.mk succFile IO.FS.Mode.append
  IO.println s!"total: {deps.size}"
  for thm in deps do
    IO.println s!"parsing theorem {thm}"
    let chk ←  hasElab thm
    count := count + 1
    if chk then
      succ := succ.push thm
      h.putStrLn thm
    else
      fail := fail.push thm
    IO.println s!"parsed: {count}"
    IO.println s!"elaborated: {succ.size}"
  return (succ, fail)

/--
Split theorems based on whether they elaborate
-/
def elabThmSplitCore(start? size?: Option Nat := none) : CoreM ((Array String) × (Array String)) :=
  (elabThmSplit start? size? |>.run' {}).run'.run'

/--
Check theorems in file and return data on success in elaboration.
-/
def outputFromCompletionsM (s: String) :
  TranslateM (String) := do
  let output ← exprStrsFromJsonStr s
  let output := output ++ (output.map (fun s => ": " ++ s))
  -- IO.println s!"output: {output}"
  let res? ← bestElab? output
  let js : Json ←  match res?.toOption with
  | some res => do
    let thm ←  res.view
    pure <| Json.mkObj [("success", Bool.true), ("theorem", thm),
            ("all-elabs", Json.arr <| res.allElaborated.map (Json.str))]
  | none => pure <| Json.mkObj [("success", Bool.false)]
  return js.compress

/--
Check theorems in file and return data on success in elaboration.
-/
def outputFromCompletionsCore (s: String) : CoreM String :=
  (outputFromCompletionsM s |>.run' {}).run'.run'

def checkStatementTranslationM (s: String) (typeString: String) (translator: Translator) :
  TranslateM <| Option (String × Array (Bool × String)) := do
  match ← elabThm4 typeString with
  | Except.error err =>
    logWarning s!"error while elaborating: {repr err}"
    return none
  | Except.ok type => do
    let triple? ←  getTypeDescriptionM type translator
    triple?.mapM fun (transl, _, defBlob?) => do
      logToStdErr `leanaide.translate.info s!"translation: {transl}"
      let checks ← ChatServer.checkEquivalence s transl defBlob? (server:= translator.reasoningServer)
      return (transl,  checks)

import LeanCodePrompts.Translate
import LeanAide.Aides
import LeanAide.Descriptions

open Lean Meta Elab
open LeanAide.Meta

/--
Translate a string to a Lean expression using the GPT model, returning the expression, all outputs and the prompt used.
-/
def translateWithDataM (s: String)(server: ChatServer)
  (params: ChatParams)(pb: PromptExampleBuilder := .embedBuilder 10 0 0)  (repeats: Nat := 0)(sleepTime : Nat := 1)
  (queryData? : Option <| (HashMap String Json)  )(toChat : ChatExampleType := .simple) (relDefs: RelevantDefs := .empty) :
  TranslateM ((Except (Array ElabError) (ElabResult)) × Array String × (Option String)) := do
  let (output, prompt?) ←  match queryData? with
  | none =>
    let (js,prompt, _) ← getLeanCodeJson s server params pb toChat (relDefs := relDefs)
    pure (← getMessageContents js, some prompt.pretty)
  | some f =>
    let res? := f.find? s.trim
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
    IO.eprintln s!"No outputs; repeating ({k} left)"
    IO.sleep (sleepTime * 1000).toUInt32
    translateWithDataM s server params
      pb k
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
def checkTranslatedThmsM(inputFile: String := "thm")(server: ChatServer)
  (params: ChatParams)(pb: PromptExampleBuilder := .embedBuilder 10 0 0)
  (delay: Nat := 20)(repeats: Nat := 0)(queryData? : Option <| (HashMap String Json) )(tag: Bool := false)(toChat : ChatExampleType := .simple)(roundtrip: Bool := false) : TranslateM Json := do
  IO.eprintln s!"Writing to file: {inputFile}-elab-{pb.signature}-{params.n}-{params.temp.mantissa}.json"
  let promptsFile := System.mkFilePath ["data",
    s!"prompts-{inputFile}-{pb.signature}-{params.n}-{params.temp.mantissa}.jsonl"]
  let gitHash ← gitHash
  let outFile :=
      if tag then
      System.mkFilePath
      ["results", server.model,gitHash,
      s!"{inputFile}-elab-{pb.signature}-{params.n}-{params.temp.mantissa}.jsonl"]
      else
      System.mkFilePath
      ["results", server.model,
      s!"{inputFile}-elab-{pb.signature}-{params.n}-{params.temp.mantissa}.jsonl"]
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
  let mut elabPairs: Array (String × String × (Array String) × Array (Array String)) := #[]
  let mut failed : Array (Array ElabError) := #[]
  for statement in statements do
    trace[Translate.info] m!"{statement}"
    IO.println ""
    IO.println statement
    let (res?, _, prompt?) ←
        translateWithDataM statement server params pb repeats 0 queryData? toChat
    let fullPrompt := prompt?.getD "No prompt (maybe using cached data)"
    let js := Json.mkObj [("text", Json.str statement),
       ("fullPrompt", Json.str fullPrompt)]
    h.putStrLn <| js.compress
    count := count + 1
    match res? with
    | Except.ok res =>
      let v ← res.view
      IO.eprintln s!"theorem {v}"
      elaborated := elaborated + 1
      let js := Json.mkObj [("text", Json.str statement),
       ("prompt", toJson prompt?),
       ("result-obtained", true),
       ("theorem", v),
       ("all-elaborations", Json.arr <| res.allElaborated.map Json.str),
       ("elaboration-groups", Json.arr <| res.groups.map (Json.arr ∘ Array.map Json.str))]

      let js ←  if roundtrip then
          let pair? ←  checkTranslationM statement res.term server params
          match pair? with
          | none =>
            pure <| js.mergeObj <|
              Json.mkObj [("roundtrip-success", false)]
          | some (statement, check) =>
            pure <| js.mergeObj (Json.mkObj [
               ("roundtrip-success", true),
              ("roundtrip-statement", Json.str statement),
              ("roundtrip-check", toJson check)
              ])
        else
          pure js
      outHandle.putStrLn <| js.compress
      elabPairs := elabPairs.push (statement, v, res.allElaborated, res.groups)
    | .error err =>
      IO.eprintln "failed to elaborate"
      failed := failed.push err
    IO.eprintln s!"total : {count}"
    IO.eprintln s!"elaborated: {elaborated}"
    IO.sleep <| (delay * 1000).toUInt32

  let js :=
    Json.mkObj
      [("total-prompts", count),
        ("elaborated", elaborated),
        ("number-similar-sentences", pb.signature),
        ("prompt-examples", toJson pb),
       ("query-number", params.n),
       ("temperature", Json.num params.temp),
       ("elaborated-prompts",
        Json.arr <| ←  elabPairs.mapM <|
          fun (p, s, thms, gps) => do
            return Json.mkObj [
            ("prompt", p), ("theorem", s),
            ("all-elabs", Json.arr <| thms.map (Json.str)),
            ("groups", Json.arr <| gps.map (Json.arr ∘ Array.map Json.str)),
            ("comments", ""), ("correct", Json.null),
            ("some-correct", Json.null)
            ]),
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

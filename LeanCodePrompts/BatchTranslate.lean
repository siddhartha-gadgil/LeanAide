import LeanCodePrompts.Translate
import LeanAide.Aides

open Lean Meta Elab

/--
Translate a string to a Lean expression using the GPT model, returning the expression, all outputs and the prompt used.
-/
def translateWithDataM (s: String)(server: ChatServer)
  (params: ChatParams)(numSim : Nat:= 10)(numConcise : Nat := 0)
  (includeFixed: Bool := Bool.false)
  (embedding: String)(repeats: Nat := 0)(sleepTime : Nat := 1)
  (queryData? : Option <| (HashMap String Json)  )(toChat : ToChatExample := simpleChatExample)  :
  TermElabM ((Option (Expr × (Array String) × (Array (Array String)) )) × Array String × (Option String)) := do
  let (output, prompt?) ←  match queryData? with
  | none =>
    let (js,prompt, _) ← getLeanCodeJson s server params numSim numConcise includeFixed  toChat
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
  | 0 => return (none, output, prompt?)
  | k + 1 =>
    IO.eprintln s!"No outputs; repeating ({k} left)"
    IO.sleep (sleepTime * 1000)
    translateWithDataM s server params
      numSim numConcise includeFixed embedding k
      (sleepTime * 2) queryData?
  else
    -- let output := params.splitOutputs output
    let res ← bestElab? output
    match res with
    | Except.error jsErr =>
      let js := Json.mkObj [
        ("input", Json.str s),
        ("error", jsErr)]
      appendLog "translate_fail" js
      pure ()
    | Except.ok _ =>
      pure ()
    return (res.toOption, output, prompt?)

/--
Translate a string to a Lean expression using the GPT model, returning the expression, all outputs and the prompt used.
-/
def translateWithDataCore (s: String)(server: ChatServer)
  (params: ChatParams)(numSim : Nat:= 10)(numConcise : Nat := 0)
  (includeFixed: Bool := Bool.false)
  (embedding: String)(repeats: Nat := 0)
  (queryData? : Option <| (HashMap String Json)  )
  (toChat : ToChatExample := simpleChatExample)  :
  CoreM ((Option (Expr × (Array String) ×  (Array (Array String)) )) × Array String × Option String) :=
    (translateWithDataM s server params
      numSim numConcise includeFixed
         embedding repeats
        (queryData? := queryData?)
        (toChat := toChat)).run'.run'

/--
Translate theorems in a given file and record results in a JSON file.
-/
def checkTranslatedThmsM(type: String := "thm")(server: ChatServer)
  (params: ChatParams)(numSim : Nat:= 10)(numConcise : Nat := 0)
  (includeFixed: Bool := Bool.false)(embedding: String)
  (delay: Nat := 20)(repeats: Nat := 0)(queryData? : Option <| (HashMap String Json) )(tag: Bool := false)(toChat : ToChatExample := simpleChatExample) : TermElabM Json := do
  IO.eprintln s!"Writing to file: {type}-elab-{numSim}-{includeFixed}-{params.n}-{params.temp.mantissa}.json"
  let promptsFile := System.mkFilePath ["data",
    s!"prompts-{type}-{numSim}-{includeFixed}-{params.n}-{params.temp.mantissa}.jsonl"]
  let outFile :=
      if tag then
      System.mkFilePath
      ["results", server.model, ← gitHash,
      s!"{type}-elab-{numSim}-{includeFixed}-{params.n}-{params.temp.mantissa}.jsonl"]
      else
      System.mkFilePath
      ["results", server.model,
      s!"{type}-elab-{numSim}-{includeFixed}-{params.n}-{params.temp.mantissa}.jsonl"]
  IO.println s!"Writing to {outFile}"
  IO.FS.writeFile outFile ""
  let outHandle ← IO.FS.Handle.mk outFile IO.FS.Mode.append
  let h ← IO.FS.Handle.mk promptsFile IO.FS.Mode.append
  let file := System.mkFilePath [s!"data/{type}-prompts.txt"]
  let statements ←  IO.FS.lines file
  let statements :=
      statements.map <| fun s => s.replace "<br>" "\n"
  let mut count := 0
  let mut elaborated := 0
  let mut elabPairs: Array (String × String × (Array String) × Array (Array String)) := #[]
  let mut failed : Array String := #[]
  for statement in statements do
    trace[Translate.info] m!"{statement}"
    IO.println ""
    IO.println statement
    let (res?, _, prompt?) ←
        translateWithDataM statement server params numSim numConcise includeFixed embedding repeats 0 queryData? toChat
    let fullPrompt := prompt?.getD "No prompt (maybe using cached data)"
    let js := Json.mkObj [("text", Json.str statement),
       ("fullPrompt", Json.str fullPrompt)]
    h.putStrLn <| js.compress
    count := count + 1
    match res? with
    | some (e, thms, gps) =>
      let v ← e.view
      IO.println s!"theorem {v}"
      elaborated := elaborated + 1
      let js := Json.mkObj [("text", Json.str statement),
       ("fullPrompt", Json.str fullPrompt),
       ("result", true),
       ("theorem", v),
       ("all_elaborations", Json.arr <|thms.map Json.str),
       ("gps", Json.arr <| gps.map (Json.arr ∘ Array.map Json.str))]
      outHandle.putStrLn <| js.compress
      elabPairs := elabPairs.push (statement, v, thms, gps)
    | none =>
      IO.eprintln "failed to elaborate"
      failed := failed.push statement
    IO.eprintln s!"total : {count}"
    IO.eprintln s!"elaborated: {elaborated}"
    IO.sleep <| delay * 1000

  let js :=
    Json.mkObj
      [("total-prompts", count),
        ("elaborated", elaborated),
        ("number-similar-sentences", numSim),
       ("include-fixed", includeFixed),
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
        ("failures", Json.arr <| failed.map (Json.str))
            ]
  return js

/--
Translate theorems in a given file and record results in a JSON file.
-/
def checkTranslatedThmsCore(type: String := "thm")(server: ChatServer)
  (params: ChatParams)(numSim : Nat:= 10)(numConcise : Nat := 0)
  (includeFixed: Bool := Bool.false)(embedding: String)
  (delay: Nat := 20)(repeats: Nat := 0)(queryData? : Option <| (HashMap String Json))(tag: Bool := false) (toChat : ToChatExample := simpleChatExample): CoreM Json :=
    (checkTranslatedThmsM type server params numSim numConcise includeFixed embedding delay repeats queryData? tag toChat).run'.run'

def parsedThmsPrompt : IO (Array String) := do
  let file := System.mkFilePath ["data/parsed_thms.txt"]
  IO.FS.lines file

/--
Split theorems based on whether they elaborate
-/
def elabThmSplit(start? size?: Option Nat := none) : TermElabM ((Array String) × (Array String)) := do
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
  (elabThmSplit start? size?).run'.run'

/--
Check theorems in file and return data on success in elaboration.
-/
def outputFromCompletionsM (s: String) :
  TermElabM (String) := do
  let output ← exprStrsFromJsonStr s
  let output := output ++ (output.map (fun s => ": " ++ s))
  -- IO.println s!"output: {output}"
  let res? ← bestElab? output
  let js : Json ←  match res?.toOption with
  | some (thm, elabs, _) => do
    let thm ←  thm.view
    pure <| Json.mkObj [("success", Bool.true), ("theorem", thm),
            ("all-elabs", Json.arr <| elabs.map (Json.str))]
  | none => pure <| Json.mkObj [("success", Bool.false)]
  return js.compress

/--
Check theorems in file and return data on success in elaboration.
-/
def outputFromCompletionsCore (s: String) : CoreM String :=
  (outputFromCompletionsM s).run'.run'

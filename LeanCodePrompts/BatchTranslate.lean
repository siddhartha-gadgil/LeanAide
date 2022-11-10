import LeanCodePrompts.Translate
import LeanCodePrompts.Utils

open Lean Meta Elab


def translateWithDataM (s: String)(numSim : Nat:= 10)(numKW: Nat := 1)(includeFixed: Bool := Bool.false)(queryNum: Nat := 5)(temp : JsonNumber := ⟨2, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : 
  TermElabM ((Option (Expr × (Array String) )) × Array String) := do
  let js ← 
    getCodeJson s numSim numKW includeFixed queryNum temp scoreBound matchBound
  let output ← jsonToExprStrArray js
  let output := output.toList.eraseDups.toArray
  let res ← arrayToExpr? output
  return (res, output)
  
def translateWithDataCore (s: String)(numSim : Nat:= 10)(numKW: Nat := 1)(includeFixed: Bool := Bool.false)(queryNum: Nat := 5)(temp : JsonNumber := ⟨2, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : 
  CoreM ((Option (Expr × (Array String) )) × Array String) := 
    (translateWithDataM s 
      numSim numKW includeFixed 
        queryNum temp scoreBound matchBound).run'.run'

def checkTranslatedThmsM(type: String := "thm")(numSim : Nat:= 10)(numKW: Nat := 1)(includeFixed: Bool := Bool.false)(queryNum: Nat := 5)(temp : JsonNumber := ⟨2, 1⟩) : TermElabM Json := do
  elabLog s!"Writing to file: {type}-elab-{numSim}-{numKW}-{includeFixed}-{queryNum}-{temp.mantissa}.json"
  let promptsFile := System.mkFilePath ["data",
    s!"prompts-{type}-{numSim}-{numKW}-{includeFixed}-{queryNum}-{temp.mantissa}.jsonl"]
  let h ← IO.FS.Handle.mk promptsFile IO.FS.Mode.append Bool.false
  let file := System.mkFilePath [s!"data/{type}-prompts.txt"]
  let prompts ←  IO.FS.lines file
  let prompts := 
      prompts.map <| fun s => s.replace "<br>" "\n"
  let mut count := 0
  let mut elaborated := 0
  let mut elabPairs: Array (String × String × (Array String)) := #[]
  let mut failed : Array String := #[]
  for prompt in prompts do 
    elabLog prompt
    IO.println ""
    IO.println prompt
    let (res?, outputs) ← 
        translateWithDataM prompt
          numSim numKW includeFixed queryNum temp
    let fullPrompt := (← logs 1).head! 
    let js := Json.mkObj [("text", Json.str prompt), ("fullPrompt", Json.str fullPrompt)]
    h.putStrLn <| js.pretty 10000
    count := count + 1
    match res? with
    | some (e, thms) =>
      elabLog "success"
      let v ← e.view
      elabLog s!"theorem {v}"
      IO.println s!"theorem {v}"
      elaborated := elaborated + 1
      elabPairs := elabPairs.push (prompt, v, thms) 
    | none =>
      elabLog "failed to elaborate"
      IO.println "failed to elaborate"
      failed := failed.push prompt
      elabLog s!"outputs: {outputs}"
    elabLog s!"total : {count}"
    elabLog s!"elaborated: {elaborated}"
    IO.println s!"total : {count}"
    IO.println s!"elaborated: {elaborated}"
    IO.sleep 20000

  let js := 
    Json.mkObj 
      [("total-prompts", count),
        ("elaborated", elaborated),
        ("number-similar-sentences", numSim),
       ("number-keyword-sentences", numKW),
       ("include-fixed", includeFixed),
       ("query-number", queryNum),
       ("temperature", Json.num temp),
       ("elaborated-prompts", 
        Json.arr <| ←  elabPairs.mapM <| 
          fun (p, s, thms) => do 
            return Json.mkObj [
            ("prompt", p), ("theorem", s),
            ("all-elabs", Json.arr <| thms.map (Json.str)),
            ("comments", ""), ("correct", Json.null), 
            ("some-correct", Json.null)   
            ]),
        ("failures", Json.arr <| failed.map (Json.str))
            ]
  return js

def checkTranslatedThmsCore(type: String := "thm")(numSim : Nat:= 10)(numKW: Nat := 1)(includeFixed: Bool := Bool.false)(queryNum: Nat := 5)(temp : JsonNumber := ⟨2, 1⟩) : CoreM Json :=
    (checkTranslatedThmsM type
      numSim numKW includeFixed queryNum temp).run'.run'

def parsedThmsPrompt : IO (Array String) := do
  let file := System.mkFilePath ["data/parsed_thms.txt"]
  IO.FS.lines file


def elabThmSplit(start? size?: Option Nat := none) : TermElabM ((Array String) × (Array String)) := do 
  let deps ← parsedThmsPrompt
  let deps := deps.toList.drop (start?.getD 0)
  let deps := deps.take (size?.getD (deps.length))
  let deps := deps.toArray
  let mut succ: Array String := Array.empty
  let mut fail: Array String := Array.empty
  let mut count := start?.getD 0
  let succFile := System.mkFilePath ["data/elab_thms.txt"]
  let h ← IO.FS.Handle.mk succFile IO.FS.Mode.append Bool.false
  IO.println s!"total: {deps.size}"
  for thm in deps do
    IO.println s!"parsing theorem {thm}"
    let chk ←  hasElab thm (some 25)
    count := count + 1
    if chk then
      succ := succ.push thm
      h.putStrLn thm
    else
      fail := fail.push thm
    IO.println s!"parsed: {count}"
    IO.println s!"elaborated: {succ.size}"
  return (succ, fail)

def elabThmSplitCore(start? size?: Option Nat := none) : CoreM ((Array String) × (Array String)) := 
  (elabThmSplit start? size?).run'.run'

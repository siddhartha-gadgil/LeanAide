import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.CheckParse
import LeanCodePrompts.Makecaps
import LeanCodePrompts.ParseJson
open Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false


def main (args: List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot) ["build/lib", "lean_packages/mathlib/build/lib/",  "lean_packages/std/build/lib/", "lean_packages/Qq/build/lib/", "lean_packages/aesop/build/lib/" ]
  let env ← 
    importModules [{module := `Mathlib},
    {module := `LeanCodePrompts.Basic},
    {module:= `LeanCodePrompts.CheckParse},
    {module:= `LeanCodePrompts.Makecaps},
    {module:= `LeanCodePrompts.ParseJson},
    {module := `Mathlib}] {}

  let (inpName, outName) := 
    match args with
    | [] => ("data/output_casemap.json", "data/results.json")
    | p :: [] => 
        if p.endsWith "/" then 
          (p ++ "output_casemap.json", p ++ "results.json")
       else  
          (p++ "/output_casemap.json", p++ "/results.json")
    | inp :: out :: _ => (inp, out) 
  let inpfile :=  System.mkFilePath [inpName]
  let inp ←  IO.FS.readFile inpfile
  let outfile :=  System.mkFilePath [outName]
  let mut out : Json := Json.null
  let core := readJsonCore inp
  let io? := 
    core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := env}
  match ← io?.toIO' with
  | Except.error e => 
    let m := e.toMessageData
    let outString ← m.toString
    out := Json.str outString
  | Except.ok js =>
    match js.getArr? with
    | Except.error e => 
      out := Json.str e
    | Except.ok arr =>
      let mut entries : Array Json := #[] 
      for js in arr do
        let mut entry := #[]
        let md? := js.getObjVal? "metadata"
        match md? with
        | Except.error _ => pure ()
        | Except.ok md => entry := entry.push ("metadata", md)
        let answer? : Option String := 
          match js.getObjVal? "answer" with
          | Except.error _ => none
          | Except.ok answerJs => do
            match answerJs.getStr? with
            | Except.error _ => none
            | Except.ok answer => answer
        match answer? with
          | none => pure ()
          | some answer => entry := entry.push ("answer", Json.str answer)
        match js.getObjVal? "outputs" with
        | Except.error e => 
            entry := entry.push ("error", Json.str e)
        | Except.ok arrJs => 
        match arrJs.getArr? with
        | Except.error e => 
            entry := entry.push ("error", Json.str e)
        | Except.ok arr =>
          -- this is where we do the actual work
          let mut elabChecks : Array Json := #[]
          let mut elabs : Array String := #[]
          let mut eql : Array String := #[]
          for sJs in arr do
            let mut elabEntry : Array (String × Json) := #[]
            match sJs.getStr? with
            | Except.error e => 
              elabEntry := elabEntry.push ("error", Json.str e)
            | Except.ok s =>
              elabEntry := elabEntry.push ("statement", Json.str s)
              let core := elabThmCore <|  s
              let io? := 
              core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := env}
              match ← io?.toIO' with
              | Except.ok res =>
                match res with 
                | Except.ok expr =>
                  elabEntry:= elabEntry.push ("success", Json.bool Bool.true)
                  elabEntry := elabEntry.push ("code", Json.str s!"{expr}")
                  elabs:= elabs.push <|  s
                  match answer? with 
                  | none => pure ()
                  | some answer =>
                    let core := compareThmsCore ( s) answer
                    let io? := 
                    core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := env}
                    match ← io?.toIO' with
                    | Except.ok res =>
                      match res with 
                      | Except.ok expr => do
                        if expr then eql := eql.push s
                        else pure ()
                        pure ()
                      | Except.error e =>
                        IO.println e
                        IO.println answer
                        pure ()
                    | Except.error e =>
                      IO.println "error"
                      let m := e.toMessageData
                      IO.println <| ← m.toString
                | Except.error err =>
                  elabEntry:= elabEntry.push ("success", Json.bool Bool.false)
                  elabEntry := elabEntry.push ("parse-message", Json.str err)
                  pure ()
              | Except.error e =>
                let m := e.toMessageData
                elabEntry := elabEntry.push ("error", Json.str <| ←  m.toString)
            elabChecks := elabChecks.push (Json.mkObj elabEntry.toList)
          entry := entry.push ("parse-checks", Json.arr elabChecks)
          entry := 
            entry.push ("parsed", Json.arr (elabs.map (Json.str)))
          entry := 
            entry.push ("number-parsed", Json.num elabs.size)
          entry :=
            entry.push ("equivalent", Json.arr (eql.map (Json.str)))
          entry := 
            entry.push ("number-equivalent", Json.num eql.size) 
          let core := groupTheoremsCore elabs
              let io? := 
              core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := env}
              match ← io?.toIO' with
              | Except.ok res => 
                let gps := toJson res
                entry := entry.push ("grouped", gps)
              | Except.error e =>
                let m := e.toMessageData
                entry := entry.push ("error", Json.str <| ←  m.toString)
        entries := entries.push <| Json.mkObj entry.toList
      out := Json.arr entries
  IO.FS.writeFile outfile out.pretty
  return ()
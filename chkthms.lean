import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.CheckParse
import LeanCodePrompts.Makecaps
open Lean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def chkDocs : String :=
"Utility to check whether a theorem string can be parsed (and elaborated) in lean.

- Give a single argument to check parsing.
- Give two arguments to compare results (if parsing is successful).

A theorem can be given in one of two forms

- the word `theorem` followed by a name, then the arguments, a `:`, finally the statement, or
- the arguments, a `:`, and the statement. 

The following examples are of these two forms:

- `theorem nonsense(n : Nat) (m : Nat) : n = m` 
- `(p : Nat)(q: Nat) : p = q`

Note that the arguments can be implicit or explicit. 

The underlying code also supports `open` for namespaces but this demo version does not use these. 
"

def main (args: List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot) ["build/lib", "lake-packages/mathlib/build/lib/",  "lake-packages/std/build/lib/", "lake-packages/Qq/build/lib/", "lake-packages/aesop/build/lib/", "lake-packages/proofwidgets/build/lib" ]
  let env ← 
    importModules [{module := `Mathlib},
    {module:= `LeanCodePrompts.CheckParse},
    {module := `Mathlib}] {}
  match args with
  | [] => IO.println chkDocs
  | s::[] => do
    let core := elabThmCore <| mkCap s
    let io? := 
    core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := env}
    match ← io?.toIO' with
    | Except.ok res =>
      match res with 
      | Except.ok expr =>
        IO.println "success"
        IO.println expr
      | Except.error err =>
        IO.println "failure"
        IO.println err
    | Except.error e =>
      IO.println "error"
      let m := e.toMessageData
      IO.println <| ← m.toString
  | s₁ :: s₂ :: [] => do
    let core := compareThmsCore (mkCap s₁) (mkCap s₂)
    let io? := 
    core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} {env := env}
    match ← io?.toIO' with
    | Except.ok res =>
      match res with 
      | Except.ok expr =>
        IO.println "success"
        IO.println expr
      | Except.error err =>
        IO.println "failure"
        IO.println err
    | Except.error e =>
      IO.println "error"
      let m := e.toMessageData
      IO.println <| ← m.toString
  | _ => IO.println s!"I don't know what to do with {args.length} arguments. Run with no arguments for help."
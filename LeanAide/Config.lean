import Lean
open Lean Meta

def initFiles : List System.FilePath := [".lake/build/lib", ".lake/packages/mathlib/.lake/build/lib",  ".lake/packages/Qq/.lake/build/lib", ".lake/packages/aesop/.lake/build/lib", ".lake/packages/proofwidgets/.lake/build/lib", ".lake/packages/importGraph/.lake/build/lib", ".lake/packages/batteries/.lake/build/lib", ".lake/packages/plausible/.lake/build/lib", ".lake/packages/batteries/.lake/CLi/lib", ".lake/packages/LeanSearchClient/.lake/build/lib" ]

initialize
  registerTraceClass `Translate.info
  registerTraceClass `Translate.debug
  registerTraceClass `Translate.warning
  registerTraceClass `leanaide.proof.info
  registerTraceClass `leanaide.codegen.info

initialize delab_bound : IO.Ref UInt32 ← IO.mkRef 50

def logHandle : IO IO.FS.Handle := do
  let logPath : System.FilePath :=
    ".lake/build/lib/leanaide.log"
  IO.FS.Handle.mk logPath IO.FS.Mode.append

def logTimed (message: String) : IO Unit := do
  let handle ← logHandle
  let time ← IO.monoMsNow
  let message := s!"[{time}]  {message}"
  IO.FS.Handle.putStrLn handle message
  IO.FS.Handle.flush handle

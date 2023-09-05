import Lean
open Lean Meta

def initFiles : List System.FilePath := ["build/lib", "lake-packages/mathlib/build/lib/",  "lake-packages/std/build/lib/", "lake-packages/Qq/build/lib/", "lake-packages/aesop/build/lib/", "lake-packages/proofwidgets/build/lib" ]

initialize
  registerTraceClass `Translate.info
  registerTraceClass `Translate.debug
  registerTraceClass `Translate.warning
  registerTraceClass `leanaide.proof.info

initialize delab_bound : IO.Ref UInt32 ← IO.mkRef 50

def logHandle : IO IO.FS.Handle := do 
  let logPath : System.FilePath := 
    "build/lib/leanaide.log"
  IO.FS.Handle.mk logPath IO.FS.Mode.append

def logTimed (message: String) : IO Unit := do
  let handle ← logHandle
  let time ← IO.monoMsNow
  let message := s!"[{time}]  {message}"
  IO.FS.Handle.putStrLn handle message
  IO.FS.Handle.flush handle
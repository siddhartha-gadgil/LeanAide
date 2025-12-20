import Lean
import Std
open Lean Meta

initialize
  registerTraceClass `Translate.info
  registerTraceClass `Translate.debug
  registerTraceClass `Translate.warning
  registerTraceClass `leanaide.proof.info
  registerTraceClass `leanaide.codegen.info
  registerTraceClass `leanaide.papercodes.info
  registerTraceClass `leanaide.papercodes.debug
  registerTraceClass `leanaide.llm.info
  registerTraceClass `leanaide.llm.debug
  registerTraceClass `leanaide.interpreter.info
  registerTraceClass `leanaide.interpreter.debug
  registerTraceClass `leanaide.elaboration.info
  registerTraceClass `leanaide.elaboration.debug

register_option leanaide.logging : Bool :=
  { defValue := false
    descr := "Enable LeanAide logging"
    group := "LeanAide" }

initialize delab_bound : IO.Ref UInt32 ← IO.mkRef 50

class LeanAideBaseDir where
  baseDir : IO System.FilePath

def baseDir [inst: LeanAideBaseDir] : IO System.FilePath := do
  inst.baseDir

variable [LeanAideBaseDir]

def leanAideLogging? : CoreM (Option String) := do
  let loggingEnabled : Bool := leanaide.logging.get (← getOptions)
  if loggingEnabled then return some "1"
  else IO.getEnv "LEANAIDE_LOGGING"

def leanAideLoggingIO? : IO (Option String) := do
  IO.getEnv "LEANAIDE_LOGGING"

def logHandle : IO IO.FS.Handle := do
  let logPath : System.FilePath :=
    (← baseDir) / ".lake/build/lib/leanaide.log"
  IO.FS.Handle.mk logPath IO.FS.Mode.append

def logTimed (message: String) : IO Unit := do
  match (← leanAideLoggingIO?) with
  | some "0" =>
    return ()
  | some _   => let handle ← logHandle
                let time ← IO.monoMsNow
                let message := s!"[{time}]  {message}"
                IO.FS.Handle.putStrLn handle message
                IO.FS.Handle.flush handle
  | _ =>
    return ()


def resourcesDir : IO System.FilePath := do
  let base ← baseDir
  return base / "resources"

-- #eval resourcesDir

import Lean
open Lean Meta

initialize
  registerTraceClass `Translate.info
  registerTraceClass `Translate.debug
  registerTraceClass `Translate.warning
  registerTraceClass `leanaide.proof.info
  registerTraceClass `leanaide.codegen.info
  registerTraceClass `PaperCodes.info
  registerTraceClass `PaperCodes.error

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

--#eval resourcesDir

initialize polyTraceIO : IO.Ref Bool ← IO.mkRef true
initialize polyTraceFile : IO.Ref Bool ← IO.mkRef false

namespace polyTraceIO
  def on (_ : Unit) : IO Unit := do
    let current ← polyTraceIO.get
    if current then pure () else polyTraceIO.set true

  def off (_ : Unit) : IO Unit := do
    let current ← polyTraceIO.get
    if current then polyTraceIO.set false else pure ()

  def status (_ : Unit) : IO Bool := do
    (← polyTraceIO.get)
    |> pure

end polyTraceIO

namespace polyTraceFile
  def on (_ : Unit) : IO Unit := do
    let current ← polyTraceFile.get
    if current then pure () else polyTraceFile.set true

  def off (_ : Unit) : IO Unit := do
    let current ← polyTraceFile.get
    if current then polyTraceFile.set false

  def status (_ : Unit) : IO Bool := do
    (← polyTraceFile.get)
    |> pure

end polyTraceFile

def polyTrace (tag : Name) (msg : String) : CoreM Unit := do
-- always print trace
  Lean.trace tag (fun _ => msg)
-- use mkRef to globally update this
  let isIO ← liftM <| polyTraceIO.status ()
  let isFile ← liftM <| polyTraceFile.status ()

  match isIO, isFile with
  | false, false =>
      return
  | true, false =>
      IO.eprintln s!"[{tag.toString}] [IO] {msg}"
  | false, true =>
      let currentDir ← IO.currentDir
      let logFilePath := System.mkFilePath [currentDir.toString, "output.log"]
      IO.eprintln s!"The output is logged to {logFilePath}"
      IO.FS.writeFile logFilePath s!"[File] {msg}"
  | true, true =>
      IO.eprintln s!"[{tag.toString}] [IO] {msg}"
      let currentDir ← IO.currentDir
      let logFilePath := System.mkFilePath [currentDir.toString, "output.log"]
      IO.eprintln s!"The output is logged to {logFilePath}"
      IO.FS.writeFile logFilePath s!"[File] {msg}"

def searchData : IO System.FilePath := do
  let base ← baseDir
  return base / "SimilaritySearch" / "Data"

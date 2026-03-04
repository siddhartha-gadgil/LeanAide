import Lean
import Std
import LeanAideCore.ConfigExts
open Lean Meta


open LeanAide
initialize
  registerTraceClass `leanaide.translate.info
  registerTraceClass `leanaide.translate.debug
  registerTraceClass `leanaide.translate.warning
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
  registerTraceClass `leanaide.frontend.info
  registerTraceClass `leanaide.frontend.debug
  registerTraceClass `leanaide.lctx.info
  registerTraceClass `leanaide.lctx.debug
  registerTraceClass `leanaide.tasks.info
  registerTraceClass `leanaide.tasks.debug

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

def getBaseDir : MetaM System.FilePath := do
  try
  let inst ← synthInstance (mkConst ``LeanAideBaseDir)
  let e ← mkAppOptM ``LeanAideBaseDir.baseDir #[some inst]
  let baseDir ← unsafe evalExpr (IO System.FilePath) (← mkAppM ``IO #[mkConst ``System.FilePath]) e
  return (← baseDir)
  catch _ =>
    logWarning "Could not get base directory from LeanAideBaseDir instance, falling back to current directory"
    IO.currentDir


def resourcesDir : IO System.FilePath := do
  let base ← baseDir
  return base / "resources"


def baseDirImpl : IO System.FilePath := do
  let pathLeanAidePackages := System.mkFilePath [".lake","packages","leanaide"]
  let leanAide := System.mkFilePath ["LeanAide"]
  let resources := System.mkFilePath ["resources"]
  if (← (((← IO.currentDir).join leanAide).pathExists)) &&
  (← (((← IO.currentDir).join resources).pathExists)) then
    return (← IO.currentDir)
  else if (← ((pathLeanAidePackages.join leanAide).pathExists)) && (← ((pathLeanAidePackages.join resources).pathExists)) then
    return pathLeanAidePackages
  else
    throw (IO.userError "LeanAide not found.")


def leanAidePath : IO System.FilePath := do
  return (← baseDir) / ".lake" /"packages" /"leanaide"

def cachePath : MetaM System.FilePath := do
  let path : System.FilePath := (← getBaseDir) /  ".leanaide_cache"
  if ← path.pathExists then
    return path
  else
    return (← IO.currentDir) / path
-- #eval resourcesDir

-- #eval getBaseDir

-- #eval topCodeM

-- #topCode ["imp?"] ["Hello world!", "Hi"]

-- #eval topCodeM


def topCode := topCodeData.toString

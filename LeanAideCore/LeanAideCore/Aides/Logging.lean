import Lean
import LeanAideCore.Aides.Basic
open Lean Meta

namespace LeanAide

initialize logProcess : IO.Ref String ← IO.mkRef "root"

def setLogProcess (name : String) : IO Unit :=
  logProcess.set name

def timestamp : IO String := do
  let now ← Std.Time.PlainDateTime.now
  return now.format "uuuu-MM-dd'T'HH:mm:ss"

def logIO (name : Name)(msg : String) : IO Unit := do
  let timeStr ← timestamp
  let head := s!"[{timeStr}] [{name}] [{← logProcess.get}] "
  let msg := m!"{head} {msg.replace "\n" ("\n" ++ head)}"
  IO.eprintln (← msg.toString)

def logToStdErr [ToString α] (name : Name) (msg : α ) : IO Unit := do
  logIO name (toString msg)

def logFile (name : Name)(msg : String) : IO Unit := do
  let timeStr ← timestamp
  let now ← Std.Time.PlainDateTime.now
  let date := now.format "uuuu-MM-dd"
  let logFilePath := System.mkFilePath [".logs", s!"{date}.log"]
  let handle ← IO.FS.Handle.mk logFilePath IO.FS.Mode.append
  let message := m!"[{timeStr}] [{name}] {msg.replace "\n" ("\n" ++ s!"[{timeStr}] [{name}] ")}"
  handle.putStrLn (← message.toString)
  handle.flush

structure LogConfig where
  logsToIO : List Name := []
  logsToFile : List Name := []
  deriving Inhabited

inductive LogConfigModify where
  | addLogToIO (name : Name) : LogConfigModify
  | removeLogFromIO (name : Name) : LogConfigModify
  | addLogToFile (name : Name) : LogConfigModify
  | removeLogFromFile (name : Name) : LogConfigModify
  deriving Inhabited

namespace LogConfig
def modify (cfg : LogConfig) (modif : LogConfigModify) : LogConfig :=
  match modif with
  | LogConfigModify.addLogToIO name =>
    { cfg with logsToIO :=
      if name ∈ cfg.logsToIO then cfg.logsToIO else
      name :: cfg.logsToIO }
  | LogConfigModify.removeLogFromIO name =>
    { cfg with logsToIO := cfg.logsToIO.filter (· ≠ name) }
  | LogConfigModify.addLogToFile name =>
    { cfg with logsToFile :=
      if name ∈ cfg.logsToFile then cfg.logsToFile else
      name :: cfg.logsToFile }
  | LogConfigModify.removeLogFromFile name =>
    { cfg with logsToFile := cfg.logsToFile.filter (· ≠ name) }
end LogConfig

initialize logConfigExt : SimpleScopedEnvExtension LogConfigModify LogConfig ←
  registerSimpleScopedEnvExtension {
    initial := {}, addEntry := LogConfig.modify }

def logsToIO (env : Environment) : List Name :=
  logConfigExt.getState env |>.logsToIO

def logsToIOM  : MetaM (List Name) := do
  return logConfigExt.getState (← getEnv) |>.logsToIO

def logsToFile (env : Environment) : List Name :=
  logConfigExt.getState env |>.logsToFile

elab "#logIO " name:ident : command => do
  let logName := name.getId
  logConfigExt.add (LogConfigModify.addLogToIO logName)

elab "#noLogIO " name:ident : command => do
  let logName := name.getId
  logConfigExt.add (LogConfigModify.removeLogFromIO logName)

elab "#logFile " name:ident : command => do
  let logName := name.getId
  logConfigExt.add (LogConfigModify.addLogToFile logName)

elab "#noLogFile " name:ident : command => do
  let logName := name.getId
  logConfigExt.add (LogConfigModify.removeLogFromFile logName)

def traceAide (tag : Name) (msg : String) : CoreM Unit := do
-- always print trace
  Lean.trace tag (fun _ => msg)
-- use logConfigExt to globally update this
  let env ← getEnv
  let ioLogs := logsToIO env
  let fileLogs := logsToFile env
  if tag ∈ ioLogs then
    logIO tag msg
  -- else
  --   logToStdErr `leanaide.translate.info s!"{tag} suppressed IO log, logs : {ioLogs}"
  if tag ∈ fileLogs ∨ tag ∈ ioLogs then
    logFile tag msg

end LeanAide

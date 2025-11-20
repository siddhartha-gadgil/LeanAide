import Lean
open Lean Meta Std.HashMap

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

-- #eval resourcesDir

inductive logType where
  | io : logType
  | file : logType
deriving Inhabited, BEq, Hashable

instance : ToString logType where
  toString x :=
    match x with
    | .io => "[IO]"
    | .file => "[FILE]"

abbrev traceName := logType × Name
abbrev traceSet := Std.HashSet (α := traceName)

initialize polyTrace : IO.Ref traceSet ← IO.mkRef <| Std.HashSet.ofList []

instance : ToString traceName where
  toString (n : traceName) := s!"[{n.fst}] : [{n.snd}]"

namespace polyTrace
  private def isClassRegistered [MonadOptions IO] (n : Name) : IO Bool := do
    (←getOptions).entries.filter (·.fst == n)
    |> List.isEmpty
    |> pure

  def on [MonadOptions IO] (t : logType) (name : Name) : IO Unit := do
      if (←isClassRegistered name) then pure ()
      else
        (←polyTrace.get)
        |>.insert ⟨t, name⟩
        |> polyTrace.set

  def off (t : logType) (name : Name) : IO Unit := do
    (←polyTrace.get)
    |>.erase ⟨t, name⟩
    |> polyTrace.set

  def status (_ : Unit) : IO Unit := do
    let list ← (←polyTrace.get).toList |> pure
    IO.eprintln s!"{list}"

  def log (tag : Name) (message : String) : CoreM Unit := do

    let message (l : logType) :=
      s!"[{tag}] [{l}] :: [{message}]"

    let logFilePath ← do
      System.mkFilePath
        [
          (←IO.currentDir).toString,
          "output.log"
        ] |> pure

    let list ← (←polyTrace.get).toList |> pure
    match list.find? (·.snd == tag) with
    | .none =>
      if list.isEmpty then
        Lean.trace `Invalid (fun _ => "The current list is empty, please add trace class at the top the *.lean file")
      else
        Lean.trace `Invalid (fun _ => s!"The {tag} is not set to any logType")
    | .some ⟨.io, _⟩ =>
        Lean.trace tag (fun _ => message .io)
        IO.eprintln <| message .io
    | .some ⟨.file, _⟩ =>
        IO.FS.writeFile logFilePath <| message .file

end polyTrace

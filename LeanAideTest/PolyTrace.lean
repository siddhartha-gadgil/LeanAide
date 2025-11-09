import LeanAide
import Lean
import Std

open Lean

-- >>> polyTrace example #1

-- example of how
-- #eval polyTraceIO.on ()
-- #eval polyTrace `PaperCodes.info "This is an example"
-- #eval polyTraceIO.off ()
-- #eval polyTraceFile.on ()
-- #eval polyTraceFile.status ()
-- #eval polyTrace `PaperCodes.info "This is a file example"
-- #eval polyTraceFile.status ()
-- #eval polyTraceIO.status ()

namespace Generate

  def polyTraceFile (fileStatus : IO Bool) (ioStatus : IO Bool) : IO (Except String Unit) := do
    match ←fileStatus, ←ioStatus with
    | false, false | true, true =>

      .error s!"invalid state"

    -- [TODO]
    -- file generated is hardcoded,
    -- create a function to have legible names

    | true, false => do

      let _ ← polyTrace `PaperCodes.info s!"[File] :: Test message" |> pure
      .ok () |> pure
      -- let outputLogPath ←
      --     (← IO.currentDir).components ++ ["output.log"]
      --     |> System.mkFilePath

      -- let outputLogExists ← System.FilePath.pathExists outputLogPath

      -- if outputLogExists then true else false

    | false, true => do

      let _ ← polyTraceIO.off () |> pure
      let _ ← polyTraceFile.on () |> pure
      let _ ← polyTrace `PaperCodes.info s!"[File] :: Test message" |> pure
      .ok () |> pure

end Generate

namespace Test

  private def fileStatus := polyTraceFile.status ()
  private def ioStatus := polyTraceIO.status ()
  private def defaultName := s!"output.log"
  private def defaultPath := do
    let currentDir ← (←IO.currentDir).toString |> pure
    System.mkFilePath [
      currentDir,
      defaultName
    ] |> pure

  def check_FileCreated (_ : Unit) : IO Unit := do
    let response ←(Generate.polyTraceFile fileStatus ioStatus)
    match response with
    | .error e => IO.eprintln s!"[FAILED] File Generated failed with error : {e}"
    | .ok _ =>
      let fileExists ←System.FilePath.pathExists (←defaultPath)
      if fileExists then IO.eprintln s!"[PASSED] File Generated"
      else IO.eprintln s!"[FAILED] File Generation failed at {←defaultPath}"

end Test

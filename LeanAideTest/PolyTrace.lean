import LeanAide
import Lean
import Std

open Lean

-- >>> traceAide example #1

-- example of how
-- #eval traceAideIO.on ()
-- #eval traceAide `leanaide.papercodes.info "This is an example"
-- #eval traceAideIO.off ()
-- #eval traceAideFile.on ()
-- #eval traceAideFile.status ()
-- #eval traceAide `leanaide.papercodes.info "This is a file example"
-- #eval traceAideFile.status ()
-- #eval traceAideIO.status ()

namespace Generate

  def traceAideFile (fileStatus : IO Bool) : IO (Except String Unit) := do
    if ←fileStatus then
      let _ ← traceAide `leanaide.papercodes.info s!"[File] :: Test message" |> pure
      .ok () |> pure
    else
      .error s!"invalid state"

end Generate

namespace Test

  private def fileStatus := traceAideFile.status ()
  private def ioStatus := traceAideIO.status ()
  private def defaultName := s!"output.log"
  private def defaultPath := do
    let currentDir ← (←IO.currentDir).toString |> pure
    System.mkFilePath [
      currentDir,
      defaultName
    ] |> pure

  def traceAideFile (_ : Unit) : IO Unit := do
    let response ←(Generate.traceAideFile fileStatus)
    match response with
    | .error e => IO.eprintln s!"[FAILED] File Generated failed with error : {e}"
    | .ok _ =>
      let fileExists ←System.FilePath.pathExists (←defaultPath)
      if fileExists then IO.eprintln s!"[PASSED] File Generated"
      else IO.eprintln s!"[FAILED] File Generation failed at {←defaultPath}"

end Test

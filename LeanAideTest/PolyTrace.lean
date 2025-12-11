import LeanAide
import Lean
import Std

open Lean

-- 1. Init.file () // adds the trace class

namespace Init

  def file
    (_ : Unit)
    : IO (Except String Unit)
  := do
    let _ ← polyTrace.on logType.file `PolyTrace.Test |> pure
    .ok () |> pure

  def io (_ : Unit) : IO (Except String Unit) := do
    let _ ← polyTrace.on logType.io `PolyTrace.Test |> pure
    .ok () |> pure

end Init

-- 2. Test.file ()
--// 2.1 log the string "Run the test" in the output.log file
--// 2.2 check if file ${current_directory}/output.log exists
--// 2.3 if exists [PASS] else [FAIL]

namespace Test

  def file (_ : Unit) : IO Unit := do

    let defaultPath ←
      System.mkFilePath
        [
          (←IO.currentDir).toString,
          "output.log"
        ] |> pure

    -- init
    match ←Init.file () with
    | .ok _ =>
        -- if init works call log
        let _ ← polyTrace.log `PolyTrace.Test s!"Run the test" |> pure

        -- if I logged something I should see the file generated
        let fileExists ←
          System.FilePath.pathExists defaultPath
        if fileExists then
          IO.eprintln s!"[PASSED] File Generated"
        else
          IO.eprintln s!"[FAILED] File Generation failed at {←defaultPath.toString |> pure}"
        pure ()
    | .error e =>
        IO.eprintln s!"[FAILED] Test for file failed with error : {e}"

  def io (_ : Unit) : IO Unit := do

    let defaultPath ←
      System.mkFilePath
        [
          "/tmp",
          "leanaide.log"
        ] |> pure

    -- init
    match ←Init.file () with
    | .ok _ =>
        -- if init works call log
        let _ ← polyTrace.log `PolyTrace.Test s!"Run the test" |> pure

        -- if I logged something I should see the file generated
        let fileExists ←
          System.FilePath.pathExists defaultPath
        if fileExists then
          IO.eprintln s!"[PASSED] File Generated"
        else
          IO.eprintln s!"[FAILED] File Generation failed at {←defaultPath.toString |> pure}"
        pure ()
    | .error e =>
        IO.eprintln s!"[FAILED] Test for file failed with error : {e}"
end Test

#eval polyTrace.on logType.file `PolyTrace.Test

#eval do
  polyTrace.log `PolyTrace.Test "This is a polytrace file test"

#eval do Test.file ()

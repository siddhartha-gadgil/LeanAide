import Scratch.Fiddle4


#eval mnVal

#eval mnIncr

#eval mnIncr

#eval mnVal

#eval mnSet 5

#eval mnVal

/--
# Markdown in DocStrings

Yes, it works, including *emphasis* and **bold**.
-/
def HelloWorld : String :=
  "Hello from LeanAideCore!"

open Lean Meta Elab
elab doc:docComment "#text" n:ident : command =>
  Command.liftTermElabM do
  let text := doc.raw.reprint.get!
  let text := text.drop 4 |>.dropRight 4
  logInfoAt n m!"{text}"
  return ()

/--
# Markdown in DocStrings

Yes, it works, including *emphasis* and **bold**.
-/
#text HelloWorld

macro doc:docComment "#text" n:ident : command =>
  let text := doc.raw.reprint.get!
  let text := text.drop 4 |>.dropRight 4
  let textStx := Syntax.mkStrLit text
  `(command| def $n := $textStx)

/--
# Markdown in DocStrings

Yes, it works, including *emphasis* and **bold** and live changes.
-/
#text HelloW

#eval HelloW

#check System.FilePath

#eval System.FilePath.readDir <| ".." / "LeanSearchClient"

example : 1 = 1 := by nlinarith

def text :=
  IO.FS.readFile <| "resources" / "ProofGuidelines.md"

#eval text

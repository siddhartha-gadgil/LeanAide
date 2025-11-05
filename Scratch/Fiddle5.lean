import Scratch.Fiddle4


#eval mnVal

#eval mnIncr

#eval mnIncr

#eval mnVal

#eval mnSet 5

#eval mnVal

macro "#set_mn" n:term : command =>
  let nStx := n
  `(command| #eval $nStx)

#set_mn 42

#eval mnVal

/--
# Markdown in DocStrings

Yes, it works, including *emphasis* and **bold**.
-/
def HelloWorld : String :=
  "Hello from LeanAideCore!"

open Lean Meta Elab
elab doc:docComment "#quote" n:ident : command =>
  Command.liftTermElabM do
  let text := doc.raw.reprint.get!
  let text := text.drop 4 |>.dropRight 4
  logInfoAt n m!"{text}"
  return ()

/--
# Markdown in DocStrings

Yes, it works, including *emphasis* and **bold**.
-/
#quote HelloWorld

macro doc:docComment "#quote" n:ident : command =>
  let text := doc.raw.reprint.get!
  let text := text.drop 4 |>.dropRight 4
  let textStx := Syntax.mkStrLit text
  `(command| def $n := $textStx)

/--
# Markdown in DocStrings

Yes, it works, including *emphasis* and **bold** and live changes.
-/
#quote HelloW

#eval HelloW

#check System.FilePath

#eval System.FilePath.readDir <| ".." / "LeanSearchClient"

example : 1 = 1 := by nlinarith

def text :=
  IO.FS.readFile <| "resources" / "ProofGuidelines.md"

#eval text

open TSyntax

open Lean Elab Term
elab "template%" s:term : term => do
  let t ← elabTerm s (mkConst ``String)
  let str ← unsafe evalExpr String (mkConst ``String) t
  let istr := s!"s!\"{str}\""
  logInfo m!"{istr}"
  let .ok stx := Parser.runParserCategory (← getEnv) `term istr
    | throwError "failed to parse {istr}"
  let res ← withoutErrToSorry do
    elabTerm stx (mkConst ``String)
  return res

def nn := 2

def s := "Hello {1 + 1 + nn}!"

def t := template% s

#eval t

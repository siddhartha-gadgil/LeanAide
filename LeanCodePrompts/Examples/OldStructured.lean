import LeanCodePrompts.ChatClient
import LeanAide.StructToLean
open Lean LeanAide.Meta

def proofExample := "## Theorem: Let $A$ be a square matrix. Prove that if $A^3 = I$ then $A$ is diagonalizable.\n## Proof: \nSince $A^3 = I$, $A$ satisfies the polynomial equation $p(x) = x^3 - 1$. The roots of $p(x)$ are the cube roots of unity, namely $1, \\omega, \\omega^2$, where $\\omega = e^{2\\pi i/3}$ is a primitive cube root of unity. These roots are distinct, so the minimal polynomial of $A$ must divide $p(x)$ and also have distinct roots. Therefore, $A$ is diagonalizable."

#eval proofExample

def gemini := ChatServer.google

def geminiFlash := ChatServer.google "gemini-1.5-flash-001"

def structExampl := gemini.structuredProof proofExample

def structExamplFlash := gemini.structuredProof proofExample

def numina :=
  ChatServer.generic (model := "AI-MO/NuminaMath-7B-TIR") (url := "10.134.13.103:8000")

def mistral :=
  ChatServer.generic (model := "mistralai/Mistral-7B-Instruct-v0.3") (url := "10.134.13.103:8000")

def mathstral :=
  ChatServer.generic (model := "mistralai/mathstral-7B-v0.1") (url := "10.134.13.103:8000")

def worst := "14546"
def best := "14590"

def basePath : System.FilePath := "results" / "gemini_results" / "um102"

def readSol (problem student : String) : IO String := do
  IO.FS.readFile (basePath / s!"problem{problem}" / s!"{student}_sol.md")

#eval readSol "5" best

def mathstralWrite (problem student : String) : CoreM String := do
  let sol ← readSol problem student
  let resArr ←  mathstral.structuredProof sol
  let res := resArr[0]!
  IO.FS.writeFile (basePath / s!"problem{problem}" / s!"{student}_mathstral.json") (res.pretty)
  return res.pretty

def mathstralEgs : CoreM (List (List String)) := do
  ["1", "3", "5"].mapM fun problem =>
    [best, worst].mapM (fun student => mathstralWrite problem student)

-- #eval mathstralWrite "3" best

def numinaExample := numina.structuredProof proofExample
/-
#[{"type": "theorem",
 "status": "proved",
 "proof":
 {"steps":
  [{"type": "assert",
    "statement": "A satisfies the polynomial equation p(x) = x^3 - 1"},
   {"type": "assert",
    "statement":
    "The roots of p(x) are the cube roots of unity: 1, omega, omega^2, where omega = e^{2pi i / 3}"},
   {"type": "assert",
    "statement":
    "These roots are distinct, so the minimal polynomial of A must divide p(x) and also have distinct roots"},
   {"type": "assert", "statement": "Therefore, A is diagonalizable"}]},
 "name": "Theorem: A matrix A satisfying A^3 = I is diagonalizable",
 "hypothesis":
 [{"variable": "A",
   "type": "let",
   "property": "square matrix",
   "kind": "matrix"},
  {"type": "assert", "statement": "A^3 = I"}],
 "conclusion": "A is diagonalizable"}]

-/
-- #eval numinaExample

def mistralExample := mistral.structuredProof proofExample
/-
#[{"type": "theorem",
 "Status": "proved",
 "Proof":
 {"Steps":
  [{"type": "assert",
    "Deduced_from": ["Assumption"],
    "Claim": "A satisfies the polynomial equation p(x) = x^3 - 1."},
   {"type": "assert",
    "Deduced_from": ["Assertion"],
    "Claim":
    "The roots of p(x) are 1, ω, and ω^2, where ω = e^(2πi/3) is a primitive cube root of unity."},
   {"type": "assert",
    "Deduced_from": ["Assertion"],
    "Claim": "These roots are distinct."},
   {"type": "assert",
    "Deduced_from": ["Assertion", "Assertion", "Assertion"],
    "Claim":
    "The minimal polynomial of A must divide p(x) and also have distinct roots."},
   {"type": "conclude", "Statement": "A is diagonalizable."}]},
 "Hypothesis":
 [{"type": "assume", "Statement": "A is a square matrix and A^3 = I"}],
 "Conclusion": "A is diagonalizable"}]
-/
-- #eval mistralExample

/-
#[{"type": "theorem",
 "name": "Diagonalizability of Matrices Satisfying A^3 = I",
 "Status": "proved",
 "Proof":
 {"type": "proof",
  "Steps":
  [{"type": "assert",
    "Deduced_from": ["$A^3 = I$"],
    "Claim": "The minimal polynomial of $A$ divides $x^3 - 1$."},
   {"type": "assert",
    "Proof-method": "direct computation",
    "Claim":
    "The roots of $x^3 - 1$ are $1, \\omega, \\omega^2$, where $\\omega = e^{2 \\pi i / 3}$."},
   {"type": "assert",
    "Proof-method": "direct verification",
    "Claim": "The roots $1, \\omega, \\omega^2$ are distinct."},
   {"type": "assert",
    "Deduced_from":
    ["The minimal polynomial of $A$ divides $x^3 - 1$",
     "The roots of $x^3 - 1$ are $1, \\omega, \\omega^2$",
     "The roots $1, \\omega, \\omega^2$ are distinct."],
    "Claim": "The minimal polynomial of $A$ has distinct roots."},
   {"type": "conclude",
    "Statement": "$A$ is diagonalizable.",
    "Deduced_from": ["The minimal polynomial of $A$ has distinct roots."]}]},
 "Hypothesis":
 [{"type": "let", "Variable": "A", "Kind": "square matrix"},
  {"type": "assume", "Statement": "$A^3 = I$"}],
 "Conclusion": "A is diagonalizable."}]
-/
-- #eval structExampl
/-
#[[{"type": "theorem",
  "status": "stated",
  "name": "Diagonalizability of Matrices Satisfying A^3 = I",
  "hypothesis":
  [{"type": "fix", "Variable": "A", "Kind": "square matrix"},
   {"type": "assume", "Statement": "$A^3 = I$"}],
  "conclusion": "$A$ is diagonalizable."},
 {"type": "proof",
  "steps":
  [{"type": "observe",
    "claim":
    "The matrix $A$ satisfies the polynomial equation $p(x) = x^3 - 1$",
    "Deduced_from": ["$A^3 = I$"]},
   {"type": "observe",
    "error":
    "This observation is ambiguous. Over which field are we considering the polynomial $p(x)$ and its roots? The field needs to be specified since the diagonalizability of the matrix $A$ depends on the field.",
    "claim":
    "The roots of $p(x)$ are $1, \\omega, \\omega^2$, where $\\omega = e^{2\\pi i/3}$ is a primitive cube root of unity."},
   {"type": "observe",
    "missing":
    [{"type": "problem",
      "statement":
      "Prove that if a matrix $A$ satisfies a polynomial equation $q(A) = 0$, then the minimal polynomial of $A$ divides $q(x)$."}],
    "claim":
    "The roots of $p(x)$ are distinct, so the minimal polynomial of $A$ must divide $p(x)$ and also have distinct roots."},
   {"type": "assert",
    "missing":
    [{"type": "problem",
      "statement":
      "Prove that if the minimal polynomial of a matrix has distinct roots, then the matrix is diagonalizable."}],
    "error":
    "The converse of this statement is true, but this statement is not true in general. It is not sufficient for the minimal polynomial to have distinct roots to guarantee diagonalizability. The minimal polynomial needs to split into linear factors over the field being considered. ",
    "claim": "Therefore, $A$ is diagonalizable.",
    "Deduced_from": ["The minimal polynomial of $A$ has distinct roots"]}]}]]

-/
-- #eval structExamplFlash

/-
#[[{"type": "theorem",
  "status": "proved",
  "proof":
  {"type": "proof",
   "steps":
   [{"type": "observe",
     "claim": "The matrix A satisfies the polynomial equation x^3 - 1 = 0"},
    {"variable": "ω", "value": "e^(2πi/3)", "type": "let"},
    {"type": "observe", "claim": "The roots of x^3 - 1 = 0 are 1, ω, and ω^2"},
    {"type": "assert",
     "proof-method": "by the definition of the minimal polynomial",
     "deduced_from": ["A satisfies the polynomial equation x^3 - 1 = 0"],
     "claim": "The minimal polynomial of A divides x^3 - 1"},
    {"type": "assert",
     "error":
     "The minimal polynomial of A could have multiple roots even if it divides x^3 - 1. For example, it could be (x-1)^2(x-ω).",
     "deduced_from":
     ["The minimal polynomial of A divides x^3 - 1",
      "The roots of x^3 - 1 = 0 are 1, ω, and ω^2"],
     "claim": "The roots of the minimal polynomial of A are distinct"},
    {"type": "assert",
     "proof-method":
     "This is a consequence of the fact that a matrix is diagonalizable if and only if its minimal polynomial has distinct roots.",
     "deduced_from": ["The roots of the minimal polynomial of A are distinct"],
     "claim": "A is diagonalizable"}]},
  "name": "Diagonalizability of Matrices Satisfying A^3 = I",
  "hypothesis":
  [{"variable": "A", "type": "fix", "kind": "square matrix"},
   {"type": "assume", "statement": "A^3 = I"}],
  "conclusion": "A is diagonalizable"}]]

-/
-- #eval structExampl

def jsEg := "{\n  \"ProofJSON\": {\n   \"theorem\": {\n      \"Hypothesis\": [\n       {\n          \"type\": \"define\",\n          \"Statement\": \"Let $ f(x, y)=x^{3}-3 x+y^{2} $ for $ x, y \\in \\mathbb{R} $.\"\n        }\n      ],\n    \"Conclusion\": \"Prove that at the points (1,0) and (-1,0) the gradient of $ f $ is zero.\",\n      \"Status\": \"proved\"\n    },\n    \"proof\": {\n    \"steps\": [\n       {\n         \"type\": \"assert\",\n       \"Claim\": \"The function is $ f(x, y) = x^2 - 3xy + y^2
$.\",\n        \"Deduced_from\": [],\n         \"Proof-method\": \"Given problem statement.\"\n      },\n        {\n
  \"type\": \"assert\",\n         \"Claim\": \"The gradient of a function $f(x, y) $ is $\\nabla f(x, y) = \\frac{\\partial
 f}{\\partial x} \\hat{i} + \\frac{\\partial f}{\\partial y} \\hat{j} $.\",\n          \"Deduced_from\": [],\n         \"Proof-me
thod\": \"Textbook definition of gradient.\"\n        },\n        {\n          \"type\": \"assert\",\n         \"Claim\": \"$\\nabla f(x, y) = (2x -3) \\hat{i} + 2y \\hat{j}$.\",\n          \"Deduced_from\": [\n           \"The function is $ f(x, y) = x^2
- 3xy + y^2 $.\",\n            \"The gradient of a function $ f(x, y) $ is $ \\nabla f(x, y) = \\frac{\\partial f}{\\partial
 x} \\hat{i} + \\frac{\\partial f}{\\partial y} \\hat{j} $.\"\n          ],\n          \"Calculation\": [\n            \"Step 1\":
 {\n              \"step\": \"Compute $\\frac{\\partial f}{\\partial x}$.\",\n              \"justification\": \"Using the parti
al derivative formula and the given function $ f(x, y) = x^2 - 3xy + y^2 $.\"\n            },\n            \"Step 2\": {\n
        \"step\": \"Compute $\\frac{\\partial f}{\\partial y}$.\",\n              \"justification\": \"Using the partial derivat
ive formula and the given function $ f(x, y) = x^2 - 3xy + y^2 $.\"\n            }\n          ]\n        },\n        {\n
  \"type\": \"assert\",\n          \"Claim\": \"If $\\nabla f = 0$, then $3x - 3 = 0$ and $2y = 0$.\",\n          \"Dedu
ced_from\": [\n            \"$\\nabla f(x, y) = (2x -3) \\hat{i} + 2y \\hat{j}$\"\n          ],\n          \"Calculation\": [\n
           \"Step 1\": {\n              \"step\": \"Set $\\frac{\\partial f}{\\partial x} = 0$.\",\n              \"justificatio
n\": \"Since $\\nabla f = 0$, its partial derivative with respect to $x$ must be zero.\"\n            },\n            \"Step
 2\": {\n              \"step\": \"Set $\\frac{\\partial f}{\\partial y} = 0$.\",\n              \"justification\": \"Since $\
\nabla f = 0$, its partial derivative with respect to $y$ must be zero.\"\n            }\n          ]\n        },\n        {\n
          \"type\": \"assert\",\n          \"Claim\": \"$x = 1$ and $y = 0$.\",\n          \"Deduced_from\": [\n
\"If $\\nabla f = 0$, then $3x - 3 = 0$ and $2y = 0$.\"\n          ],\n          \"Calculation\": [\n            \"Step
1\": {\n              \"step\": \"Solve $3x - 3 = 0$ for $x$.\",\n              \"justification\": \"Using basic algebra.\"\
n            },\n            \"Step 2\": {\n              \"step\": \"Solve $2y = 0$ for $y$.\",\n              \"justificat
ion\": \"Using basic algebra.\"\n            }\n          ]\n        },\n        {\n          \"type\": \"assert\",\n          \"Cla
im\": \"$\\nabla f = 0$ at $(1,0)$ and $(0,1)$.\",\n          \"Deduced_from\": [\n            \"$x = 1$ and $y =
0$.\"\n          ],\n          \"Calculation\": [\n            \"Step 1\": {\n              \"step\": \"Substitute $x = 1$ and
 $y = 0$ into $\\nabla f(x, y) = (2x -3) \\hat{i} + 2y \\hat{j}$.\",\n              \"justification\": \"Using the expressio
n for $\\nabla f$.\"\n            }"

def escapeJson (s: String) := s.replace "\\" "\\\\" |>.replace "\n" " "
#eval escapeJson jsEg
#eval Json.parse (escapeJson jsEg)
#eval (escapeJson jsEg).toList.drop 1270 |>.take 15 |>.toString

def client := ChatServer.openAI
def prime_thm := "There are infinitely many prime numbers ending in 7."
def writeSoln : CoreM String := do
  let resArr ← client.prove prime_thm 1
  let res := resArr[0]!
  IO.FS.writeFile "llm_data/gpt-4o/prime_thm.md" res
  return res

/-
#[{"type": "theorem",
 "status": "incomplete proof",
 "proof":
 {"type": "proof",
  "steps":
  [{"type": "assert",
    "deduced_from":
    {"known_results":
     ["For any matrix A, if A^k = I, then A is a root of the polynomial x^k - 1."],
     "from_context": ["A^3 = I"]},
    "claim": "A satisfies the polynomial equation $p(x) = x^3 - 1$."},
   {"type": "assert",
    "deduced_from":
    {"known_results":
     ["The roots of the polynomial x^3 - 1 are the cube roots of unity."]},
    "claim":
    "The roots of $p(x) = x^3 - 1$ are the cube roots of unity, namely $1, \\omega, \\omega^2$, where $\\omega = e^{2\\pi i/3}$."},
   {"type": "assert",
    "deduced_from":
    {"known_results": ["The cube roots of unity are distinct."]},
    "claim": "The roots $1, \\omega, \\omega^2$ are distinct."},
   {"type": "assert",
    "proof-method":
    "By the definition of the minimal polynomial and properties of the polynomial p(x).",
    "deduced_from":
    {"from_context":
     ["A satisfies the polynomial equation $p(x) = x^3 - 1$.",
      "The roots $1, \\omega, \\omega^2$ are distinct."]},
    "claim":
    "The minimal polynomial of A must divide $p(x) = x^3 - 1$ and have distinct roots."},
   {"type": "assert",
    "missing":
    [{"type": "problem",
      "statement":
      "Justify why the minimal polynomial having distinct roots implies A is diagonalizable."}],
    "deduced_from":
    {"known_results":
     ["A matrix A is diagonalizable if and only if its minimal polynomial has distinct roots."],
     "from_context":
     ["The minimal polynomial of A must divide $p(x) = x^3 - 1$ and have distinct roots."]},
    "claim": "A is diagonalizable."}]},
 "name": "Diagonalizability of A",
 "hypothesis":
 [{"type": "assume", "statement": "A is a square matrix."},
  {"type": "assume", "statement": "A^3 = I."}],
 "conclusion": "A is diagonalizable."}]

-/
-- #eval client.structuredProof proofExample

def cubeJson : IO Json := do
  let src ← IO.FS.readFile "llm_data/gpt-4o/cube.json"
  return Json.parse src |>.toOption.get!

#eval cubeJson
open Lean Meta Elab
def cubeCode : TranslateM <| Option String := do
  let cube ← cubeJson
  logInfo s!"{cube}"
  let cubeCode? ← structToCommand? (params := {n := 12}) (context := #[])  (pb := PromptExampleBuilder.embedBuilder 8 0 0) (input := cube)
  cubeCode?.mapM fun code => do
    let fmt ← PrettyPrinter.ppCommand code
    pure <| topCode ++ fmt.pretty

-- #eval cubeCode
def cubeCodeCore : CoreM <| Option String := cubeCode.runToCore

import LeanCodePrompts.ChatClient
open Lean

#eval proofExample

def gemini := ChatServer.google

def geminiFlash := ChatServer.google "gemini-1.5-flash-001"

def structExampl := gemini.structuredProof proofExample

def structExamplFlash := gemini.structuredProof proofExample

def numina :=
  ChatServer.generic (model := "AI-MO/NuminaMath-7B-TIR") (url := "10.134.13.103:8000")

def mistral :=
  ChatServer.generic (model := "mistralai/Mistral-7B-Instruct-v0.3") (url := "10.134.13.103:8000")

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

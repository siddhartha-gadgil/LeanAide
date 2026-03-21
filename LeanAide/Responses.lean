import LeanAide.TranslatorParams
import LeanAideCore.Translate
import LeanAide.TranslatorParams
import LeanAide.Codegen
import LeanAide.PaperCodes
import LeanAideCore.ResponseExt
import LeanAideCore.Kernel
import LeanAideCore.Responses
import Lean

namespace LeanAide
open LeanAide Lean Codegen

/-!
Executing various tasks with Json input and output. These are for the server. We may switch to an attribute based system instead of case-based.

### **Tasks with Inputs & Outputs**

* **`translate_thm`** — *Translate a natural-language theorem into Lean and elaborate its type*

  * **Inputs:**

    * `theorem_text : String` — natural-language statement of the theorem
  * **Outputs:**

    * `Except (Array ElabError) Expr` — either a successfully elaborated theorem type (`Expr`) or a list of elaboration errors

* **`translate_thm_detailed`** — *Translate a natural-language theorem with name and produce Lean declaration*

  * **Inputs:**

    * `theorem_text : String` — natural-language statement
    * `theorem_name : Option Name` — optional name to assign to the theorem
  * **Outputs:**

    * `(Name × Expr × Syntax.Command)`

      * `Name` — theorem name
      * `Expr` — elaborated type of the theorem
      * `Syntax.Command` — Lean command syntax for the full theorem declaration

* **`translate_def`** — *Translate a natural-language definition into Lean code*

  * **Inputs:**

    * `definition_text : String` — natural-language definition
  * **Outputs:**

    * `Except (Array CmdElabError) Syntax.Command` — either a Lean definition command or elaboration errors

* **`theorem_doc`** — *Generate natural-language documentation for a theorem*

  * **Inputs:**

    * `theorem_name : Name` — name of the theorem
    * `theorem_statement : Syntax.Command` — Lean syntax of the theorem statement
  * **Outputs:**

    * `String` — natural-language documentation of the theorem

* **`def_doc`** — *Generate natural-language documentation for a definition*

  * **Inputs:**

    * `definition_name : Name` — name of the definition
    * `definition_code : Syntax.Command` — Lean syntax of the definition
  * **Outputs:**

    * `String` — natural-language documentation for the definition

* **`theorem_name`** — *Generate a Lean Prover name for the theorem*

  * **Inputs:**

    * `theorem_text : String` — natural-language statement
  * **Outputs:**

    * `Name` — automatically generated Lean name for the theorem

* **`prove_for_formalization`** — *Generate a detailed proof or proof sketch for a theorem*

  * **Inputs:**

    * `theorem_text : String` — natural-language theorem
    * `theorem_code : Expr` — elaborated theorem type
    * `theorem_statement : Syntax.Command` — full Lean statement
  * **Outputs:**

    * `String` — a document (likely a natural-language or partially formal proof)

* **`json_structured`** — *Convert a natural-language document into a structured JSON representation*

  * **Inputs:**

    * `document_text : String` — some natural-language math text
  * **Outputs:**

    * `Json` — structured JSON representation of the document

* **`lean_from_json_structured`** — *Generate Lean code from structured JSON*

  * **Inputs:**

    * `document_json : Json` — structured JSON of a document
  * **Outputs:**

    * `TSyntax ``commandSeq` — Lean code parsed from the JSON

* **`elaborate`** — *Elaborate Lean code and collect results, logs, and unsolved goals*

  * **Inputs:**

    * `document_code : String` — Lean code (as text)
  * **Outputs:**

    * `CodeElabResult` — structured result with:

      * `declarations : List Name` — names of elaborated declarations
      * `logs : List String` — log messages
      * `sorries : List (Name × Expr)` — unproven obligations
      * `sorriesAfterPurge : List (Name × Expr)` — remaining obligations after simplification

* **`math_query`** — *Answer a math question in natural language*

  * **Inputs:**

    * `query : String` — math question
    * `history : List ChatPair` (optional, default `[]`) — conversation context
    * `n : Nat` (optional, default `3`) — number of answers to generate
  * **Outputs:**

    * `List String` — candidate answers to the math question
-/



end LeanAide

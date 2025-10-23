import LeanAideCore.JsonSchemas
import LeanAideCore.DocumentSchema
import LeanAide.JsonDiff
import LeanAideCore.Resources

namespace LeanAide
open JsonSchemas Lean Meta

/--
info: #["case", "pattern_case", "assert_statement", "Citation", "Figure", "assume_statement", "multi-condition_cases_proof",
  "bi-implication_cases_proof", "Proof", "condition_cases_proof", "Table", "Paragraph", "calculation_step",
  "BibliographyEntry", "Bibliography", "Author", "let_statement", "contradiction_statement", "conclude_statement",
  "induction_case", "LogicalStepSequence", "calculation", "general_induction_proof", "Definition", "some_statement",
  "Section", "InternalReference", "Theorem", "induction_proof", "condition_case", "pattern_cases_proof", "ResultUsed"]
-/
#guard_msgs in
#eval schemaElementsList

/-- info: #["LogicalStep", "Hypothesis_statement", "ProofDetails"] -/
#guard_msgs in
#eval groupList

open Json in
def diffWithResource : MetaM (List JsonDiff) := do
  let schema ← withAllDefs docSchema #[]
  return jsonDiff schema Resources.paperStructure

/--
info: [LeanAide.JsonDiff.atKey "$defs" (LeanAide.JsonDiff.existsKey2only "Author"),
 LeanAide.JsonDiff.atKey "$defs" (LeanAide.JsonDiff.existsKey2only "Bibliography"),
 LeanAide.JsonDiff.atKey "$defs" (LeanAide.JsonDiff.existsKey2only "BibliographyEntry"),
 LeanAide.JsonDiff.atKey "$defs" (LeanAide.JsonDiff.existsKey2only "case")]
-/
#guard_msgs in
#eval diffWithResource

def allDefsView : MetaM Unit := do
  let all ← withAllDefs docSchema #[]
  logInfo all.pretty

/--
info: {"type": "object",
 "title": "Mathematical Document Wrapper",
 "required": ["document"],
 "properties":
 {"document":
  {"type": "object",
   "required": ["type", "body"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this document element.",
     "const": "document"},
    "title":
    {"type": "string", "description": "(OPTIONAL) The title of the document."},
    "metadata":
    {"type": "object",
     "properties":
     {"date":
      {"type": "string",
       "format": "date",
       "description": "(OPTIONAL) Date of the document."},
      "authors":
      {"type": "array",
       "items": {"type": "string"},
       "description": "(OPTIONAL) List of authors of the document."}},
     "description":
     "(OPTIONAL) Metadata about the document, such as authors, date, etc."},
    "body": {"$ref": "#/$defs/LogicalStepSequence"},
    "abstract":
    {"type": "string",
     "description": "(OPTIONAL) The abstract of the document."}},
   "description":
   "The root of the mathematical document, containing a sequence of environments.",
   "additionalProperties": false}},
 "description": "JSON schema for a structured mathematical document.",
 "additionalProperties": false,
 "$schema": "https://json-schema.org/draft/2020-12/schema",
 "$defs":
 {"some_statement":
  {"type": "object",
   "required": ["type", "variable_name"],
   "properties":
   {"variable_name":
    {"type": "string",
     "description":
     "The variable being defined (use `<anonymous>` if there is no name such as in `We have a group structure on S`)"},
    "variable_kind":
    {"type": "string",
     "description":
     "(OPTIONAL) The type of the variable, such as `real number`, `function from S to T`, `element of G` etc."},
    "type":
    {"type": "string",
     "description": "The type of this logical step.",
     "const": "some_statement"},
    "statement": {"type": "string", "description": "The full statement made."},
    "properties":
    {"type": "string",
     "description":
     "(OPTIONAL) Specific properties of the variable beyond the type"}},
   "description":
   "A statement introducing a new variable and saying that **some** value of this variable is as required (i.e., an existence statement). This is possibly with given type and/or property. This corresponds to statements like 'for some integer `n` ...' or 'There exists an integer `n` ....'. **NOTE:** It is better to use `assert_statement` instead if the variable is not being defined but rather asserted to exist.",
   "additionalProperties": false},
  "pattern_cases_proof":
  {"type": "object",
   "required": ["type", "on", "proof_cases"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this logical step.",
     "const": "pattern_cases_proof"},
    "proof_cases":
    {"type": "array",
     "items": {"$ref": "#/$defs/pattern_case"},
     "description": "A list of elements of type `case`."},
    "on":
    {"type": "string",
     "description":
     "The variable or expression which is being matched against patterns."}},
   "description":
   "A proof by cases, with cases determined by matching a pattern.",
   "additionalProperties": false},
  "pattern_case":
  {"type": "object",
   "required": ["pattern", "proof"],
   "properties":
   {"proof":
    {"description": "Proof of this case.", "$ref": "#/$defs/ProofDetails"},
    "pattern":
    {"type": "string", "description": "The pattern determining this case."}},
   "description":
   "A case in a proof by cases with cases determined by matching patterns.",
   "additionalProperties": false},
  "multi-condition_cases_proof":
  {"type": "object",
   "required": ["type", "proof_cases"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this logical step.",
     "const": "multi-condition_cases_proof"},
    "proof_cases":
    {"type": "array",
     "items": {"$ref": "#/$defs/condition_case"},
     "description": "The conditions and proofs in the different cases."},
    "exhaustiveness":
    {"description": "(OPTIONAL) Proof that the cases are exhaustive.",
     "$ref": "#/$defs/ProofDetails"}},
   "description": "A proof by cases given by three or more conditions.",
   "additionalProperties": false},
  "let_statement":
  {"type": "object",
   "required": ["type", "variable_name"],
   "properties":
   {"variable_type":
    {"type": "string",
     "description":
     "(OPTIONAL) The type of the variable, such as `real number`, `function from S to T`, `element of G` etc."},
    "variable_name":
    {"type": "string",
     "description":
     "The variable being defined (use `<anonymous>` if there is no name such as in `We have a group structure on S`)"},
    "value":
    {"type": "string",
     "description":
     "(OPTIONAL) The value of the variable being defined. This MUST BE an explicit value. If the value is the obtained from an existence statement, use `assert_statement` instead."},
    "type":
    {"type": "string",
     "description": "The type of this logical step.",
     "const": "let_statement"},
    "statement": {"type": "string", "description": "The full statement made."},
    "properties":
    {"type": "string",
     "description":
     "(OPTIONAL) Specific properties of the variable beyond the type"}},
   "description":
   "A statement introducing a new variable with given value, type and/or property.",
   "additionalProperties": false},
  "induction_proof":
  {"type": "object",
   "required": ["type", "on", "base_case_proof", "induction_step_proof"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this logical step.",
     "const": "induction_proof"},
    "prev_var":
    {"type": "string",
     "description":
     "(OPTIONAL) The variable `m` so that the induction case if `m + 1`. If omitted it is assumed that it is the same as the 'on' variable, i.e., the induction step is `n + 1` where `n` is the variable on which induction is done."},
    "on":
    {"type": "string",
     "description":
     "The variable or expression on which induction is being done."},
    "induction_step_proof":
    {"description":
     "Proof of the induction step, which typically shows that if the statement holds for `n`, it holds for `n+1`.",
     "$ref": "#/$defs/ProofDetails"},
    "base_case_proof":
    {"description": "Proof of the base case.", "$ref": "#/$defs/ProofDetails"}},
   "description":
   "A proof by induction, with a base case and an induction step. For strong induction or structural induction, USE INSTEAD 'general_induction_proof'.",
   "additionalProperties": false},
  "induction_case":
  {"type": "object",
   "required": ["condition", "proof"],
   "properties":
   {"proof":
    {"description": "Proof for this case.", "$ref": "#/$defs/ProofDetails"},
    "induction_hypotheses":
    {"type": "array",
     "items": {"type": "string"},
     "description":
     "(OPTIONAL) The induction hypotheses. Give the full assumption for the case. Omit for base cases."},
    "condition":
    {"type": "string", "description": "The condition determining this case."}},
   "description":
   "A case in a proof by a general form of induction, such as strong induction or structural induction.",
   "additionalProperties": false},
  "general_induction_proof":
  {"type": "object",
   "required": ["type", "induction_principle", "proof_cases"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this logical step.",
     "const": "general_induction_proof"},
    "proof_cases":
    {"type": "array",
     "items": {"$ref": "#/$defs/induction_case"},
     "description": "The conditions and proofs in the different cases."},
    "induction_principle":
    {"type": "string",
     "description":
     "The induction principle being used, such as 'strong induction for natural numbers' or 'structural induction for binary trees'."}},
   "description": "A proof by cases given by three or more conditions.",
   "additionalProperties": false},
  "contradiction_statement":
  {"type": "object",
   "required": ["type", "assumption", "proof"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this logical step.",
     "const": "contradiction_statement"},
    "proof":
    {"description": "The proof of the contradiction given the assumption.",
     "$ref": "#/$defs/ProofDetails"},
    "assumption":
    {"type": "string",
     "description": "The assumption being made to be contradicted."}},
   "description":
   "A proof by contradiction, with an assumption and a proof of the contradiction.",
   "additionalProperties": false},
  "condition_cases_proof":
  {"type": "object",
   "required": ["type", "condition", "true_case_proof", "false_case_proof"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this logical step.",
     "const": "condition_cases_proof"},
    "true_case_proof":
    {"description": "Proof of the case where the condition is true.",
     "$ref": "#/$defs/ProofDetails"},
    "false_case_proof":
    {"description": "Proof of the case where the condition is false.",
     "$ref": "#/$defs/ProofDetails"},
    "condition":
    {"type": "string",
     "description": "The condition based on which the proof is split."}},
   "description":
   "Proof of a statement based on splitting into cases where a condition is true and false, i.e., an if-then-else proof.",
   "additionalProperties": false},
  "condition_case":
  {"type": "object",
   "required": ["condition", "proof"],
   "properties":
   {"proof":
    {"description": "Proof for this case.", "$ref": "#/$defs/ProofDetails"},
    "condition":
    {"type": "string", "description": "The condition determining this case."}},
   "description":
   "A case in a proof by cases with cases determined by conditions.",
   "additionalProperties": false},
  "conclude_statement":
  {"type": "object",
   "required": ["type"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this logical step.",
     "const": "conclude_statement"},
    "results_used":
    {"type": "array",
     "items": {"$ref": "#/$defs/ResultUsed"},
     "description":
     "(OPTIONAL) Explicit list of results used in the proof, for example where the assertion says \"using ...\". Include both standard results and results from the document itself, with references where available."},
    "claim":
    {"type": "string",
     "description":
     "(OPTIONAL) conclusion of the proof.This is typically the final statement of a proof giving the conclusion of the theorem. If this is not given, it is assumed to be the claim of the theorem being proved."}},
   "description":
   "Conclude a claim obtained from the steps so far. This is typically the final statement of a proof giving the conclusion of the theorem.",
   "additionalProperties": false},
  "calculation_step":
  {"type": "string",
   "description":
   "A step, typically an equality or inequality, in a calculation or computation. Write the step fully: e.g. in the sequence `a=b\n=c`, write `a=b` and `b=c` as two separate steps and DO NOT OMIT `b` in the second step."},
  "calculation":
  {"type": "object",
   "required": ["type"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this logical step.",
     "const": "calculation"},
    "inline_calculation":
    {"type": "string",
     "description":
     "A simple calculation or computation written as a single line."},
    "calculation_sequence":
    {"type": "array",
     "items": {"$ref": "#/$defs/calculation_step"},
     "description": "A list of elements of type `calculation_step`."}},
   "minProperties": 2,
   "maxProperties": 2,
   "description": "An equation, inequality, short calculation etc.",
   "additionalProperties": false},
  "bi-implication_cases_proof":
  {"type": "object",
   "required": ["type", "if_proof", "only_if_proof"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this logical step.",
     "const": "bi-implication_cases_proof"},
    "only_if_proof":
    {"description": "Proof that `Q` implies `P`.",
     "$ref": "#/$defs/ProofDetails"},
    "if_proof":
    {"description": "Proof that `P` implies `Q`.",
     "$ref": "#/$defs/ProofDetails"}},
   "description": "Proof of a statement `P ↔ Q`.",
   "additionalProperties": false},
  "assume_statement":
  {"type": "object",
   "required": ["type", "assumption"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this logical step.",
     "const": "assume_statement"},
    "label":
    {"type": "string",
     "description": "(OPTIONAL) The label of the assumption, if any."},
    "internal_references":
    {"type": "array",
     "items": {"$ref": "#/$defs/InternalReference"},
     "description":
     "(OPTIONAL) Internal references related to the assumption."},
    "citations":
    {"type": "array",
     "items": {"$ref": "#/$defs/Citation"},
     "description":
     "(OPTIONAL) Citations supporting or related to the assumption."},
    "assumption": {"type": "string", "description": "The assumption text."}},
   "description":
   "A mathematical assumption being made. Use 'let_statement' or 'some_statement' if introducing variables or 'assert_statement' to introduce a variable in terms of a property.",
   "additionalProperties": false},
  "assert_statement":
  {"type": "object",
   "required": ["type", "claim"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this logical step.",
     "const": "assert_statement"},
    "results_used":
    {"type": "array",
     "items": {"$ref": "#/$defs/ResultUsed"},
     "description":
     "(OPTIONAL) Explicit list of results used in the proof, for example where the assertion says \"using ...\". Include both standard results and results from the document itself, with references where available."},
    "proof_method":
    {"type": "string",
     "description":
     "(OPTIONAL) The method used to prove the claim. This could be a direct proof, proof by contradiction, proof by induction, etc. this should be a single phrase or a fairly simple sentence; if a longer justification is needed break the step into smaller steps. If the method is deduction from a result, use `citations`or `internal_references`."},
    "label":
    {"type": "string",
     "description":
     "The label of the statement, if any. If this statement is used in a proof or as justification for an assertion, it should be labeled so that it can be referenced later."},
    "internal_references":
    {"type": "array",
     "items": {"$ref": "#/$defs/InternalReference"},
     "description":
     "(OPTIONAL) Explicit list of internal references mentioned in the theorem statement."},
    "claim":
    {"type": "string",
     "description":
     "The mathematical claim being asserted, NOT INCLUDING proofs, justifications or results used. The claim should be purely a logical statement which is the *consequence* obtained."},
    "citations":
    {"type": "array",
     "items": {"$ref": "#/$defs/Citation"},
     "description":
     "(OPTIONAL) Explicit list of citations relevant to this theorem statement."},
    "calculation":
    {"description":
     "(OPTIONAL) An equation, inequality, short calculation etc.",
     "$ref": "#/$defs/calculation"}},
   "description":
   "A mathematical statement whose proof is a straightforward consequence of given and known results following some method.",
   "additionalProperties": false},
  "Theorem":
  {"type": "object",
   "required": ["type", "label", "header", "claim"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this document element.",
     "const": "Theorem"},
    "proof":
    {"description":
     "Proof of the theorems, if it is present soon after the statement.",
     "$ref": "#/$defs/ProofDetails"},
    "label":
    {"type": "string",
     "description":
     "Unique identifier/label for referencing (e.g., 'thm:main', 'lem:pumping')."},
    "internal_references":
    {"type": "array",
     "items": {"$ref": "#/$defs/InternalReference"},
     "description":
     "(OPTIONAL) Explicit list of internal references mentioned in the statement."},
    "hypothesis":
    {"type": "array",
     "items": {"$ref": "#/$defs/Hypothesis_statement"},
     "description":
     "(OPTIONAL) The hypothesis or assumptions of the theorem, consisting of statements like 'let', 'assume', etc."},
    "header":
    {"type": "string",
     "enum": ["Theorem", "Lemma", "Proposition", "Corollary", "Claim"],
     "description":
     "The type of theorem-like environment. Must be one of the predefined values."},
    "claim": {"type": "string", "description": "The statement."},
    "citations":
    {"type": "array",
     "items": {"$ref": "#/$defs/Citation"},
     "description":
     "(OPTIONAL) Explicit list of citations relevant to this statement."}},
   "description":
   "A mathematical theorem, lemma, proposition, corollary, or claim.",
   "additionalProperties": false},
  "Table":
  {"type": "object",
   "required": ["type", "label", "content"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this document element.",
     "const": "Table"},
    "label":
    {"type": "string",
     "description":
     "Unique identifier/label for referencing (e.g., 'tab:results')."},
    "header_row":
    {"type": "boolean",
     "description":
     "(OPTIONAL) Indicates if the first row in 'content' is a header row. Default: false",
     "default": false},
    "content":
    {"type": "array",
     "items": {"type": "array", "items": {"type": "string"}},
     "description":
     "Table data, represented as an array of rows, where each row is an array of cell strings."},
    "caption":
    {"type": "string",
     "description": "(OPTIONAL) Caption describing the table."}},
   "description": "A data table.",
   "additionalProperties": false},
  "Section":
  {"type": "object",
   "required": ["type", "label", "header", "content"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this document element.",
     "const": "Section"},
    "level":
    {"type": "integer",
     "description":
     "The section level such as `1` for a section, `2` for a subsection."},
    "label": {"type": "string", "description": "Section identifier."},
    "header": {"type": "string", "description": "The section header."},
    "content": {"$ref": "#/$defs/LogicalStepSequence"}},
   "description": "A section of the document.",
   "additionalProperties": false},
  "ResultUsed":
  {"type": "object",
   "required": ["statement"],
   "properties":
   {"target_identifier":
    {"type": "string",
     "description":
     "(OPTIONAL) The unique 'label' of the document element being referenced (e.g., 'sec:intro', 'thm:main', 'fig:,diagram')."},
    "statement":
    {"type": "string", "description": "The statement of the result used."},
    "mathlib_identifier":
    {"type": "string",
     "description":
     "(OPTIONAL) The name of the result being used in Lean Prover or its library Mathlib)."}},
   "additionalProperties": false},
  "ProofDetails":
  {"anyOf":
   [{"$ref": "#/$defs/LogicalStepSequence"},
    {"$ref": "#/$defs/pattern_cases_proof"},
    {"$ref": "#/$defs/bi-implication_cases_proof"},
    {"$ref": "#/$defs/condition_cases_proof"},
    {"$ref": "#/$defs/multi-condition_cases_proof"},
    {"$ref": "#/$defs/induction_proof"},
    {"$ref": "#/$defs/general_induction_proof"}]},
  "Proof":
  {"type": "object",
   "required": ["type", "claim_label", "proof_steps"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this document element.",
     "const": "Proof"},
    "proof_steps": {"$ref": "#/$defs/ProofDetails"},
    "claim_label":
    {"type": "string", "description": "Theorem label being proved."}},
   "description":
   "A proof environment for a statement made earlier. If adjacent to the theorem, instead include as the `proof` property of the theorem.",
   "additionalProperties": false},
  "Paragraph":
  {"type": "object",
   "required": ["type", "text"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this document element.",
     "const": "Paragraph"},
    "text":
    {"type": "string",
     "description":
     "The main text content of the paragraph. Inline citations (e.g., [1], [Knuth74]) and internal references (e.g., see Section 2, Theorem 3) might be embedded within this string or explicitly listed in 'citations'/'internal_references'."},
    "internal_references":
    {"type": "array",
     "items": {"$ref": "#/$defs/InternalReference"},
     "description":
     "(OPTIONAL) Explicit list of internal references mentioned in this paragraph."},
    "citations":
    {"type": "array",
     "items": {"$ref": "#/$defs/Citation"},
     "description":
     "(OPTIONAL) Explicit list of citations mentioned in this paragraph."}},
   "description":
   "A block of **plain** text, potentially containing inline references but NOT CONTAINING ANY MATHEMATICS other than motivational remarks.",
   "additionalProperties": false},
  "LogicalStepSequence":
  {"type": "array",
   "items": {"$ref": "#/$defs/LogicalStep"},
   "description":
   "A sequence of structured logical steps, typically used within a proof or derivation, consisting of statements like 'let', 'assert', 'assume', etc."},
  "LogicalStep":
  {"anyOf":
   [{"$ref": "#/$defs/Theorem"},
    {"$ref": "#/$defs/Definition"},
    {"$ref": "#/$defs/let_statement"},
    {"$ref": "#/$defs/assert_statement"},
    {"$ref": "#/$defs/assume_statement"},
    {"$ref": "#/$defs/some_statement"},
    {"$ref": "#/$defs/pattern_cases_proof"},
    {"$ref": "#/$defs/bi-implication_cases_proof"},
    {"$ref": "#/$defs/condition_cases_proof"},
    {"$ref": "#/$defs/multi-condition_cases_proof"},
    {"$ref": "#/$defs/induction_proof"},
    {"$ref": "#/$defs/general_induction_proof"},
    {"$ref": "#/$defs/calculation"},
    {"$ref": "#/$defs/contradiction_statement"},
    {"$ref": "#/$defs/conclude_statement"},
    {"$ref": "#/$defs/Section"},
    {"$ref": "#/$defs/Proof"},
    {"$ref": "#/$defs/Paragraph"},
    {"$ref": "#/$defs/Figure"},
    {"$ref": "#/$defs/Table"}]},
  "InternalReference":
  {"type": "object",
   "required": ["target_identifier"],
   "properties":
   {"target_identifier":
    {"type": "string",
     "description":
     "The unique 'label' of the document element being referenced (e.g., 'sec:intro', 'thm:main', 'fig:diagram')."}},
   "description":
   "An inline reference to another labeled part of the document (e.g., Section, Theorem, Figure).",
   "additionalProperties": false},
  "Hypothesis_statement":
  {"anyOf":
   [{"$ref": "#/$defs/let_statement"},
    {"$ref": "#/$defs/assume_statement"},
    {"$ref": "#/$defs/some_statement"}]},
  "Figure":
  {"type": "object",
   "required": ["type", "label", "source"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this document element.",
     "const": "Figure"},
    "source":
    {"type": "string", "description": "URL or path to the image file."},
    "label":
    {"type": "string",
     "description":
     "Unique identifier/label for referencing (e.g., 'fig:flowchart')."},
    "caption":
    {"type": "string",
     "description": "(OPTIONAL) Caption describing the figure."},
    "alt_text":
    {"type": "string",
     "description": "(OPTIONAL) Alternative text for accessibility."}},
   "description": "A figure or image.",
   "additionalProperties": false},
  "Definition":
  {"type": "object",
   "required": ["type", "label", "header", "definition", "name"],
   "properties":
   {"type":
    {"type": "string",
     "description": "The type of this document element.",
     "const": "Definition"},
    "name":
    {"type": "string",
     "description":
     "The name of the defined object, concept or property. This should be a single word and appear in the definition text."},
    "label": {"type": "string", "description": "Definition identifier."},
    "internal_references":
    {"type": "array",
     "items": {"$ref": "#/$defs/InternalReference"},
     "description":
     "(OPTIONAL) Explicit list of internal references mentioned in the theorem statement."},
    "header":
    {"type": "string",
     "enum": ["Definition", "Notation", "Terminology", "Convention"],
     "description": "The definition type."},
    "definition": {"type": "string", "description": "Definition content."},
    "citations":
    {"type": "array",
     "items": {"$ref": "#/$defs/Citation"},
     "description":
     "(OPTIONAL) Explicit list of citations relevant to this theorem statement."}},
   "description":
   "A mathematical definition. DO NOT include additional properties in the definition. Use a separate `assert_statement` for additional properties.",
   "additionalProperties": false},
  "Citation":
  {"type": "object",
   "required": ["cite_keys"],
   "properties":
   {"cite_keys":
    {"type": "array",
     "minItems": 1,
     "items": {"type": "string"},
     "description": "An array of bibliography keys being cited."}},
   "description":
   "An inline citation pointing to one or more bibliography entries.",
   "additionalProperties": false}}}
-/
#guard_msgs in
#eval allDefsView

end LeanAide

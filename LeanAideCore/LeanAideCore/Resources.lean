import Lean

namespace LeanAide.Resources

def templates :=
  json% {
  "lean_trans_prompt": "You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. Follow EXACTLY the examples given.",
  "sys_prompt": "You are a Mathematics, Lean 4 and coding assistant who answers questions about Mathematics and Lean 4, gives hints while coding in Lean 4. You also translates from natural language to Lean Theorem Prover code and vice versa when asked.",
  "translate_sys_prompt": "Follow EXACTLY any examples given when generating Lean code.",
  "math_sys_prompt": "You are a mathematics assistant for research mathematicians and advanced students who also helps with computer-assisted mathematics. Answer mathematical questions with the level of precision and detail expected in graduate level mathematics courses and in mathematics research papers. Be concise and give only what is asked for, avoiding phrases like 'Here is the proof'. Some of your output is designed to be used as input to programs, so give answers to questions as best as you can in the form requested. In particular give valid JSON when this is asked for. Do not explain the process by which the answer can be obtained instead of giving the answer.",
  "theorem_proof": "##Theorem:\n${theorem}\n## Proof\n${proof}\n",
  "prove": "Prove the following theorem:\n## Theorem \n${theorem}\n\nGive ONLY the proof.",
  "solve": "Solve the following problem:\n## Problem \n${problem}\n\nGive only the solution.",
  "solution_to_theory": "The following is a mathematical problem and its solution\n## Problem\n${problem}\n## Solution\n${solution}\n-----\n\nRewrite this as one or more theorems and their proofs.",
  "prove_or_disprove": "Prove or disprove the following theorem:\n## Theorem \n${theorem}\n",
  "theorems_proved": "The given document contains one or more mathematical theorems and their proofs. \n\n## Document\n${document}\n\nGive ONLY the list of **statements** of theorems proved in the document as a JSON list (of JSON strings).",
  "theorems_used": "The given document contains one or more mathematical theorems and their proofs. \n\n## Document\n${document}\n\nPlease give the statements of theorems (from the literature) **used** in the **proofs** in the document. Give the **full statements** in general form as in the literature. Give ONLY the list of statements of theorems **used in proofs** in the document as a JSON list (of JSON strings).",
  "json_structured": "The following is a JSON schema for representing mathematical documents ranging from theorems with proofs to papers:\n\n```json\n${schema}\n```\n.Write the following document in the above schema.\n\n---\n${document}\n---\n\nOutput ONLY the JSON document in the above schema.\n",
  "make_structured": "Your goal is to write the following mathematics in a specific JSON format, `ProofJSON`, which is described as follows:\n\n${proof_json}\n\nTranslate the following proof into the `ProofJSON` format.\n${text}\n",
  "extend_structured": "Your goal is to write the following mathematics in a specific JSON format, `ProofJSON`, which is described as follows:\n\n${proof_json}\n\nThe following is a summary of the results of the earlier sections of the document in a simpler JSON format, with proofs omitted.\n\n${preceding}\n---------\n\nTranslate the following proof into the `ProofJSON` format.\n${text}\n",
  "add_statements": " The following is a body of mathematics in the `ProofJSON` format, a particular JSON schema.\n\n${json}\nFor each object of type `assertion`, add a field `statement` which is a self-contained statement of the assertion (including all the assumptions and relevant `let` statements) like the statement of a lemma: for example make the statement `if H is a subgroup of Z/10 then the order of Z divides 10` if the **claim** is `H is a subgroup of Z/10` and **deduced-from** includes `the order of Z divides 10`. Give the modified JSON only.",
  "prove_with_outline": "Prove the following theorem, using the outline provided.\n## Theorem\n${theorem}\n## Outline\n${outline}\n",
  "expand_deductions": "The following is a body of mathematics in the `ProofJSON` format, a particular JSON schema.\n\n${json}\nFor each object of type `assertion`, check whether the `claim` indeed follows from the results in `deduced_from`. If there is a mathematical error in the claim, add a field `error` with a description of the error. If the `claim` follows from the `deduced_from` results, expand each theorem in the `deduced_from` list to have fields `name`, `statement` (the general form of the statement applied), `applied-to` (the instantiantiations, i.e. values of the variables, for the specific application), `assumptions-satisfied` (the assumptions of the general statements that are satisfied here allowing the statement to be applied). For example, if the claim is `H is a subgroup of Z/10` and `deduced_from` includes `the order of Z divides 10` and `Lagrange's theorem, then replace `Lagrange's theorem` by the object `{\"name\": \"Lagrange's theorem\", \"statement\": \"If H is a subgroup of a group G then the order of H divides the order of G\", \"applied-to\": {\"H\": \"H\", \"G\": \"Z/10\"}, \"assumptions-satisfied\": [\"Z/10 is a group\", \"H is a subgroup of Z/10\"] }`. Carefully read the proof and give the modified JSON (with more details for the proof) only.",
  "expand_observations": "Your goal is to check and report errors or supply details as appropriate for a body of mathematics in the `ProofJSON` format, a particular JSON schema. For reference, the description of `ProofJson` is the following:\n${proof_json}\nThe following is the body of mathematics which you have to review and rewrite:\n${json}\nFor each object of type `observation`,\n* If the observation is mathematically incorrect, add a field `error` with the error.\n* If the observation is correct and simple enough that it will be given without proof in a graduate text, leave it unchanged.\n* If the observation is correct but not obvious, replace the corresponding object with one of type `assertion`, `lemma` or `theorem` with fields as in the ProofJSON format.\n\nCarefully read the proof and give the modified JSON (with more details for the proof) only.",
  "expand_justifications": "Your goal is to check and report errors or supply details as appropriate for a body of mathematics in the `ProofJSON` format, a particular JSON schema. For reference, the description of `ProofJson` is the following:\n${proof_json}\nThe following is the body of mathematics which you have to review and rewrite:\n${json}\nFor each object of type `assertion` which has a `justification` field,\n* If the `claim` is mathematically incorrect, add a field `error` with the error.\n* If the `claime` is correct and a simple enough consequence of the `deduced_from` that it will be stated as a consequence of these without further proof in a graduate text, remove the justification.\n* If the `claim` is correct but not an obvious consequence of the statements in `deduced_from`, replace the corresponding object with one of type `lemma` or `theorem` with fields as in the ProofJSON format.\n\nCarefully read the proof and give the modified JSON (with more details for the proof) only.",
  "add_names": "The following is a body of mathematics in the `ProofJSON` format, a particular JSON schema.\n\n${json}\nFor each of the objects of add a field `name` which is a unique name for the let statement following the conventions of the Lean Mathematics library.\n\n${json}\n--------\nThe following are some theorems and definitions as examples of the desired format.\n\n${examples}\n",
  "explicit_references": "The following is a body of mathematics in the `ProofJSON` format, a particular JSON schema.\n\n${json}\nFor each object of type `assertion`, modify `deduced_from` if necessary so that each entry is either the name of some object mentioned earlier or that of a standard theorem, or an object with fields `result` and `applied_to` both of which are names of objects mentioned earlier. If needed introduce objects of type `theorem`, `let` or `definition` to make this possible.",
  "summarize": "The following is a body of mathematics in the `ProofJSON` format, a particular JSON schema.\n\n${json}\nSummarize the contents for use in subsequent sections of the document by omitting all proofs and using a similar JSON format with only `definition` and `theorem` types. For objects with type `theorem` include a `status` field.\n",
  "doc_string": "Describe the following ${kind} briefly in natural language, similar to a documentation string. The description should be either a single sentence or a paragraph with 2-3 sentences, and may contain LaTeX mathematics.\n```lean\n${head} ${theorem} := by sorry\n```.",
  "informalize": "Translate the following Lean 4 code briefly into natural language. The translation can contain LaTeX mathematics. Note that a variable in Lean that has type a proposition can be interpreted as an assumption. Proofs of theorems have been omitted for brevity but all theorems have been proved.\n```lean\n${code}\n```\n",
  "describe_theorem": "Describe the following theorem (whose proof is suppressed for brevity) in natural language, similar to a documentation string. The description should be either a single sentence or a paragraph with 2-3 sentences, and may contain LaTeX mathematics.\n```lean\n${theorem}\n```\n",
  "describe_theorem_with_defs": "The following are some definitions in Lean 4 that are involved in the statement of a theorem which you have to describe in natural language.\n```lean\n${definitions}\n```\n\nDescribe the following theorem (whose proof is suppressed for brevity) in natural language, similar to a documentation string. The description should be either a single sentence or a paragraph with 2-3 sentences, and may contain LaTeX mathematics.\n```lean\n${theorem}\n```\n",
  "state_theorem": "State the following theorem (whose proof is suppressed for brevity) in natural language concisely in a single sentence, which may contain LaTeX mathematics (enclosed in `$` signs).\n```lean\n${theorem}\n```\n",
  "state_theorem_with_defs": "The following are some definitions in Lean 4 that are involved in the statement of a theorem which you have to state in natural language.\n```lean\n${definitions}\n```\n\nState the following theorem (whose proof is suppressed for brevity) in natural language concisely in a single sentence, which may contain LaTeX mathematics (enclosed in `$` signs).\n```lean\n${theorem}\n```\n",
  "state_def": "State the following theorem Lean 4 definition in natural language concisely in a single sentence, which may contain LaTeX mathematics (enclosed in `$` signs).\n```lean\n${defn}\n```\n",
  "state_def_with_defs": "The following are some definitions in Lean 4 that are involved in the statement of a theorem which you have to state in natural language.\n```lean\n${definitions}\n```\n\nState the following Lean 4 definition in natural language concisely in a single sentence, which may contain LaTeX mathematics (enclosed in `$` signs).\n```lean\n${defn}\n```\n",
  "prove_theorem": "State and prove the following theorem (whose Lean proof is suppressed for brevity) in natural language using markdown, which may contain LaTeX mathematics (enclosed in `$` signs).\n```lean\n${theorem}\n```\n",
  "prove_theorem_with_defs": "The following are some definitions in Lean 4 that are involved in the statement of a theorem which you have to state and prove in natural language.\n```lean\n${definitions}\n```\n\nState and prove the following theorem (whose Lean proof is suppressed for brevity) in natural language using markdown, which may contain LaTeX mathematics (enclosed in `$` signs).\n```lean\n${theorem}\n```\n",
  "prove_theorem_for_formalization": "Your goal is to give a **natural language** proof of a theorem so that the proof can be further processed to generate Lean Code. To facilitate formalisation, follow the following guidelines:\n\n${proof_guidelines}.\n\nThe theorem you need to prove is the following:\n\n## Theorem: {thm}\n\n The statement of the theorem (with proof given as `sorry`) in Lean and  some definitions in Lean 4 that are involved in the statement of the theorem are below.\n```lean\n/-- ${thm}-/\n${statement}\n\n${definitions}\n```\n\nGive a proof of the theorem in **natural language** following the **guidelines** and using definitions as in Lean (as given above). The proof can use markdown, which may contain LaTeX mathematics (enclosed in `$` signs) and unicode characters for mathematics but **should not contain Lean Code**.",
  "math_terms": "In the following statement, give a list of mathematical terms whose definition may not be familiar to typical advanced mathematics students. This could be an empty list or a singleton:\n\n${statement}\nGive ONLY a JSON list of objects, each with two fields: `term` and `definition`",
  "math_terms_excluding": "In the following statement, give a list of mathematical terms whose definition may not be familiar to typical advanced mathematics students. The list of terms co could be an empty list or a singleton:\n\n${statement}\n---\nExclude the following definitions which are assumed to be known\n\n${exclusions}\n---\n\nGive ONLY a JSON list of objects, each with two fields: `term` and `definition`",
  "math_synonyms": "For each of the mathematical terms in the following JSON list, give synonyms in JSON format as list of objects with two fields: \"term\" and \"synonyms\". If there are no synonyms, return an empty list.\n\n{terms}\n",
  "summarise": "Summarise the following mathematical text briefly. The summary should include the main definitions, the statements of the main theorems and the main ideas in the proofs of the theorems. Definitions and theorems should be precisely stated. Include precise statements of the theorems used.\n\n---\n${text}\n",
  "suggest_lemma": "The following is a mathematical statement in Lean (with proof omitted) preceded by a decription as a documentation string (enclosed between `/--` and `-/`).\n```lean\n/-- ${description} -/\ntheorem ${name} : ${theorem} := by sorry\n```\n Suggest a lemma that could be used to prove the theorem. The lemma should be a mathematical statement in Lean that is simpler than the theorem and is used in the proof of the theorem. Give ONLY the Lean code for the statement of the lemma.\n",
  "known_results": "The following are known results that can be used without proof, even implicitly. DO NOT report the use of these results as errors or missing steps.",
  "check_equivalence": "The following are two statements which are supposed to state the same theorem.\n\n## Theorem 1\n\n${theorem1}\n\n---\n\n## Theorem 2\n\n${theorem2}\n\n---\n\nDo these statements state the same theorem? Identical statements are fine. It is fine if one version omits assumptions that are generally implicit. \nAnswer ONLY `true` if the statements are the same; if they are different output `false` as the first line and then a brief explanation in a single short sentence why the statements do not state the same result.",
  "check_equivalence_with_defs": "The following are some definitions in Lean 4 that are involved in the statements of theorems which you have to compare.\n```lean\n${definitions}\n```\n\nThe following are two statements which are supposed to state the same theorem.\n\n## Theorem 1\n\n${theorem1}\n\n---\n\n## Theorem 2\n\n${theorem2}\n\n---\n\nDo these statements state the same theorem? Identical statements are fine. It is fine if one version omits assumptions that are generally implicit. \nAnswer ONLY `true` if the statements are the same; if they are different output `false` as the first line and then a brief explanation in a single short sentence why the statements do not state the same result."
}

def paperStructure :=
  json% {
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "Mathematical Document Wrapper",
  "description": "JSON schema for a structured mathematical document.",
  "type": "object",
  "properties": {
    "document": {
      "type": "object",
      "description": "The root of the mathematical document, containing a sequence of environments.",
      "properties": {
        "type": {
          "type": "string",
          "const": "document",
          "description": "The type of this document element."
        },
        "body": {
          "$ref": "#/$defs/LogicalStepSequence"
        },
        "title": {
          "type": "string",
          "description": "(OPTIONAL) The title of the document."
        },
        "abstract": {
          "type": "string",
          "description": "(OPTIONAL) The abstract of the document."
        },
        "metadata": {
          "type": "object",
          "description": "(OPTIONAL) Metadata about the document, such as authors, date, etc.",
          "properties": {
            "authors": {
              "type": "array",
              "description": "(OPTIONAL) List of authors of the document.",
              "items": {
                "type": "string"
              }
            },
            "date": {
              "type": "string",
              "format": "date",
              "description": "(OPTIONAL) Date of the document."
            }
          }
        }
      },
      "required": [
        "type",
        "body"
      ],
      "additionalProperties": false
    }
  },
  "required": [
    "document"
  ],
  "additionalProperties": false,
  "$defs": {
    "Section": {
      "type": "object",
      "description": "A section of the document.",
      "properties": {
        "type": {
          "type": "string",
          "const": "Section",
          "description": "The type of this document element."
        },
        "content": {
          "$ref": "#/$defs/LogicalStepSequence"
        },
        "label": {
          "type": "string",
          "description": "Section identifier."
        },
        "level": {
          "type": "integer",
          "description": "The section level such as `1` for a section, `2` for a subsection."
        },
        "header": {
          "type": "string",
          "description": "The section header."
        }
      },
      "required": [
        "type",
        "label",
        "header",
        "content"
      ],
      "additionalProperties": false
    },
    "Hypothesis_statement": {
            "anyOf": [
              {
                "$ref": "#/$defs/let_statement"
              },
              {
                "$ref": "#/$defs/assume_statement"
              },
              {
                "$ref": "#/$defs/some_statement"
              }
            ]
          },
    "Theorem": {
      "type": "object",
      "description": "A mathematical theorem, lemma, proposition, corollary, or claim.",
      "properties": {
        "type": {
          "type": "string",
          "const": "Theorem",
          "description": "The type of this document element."
        },
        "hypothesis": {
          "type": "array",
          "description": "(OPTIONAL) The hypothesis or assumptions of the theorem, consisting of statements like 'let', 'assume', etc.",
          "items": {
          "$ref": "#/$defs/Hypothesis_statement"
        }
        },
        "claim": {
          "type": "string",
          "description": "The statement."
        },
        "label": {
          "type": "string",
          "description": "Unique identifier/label for referencing (e.g., 'thm:main', 'lem:pumping')."
        },
        "proof": {
          "$ref": "#/$defs/ProofDetails",
          "description": "Proof of the theorems, if it is present soon after the statement."
        },
        "header": {
          "type": "string",
          "description": "The type of theorem-like environment. Must be one of the predefined values.",
          "enum": [
            "Theorem",
            "Lemma",
            "Proposition",
            "Corollary",
            "Claim"
          ]
        },
        "citations": {
          "type": "array",
          "description": "(OPTIONAL) Explicit list of citations relevant to this statement.",
          "items": {
            "$ref": "#/$defs/Citation"
          }
        },
        "internal_references": {
          "type": "array",
          "description": "(OPTIONAL) Explicit list of internal references mentioned in the statement.",
          "items": {
            "$ref": "#/$defs/InternalReference"
          }
        }
      },
      "required": [
        "type",
        "label",
        "header",
        "claim"
      ],
      "additionalProperties": false
    },
    "Definition": {
      "type": "object",
      "description": "A mathematical definition. DO NOT include additional properties in the definition. Use a separate `assert_statement` for additional properties.",
      "properties": {
        "type": {
          "type": "string",
          "const": "Definition",
          "description": "The type of this document element."
        },
        "definition": {
          "type": "string",
          "description": "Definition content."
        },
        "name": {
          "type": "string",
          "description": "The name of the defined object, concept or property. This should be a single word and appear in the definition text."
        },
        "label": {
          "type": "string",
          "description": "Definition identifier."
        },
        "header": {
          "type": "string",
          "description": "The definition type.",
          "enum": [
            "Definition",
            "Notation",
            "Terminology",
            "Convention"
          ]
        },
        "citations": {
          "type": "array",
          "description": "(OPTIONAL) Explicit list of citations relevant to this theorem statement.",
          "items": {
            "$ref": "#/$defs/Citation"
          }
        },
        "internal_references": {
          "type": "array",
          "description": "(OPTIONAL) Explicit list of internal references mentioned in the theorem statement.",
          "items": {
            "$ref": "#/$defs/InternalReference"
          }
        }
      },
      "required": [
        "type",
        "label",
        "header",
        "definition",
        "name"
      ],
      "additionalProperties": false
    },
    "LogicalStep": {
      "anyOf": [
        {
          "$ref": "#/$defs/Theorem"
        },
        {
          "$ref": "#/$defs/Definition"
        },
        {
          "$ref": "#/$defs/let_statement"
        },
        {
          "$ref": "#/$defs/assert_statement"
        },
        {
          "$ref": "#/$defs/assume_statement"
        },
        {
          "$ref": "#/$defs/some_statement"
        },
        {
          "$ref": "#/$defs/pattern_cases_proof"
        },
        {
          "$ref": "#/$defs/bi-implication_cases_proof"
        },
        {
          "$ref": "#/$defs/condition_cases_proof"
        },
        {
          "$ref": "#/$defs/multi-condition_cases_proof"
        },
        {
          "$ref": "#/$defs/induction_proof"
        },
        {
          "$ref": "#/$defs/general_induction_proof"
        },
        {
          "$ref": "#/$defs/calculation"
        },
        {
          "$ref": "#/$defs/contradiction_statement"
        },
        {
          "$ref": "#/$defs/conclude_statement"
        },
        {
          "$ref": "#/$defs/Section"
        },
        {
          "$ref": "#/$defs/Proof"
        },
        {
          "$ref": "#/$defs/Paragraph"
        },
        {
          "$ref": "#/$defs/Figure"
        },
        {
          "$ref": "#/$defs/Table"
        }
      ]
    },
    "LogicalStepSequence": {
      "type": "array",
      "description": "A sequence of structured logical steps, typically used within a proof or derivation, consisting of statements like 'let', 'assert', 'assume', etc.",
      "items": {
        "$ref": "#/$defs/LogicalStep"
      }
    },
    "ProofDetails": {
      "anyOf": [
        {
          "$ref": "#/$defs/LogicalStepSequence"
        },
        {
          "$ref": "#/$defs/pattern_cases_proof"
        },
        {
          "$ref": "#/$defs/bi-implication_cases_proof"
        },
        {
          "$ref": "#/$defs/condition_cases_proof"
        },
        {
          "$ref": "#/$defs/multi-condition_cases_proof"
        },
        {
          "$ref": "#/$defs/induction_proof"
        },
        {
          "$ref": "#/$defs/general_induction_proof"
        }
      ]
    },
    "Proof": {
      "type": "object",
      "description": "A proof environment for a statement made earlier. If adjacent to the theorem, instead include as the `proof` property of the theorem.",
      "properties": {
        "type": {
          "type": "string",
          "const": "Proof",
          "description": "The type of this document element."
        },
        "claim_label": {
          "type": "string",
          "description": "Theorem label being proved."
        },
        "proof_steps": {
          "$ref": "#/$defs/ProofDetails"
        }
      },
      "required": [
        "type",
        "claim_label",
        "proof_steps"
      ],
      "additionalProperties": false
    },
    "let_statement": {
      "type": "object",
      "description": "A statement introducing a new variable with given value, type and/or property.",
      "properties": {
        "type": {
          "type": "string",
          "const": "let_statement",
          "description": "The type of this logical step."
        },
        "variable_name": {
          "type": "string",
          "description": "The variable being defined (use `<anonymous>` if there is no name such as in `We have a group structure on S`)"
        },
        "value": {
          "type": "string",
          "description": "(OPTIONAL) The value of the variable being defined. This MUST BE an explicit value. If the value is the obtained from an existence statement, use `assert_statement` instead."
        },
        "variable_type": {
          "type": "string",
          "description": "(OPTIONAL) The type of the variable, such as `real number`, `function from S to T`, `element of G` etc."
        },
        "properties": {
          "type": "string",
          "description": "(OPTIONAL) Specific properties of the variable beyond the type"
        },
        "statement": {
          "type": "string",
          "description": "The full statement made."
        }
      },
      "required": [
        "type",
        "variable_name"
      ],
      "additionalProperties": false
    },
    "some_statement": {
      "type": "object",
      "description": "A statement introducing a new variable and saying that **some** value of this variable is as required (i.e., an existence statement). This is possibly with given type and/or property. This corresponds to statements like 'for some integer `n` ...' or 'There exists an integer `n` ....'. **NOTE:** It is better to use `assert_statement` instead if the variable is not being defined but rather asserted to exist.",
      "properties": {
        "type": {
          "type": "string",
          "const": "some_statement",
          "description": "The type of this logical step."
        },
        "variable_name": {
          "type": "string",
          "description": "The variable being defined (use `<anonymous>` if there is no name such as in `We have a group structure on S`)"
        },
        "variable_kind": {
          "type": "string",
          "description": "(OPTIONAL) The type of the variable, such as `real number`, `function from S to T`, `element of G` etc."
        },
        "properties": {
          "type": "string",
          "description": "(OPTIONAL) Specific properties of the variable beyond the type"
        },
        "statement": {
          "type": "string",
          "description": "The full statement made."
        }
      },
      "required": [
        "type",
        "variable_name"
      ],
      "additionalProperties": false
    },
    "assume_statement": {
      "type": "object",
      "description": "A mathematical assumption being made. Use 'let_statement' or 'some_statement' if introducing variables or 'assert_statement' to introduce a variable in terms of a property.",
      "properties": {
        "type": {
          "type": "string",
          "const": "assume_statement",
          "description": "The type of this logical step."
        },
        "assumption": {
          "type": "string",
          "description": "The assumption text."
        },
        "label": {
          "type": "string",
          "description": "(OPTIONAL) The label of the assumption, if any."
        },
        "citations": {
          "type": "array",
          "description": "(OPTIONAL) Citations supporting or related to the assumption.",
          "items": {
            "$ref": "#/$defs/Citation"
          }
        },
        "internal_references": {
          "type": "array",
          "description": "(OPTIONAL) Internal references related to the assumption.",
          "items": {
            "$ref": "#/$defs/InternalReference"
          }
        }
      },
      "required": [
        "type",
        "assumption"
      ],
      "additionalProperties": false
    },
    "assert_statement": {
      "type": "object",
      "description": "A mathematical statement whose proof is a straightforward consequence of given and known results following some method.",
      "properties": {
        "type": {
          "type": "string",
          "const": "assert_statement",
          "description": "The type of this logical step."
        },
        "claim": {
          "type": "string",
          "description": "The mathematical claim being asserted, NOT INCLUDING proofs, justifications or results used. The claim should be purely a logical statement which is the *consequence* obtained."
        },
        "proof_method": {
          "type": "string",
          "description": "(OPTIONAL) The method used to prove the claim. This could be a direct proof, proof by contradiction, proof by induction, etc. this should be a single phrase or a fairly simple sentence; if a longer justification is needed break the step into smaller steps. If the method is deduction from a result, use `citations`or `internal_references`."
        },
        "label": {
          "type": "string",
          "description": "The label of the statement, if any. If this statement is used in a proof or as justification for an assertion, it should be labeled so that it can be referenced later."
        },
        "citations": {
          "type": "array",
          "description": "(OPTIONAL) Explicit list of citations relevant to this theorem statement.",
          "items": {
            "$ref": "#/$defs/Citation"
          }
        },
        "results_used": {
          "type": "array",
          "description": "(OPTIONAL) Explicit list of results used in the proof, for example where the assertion says \"using ...\". Include both standard results and results from the document itself, with references where available.",
          "items": {
            "$ref": "#/$defs/ResultUsed"
          }
        },
        "internal_references": {
          "type": "array",
          "description": "(OPTIONAL) Explicit list of internal references mentioned in the theorem statement.",
          "items": {
            "$ref": "#/$defs/InternalReference"
          }
        },
        "calculation": {
          "$ref": "#/$defs/calculation",
          "description": "(OPTIONAL) An equation, inequality, short calculation etc."
        }
      },
      "required": [
        "type",
        "claim"
      ],
      "additionalProperties": false
    },
    "calculation": {
      "type": "object",
      "description": "An equation, inequality, short calculation etc.",
      "minProperties": 2,
      "maxProperties": 2,
      "properties": {
        "type": {
          "type": "string",
          "const": "calculation",
          "description": "The type of this logical step."
        },
        "inline_calculation": {
          "type": "string",
          "description": "A simple calculation or computation written as a single line."
        },
        "calculation_sequence": {
          "type": "array",
          "description": "A list of elements of type `calculation_step`.",
          "items": {
            "$ref": "#/$defs/calculation_step"
          }
        }
      },
      "required": [
        "type"
      ],
      "additionalProperties": false
    },
    "calculation_step": {
      "type": "string",
      "description": "A step, typically an equality or inequality, in a calculation or computation. Write the step fully: e.g. in the sequence `a=b\n=c`, write `a=b` and `b=c` as two separate steps and DO NOT OMIT `b` in the second step."
    },
    "pattern_cases_proof": {
      "type": "object",
      "description": "A proof by cases, with cases determined by matching a pattern.",
      "properties": {
        "type": {
          "type": "string",
          "const": "pattern_cases_proof",
          "description": "The type of this logical step."
        },
        "on": {
          "type": "string",
          "description": "The variable or expression which is being matched against patterns."
        },
        "proof_cases": {
          "type": "array",
          "description": "A list of elements of type `case`.",
          "items": {
            "$ref": "#/$defs/pattern_case"
          }
        }
      },
      "required": [
        "type",
        "on",
        "proof_cases"
      ],
      "additionalProperties": false
    },
    "bi-implication_cases_proof": {
      "type": "object",
      "description": "Proof of a statement `P ↔ Q`.",
      "properties": {
        "type": {
          "type": "string",
          "const": "bi-implication_cases_proof",
          "description": "The type of this logical step."
        },
        "if_proof": {
          "$ref": "#/$defs/ProofDetails",
          "description": "Proof that `P` implies `Q`."
        },
        "only_if_proof": {
          "$ref": "#/$defs/ProofDetails",
          "description": "Proof that `Q` implies `P`."
        }
      },
      "required": [
        "type",
        "if_proof",
        "only_if_proof"
      ],
      "additionalProperties": false
    },
    "condition_cases_proof": {
      "type": "object",
      "description": "Proof of a statement based on splitting into cases where a condition is true and false, i.e., an if-then-else proof.",
      "properties": {
        "type": {
          "type": "string",
          "const": "condition_cases_proof",
          "description": "The type of this logical step."
        },
        "condition": {
          "type": "string",
          "description": "The condition based on which the proof is split."
        },
        "true_case_proof": {
          "$ref": "#/$defs/ProofDetails",
          "description": "Proof of the case where the condition is true."
        },
        "false_case_proof": {
          "$ref": "#/$defs/ProofDetails",
          "description": "Proof of the case where the condition is false."
        }
      },
      "required": [
        "type",
        "condition",
        "true_case_proof",
        "false_case_proof"
      ],
      "additionalProperties": false
    },
    "multi-condition_cases_proof": {
      "type": "object",
      "description": "A proof by cases given by three or more conditions.",
      "properties": {
        "type": {
          "type": "string",
          "const": "multi-condition_cases_proof",
          "description": "The type of this logical step."
        },
        "proof_cases": {
          "type": "array",
          "description": "The conditions and proofs in the different cases.",
          "items": {
            "$ref": "#/$defs/condition_case"
          }
        },
        "exhaustiveness": {
          "$ref": "#/$defs/ProofDetails",
          "description": "(OPTIONAL) Proof that the cases are exhaustive."
        }
      },
      "required": [
        "type",
        "proof_cases"
      ],
      "additionalProperties": false
    },
    "general_induction_proof": {
      "type": "object",
      "description": "A proof by cases given by three or more conditions.",
      "properties": {
        "type": {
          "type": "string",
          "const": "general_induction_proof",
          "description": "The type of this logical step."
        },
        "induction_principle": {
          "type": "string",
          "description": "The induction principle being used, such as 'strong induction for natural numbers' or 'structural induction for binary trees'."
        },
        "proof_cases": {
          "type": "array",
          "description": "The conditions and proofs in the different cases.",
          "items": {
            "$ref": "#/$defs/induction_case"
          }
        }
      },
      "required": [
        "type",
        "induction_principle",
        "proof_cases"
      ],
      "additionalProperties": false
    },
    "pattern_case": {
      "type": "object",
      "description": "A case in a proof by cases with cases determined by matching patterns.",
      "properties": {
        "pattern": {
          "type": "string",
          "description": "The pattern determining this case."
        },
        "proof": {
          "$ref": "#/$defs/ProofDetails",
          "description": "Proof of this case."
        }
      },
      "required": [
        "pattern",
        "proof"
      ],
      "additionalProperties": false
    },
    "condition_case": {
      "type": "object",
      "description": "A case in a proof by cases with cases determined by conditions.",
      "properties": {
        "condition": {
          "type": "string",
          "description": "The condition determining this case."
        },
        "proof": {
          "$ref": "#/$defs/ProofDetails",
          "description": "Proof for this case."
        }
      },
      "required": [
        "condition",
        "proof"
      ],
      "additionalProperties": false
    },
    "induction_case": {
      "type": "object",
      "description": "A case in a proof by a general form of induction, such as strong induction or structural induction.",
      "properties": {
        "condition": {
          "type": "string",
          "description": "The condition determining this case."
        },
        "induction_hypotheses": {
          "type": "array",
          "description": "(OPTIONAL) The induction hypotheses. Give the full assumption for the case. Omit for base cases.",
          "items": {
            "type": "string"
          }
        },
        "proof": {
          "$ref": "#/$defs/ProofDetails",
          "description": "Proof for this case."
        }
      },
      "required": [
        "condition",
        "proof"
      ],
      "additionalProperties": false
    },
    "case": {
      "type": "object",
      "description": "A case in a proof by cases or proof by induction.",
      "properties": {
        "type": {
          "type": "string",
          "const": "case",
          "description": "The type of this logical step."
        },
        "condition": {
          "type": "string",
          "description": "The case condition or pattern; for induction one of 'base' or 'induction-step'; for a side of an 'iff' statement write the claim being proved (i.e., the statement `P => Q` or `Q => P`)."
        },
        "proof": {
          "$ref": "#/$defs/ProofDetails",
          "description": "Proof of this case."
        }
      },
      "required": [
        "type",
        "condition",
        "proof"
      ],
      "additionalProperties": false
    },
    "induction_proof": {
      "type": "object",
      "description": "A proof by induction, with a base case and an induction step. For strong induction or structural induction, USE INSTEAD 'general_induction_proof'.",
      "properties": {
        "type": {
          "type": "string",
          "const": "induction_proof",
          "description": "The type of this logical step."
        },
        "on": {
          "type": "string",
          "description": "The variable or expression on which induction is being done."
        },
        "prev_var": {
          "type": "string",
          "description": "(OPTIONAL) The variable `m` so that the induction case if `m + 1`. If omitted it is assumed that it is the same as the 'on' variable, i.e., the induction step is `n + 1` where `n` is the variable on which induction is done."
        },
        "base_case_proof": {
          "$ref": "#/$defs/ProofDetails",
          "description": "Proof of the base case."
        },
        "induction_step_proof": {
          "$ref": "#/$defs/ProofDetails",
          "description": "Proof of the induction step, which typically shows that if the statement holds for `n`, it holds for `n+1`."
        }
      },
      "required": [
        "type",
        "on",
        "base_case_proof",
        "induction_step_proof"
      ],
      "additionalProperties": false
    },
    "contradiction_statement": {
      "type": "object",
      "description": "A proof by contradiction, with an assumption and a proof of the contradiction.",
      "properties": {
        "type": {
          "type": "string",
          "const": "contradiction_statement",
          "description": "The type of this logical step."
        },
        "assumption": {
          "type": "string",
          "description": "The assumption being made to be contradicted."
        },
        "proof": {
          "$ref": "#/$defs/ProofDetails",
          "description": "The proof of the contradiction given the assumption."
        }
      },
      "required": [
        "type",
        "assumption",
        "proof"
      ],
      "additionalProperties": false
    },
    "conclude_statement": {
      "type": "object",
      "description": "Conclude a claim obtained from the steps so far. This is typically the final statement of a proof giving the conclusion of the theorem.",
      "properties": {
        "type": {
          "type": "string",
          "const": "conclude_statement",
          "description": "The type of this logical step."
        },
        "claim": {
          "type": "string",
          "description": "(OPTIONAL) conclusion of the proof.This is typically the final statement of a proof giving the conclusion of the theorem. If this is not given, it is assumed to be the claim of the theorem being proved."
        },
        "results_used": {
          "type": "array",
          "description": "(OPTIONAL) Explicit list of results used in the proof, for example where the assertion says \"using ...\". Include both standard results and results from the document itself, with references where available.",
          "items": {
            "$ref": "#/$defs/ResultUsed"
          }
        }
      },
      "required": [
        "type"
      ],
      "additionalProperties": false
    },
    "ResultUsed": {
      "type": "object",
      "properties": {
        "statement": {
          "type": "string",
          "description": "The statement of the result used."
        },
        "target_identifier": {
          "type": "string",
          "description": "(OPTIONAL) The unique 'label' of the document element being referenced (e.g., 'sec:intro', 'thm:main', 'fig:,diagram')."
        },
        "mathlib_identifier": {
          "type": "string",
          "description": "(OPTIONAL) The name of the result being used in Lean Prover or its library Mathlib)."
        }
      },
      "required": [
        "statement"
      ],
      "additionalProperties": false
    },
    "Author": {
      "type": "object",
      "description": "An author of the document.",
      "properties": {
        "name": {
          "type": "string",
          "description": "Full name of the author."
        },
        "affiliation": {
          "type": "string",
          "description": "(OPTIONAL) Author's affiliation."
        }
      },
      "required": [
        "name"
      ],
      "additionalProperties": false
    },
    "Paragraph": {
      "type": "object",
      "description": "A block of **plain** text, potentially containing inline references but NOT CONTAINING ANY MATHEMATICS other than motivational remarks.",
      "properties": {
        "type": {
          "type": "string",
          "const": "Paragraph",
          "description": "The type of this document element."
        },
        "text": {
          "type": "string",
          "description": "The main text content of the paragraph. Inline citations (e.g., [1], [Knuth74]) and internal references (e.g., see Section 2, Theorem 3) might be embedded within this string or explicitly listed in 'citations'/'internal_references'."
        },
        "citations": {
          "type": "array",
          "description": "(OPTIONAL) Explicit list of citations mentioned in this paragraph.",
          "items": {
            "$ref": "#/$defs/Citation"
          }
        },
        "internal_references": {
          "type": "array",
          "description": "(OPTIONAL) Explicit list of internal references mentioned in this paragraph.",
          "items": {
            "$ref": "#/$defs/InternalReference"
          }
        }
      },
      "required": [
        "type",
        "text"
      ],
      "additionalProperties": false
    },
    "Figure": {
      "type": "object",
      "description": "A figure or image.",
      "properties": {
        "type": {
          "type": "string",
          "const": "Figure",
          "description": "The type of this document element."
        },
        "label": {
          "type": "string",
          "description": "Unique identifier/label for referencing (e.g., 'fig:flowchart')."
        },
        "source": {
          "type": "string",
          "description": "URL or path to the image file."
        },
        "caption": {
          "type": "string",
          "description": "(OPTIONAL) Caption describing the figure."
        },
        "alt_text": {
          "type": "string",
          "description": "(OPTIONAL) Alternative text for accessibility."
        }
      },
      "required": [
        "type",
        "label",
        "source"
      ],
      "additionalProperties": false
    },
    "Table": {
      "type": "object",
      "description": "A data table.",
      "properties": {
        "type": {
          "type": "string",
          "const": "Table",
          "description": "The type of this document element."
        },
        "label": {
          "type": "string",
          "description": "Unique identifier/label for referencing (e.g., 'tab:results')."
        },
        "caption": {
          "type": "string",
          "description": "(OPTIONAL) Caption describing the table."
        },
        "content": {
          "type": "array",
          "description": "Table data, represented as an array of rows, where each row is an array of cell strings.",
          "items": {
            "type": "array",
            "items": {
              "type": "string"
            }
          }
        },
        "header_row": {
          "type": "boolean",
          "description": "(OPTIONAL) Indicates if the first row in 'content' is a header row. Default: false",
          "default": false
        }
      },
      "required": [
        "type",
        "label",
        "content"
      ],
      "additionalProperties": false
    },
    "Bibliography": {
      "type": "object",
      "description": "The bibliography or list of references section.",
      "properties": {
        "type": {
          "type": "string",
          "const": "Bibliography",
          "description": "The type of this document element."
        },
        "header": {
          "type": "string",
          "description": "The section header (e.g., 'References', 'Bibliography')."
        },
        "entries": {
          "type": "array",
          "description": "List of bibliography entries.",
          "items": {
            "$ref": "#/$defs/BibliographyEntry"
          }
        }
      },
      "required": [
        "type",
        "header",
        "entries"
      ],
      "additionalProperties": false
    },
    "BibliographyEntry": {
      "type": "object",
      "description": "A single entry in the bibliography.",
      "properties": {
        "key": {
          "type": "string",
          "description": "Unique key used for citations (e.g., 'Knuth1974', '[1]')."
        },
        "formatted_entry": {
          "type": "string",
          "description": "The full bibliographic reference, formatted as text (e.g., APA, BibTeX style)."
        }
      },
      "required": [
        "key",
        "formatted_entry"
      ],
      "additionalProperties": false
    },
    "Citation": {
      "type": "object",
      "description": "An inline citation pointing to one or more bibliography entries.",
      "properties": {
        "cite_keys": {
          "type": "array",
          "description": "An array of bibliography keys being cited.",
          "items": {
            "type": "string"
          },
          "minItems": 1
        }
      },
      "required": [
        "cite_keys"
      ],
      "additionalProperties": false
    },
    "InternalReference": {
      "type": "object",
      "description": "An inline reference to another labeled part of the document (e.g., Section, Theorem, Figure).",
      "properties": {
        "target_identifier": {
          "type": "string",
          "description": "The unique 'label' of the document element being referenced (e.g., 'sec:intro', 'thm:main', 'fig:diagram')."
        }
      },
      "required": [
        "target_identifier"
      ],
      "additionalProperties": false
    }
  }
}

def proofGuidelines := "Please write the proof in a style suitable for formalization in the Lean Theorem Prover. Concretely, follow the following guidelines:\n\n### **Declarative over imperative**: focusing on what is true, not instructing the reader.\n  \n### **Explicit naming of quantities**: introducing objects with clear, reusable identifiers.\n\n###  State All Assumptions and Types Upfront\n\nA formal proof operates within a specific **context**. Clearly stating everything you're assuming at the beginning makes this context explicit.\n* **Instead of:** \"In this proof, $n$ is a natural number greater than 1.\"\n* **Do this:** \"Assume $n$ is a natural number and $n > 1$.\"\n\n\n###  Justify Every Step, Citing Its Premises\n\nEvery new conclusion must logically follow from previous statements. In an informal proof, we often combine steps. For formalization, it's better to make each logical leap a separate, justified statement.\n* **Instead of:** \"Since $p$ is the smallest prime factor of $n$, and $d$ divides $n$ with $d < p$, $d$ must be 1.\"\n* **Do this:** \"Let $p$ be the smallest prime factor of $n$. Assume $d$ is a divisor of $n$ and $d < p$. By the definition of a prime factor, any divisor of $n$ other than 1 must be greater than or equal to the smallest prime factor $p$. Since $d < p$, $d$ cannot be a prime factor. Since $d$ divides $n$, this leaves $d=1$.\"\n* In case something is true *by definition*, spell out by definition of what. For instance, numbers $p$ and $q$ could be equal because of the definition of $p$ or the definition of $q$.\n\n###  Decompose the Proof into Lemmas\n\nComplex proofs are rarely formalized in one go. Breaking a large proof into smaller, self-contained **lemmas** is standard practice and highly encouraged. This makes the proof modular, easier to read, and promotes reusability.\n\nBefore starting the main proof, state and prove the small, intermediate results you'll need.\n* **Example:** When proving that every integer $n > 1$ has a prime factor, you might first prove a lemma:\n\n    * **Lemma 1:** If an integer $k > 1$ is not prime, it has a divisor $d$ such that $1 < d < k$.\n\n    * **Main Proof:** \"Proceed by strong induction on $n$. ... If $n$ is not prime, by Lemma 1, there exists a divisor $d$ such that $1 < d < n$. By the induction hypothesis, $d$ has a prime factor, which is also a prime factor of $n$.\"\n\n###  Be Explicit with Case Analysis\n\nWhen a proof splits into cases, state the justification for the case split and ensure the cases are exhaustive.\n* **Instead of:** \"Now consider if $n$ is even or odd.\"\n* **Do this:** \"Every integer $n$ is either even or odd. We proceed by case analysis.\n\n    * **Case 1:** Assume $n$ is even. Then by definition, $n = 2k$ for some integer $k$. ...\n\n    * **Case 2:** Assume $n$ is odd. Then by definition, $n = 2k + 1$ for some integer $k$. ...\n\n    Since we have proven the result in all cases, the statement holds for all integers $n$.\"\n\n### Prefer Constructive Arguments\n\nWhen proving an existence statement (e.g., \"there exists an $x$ such that $P(x)$\"), a proof that provides the object $x$ (a \"witness\") is **constructive**. A proof that shows the non-existence of $x$ leads to a contradiction is **non-constructive**.\n\nWhile Lean can handle non-constructive proofs, constructive proofs are often more direct and simpler to formalize.\n* **Non-constructive:** \"Assume for contradiction that no such $x$ exists. ... This leads to a contradiction. Therefore, such an $x$ must exist.\"\n* **Constructive:** \"Let $x_0 = f(y)$. We now show that $P(x_0)$ holds. ... Thus, an $x$ satisfying $P(x)$ exists.\"\n\n### Be Fully Explicit About Assumptions and Quantifiers\n\nAvoid relying on \"it is clear that...\" or implicit assumptions. Instead:\n* State all hypotheses explicitly before using them.\n  \n* For example, instead of \"this holds because a < b\", write:\n  \"Since a<ba < b, and ff is monotonic by hypothesis hh, we have f(a)<f(b)f(a) < f(b).\"\n  \n\nIn Lean, every assumption must be named and passed to functions or lemmas.\n* * *\n\n###  Use Modular Lemmas and Definitions\n\nStructure proofs so that each step can, in principle, be factored into a lemma:\n* If a proof uses an idea more than once, define it as a named helper.\n  \n* Prefer referring to known lemmas (e.g., \"by the triangle inequality\") rather than rederiving facts.\n  \n\nIn Lean, this encourages reuse and better composability.\n* * *\n\n###  Avoid Ambiguity in Notation or Scope\n\nHuman readers disambiguate easily; Lean does not.\n* Clarify the scope of variables and the domains of quantification.\n  \n* Prefer “Let x∈X \\in X” over “Take x”.\n  \n\nIn Lean, `x : X` is always the form in contexts and proofs.\n* * *\n\n###  Avoid Pronouns and Natural Language Shortcuts\n\nExpressions like “this”, “that one”, or “the former” create ambiguity.\n* Instead of \"this function\", say \"the function ff\".\n  \n* Instead of \"it follows\", say \"it follows from hypothesis h1h_1 and lemma foofoo\".\n  \n* * *\n\n### Use Definitions When Needed\n\n* Instead of “the set of all xx such that ...”, say\n  “Let S:={x∈N∣P(x)}S := \\{ x \\in \\mathbb{N} \\mid P(x) \\}.”\n  \n### Define only ONE object per definition\n\n* Avoid a chain of definitions in a single statement, such as \"let $p(x)$ be the minimal polynomial of the field $F$ and let $a$ be its root\". Instead split into two or more definitions.\n* Do not include assertions about the object being defined as part of the definition. Instead make a separate assertion/lemma/theorem.\n\n### Avoid Overloaded Language\n\nMany words (e.g., “is trivial”, “clearly”, “obviously”) are informal and vague.\n* Instead of “the result is trivial”, say what the result is and *why* it follows directly.\n  \n\n### State the Goal Clearly at Each Step\n\nBreak long arguments into intermediate goals.\n* Use \"We aim to show that...\" or \"It suffices to prove...\" with precision.\n  \n###  Respect the Order of Dependencies\n\nOnly use objects after they are introduced.\n\n### Use Consistent Naming for Hypotheses and Objects\n\nYou can adopt Lean's naming conventions:\n* Use lowercase for objects (`x`, `n`, `f`)\n  \n* Prefix hypotheses (`h1`, `hf`, `hp`) consistently\n  \n\n### Minimize Appeals to Intuition or Visual Reasoning\n\nIf the step relies on a diagram or an appeal to intuition (e.g., “as can be seen from the graph”), wherever possible replace it with a precise statement or lemma.\n"

end LeanAide.Resources

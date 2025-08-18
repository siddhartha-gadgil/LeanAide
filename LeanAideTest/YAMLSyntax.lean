import LeanAide.YAML_syntaxCategory

/-- info: "apple" -/
#guard_msgs in
#eval yaml% "apple"

/-- info: {"key": "value"} -/
#guard_msgs in
#eval yaml% key : "value"

/-- info: {"obj": {"key": "value"}} -/
#guard_msgs in
#eval yaml% obj :
              key : "value"

/-- info: {"list": ["item1", "item2"]} -/
#guard_msgs in
#eval yaml% list:["item1", "item2"]

/-- info: {"list": ["item1", "item2"]} -/
#guard_msgs in
#eval yaml% list:
              - "item1"
              - "item2"

/--
info: {"obj2":
 {"subobj2":
  [{"subsubobj21": {"key21": "value21"}},
   {"subsubobj22": {"key22": "value22"}}],
  "list2": ["item21", "item22"]},
 "obj1":
 {"subobj1": {"key11": "val11"},
  "list1": ["item11", "item12"],
  "key2": "val2",
  "key1": "val1"}}
-/
#guard_msgs in
#eval yaml% obj1 :
              key1 : "val1"
              key2 : "val2"
              subobj1 :
                key11: "val11"
              list1 : ["item11","item12"]
            obj2:
             list2:
              - "item21"
              - "item22"
             subobj2:
              - subsubobj21 :
                  key21 : "value21"
              - subsubobj22 :
                  key22 : "value22"

--An example of a proof following the schema from PaperStructure--
/--
info: {"document":
 [{"type": "Theorem",
   "proof":
   {"type": "Proof",
    "proof_steps":
    [[{"type": "pattern_cases_statement",
       "proof_cases":
       [{"type": "pattern_case",
         "proof":
         {"type": "Proof",
          "proof_steps":
          [[{"variable_type": "integer",
             "variable_name": "k",
             "type": "let_statement",
             "statement": "k is an integer such that n = 4k"},
            {"type": "calculation",
             "calculation_sequence":
             ["n^2 = (4k)^2 = 16k^2", "16k^2 ≡ 0 (mod 4)"]},
            {"type": "conclude_statement", "claim": "n^2 ≡ 0 (mod 4)"}]],
          "claim_label": "thm:mod4-square"},
         "pattern": "0"},
        {"type": "pattern_case",
         "proof":
         {"type": "Proof",
          "proof_steps":
          [[{"variable_type": "integer",
             "variable_name": "k",
             "type": "let_statement",
             "statement": "k is an integer such that n = 4k + 1"},
            {"type": "calculation",
             "calculation_sequence":
             ["n^2 = (4k + 1)^2 = 16k^2 + 8k + 1",
              "16k^2 + 8k + 1 ≡ 1 (mod 4)"]},
            {"type": "conclude_statement", "claim": "n^2 ≡ 1 (mod 4)"}]],
          "claim_label": "thm:mod4-square"},
         "pattern": "1"},
        {"type": "pattern_case",
         "proof":
         {"type": "Proof",
          "proof_steps":
          [[{"variable_type": "integer",
             "variable_name": "k",
             "type": "let_statement",
             "statement": "k is an integer such that n = 4k + 2"},
            {"type": "calculation",
             "calculation_sequence":
             ["n^2 = (4k + 2)^2 = 16k^2 + 16k + 4",
              "16k^2 + 16k + 4 ≡ 0 (mod 4)"]},
            {"type": "conclude_statement", "claim": "n^2 ≡ 0 (mod 4)"}]],
          "claim_label": "thm:mod4-square"},
         "pattern": "2"},
        {"type": "pattern_case",
         "proof":
         {"type": "Proof",
          "proof_steps":
          [[{"variable_type": "integer",
             "variable_name": "k",
             "type": "let_statement",
             "statement": "k is an integer such that n = 4k + 3"},
            {"type": "calculation",
             "calculation_sequence":
             ["n^2 = (4k + 3)^2 = 16k^2 + 24k + 9",
              "16k^2 + 24k + 9 ≡ 1 (mod 4)"]},
            {"type": "conclude_statement", "claim": "n^2 ≡ 1 (mod 4)"}]],
          "claim_label": "thm:mod4-square"},
         "pattern": "3"}],
       "on": "n mod 4"},
      {"type": "conclude_statement", "claim": "n^2 mod 4 ∈ {0, 1}"}]],
    "claim_label": "thm:mod4-square"},
   "label": "thm:mod4-square",
   "header": "Theorem",
   "claim": "For any integer n, n^2 mod 4 ∈ {0, 1}"}]}
-/
#guard_msgs in
#eval yaml% document:
  - type: "Theorem"
    header: "Theorem"
    label: "thm:mod4-square"
    claim: "For any integer n, n^2 mod 4 ∈ {0, 1}"
    proof:
      type: "Proof"
      claim_label: "thm:mod4-square"
      proof_steps:
        - - type: "pattern_cases_statement"
            on: "n mod 4"
            proof_cases:
              - type: "pattern_case"
                pattern: "0"
                proof:
                  type: "Proof"
                  claim_label: "thm:mod4-square"
                  proof_steps:
                    - - type: "let_statement"
                        variable_name: "k"
                        variable_type: "integer"
                        statement: "k is an integer such that n = 4k"
                      - type: "calculation"
                        calculation_sequence:
                          - "n^2 = (4k)^2 = 16k^2"
                          - "16k^2 ≡ 0 (mod 4)"
                      - type: "conclude_statement"
                        claim: "n^2 ≡ 0 (mod 4)"
              - type: "pattern_case"
                pattern: "1"
                proof:
                  type: "Proof"
                  claim_label: "thm:mod4-square"
                  proof_steps:
                    - - type: "let_statement"
                        variable_name: "k"
                        variable_type: "integer"
                        statement: "k is an integer such that n = 4k + 1"
                      - type: "calculation"
                        calculation_sequence:
                          - "n^2 = (4k + 1)^2 = 16k^2 + 8k + 1"
                          - "16k^2 + 8k + 1 ≡ 1 (mod 4)"
                      - type: "conclude_statement"
                        claim: "n^2 ≡ 1 (mod 4)"
              - type: "pattern_case"
                pattern: "2"
                proof:
                  type: "Proof"
                  claim_label: "thm:mod4-square"
                  proof_steps:
                    - - type: "let_statement"
                        variable_name: "k"
                        variable_type: "integer"
                        statement: "k is an integer such that n = 4k + 2"
                      - type: "calculation"
                        calculation_sequence:
                          - "n^2 = (4k + 2)^2 = 16k^2 + 16k + 4"
                          - "16k^2 + 16k + 4 ≡ 0 (mod 4)"
                      - type: "conclude_statement"
                        claim: "n^2 ≡ 0 (mod 4)"
              - type: "pattern_case"
                pattern: "3"
                proof:
                  type: "Proof"
                  claim_label: "thm:mod4-square"
                  proof_steps:
                    - - type: "let_statement"
                        variable_name: "k"
                        variable_type: "integer"
                        statement: "k is an integer such that n = 4k + 3"
                      - type: "calculation"
                        calculation_sequence:
                          - "n^2 = (4k + 3)^2 = 16k^2 + 24k + 9"
                          - "16k^2 + 24k + 9 ≡ 1 (mod 4)"
                      - type: "conclude_statement"
                        claim: "n^2 ≡ 1 (mod 4)"
          - type: "conclude_statement"
            claim: "n^2 mod 4 ∈ {0, 1}"

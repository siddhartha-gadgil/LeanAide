import LeanAideCore.Aides
import Lean.Data.Json

open LeanAide
/--
info: {"theorem-proof":
 {"theorem": {"val": {"statement": "This is a Theorem"}}, "proof": "magic"}}
-/
#guard_msgs in
#eval readableJson (json% {"type": "theorem-proof",
  "theorem": {"type": "val","statement":"This is a Theorem"},
  "proof" : "magic"
})

/--
info: {"document":
 [{"Theorem":
   {"proof":
    {"Proof":
     {"proof_steps":
      [[{"pattern_cases_statement":
         {"proof_cases":
          [{"pattern_case":
            {"proof":
             {"Proof":
              {"proof_steps":
               [[{"let_statement":
                  {"variable_type": "integer",
                   "variable_name": "k",
                   "statement": "k is an integer such that n = 4k"}},
                 {"calculation":
                  {"calculation_sequence":
                   ["n^2 = (4k)^2 = 16k^2", "16k^2 ≡ 0 (mod 4)"]}},
                 {"conclude_statement": {"claim": "n^2 ≡ 0 (mod 4)"}}]],
               "claim_label": "thm:mod4-square"}},
             "pattern": "0"}},
           {"pattern_case":
            {"proof":
             {"Proof":
              {"proof_steps":
               [[{"let_statement":
                  {"variable_type": "integer",
                   "variable_name": "k",
                   "statement": "k is an integer such that n = 4k + 1"}},
                 {"calculation":
                  {"calculation_sequence":
                   ["n^2 = (4k + 1)^2 = 16k^2 + 8k + 1",
                    "16k^2 + 8k + 1 ≡ 1 (mod 4)"]}},
                 {"conclude_statement": {"claim": "n^2 ≡ 1 (mod 4)"}}]],
               "claim_label": "thm:mod4-square"}},
             "pattern": "1"}},
           {"pattern_case":
            {"proof":
             {"Proof":
              {"proof_steps":
               [[{"let_statement":
                  {"variable_type": "integer",
                   "variable_name": "k",
                   "statement": "k is an integer such that n = 4k + 2"}},
                 {"calculation":
                  {"calculation_sequence":
                   ["n^2 = (4k + 2)^2 = 16k^2 + 16k + 4",
                    "16k^2 + 16k + 4 ≡ 0 (mod 4)"]}},
                 {"conclude_statement": {"claim": "n^2 ≡ 0 (mod 4)"}}]],
               "claim_label": "thm:mod4-square"}},
             "pattern": "2"}},
           {"pattern_case":
            {"proof":
             {"Proof":
              {"proof_steps":
               [[{"let_statement":
                  {"variable_type": "integer",
                   "variable_name": "k",
                   "statement": "k is an integer such that n = 4k + 3"}},
                 {"calculation":
                  {"calculation_sequence":
                   ["n^2 = (4k + 3)^2 = 16k^2 + 24k + 9",
                    "16k^2 + 24k + 9 ≡ 1 (mod 4)"]}},
                 {"conclude_statement": {"claim": "n^2 ≡ 1 (mod 4)"}}]],
               "claim_label": "thm:mod4-square"}},
             "pattern": "3"}}],
          "on": "n mod 4"}},
        {"conclude_statement": {"claim": "n^2 mod 4 ∈ {0, 1}"}}]],
      "claim_label": "thm:mod4-square"}},
    "label": "thm:mod4-square",
    "header": "Theorem",
    "claim": "For any integer n, n^2 mod 4 ∈ {0, 1}"}}]}
-/
#guard_msgs in
#eval readableJson (json% {"document":
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
   "claim": "For any integer n, n^2 mod 4 ∈ {0, 1}"}]})

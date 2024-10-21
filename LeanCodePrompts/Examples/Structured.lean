import LeanCodePrompts.ChatClient

namespace Structured

def server := ChatServer.openAI

def eg1 := server.structuredProofFromStatement "There are infinitely many odd numbers."

/-
#[{"math_document":
 [{"theorem":
   {"proved": true,
    "proof":
    [{"contradiction":
      {"proof":
       [{"let":
         {"variable": "O",
          "value": "{o_1, o_2, \\ldots, o_n}",
          "kind": "set of all odd numbers"}},
        {"assert":
         {"deductions":
          [{"deduction":
            {"in_context": true, "deduced_from": "definition of odd numbers"}}],
          "claim":
          "Every odd number is of the form 2k + 1 for some integer k."}},
        {"let":
         {"variable": "m",
          "value": "2 \\cdot \\max(o_1, o_2, \\ldots, o_n) + 3",
          "properties": "greater than any element in O"}},
        {"assert":
         {"proof_method": "can be expressed in the form 2k + 1",
          "deductions":
          [{"deduction":
            {"instantiations":
             [{"instantiation": "k = \\max(o_1, o_2, \\ldots, o_n) + 1"}],
             "in_context": true,
             "deduced_from": "definition of odd numbers"}}],
          "claim": "m is an odd number."}},
        {"assert": {"claim": "m is not in the set O."}},
        {"assert":
         {"claim":
          "There is a contradiction in the assumption that O contains all odd numbers."}}],
       "assumption": "There are only finitely many odd numbers."}},
     {"conclude": {"claim": "There are infinitely many odd numbers."}}],
    "hypothesis": [],
    "conclusion": "There are infinitely many odd numbers."}}]}]

-/
-- #eval eg1

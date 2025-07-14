import LeanAide

open LeanAide Meta CodeGenerator

namespace LeanAideTest.FVarError

def eg := json% {
    "document": [
         {
            "type": "Theorem",
            "label": "thm:cyclic_group_abelian",
            "header": "Theorem",
            "hypothesis": [
                {
                    "type": "assume_statement",
                    "assumption": "G : Type _"
                },
                {
                    "type": "assume_statement",
                    "assumption": "[inst : Group G]"
                },
                {
                    "type": "assume_statement",
                    "assumption": "∃ (g₀ : G), ∀ x : G, ∃ k : ℤ, x = g₀^k"
                }
            ],
            "claim": "Every cyclic group is Abelian."
        },
        {
            "type": "Proof",
            "claim_label": "thm:cyclic_group_abelian",
            "proof_steps": []
        }
    ]
}

universe u_1


-- #guard_msgs in
#codegen eg

example : ∀ {G : Type u_1} [inst : Group G], ∃ (g₀ : G), ∀ (x : G), ∃ (k : ℤ), x = g₀ ^ k := by
  first
  | (simp?; done)
  |
  intro G inst
  sorry

-- #eval Translator.translateToPropStrict "Every cyclic group is Abelian." {}
end LeanAideTest.FVarError

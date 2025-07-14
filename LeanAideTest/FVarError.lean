import LeanAide

open LeanAide Meta CodeGenerator

namespace LeanAideTest.LeanInOutput

def eg := json% {
    "document": [
        {
            "type": "Theorem",
            "label": "lem:pow_add",
            "header": "Lemma",
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
                    "type": "let_statement",
                    "variable_name": "g",
                    "variable_type": "G"
                },
                {
                    "type": "let_statement",
                    "variable_name": "m",
                    "variable_type": "ℤ"
                },
                {
                    "type": "let_statement",
                    "variable_name": "n",
                    "variable_type": "ℤ"
                }
            ],
            "claim": "g^m * g^n = g^{m + n}"
        },
        {
            "type": "Proof",
            "claim_label": "lem:pow_add",
            "proof_steps": []
        },
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
                    "type": "some_statement",
                    "variable_name": "hcyc",
                    "statement": "∃ (g₀ : G), ∀ x : G, ∃ k : ℤ, x = g₀^k"
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

#codegen eg

example : ∀ {G : Type u_1} [inst : Group G] (g : G) (m n : ℤ),
  (∃ (g₀ : G), ∀ (x : G), ∃ (k : ℤ), x = g₀ ^ k) →
    (∃ (g₀ : G), ∀ (x : G), ∃ (k : ℤ), x = g₀ ^ k) → ∃ (g₀ : G), ∀ (x : G), ∃ (k : ℤ), x = g₀ ^ k := by
  simp only [imp_self, implies_true]
end LeanAideTest.LeanInOutput

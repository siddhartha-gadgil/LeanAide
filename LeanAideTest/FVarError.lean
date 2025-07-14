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

/--
info: codegen: trying LeanAide.documentCode for key document
---
info: codegen: trying LeanAide.theoremCode for key theorem
---
info: codegen: trying LeanAide.assumeCode for key assume_statement
---
info: codegen: trying LeanAide.assumeCode for key assume_statement
---
info: codegen: trying LeanAide.someCode for key some_statement
---
info: codegen: trying LeanAide.assertionCode for key assert_statement
---
info: codegen: trying LeanAide.assumeCode for key assume_statement
---
info: codegen: trying LeanAide.assumeCode for key assume_statement
---
info: codegen: trying LeanAide.someCode for key some_statement
---
info: codegen: trying LeanAide.assertionCode for key assert_statement
---
info: All theorems : [thm:cyclic_group_abelian]
---
info: codegen: trying LeanAide.proofCode for key proof
---
info: codegen: trying LeanAide.assumeCode for key assume_statement
---
info: codegen: trying LeanAide.assumeCode for key assume_statement
---
info: codegen: trying LeanAide.someCode for key some_statement
---
info: codegen: trying LeanAide.assertionCode for key assert_statement
---
info: Try this: ⏎
  def cyclic_group_is_abelian.prop : Prop :=
    ∀ {G : Type u_1} [inst : Group G], (∃ (g₀ : G), ∀ (x : G), ∃ (k : ℤ), x = g₀ ^ k) → ∀ (a b : G), a * b = b * a
  def deferred.cyclic_group_is_abelian [assume_cyclic_group_is_abelian : Fact cyclic_group_is_abelian.prop] :
      cyclic_group_is_abelian.prop :=
    assume_cyclic_group_is_abelian.elim
  theorem cyclic_group_is_abelian :
      ∀ {G : Type u_1} [inst : Group G], (∃ (g₀ : G), ∀ (x : G), ∃ (k : ℤ), x = g₀ ^ k) → ∀ (a b : G), a * b = b * a :=
    by
    intro G inst_14157295161945824867 a_1008755775771949303 a b
    trace
      "Automation Tactics first\n  | (simp?; done)\n  | hammer {aesopPremises := 5, autoPremises := 0} for goal: a * b = b * a"
    obtain ⟨w, h⟩ := a_1008755775771949303
    sorry
    trace
      "Finished Automation Tactics first\n  | (simp?; done)\n  | hammer {aesopPremises := 5, autoPremises := 0} for goal: a * b = b * a"
-/
#guard_msgs in
#codegen eg

example : ∀ {G : Type u_1} [inst : Group G], ∃ (g₀ : G), ∀ (x : G), ∃ (k : ℤ), x = g₀ ^ k := by
  first
  | (simp?; done)
  |
  intro G inst
  sorry

-- #eval Translator.translateToPropStrict "Every cyclic group is Abelian."
end LeanAideTest.FVarError

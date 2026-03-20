import Mathlib
import LeanAideCore.LLMTactic



example : 2+2 = 4 := by
  llm? -- Try this: [apply] decide
  sorry

theorem commutative (P Q : Prop) : P ∧ Q → Q ∧ P := by
  llm? --Try this:
              --[apply]  intro h
              --exact And.symm h
  sorry

/-`llm?` tactic is used to find a proof in every lemma of the following theorem. It succeeds to proof everything except the final two lemmas-/
noncomputable def is_abelian_of_forall_mul_pow_two_eq_pow_two_mul_pow_two :
      {G : Type u_1} →
        [inst : Group G] →
          (∀ (a b : G), (a * b) ^ (2 : ℕ) = a ^ (2 : ℕ) * b ^ (2 : ℕ)) → CommGroup G :=
    by
    intro G inst a_180468121275325397
    have assert_11371057909598991355 : ∀ (a b : G), a * b * a * b = a * a * b * b := by
          intro a b
          have h := a_180468121275325397 a b
          simpa [pow_two, mul_assoc] using h --llm?
    have assert_12084550143141261290 : ∀ (a b : G), a * b * (a * b) = a * a * (b * b) := by
          intro a b
          have h := a_180468121275325397 a b
          simpa [pow_two, mul_assoc] using h --llm?
    have assert_3045592514326845003 :
      ∀ (a b : G), a⁻¹ * (a * b * (a * b)) = a⁻¹ * (a * a * (b * b)) := by
        intro a b
        simpa using congrArg (fun t => a⁻¹ * t) (assert_12084550143141261290 a b) --llm?
    have assert_2584691247916677600 : ∀ (a b : G), a⁻¹ * a * b * a * b = a⁻¹ * a * a * b * b := by
            intro a b
            calc
              a⁻¹ * a * b * a * b = (((a⁻¹ * a) * b) * a) * b := by simp [mul_assoc]
              _ = ((a⁻¹ * a) * b) * (a * b) := by simp [mul_assoc]
              _ = (a⁻¹ * (a * b)) * (a * b) := by simpa [mul_assoc]
              _ = a⁻¹ * (a * b * (a * b)) := by simp [mul_assoc]
              _ = a⁻¹ * (a * a * (b * b)) := (assert_3045592514326845003 a b)
              _ = (a⁻¹ * (a * a)) * (b * b) := by simp [mul_assoc]
              _ = ((a⁻¹ * (a * a)) * b) * b := by simp [mul_assoc]
              _ = (((a⁻¹ * a) * a) * b) * b := by simpa [mul_assoc]
              _ = a⁻¹ * a * a * b * b := by simp [mul_assoc] --llm?

    have assert_4512232750963544230 : ∀ (a b : G), b * a * b = a * b * b := by
        intro a b
        simpa [mul_assoc] using assert_2584691247916677600 a b  --llm?
    have assert_7951337427665103720 : ∀ (a b : G), b * a * b * b⁻¹ = a * b * b * b⁻¹ := by
        intro a b
        have h := assert_4512232750963544230 a b
        calc
          b * a * b * b⁻¹ = (b * a * b) * b⁻¹ := by simp [mul_assoc]
          _ = (a * b * b) * b⁻¹ := by simpa [h]
          _ = a * b * b * b⁻¹ := by simp [mul_assoc] --llm?
    have assert_12054441707386195591 : ∀ (a b : G), b * a * (b * b⁻¹) = a * b * (b * b⁻¹) := by
          intro a b
          simpa [mul_assoc] using assert_7951337427665103720 a b --llm?
    have assert_16921761843838546612 : ∀ (a b : G), b * a = a * b := by
      -- intro a b
      -- simpa [mul_right_inv, mul_one] using assert_12054441707386195591 a b
      -- llm? gives above proof which has errors
      simp_all
    have : CommGroup G := by
      -- classical
      --   haveI := inst
      --   refine { (inferInstance : Group G) with mul_comm := ?_ }
      --   intro a b
      --   have h1 : a * b * (a * b) = a * a * (b * b) := by
      --     simpa [pow_two, mul_assoc] using a_180468121275325397 a b
      --   have h2' : b * (a * b) = a * (b * b) :=
      --     by
      --     have h' := congrArg (fun x => a⁻¹ * x) h1
      --     simpa [mul_assoc] using h'
      --   have h2 : b * a * b = a * b * b := by simpa [mul_assoc] using h2'
      --   have h3 := congrArg (fun x => x * b⁻¹) h2
      --   simpa [mul_assoc] using h3
      --   llm? gives above proof which has errors
      constructor
      grind only [#2923]
    assumption

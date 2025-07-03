import LeanAide
import Lean
import Qq

open LeanAide Lean Meta Elab Parser Tactic
set_option linter.unusedTactic false

open Nat

open Qq

def egTheorem : Json :=
  json% {
    "type": "theorem",
    "name": "egTheorem",
    "claim_label": "egTheorem",
    "claim": "There are infinitely many odd numbers.",
    "proof": {
      "proof_steps": []
    }
  }

-- #codegen {
--     "type": "theorem",
--     "name": "egTheorem",
--     "claim_label": "egTheorem",
--     "claim": "There are infinitely many odd numbers.",
--     "proof": {
--       "proof_steps": []
--     }
--   }

  theorem group.inv_eq_one_of_eq_one : ∀ {G : Type u} [inst : Group G] {a : G}, a = 1 → a⁻¹ = 1 :=
    by
    intro G inst_10173403757143075236 a h₁
    have assert_1795224800169208544 : ∀ [inst : Group G] (a : G), a = 1 → a⁻¹ = 1⁻¹ :=
      by
      trace
        "Automation Tactics hammer [Eq.subst] for goal: ∀ [inst : Group G] (a : G), a = 1 → a⁻¹ = 1⁻¹"
      intro inst a_2 a_3
      subst h₁ a_3
      simp_all only [inv_one]
      trace
        "Finished Automation Tactics hammer [Eq.subst] for goal: ∀ [inst : Group G] (a : G), a = 1 → a⁻¹ = 1⁻¹"
    have assert_2553174354512223270 : ∀ [inst : Group G] {a : G}, a = 1 → (1 : G)⁻¹ = 1 := -- correction
      by
      trace "Automation Tactics hammer [] for goal: ∀ [inst : Group G] {a : G}, a = 1 → 1⁻¹ = 1"
      intro inst a_2 a_3
      subst h₁ a_3
      simp_all only [inv_one, implies_true]
      -- sorry
      trace
        "Finished Automation Tactics hammer [] for goal: ∀ [inst : Group G] {a : G}, a = 1 → 1⁻¹ = 1"
    have assert_14152979867489898528 : ∀ [inst : Group G] {a : G}, a = 1 → a⁻¹ = 1 :=
      by
      trace "Automation Tactics hammer [] for goal: ∀ [inst : Group G] {a : G}, a = 1 → a⁻¹ = 1"
      intro inst a_2 a_3
      subst a_3 h₁
      simp -- sorry -- correction
      trace
        "Finished Automation Tactics hammer [] for goal: ∀ [inst : Group G] {a : G}, a = 1 → a⁻¹ = 1"
    have : a⁻¹ = 1 := by
      trace "Automation Tactics hammer [] for goal: a⁻¹ = 1"
      subst h₁
      simp_all only [implies_true, inv_one, forall_eq]
      -- sorry
      trace "Finished Automation Tactics hammer [] for goal: a⁻¹ = 1"
    assumption
  theorem inv_eq_of_eq_one : ∀ {G : Type u} [inst : Group G] {e : G}, e = 1 → e⁻¹ = e :=
    by
    intro G inst_2343502792650069773 e h₂
    have assert_13412815512804423344 : ∀ [inst : Group G] {e : G}, e = 1 → e⁻¹ = 1 :=
      by
      trace "Automation Tactics hammer [] for goal: ∀ [inst : Group G] {e : G}, e = 1 → e⁻¹ = 1"
      intro inst e_2 a
      subst a h₂
      simp_all only [inv_one]
      trace
        "Finished Automation Tactics hammer [] for goal: ∀ [inst : Group G] {e : G}, e = 1 → e⁻¹ = 1"
    have assert_15068206506407136462 : ∀ [inst : Group G] {e : G}, e = 1 → 1 = e :=
      by
      trace "Automation Tactics hammer [] for goal: ∀ [inst : Group G] {e : G}, e = 1 → 1 = e"
      intro inst e_2 a
      subst h₂ a
      simp_all only [inv_one, implies_true]
      trace
        "Finished Automation Tactics hammer [] for goal: ∀ [inst : Group G] {e : G}, e = 1 → 1 = e"
    have assert_7201253128521190897 : ∀ [inst : Group G] {e : G}, e = 1 → e⁻¹ = e :=
      by
      trace "Automation Tactics hammer [] for goal: ∀ [inst : Group G] {e : G}, e = 1 → e⁻¹ = e"
      intro inst e_2 a
      subst a h₂
      simp_all only [inv_one, implies_true]
      trace
        "Finished Automation Tactics hammer [] for goal: ∀ [inst : Group G] {e : G}, e = 1 → e⁻¹ = e"
    have : e⁻¹ = e := by
      trace "Automation Tactics hammer [] for goal: e⁻¹ = e"
      subst h₂
      simp_all only [implies_true, inv_one]
      -- sorry
      trace "Finished Automation Tactics hammer [] for goal: e⁻¹ = e"
    assumption


def egTheorem' : Json :=
  json% {
    "type": "theorem",
    "name": "egTheorem",
    "label": "egTheorem",
    "claim": "There are infinitely many odd numbers."
  }


def egTheorem'' : Json :=
  json% {
    "type": "theorem",
    "name": "egTheorem",
    "claim_label": "egTheorem",
    "claim": "There are infinitely many odd numbers.",
    "proof": {
      "proof_steps": []
    }
  }

def egLet : Json :=
  json% {
    "type" : "let_statement",
    "variable_name": "n",
    "variable_type": "natural number",
    "properties": "n is odd and n > 0"
  }

def egTheorem₀ : Json :=
  json% {
    "type": "theorem",
    "name": "egTheorem",
    "claim_label": "egTheorem",
    "claim": "Every natural number is less than its successor.",
    "proof": {
      "proof_steps": []
    }
  }

def egErrorProof : Json :=
  json% {"document" :
    [{
    "type": "theorem",
    "name": "egTheorem",
    "label": "egTheorem",
    "claim": "There are infinitely many odd numbers."
  },
      {"type": "proof",
    "claim_label": "egErrorProof",
    "proof_steps": []}]

  }

open Codegen

def showStx (source: Json) (cat: Name := ``commandSeq) (translator: CodeGenerator := {})(goal? : Option (MVarId) := none)
   :
    TranslateM (Format) := do
    match ← getCode translator  goal? cat source with
    | none => do
      return "No code generated"
    | some stx => do
      PrettyPrinter.ppCategory cat stx

#eval showStx egErrorProof

-- #eval showStx egTheorem₀

-- #eval showStx egTheorem

-- #eval showStx egTheorem''



-- #eval egTheorem


-- #eval showStx egLet

def egView : MetaM Format := do
  let .ok js := runParserCategory (← getEnv) `json egTheorem.pretty | throwError
    "Failed to parse egLet as JSON"
  PrettyPrinter.ppCategory `json js

#eval egView

def egTacs : TermElabM <|  Format := do
  let goal := q(∀ (N : ℤ), N % 10 = 0 ∨ N % 10 = 5 → 5 ∣ N)
  let autoTac ← `(tactic| aesop?)
  let tacs ← runTacticsAndGetTryThisI goal #[autoTac]
  PrettyPrinter.ppCategory ``tacticSeq <| ← `(tacticSeq|$tacs*)


#eval egTacs

/--
info: Try this:
  intro a
  simp_all only [EuclideanDomain.mod_eq_zero]
  cases a with
  | inl h => sorry
  | inr h_1 => sorry
---
warning: aesop: failed to prove the goal after exhaustive search.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example: ∀ (N : ℤ), N % 10 = 0 ∨ N % 10 = 5 → 5 ∣ N := by
  intro
  aesop?
  · sorry
  · sorry

#eval (ChatServer.default).fullStatement "p ∤ m!"

#eval Translator.translateToPropStrict "p ∤ m!" {}

example : 5 ∣ 10 := by
  hammer

theorem nat_lt_succ : ∀ (n : ℕ), n < succ n := by
    intro n
    trace "Automation tactics found for n < n.succ, closing goal"
    simp_all only [succ_eq_add_one, lt_add_iff_pos_right, lt_one_iff, pos_of_gt]

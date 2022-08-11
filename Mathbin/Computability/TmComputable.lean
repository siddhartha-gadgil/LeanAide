/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/
import Mathbin.Computability.Encoding
import Mathbin.Computability.TuringMachine
import Mathbin.Data.Polynomial.Basic
import Mathbin.Data.Polynomial.Eval

/-!
# Computable functions

This file contains the definition of a Turing machine with some finiteness conditions
(bundling the definition of TM2 in turing_machine.lean), a definition of when a TM gives a certain
output (in a certain time), and the definition of computability (in polytime or any time function)
of a function between two types that have an encoding (as in encoding.lean).

## Main theorems

- `id_computable_in_poly_time` : a TM + a proof it computes the identity on a type in polytime.
- `id_computable`              : a TM + a proof it computes the identity on a type.

## Implementation notes

To count the execution time of a Turing machine, we have decided to count the number of times the
`step` function is used. Each step executes a statement (of type stmt); this is a function, and
generally contains multiple "fundamental" steps (pushing, popping, so on). However, as functions
only contain a finite number of executions and each one is executed at most once, this execution
time is up to multiplication by a constant the amount of fundamental steps.
-/


open Computability

namespace Turing

/-- A bundled TM2 (an equivalent of the classical Turing machine, defined starting from
the namespace `turing.TM2` in `turing_machine.lean`), with an input and output stack,
 a main function, an initial state and some finiteness guarantees. -/
structure FinTm2 where
  {k : Type}
  [kDecidableEq : DecidableEq K]
  [kFin : Fintype K]
  -- index type of stacks
  (k₀ k₁ : K)
  -- input and output stack
  Γ : K → Type
  -- type of stack elements
  Λ : Type
  main : Λ
  [ΛFin : Fintype Λ]
  -- type of function labels
  σ : Type
  initialState : σ
  -- type of states of the machine
  [σFin : Fintype σ]
  [Γk₀Fin : Fintype (Γ k₀)]
  m : Λ → Turing.TM2.Stmt Γ Λ σ

-- the program itself, i.e. one function for every function label
namespace FinTm2

section

variable (tm : FinTm2)

instance : DecidableEq tm.k :=
  tm.kDecidableEq

instance : Inhabited tm.σ :=
  ⟨tm.initialState⟩

/-- The type of statements (functions) corresponding to this TM. -/
def Stmt : Type :=
  Turing.TM2.Stmt tm.Γ tm.Λ tm.σ deriving Inhabited

/-- The type of configurations (functions) corresponding to this TM. -/
def Cfg : Type :=
  Turing.TM2.Cfg tm.Γ tm.Λ tm.σ

instance inhabitedCfg : Inhabited (Cfg tm) :=
  Turing.TM2.Cfg.inhabited _ _ _

/-- The step function corresponding to this TM. -/
@[simp]
def step : tm.Cfg → Option tm.Cfg :=
  Turing.TM2.step tm.m

end

end FinTm2

/-- The initial configuration corresponding to a list in the input alphabet. -/
def initList (tm : FinTm2) (s : List (tm.Γ tm.k₀)) : tm.Cfg where
  l := Option.some tm.main
  var := tm.initialState
  stk := fun k =>
    @dite (List (tm.Γ k)) (k = tm.k₀) (tm.kDecidableEq k tm.k₀)
      (fun h => by
        rw [h]
        exact s)
      fun _ => []

/-- The final configuration corresponding to a list in the output alphabet. -/
def haltList (tm : FinTm2) (s : List (tm.Γ tm.k₁)) : tm.Cfg where
  l := Option.none
  var := tm.initialState
  stk := fun k =>
    @dite (List (tm.Γ k)) (k = tm.k₁) (tm.kDecidableEq k tm.k₁)
      (fun h => by
        rw [h]
        exact s)
      fun _ => []

/-- A "proof" of the fact that f eventually reaches b when repeatedly evaluated on a,
remembering the number of steps it takes. -/
structure EvalsTo {σ : Type _} (f : σ → Option σ) (a : σ) (b : Option σ) where
  steps : ℕ
  evals_in_steps : (flip bind f^[steps]) a = b

/-- A "proof" of the fact that `f` eventually reaches `b` in at most `m` steps when repeatedly
evaluated on `a`, remembering the number of steps it takes. -/
-- note: this cannot currently be used in `calc`, as the last two arguments must be `a` and `b`.
-- If this is desired, this argument order can be changed, but this spelling is I think the most
-- natural, so there is a trade-off that needs to be made here. A notation can get around this.
structure EvalsToInTime {σ : Type _} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) extends EvalsTo f a b where
  steps_le_m : steps ≤ m

/-- Reflexivity of `evals_to` in 0 steps. -/
@[refl]
def EvalsTo.refl {σ : Type _} (f : σ → Option σ) (a : σ) : EvalsTo f a a :=
  ⟨0, rfl⟩

/-- Transitivity of `evals_to` in the sum of the numbers of steps. -/
@[trans]
def EvalsTo.trans {σ : Type _} (f : σ → Option σ) (a : σ) (b : σ) (c : Option σ) (h₁ : EvalsTo f a b)
    (h₂ : EvalsTo f b c) : EvalsTo f a c :=
  ⟨h₂.steps + h₁.steps, by
    rw [Function.iterate_add_apply, h₁.evals_in_steps, h₂.evals_in_steps]⟩

/-- Reflexivity of `evals_to_in_time` in 0 steps. -/
@[refl]
def EvalsToInTime.refl {σ : Type _} (f : σ → Option σ) (a : σ) : EvalsToInTime f a a 0 :=
  ⟨EvalsTo.refl f a, le_reflₓ 0⟩

/-- Transitivity of `evals_to_in_time` in the sum of the numbers of steps. -/
@[trans]
def EvalsToInTime.trans {σ : Type _} (f : σ → Option σ) (m₁ : ℕ) (m₂ : ℕ) (a : σ) (b : σ) (c : Option σ)
    (h₁ : EvalsToInTime f a b m₁) (h₂ : EvalsToInTime f b c m₂) : EvalsToInTime f a c (m₂ + m₁) :=
  ⟨EvalsTo.trans f a b c h₁.toEvalsTo h₂.toEvalsTo, add_le_add h₂.steps_le_m h₁.steps_le_m⟩

/-- A proof of tm outputting l' when given l. -/
def Tm2Outputs (tm : FinTm2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) :=
  EvalsTo tm.step (initList tm l) ((Option.map (haltList tm)) l')

/-- A proof of tm outputting l' when given l in at most m steps. -/
def Tm2OutputsInTime (tm : FinTm2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) (m : ℕ) :=
  EvalsToInTime tm.step (initList tm l) ((Option.map (haltList tm)) l') m

/-- The forgetful map, forgetting the upper bound on the number of steps. -/
def Tm2OutputsInTime.toTm2Outputs {tm : FinTm2} {l : List (tm.Γ tm.k₀)} {l' : Option (List (tm.Γ tm.k₁))} {m : ℕ}
    (h : Tm2OutputsInTime tm l l' m) : Tm2Outputs tm l l' :=
  h.toEvalsTo

/-- A Turing machine with input alphabet equivalent to Γ₀ and output alphabet equivalent to Γ₁. -/
structure Tm2ComputableAux (Γ₀ Γ₁ : Type) where
  tm : FinTm2
  inputAlphabet : tm.Γ tm.k₀ ≃ Γ₀
  outputAlphabet : tm.Γ tm.k₁ ≃ Γ₁

/-- A Turing machine + a proof it outputs f. -/
structure Tm2Computable {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) (f : α → β) extends
  Tm2ComputableAux ea.Γ eb.Γ where
  outputsFun :
    ∀ a,
      Tm2Outputs tm (List.map input_alphabet.invFun (ea.encode a))
        (Option.some ((List.map output_alphabet.invFun) (eb.encode (f a))))

/-- A Turing machine + a time function + a proof it outputs f in at most time(len(input)) steps. -/
structure Tm2ComputableInTime {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) (f : α → β) extends
  Tm2ComputableAux ea.Γ eb.Γ where
  time : ℕ → ℕ
  outputsFun :
    ∀ a,
      Tm2OutputsInTime tm (List.map input_alphabet.invFun (ea.encode a))
        (Option.some ((List.map output_alphabet.invFun) (eb.encode (f a)))) (time (ea.encode a).length)

/-- A Turing machine + a polynomial time function + a proof it outputs f in at most time(len(input))
steps. -/
structure Tm2ComputableInPolyTime {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) (f : α → β) extends
  Tm2ComputableAux ea.Γ eb.Γ where
  time : Polynomial ℕ
  outputsFun :
    ∀ a,
      Tm2OutputsInTime tm (List.map input_alphabet.invFun (ea.encode a))
        (Option.some ((List.map output_alphabet.invFun) (eb.encode (f a)))) (time.eval (ea.encode a).length)

/-- A forgetful map, forgetting the time bound on the number of steps. -/
def Tm2ComputableInTime.toTm2Computable {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β} {f : α → β}
    (h : Tm2ComputableInTime ea eb f) : Tm2Computable ea eb f :=
  ⟨h.toTm2ComputableAux, fun a => Tm2OutputsInTime.toTm2Outputs (h.outputsFun a)⟩

/-- A forgetful map, forgetting that the time function is polynomial. -/
def Tm2ComputableInPolyTime.toTm2ComputableInTime {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β} {f : α → β}
    (h : Tm2ComputableInPolyTime ea eb f) : Tm2ComputableInTime ea eb f :=
  ⟨h.toTm2ComputableAux, fun n => h.time.eval n, h.outputsFun⟩

open Turing.TM2.Stmt

/-- A Turing machine computing the identity on α. -/
def idComputer {α : Type} (ea : FinEncoding α) : FinTm2 where
  k := Unit
  k₀ := ⟨⟩
  k₁ := ⟨⟩
  Γ := fun _ => ea.Γ
  Λ := Unit
  main := ⟨⟩
  σ := Unit
  initialState := ⟨⟩
  Γk₀Fin := ea.ΓFin
  m := fun _ => halt

instance inhabitedFinTm2 : Inhabited FinTm2 :=
  ⟨idComputer Computability.inhabitedFinEncoding.default⟩

noncomputable section

/-- A proof that the identity map on α is computable in polytime. -/
def idComputableInPolyTime {α : Type} (ea : FinEncoding α) : @Tm2ComputableInPolyTime α α ea ea id where
  tm := idComputer ea
  inputAlphabet := Equivₓ.cast rfl
  outputAlphabet := Equivₓ.cast rfl
  time := 1
  outputsFun := fun _ =>
    { steps := 1, evals_in_steps := rfl,
      steps_le_m := by
        simp only [← Polynomial.eval_one] }

instance inhabitedTm2ComputableInPolyTime :
    Inhabited (Tm2ComputableInPolyTime (default : FinEncoding Bool) default id) :=
  ⟨idComputableInPolyTime Computability.inhabitedFinEncoding.default⟩

instance inhabitedTm2OutputsInTime :
    Inhabited
      (Tm2OutputsInTime (idComputer finEncodingBoolBool) (List.map (Equivₓ.cast rfl).invFun [false])
        (some (List.map (Equivₓ.cast rfl).invFun [false])) _) :=
  ⟨(idComputableInPolyTime finEncodingBoolBool).outputsFun false⟩

instance inhabitedTm2Outputs :
    Inhabited
      (Tm2Outputs (idComputer finEncodingBoolBool) (List.map (Equivₓ.cast rfl).invFun [false])
        (some (List.map (Equivₓ.cast rfl).invFun [false]))) :=
  ⟨Tm2OutputsInTime.toTm2Outputs Turing.inhabitedTm2OutputsInTime.default⟩

instance inhabitedEvalsToInTime : Inhabited (EvalsToInTime (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩) 0) :=
  ⟨EvalsToInTime.refl _ _⟩

instance inhabitedTm2EvalsTo : Inhabited (EvalsTo (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩)) :=
  ⟨EvalsTo.refl _ _⟩

/-- A proof that the identity map on α is computable in time. -/
def idComputableInTime {α : Type} (ea : FinEncoding α) : @Tm2ComputableInTime α α ea ea id :=
  tm2_computable_in_poly_time.to_tm2_computable_in_time <| idComputableInPolyTime ea

instance inhabitedTm2ComputableInTime : Inhabited (Tm2ComputableInTime finEncodingBoolBool finEncodingBoolBool id) :=
  ⟨idComputableInTime Computability.inhabitedFinEncoding.default⟩

/-- A proof that the identity map on α is computable. -/
def idComputable {α : Type} (ea : FinEncoding α) : @Tm2Computable α α ea ea id :=
  tm2_computable_in_time.to_tm2_computable <| idComputableInTime ea

instance inhabitedTm2Computable : Inhabited (Tm2Computable finEncodingBoolBool finEncodingBoolBool id) :=
  ⟨idComputable Computability.inhabitedFinEncoding.default⟩

instance inhabitedTm2ComputableAux : Inhabited (Tm2ComputableAux Bool Bool) :=
  ⟨(default : Tm2Computable finEncodingBoolBool finEncodingBoolBool id).toTm2ComputableAux⟩

end Turing


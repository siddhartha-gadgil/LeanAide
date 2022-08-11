/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Converter monad for building simplifiers.
-/
import Mathbin.Control.Basic

open Tactic

unsafe structure old_conv_result (α : Type) where
  val : α
  rhs : expr
  proof : Option expr

unsafe def old_conv (α : Type) : Type :=
  Name → expr → tactic (old_conv_result α)

namespace OldConv

unsafe def lhs : old_conv expr := fun r e => return ⟨e, e, none⟩

unsafe def change (new_p : pexpr) : old_conv Unit := fun r e => do
  let e_type ← infer_type e
  let new_e ← to_expr (pquote.1 (%%ₓnew_p : %%ₓe_type))
  unify e new_e
  return ⟨(), new_e, none⟩

protected unsafe def pure {α : Type} : α → old_conv α := fun a r e => return ⟨a, e, none⟩

private unsafe def join_proofs (r : Name) (o₁ o₂ : Option expr) : tactic (Option expr) :=
  match o₁, o₂ with
  | none, _ => return o₂
  | _, none => return o₁
  | some p₁, some p₂ => do
    let env ← get_env
    match env r with
      | some trans => do
        let pr ← mk_app trans [p₁, p₂]
        return <| some pr
      | none => fail f! "converter failed, relation '{r}' is not transitive"

protected unsafe def seq {α β : Type} (c₁ : old_conv (α → β)) (c₂ : old_conv α) : old_conv β := fun r e => do
  let ⟨fn, e₁, pr₁⟩ ← c₁ r e
  let ⟨a, e₂, pr₂⟩ ← c₂ r e₁
  let pr ← join_proofs r pr₁ pr₂
  return ⟨fn a, e₂, pr⟩

protected unsafe def fail {α β : Type} [has_to_format β] (msg : β) : old_conv α := fun r e => tactic.fail msg

protected unsafe def failed {α : Type} : old_conv α := fun r e => tactic.failed

protected unsafe def orelse {α : Type} (c₁ : old_conv α) (c₂ : old_conv α) : old_conv α := fun r e => c₁ r e <|> c₂ r e

protected unsafe def map {α β : Type} (f : α → β) (c : old_conv α) : old_conv β := fun r e => do
  let ⟨a, e₁, pr⟩ ← c r e
  return ⟨f a, e₁, pr⟩

protected unsafe def bind {α β : Type} (c₁ : old_conv α) (c₂ : α → old_conv β) : old_conv β := fun r e =>
  Bind.bind (c₁ r e) fun ⟨a, e₁, pr₁⟩ =>
    Bind.bind (c₂ a r e₁) fun ⟨b, e₂, pr₂⟩ => Bind.bind (join_proofs r pr₁ pr₂) fun pr => return ⟨b, e₂, pr⟩

/- do -- wrong bind instance something with `name`?
  ⟨a, e₁, pr₁⟩ ← c₁ r e,
  ⟨b, e₂, pr₂⟩ ← c₂ a r e₁,
  pr           ← join_proofs r pr₁ pr₂,
  return ⟨b, e₂, pr⟩
  -/
unsafe instance : Monadₓ old_conv where
  map := @old_conv.map
  pure := @old_conv.pure
  bind := @old_conv.bind

unsafe instance : Alternativeₓ old_conv :=
  { old_conv.monad with failure := @old_conv.failed, orelse := @old_conv.orelse }

unsafe def whnf (md : Transparency := reducible) : old_conv Unit := fun r e => do
  let n ← tactic.whnf e md
  return ⟨(), n, none⟩

unsafe def dsimp : old_conv Unit := fun r e => do
  let s ← simp_lemmas.mk_default
  let n ← s.dsimplify [] e
  return ⟨(), n, none⟩

unsafe def trace {α : Type} [has_to_tactic_format α] (a : α) : old_conv Unit := fun r e =>
  tactic.trace a >> return ⟨(), e, none⟩

unsafe def trace_lhs : old_conv Unit :=
  lhs >>= trace

unsafe def apply_lemmas_core (s : simp_lemmas) (prove : tactic Unit) : old_conv Unit := fun r e => do
  let (new_e, pr) ← s.rewrite e prove r
  return ⟨(), new_e, some pr⟩

unsafe def apply_lemmas (s : simp_lemmas) : old_conv Unit :=
  apply_lemmas_core s failed

-- adapter for using iff-lemmas as eq-lemmas
unsafe def apply_propext_lemmas_core (s : simp_lemmas) (prove : tactic Unit) : old_conv Unit := fun r e => do
  guardₓ (r = `eq)
  let (new_e, pr) ← s.rewrite e prove `iff
  let new_pr ← mk_app `propext [pr]
  return ⟨(), new_e, some new_pr⟩

unsafe def apply_propext_lemmas (s : simp_lemmas) : old_conv Unit :=
  apply_propext_lemmas_core s failed

private unsafe def mk_refl_proof (r : Name) (e : expr) : tactic expr := do
  let env ← get_env
  match environment.refl_for env r with
    | some refl => do
      let pr ← mk_app refl [e]
      return pr
    | none => fail f! "converter failed, relation '{r}' is not reflexive"

unsafe def to_tactic (c : old_conv Unit) : Name → expr → tactic (expr × expr) := fun r e => do
  let ⟨u, e₁, o⟩ ← c r e
  match o with
    | none => do
      let p ← mk_refl_proof r e
      return (e₁, p)
    | some p => return (e₁, p)

unsafe def lift_tactic {α : Type} (t : tactic α) : old_conv α := fun r e => do
  let a ← t
  return ⟨a, e, none⟩

unsafe def apply_simp_set (attr_name : Name) : old_conv Unit :=
  lift_tactic (get_user_simp_lemmas attr_name) >>= apply_lemmas

unsafe def apply_propext_simp_set (attr_name : Name) : old_conv Unit :=
  lift_tactic (get_user_simp_lemmas attr_name) >>= apply_propext_lemmas

unsafe def skip : old_conv Unit :=
  return ()

unsafe def repeat : old_conv Unit → old_conv Unit
  | c, r, lhs =>
    (do
        let ⟨_, rhs₁, pr₁⟩ ← c r lhs
        guardₓ ¬expr.alpha_eqv lhs rhs₁
        let ⟨_, rhs₂, pr₂⟩ ← repeat c r rhs₁
        let pr ← join_proofs r pr₁ pr₂
        return ⟨(), rhs₂, pr⟩) <|>
      return ⟨(), lhs, none⟩

unsafe def first {α : Type} : List (old_conv α) → old_conv α
  | [] => old_conv.failed
  | c :: cs => c <|> first cs

unsafe def match_pattern (p : pattern) : old_conv Unit := fun r e => tactic.match_pattern p e >> return ⟨(), e, none⟩

unsafe def mk_match_expr (p : pexpr) : tactic (old_conv Unit) := do
  let new_p ← pexpr_to_pattern p
  return fun r e => tactic.match_pattern new_p e >> return ⟨(), e, none⟩

unsafe def match_expr (p : pexpr) : old_conv Unit := fun r e => do
  let new_p ← pexpr_to_pattern p
  tactic.match_pattern new_p e >> return ⟨(), e, none⟩

unsafe def funext (c : old_conv Unit) : old_conv Unit := fun r lhs => do
  guardₓ (r = `eq)
  let expr.lam n bi d b ← return lhs
  let aux_type := expr.pi n bi d (expr.const `true [])
  let (result, _) ←
    solve_aux aux_type <| do
        let x ← intro1
        let c_result ← c r (b.instantiate_var x)
        let rhs := expr.lam n bi d (c_result.rhs.abstract x)
        match c_result with
          | some pr => do
            let aux_pr := expr.lam n bi d (pr x)
            let new_pr ← mk_app `funext [lhs, rhs, aux_pr]
            return ⟨(), rhs, some new_pr⟩
          | none => return ⟨(), rhs, none⟩
  return result

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `f_type
unsafe def congr_core (c_f c_a : old_conv Unit) : old_conv Unit := fun r lhs => do
  guardₓ (r = `eq)
  let expr.app f a ← return lhs
  let f_type ← infer_type f >>= tactic.whnf
  guardₓ (f_type f_type.is_arrow)
  let ⟨(), new_f, of⟩ ← mtry c_f r f
  let ⟨(), new_a, oa⟩ ← mtry c_a r a
  let rhs ← return <| new_f new_a
  match of, oa with
    | none, none => return ⟨(), rhs, none⟩
    | none, some pr_a => do
      let pr ← mk_app `congr_arg [a, new_a, f, pr_a]
      return ⟨(), new_f new_a, some pr⟩
    | some pr_f, none => do
      let pr ← mk_app `congr_fun [f, new_f, pr_f, a]
      return ⟨(), rhs, some pr⟩
    | some pr_f, some pr_a => do
      let pr ← mk_app `congr [f, new_f, a, new_a, pr_f, pr_a]
      return ⟨(), rhs, some pr⟩

unsafe def congr (c : old_conv Unit) : old_conv Unit :=
  congr_core c c

unsafe def bottom_up (c : old_conv Unit) : old_conv Unit := fun r e => do
  let s ← simp_lemmas.mk_default
  let (a, new_e, pr) ←
    ext_simplify_core () {  } s (fun u => return u) (fun a s r p e => failed)
        (fun a s r p e => do
          let ⟨u, new_e, pr⟩ ← c r e
          return ((), new_e, pr, tt))
        r e
  return ⟨(), new_e, some pr⟩

unsafe def top_down (c : old_conv Unit) : old_conv Unit := fun r e => do
  let s ← simp_lemmas.mk_default
  let (a, new_e, pr) ←
    ext_simplify_core () {  } s (fun u => return u)
        (fun a s r p e => do
          let ⟨u, new_e, pr⟩ ← c r e
          return ((), new_e, pr, tt))
        (fun a s r p e => failed) r e
  return ⟨(), new_e, some pr⟩

unsafe def find (c : old_conv Unit) : old_conv Unit := fun r e => do
  let s ← simp_lemmas.mk_default
  let (a, new_e, pr) ←
    ext_simplify_core () {  } s (fun u => return u)
        (fun a s r p e =>
          (do
              let ⟨u, new_e, pr⟩ ← c r e
              return ((), new_e, pr, ff)) <|>
            return ((), e, none, true))
        (fun a s r p e => failed) r e
  return ⟨(), new_e, some pr⟩

unsafe def find_pattern (pat : pattern) (c : old_conv Unit) : old_conv Unit := fun r e => do
  let s ← simp_lemmas.mk_default
  let (a, new_e, pr) ←
    ext_simplify_core () {  } s (fun u => return u)
        (fun a s r p e => do
          let matched ← tactic.match_pattern pat e >> return true <|> return false
          if matched then do
              let ⟨u, new_e, pr⟩ ← c r e
              return ((), new_e, pr, ff)
            else return ((), e, none, tt))
        (fun a s r p e => failed) r e
  return ⟨(), new_e, some pr⟩

unsafe def findp : pexpr → old_conv Unit → old_conv Unit := fun p c r e => do
  let pat ← pexpr_to_pattern p
  find_pattern pat c r e

unsafe def conversion (c : old_conv Unit) : tactic Unit := do
  let (r, lhs, rhs) ← target_lhs_rhs <|> fail "conversion failed, target is not of the form 'lhs R rhs'"
  let (new_lhs, pr) ← to_tactic c r lhs
  unify new_lhs rhs <|> do
      let new_lhs_fmt ← pp new_lhs
      let rhs_fmt ← pp rhs
      fail (to_fmt "conversion failed, expected" ++ rhs_fmt 4 ++ format.line ++ "provided" ++ new_lhs_fmt 4)
  exact pr

end OldConv


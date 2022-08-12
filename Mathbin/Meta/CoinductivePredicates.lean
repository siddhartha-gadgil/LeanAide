/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl (CMU)
-/
import Mathbin.Tactic.Core

section

universe u

@[user_attribute]
unsafe def monotonicity : user_attribute where
  Name := `monotonicity
  descr := "Monotonicity rules for predicates"

theorem Monotonicity.pi {α : Sort u} {p q : α → Prop} (h : ∀ a, Implies (p a) (q a)) : Implies (∀ a, p a) (∀ a, q a) :=
  fun h' a => h a (h' a)

theorem Monotonicity.imp {p p' q q' : Prop} (h₁ : Implies p' q') (h₂ : Implies q p) : Implies (p → p') (q → q') :=
  fun h => h₁ ∘ h ∘ h₂

@[monotonicity]
theorem Monotonicity.const (p : Prop) : Implies p p :=
  id

@[monotonicity]
theorem Monotonicity.true (p : Prop) : Implies p True := fun _ => trivialₓ

@[monotonicity]
theorem Monotonicity.false (p : Prop) : Implies False p :=
  False.elim

@[monotonicity]
theorem Monotonicity.exists {α : Sort u} {p q : α → Prop} (h : ∀ a, Implies (p a) (q a)) :
    Implies (∃ a, p a) (∃ a, q a) :=
  exists_imp_exists h

@[monotonicity]
theorem Monotonicity.and {p p' q q' : Prop} (hp : Implies p p') (hq : Implies q q') : Implies (p ∧ q) (p' ∧ q') :=
  And.imp hp hq

@[monotonicity]
theorem Monotonicity.or {p p' q q' : Prop} (hp : Implies p p') (hq : Implies q q') : Implies (p ∨ q) (p' ∨ q') :=
  Or.imp hp hq

@[monotonicity]
theorem Monotonicity.not {p q : Prop} (h : Implies p q) : Implies (¬q) ¬p :=
  mt h

end

namespace Tactic

open Expr Tactic

-- TODO: use backchaining
private unsafe def mono_aux (ns : List Name) (hs : List expr) : tactic Unit := do
  intros
  (do
        let quote.1 (Implies (%%ₓp) (%%ₓq)) ← target
        (do
              is_def_eq p q
              eapplyc `monotone.const) <|>
            do
            let expr.pi pn pbi pd pb ← whnf p
            let expr.pi qn qbi qd qb ← whnf q
            let sort u ← infer_type pd
            (do
                  is_def_eq pd qd
                  let p' := expr.lam pn pbi pd pb
                  let q' := expr.lam qn qbi qd qb
                  eapply ((const `monotonicity.pi [u] : expr) pd p' q')
                  skip) <|>
                do
                guardₓ <| u = level.zero ∧ is_arrow p ∧ is_arrow q
                let p' := pb 0 1
                let q' := qb 0 1
                eapply ((const `monotonicity.imp [] : expr) pd p' qd q')
                skip) <|>
      first (hs fun h => apply_core h { md := transparency.none, NewGoals := new_goals.non_dep_only } >> skip) <|>
        first
          (ns fun n => do
            let c ← mk_const n
            apply_core c { md := transparency.none, NewGoals := new_goals.non_dep_only }
            skip)
  all_goals' mono_aux

unsafe def mono (e : expr) (hs : List expr) : tactic Unit := do
  let t ← target
  let t' ← infer_type e
  let ns ← attribute.get_instances `monotonicity
  let ((), p) ← solve_aux (quote.1 (Implies (%%ₓt') (%%ₓt))) (mono_aux ns hs)
  exact (p e)

end Tactic

/-
The coinductive predicate `pred`:

  coinductive {u} pred (A) : a → Prop
  | r : ∀A b, pred A p

where
  `u` is a list of universe parameters
  `A` is a list of global parameters
  `pred` is a list predicates to be defined
  `a` are the indices for each `pred`
  `r` is a list of introduction rules for each `pred`
  `b` is a list of parameters for each rule in `r` and `pred`
  `p` is are the instances of `a` using `A` and `b`

`pred` is compiled to the following defintions:

  inductive {u} pred.functional (A) ([pred'] : a → Prop) : a → Prop
  | r : ∀a [f], b[pred/pred'] → pred.functional a [f] p

  lemma {u} pred.functional.mono (A) ([pred₁] [pred₂] : a → Prop) [(h : ∀b, pred₁ b → pred₂ b)] :
    ∀p, pred.functional A pred₁ p → pred.functional A pred₂ p

  def {u} pred_i (A) (a) : Prop :=
  ∃[pred'], (Λi, ∀a, pred_i a → pred_i.functional A [pred] a) ∧ pred'_i a

  lemma {u} pred_i.corec_functional (A) [Λi, C_i : a_i → Prop]
    [Λi, h : ∀a, C_i a → pred_i.functional A C_i a] :
    ∀a, C_i a → pred_i A a

  lemma {u} pred_i.destruct (A) (a) : pred A a → pred.functional A [pred A] a

  lemma {u} pred_i.construct (A) : ∀a, pred_i.functional A [pred A] a → pred_i A a

  lemma {u} pred_i.cases_on (A) (C : a → Prop) {a} (h : pred_i a) [Λi, ∀a, b → C p] → C a

  lemma {u} pred_i.corec_on (A) [(C : a → Prop)] (a) (h : C_i a)
    [Λi, h_i : ∀a, C_i a → [V j ∃b, a = p]] : pred_i A a

  lemma {u} pred.r (A) (b) : pred_i A p
-/
namespace Tactic

open Level Expr Tactic

namespace AddCoinductivePredicate

-- private
unsafe structure coind_rule : Type where
  orig_nm : Name
  func_nm : Name
  type : expr
  loc_type : expr
  args : List expr
  loc_args : List expr
  concl : expr
  insts : List expr

-- private
unsafe structure coind_pred : Type where
  u_names : List Name
  params : List expr
  pd_name : Name
  type : expr
  intros : List coind_rule
  locals : List expr
  (f₁ f₂ : expr)
  u_f : level

namespace CoindPred

unsafe def u_params (pd : coind_pred) : List level :=
  pd.u_names.map param

unsafe def f₁_l (pd : coind_pred) : expr :=
  pd.f₁.app_of_list pd.locals

unsafe def f₂_l (pd : coind_pred) : expr :=
  pd.f₂.app_of_list pd.locals

unsafe def pred (pd : coind_pred) : expr :=
  const pd.pd_name pd.u_params

unsafe def func (pd : coind_pred) : expr :=
  const (pd.pd_name ++ "functional") pd.u_params

unsafe def func_g (pd : coind_pred) : expr :=
  pd.func.app_of_list <| pd.params

unsafe def pred_g (pd : coind_pred) : expr :=
  pd.pred.app_of_list <| pd.params

unsafe def impl_locals (pd : coind_pred) : List expr :=
  pd.locals.map to_implicit_binder

unsafe def impl_params (pd : coind_pred) : List expr :=
  pd.params.map to_implicit_binder

unsafe def le (pd : coind_pred) (f₁ f₂ : expr) : expr :=
  (imp (f₁.app_of_list pd.locals) (f₂.app_of_list pd.locals)).pis pd.impl_locals

unsafe def corec_functional (pd : coind_pred) : expr :=
  const (pd.pd_name ++ "corec_functional") pd.u_params

unsafe def mono (pd : coind_pred) : expr :=
  const (pd.func.const_name ++ "mono") pd.u_params

unsafe def rec' (pd : coind_pred) : tactic expr := do
  let c := pd.func.const_name ++ "rec"
  let env ← get_env
  let decl ← env.get c
  let num := decl.univ_params.length
  return (const c <| if num = pd then pd else level.zero :: pd)

-- ^^ `rec`'s universes are not always `u_params`, e.g. eq, wf, false
unsafe def construct (pd : coind_pred) : expr :=
  const (pd.pd_name ++ "construct") pd.u_params

unsafe def destruct (pd : coind_pred) : expr :=
  const (pd.pd_name ++ "destruct") pd.u_params

unsafe def add_theorem (pd : coind_pred) (n : Name) (type : expr) (tac : tactic Unit) : tactic expr :=
  add_theorem_by n pd.u_names type tac

end CoindPred

end AddCoinductivePredicate

open AddCoinductivePredicate

/-- compact_relation bs as_ps: Product a relation of the form:
  R := λ as, ∃ bs, Λ_i a_i = p_i[bs]
This relation is user visible, so we compact it by removing each `b_j` where a `p_i = b_j`, and
hence `a_i = b_j`. We need to take care when there are `p_i` and `p_j` with `p_i = p_j = b_k`. -/
unsafe def compact_relation : List expr → List (expr × expr) → List expr × List (expr × expr)
  | [], ps => ([], ps)
  | List.cons b bs, ps =>
    match ps.span fun ap : expr × expr => ¬expr.alpha_eqv ap.2 b with
    | (_, []) =>
      let (bs, ps) := compact_relation bs ps
      (b :: bs, ps)
    | (ps₁, List.cons (a, _) ps₂) =>
      let i := a.instantiate_local b.local_uniq_name
      compact_relation (bs.map i) ((ps₁ ++ ps₂).map fun ⟨a, p⟩ => (a, i p))

unsafe def add_coinductive_predicate (u_names : List Name) (params : List expr) (preds : List <| expr × List expr) :
    Tactic Unit := do
  let params_names := params.map local_pp_name
  let u_params := u_names.map param
  let pre_info ←
    preds.mmap fun ⟨c, is⟩ => do
        let (ls, t) ← open_pis c.local_type
        is_def_eq t (quote.1 Prop) <|>
            fail ((f! "Type of {c} is not Prop. Currently only ") ++ "coinductive predicates are supported.")
        let n := if preds.length = 1 then "" else "_" ++ c.local_pp_name.lastString
        let f₁ ← mk_local_def (mkSimpleName <| "C" ++ n) c.local_type
        let f₂ ← mk_local_def (mkSimpleName <| "C₂" ++ n) c.local_type
        return (ls, (f₁, f₂))
  let fs := pre_info.map Prod.snd
  let fs₁ := fs.map Prod.fst
  let fs₂ := fs.map Prod.snd
  let pds ←
    (preds.zip pre_info).mmap fun ⟨⟨c, is⟩, ls, f₁, f₂⟩ => do
        let sort u_f ← infer_type f₁ >>= infer_type
        let pred_g := fun c : expr => (const c.local_uniq_name u_params : expr).app_of_list params
        let intros ←
          is.mmap fun i => do
              let (args, t') ← open_pis i.local_type
              let Name.mk_string sub p ← return i.local_uniq_name
              let loc_args :=
                args.map fun e => (fs₁.zip preds).foldl (fun (e : expr) ⟨f, c, _⟩ => e.replace_with (pred_g c) f) e
              let t' := t'.replace_with (pred_g c) f₂
              return
                  { orig_nm := i, func_nm := p ++ "functional" ++ sub, type := i, loc_type := t' loc_args, concl := t',
                    loc_args, args, insts := t' }
        return { pd_name := c, type := c, f₁, f₂, u_f, intros, locals := ls, params, u_names }
  -- Introduce all functionals
      pds
      fun pd : coind_pred => do
      let func_f₁ := pd <| fs₁
      let func_f₂ := pd <| fs₂
      let func_intros
        ←-- Define functional for `pd` as inductive predicate
            pd
            fun r : coind_rule => do
            let t := instantiate_local pd (pd fs₁) r
            return (r, r, t <| params ++ fs₁)
      add_inductive pd u_names (params + preds) (pd <| params ++ fs₁) (func_intros fun ⟨t, _, r⟩ => (t, r))
      let mono_params
        ←-- Prove monotonicity rule
            pds
            fun pd => do
            let h ← mk_local_def `h <| pd pd pd
            return [pd, pd, h]
      pd (pd ++ "mono") ((pd func_f₁ func_f₂).pis <| params ++ mono_params) do
          let ps ← intro_lst <| params expr.local_pp_name
          let fs ←
            pds fun pd => do
                let [f₁, f₂, h] ← intro_lst [pd, pd, `h]
                let-- the type of h' reduces to h
                h' :=
                  local_const h h h <|
                    (((const `implies [] : expr) (f₁ pd) (f₂ pd)).pis pd).instantiate_locals <|
                      (ps params).map fun ⟨lv, p⟩ => (p, lv)
                return (f₂, h')
          let m ← pd
          eapply <| m ps
          -- somehow `induction` / `cases` doesn't work?
              func_intros
              fun ⟨n, pp_n, t⟩ =>
              solve1 <| do
                let bs ← intros
                let ms ← apply_core ((const n u_params).app_of_list <| ps ++ fs Prod.fst) { NewGoals := new_goals.all }
                let params ← (ms bs).enum.mfilter fun ⟨n, m, d⟩ => bnot <$> is_assigned m.2
                params fun ⟨n, m, d⟩ =>
                    mono d (fs Prod.snd) <|>
                      fail f!"failed to prove montonoicity of {(n + 1)}. parameter of intro-rule {pp_n}"
  pds fun pd => do
      let func_f := fun pd : coind_pred => pd <| pds coind_pred.f₁
      let pred_body
        ←-- define final predicate
              mk_exists_lst
              (pds coind_pred.f₁) <|
            mk_and_lst <| (pds fun pd => pd pd (func_f pd)) ++ [pd pd]
      add_decl <| mk_definition pd u_names (pd <| params) <| pred_body <| params ++ pd
      let hs
        ←-- prove `corec_functional` rule
            pds
            fun pd : coind_pred => mk_local_def `hc <| pd pd (func_f pd)
      pd (pd ++ "corec_functional") ((pd pd pd).pis <| params ++ fs₁ ++ hs) do
          intro_lst <| params local_pp_name
          let fs ← intro_lst <| fs₁ local_pp_name
          let hs ← intro_lst <| hs local_pp_name
          let ls ← intro_lst <| pd local_pp_name
          let h ← intro `h
          whnf_target
          fs existsi
          hs fun f => econstructor >> exact f
          exact h
  let func_f := fun pd : coind_pred => pd.func_g.app_of_list <| pds.map coind_pred.pred_g
  -- prove `destruct` rules
      pds
      fun ⟨n, pd⟩ => do
      let destruct := pd pd (func_f pd)
      pd (pd ++ "destruct") (destruct params) do
          let ps ← intro_lst <| params local_pp_name
          let ls ← intro_lst <| pd local_pp_name
          let h ← intro `h
          let (fs, h, _) ← elim_gen_prod pds h [] []
          let (hs, h, _) ← elim_gen_prod pds h [] []
          eapply <| pd ps
          pds fun pd : coind_pred =>
              focus1 <| do
                eapply <| pd
                focus <| hs exact
          let some h' ← return <| hs n
          eapply h'
          exact h
  -- prove `construct` rules
      pds
      fun pd =>
      pd (pd ++ "construct") ((pd (func_f pd) pd).pis params) do
        let ps ← intro_lst <| params local_pp_name
        let func_pred_g := fun pd : coind_pred => pd <| ps ++ pds fun pd : coind_pred => pd ps
        eapply <| pd <| ps ++ pds func_pred_g
        pds fun pd : coind_pred =>
            solve1 <| do
              eapply <| pd ps
              pds fun pd => solve1 <| eapply (pd ps) >> skip
  -- prove `cases_on` rules
      pds
      fun pd => do
      let C := pd
      let h ← mk_local_def `h <| pd pd
      let rules ←
        pd fun r : coind_rule => do
            mk_local_def (mkSimpleName r) <| (C r).pis r
      let cases_on ←
        pd (pd ++ "cases_on") ((C pd).pis <| params ++ [C] ++ pd ++ [h] ++ rules) do
            let ps ← intro_lst <| params local_pp_name
            let C ← intro `C
            let ls ← intro_lst <| pd local_pp_name
            let h ← intro `h
            let rules ← intro_lst <| rules local_pp_name
            let func_rec ← pd
            eapply <| func_rec <| (ps ++ pds fun pd => pd ps) ++ [C] ++ rules
            eapply <| pd
            exact h
      set_basic_attribute `elab_as_eliminator cases_on
  -- prove `corec_on` rules
      pds
      fun pd => do
      let rules ←
        pds fun pd => do
            let intros ←
              pd fun r => do
                  let (bs, eqs) := compact_relation r <| pd r
                  let eqs ←
                    eqs fun ⟨l, i⟩ => do
                        let sort u ← infer_type l
                        return <| (const `eq [u] : expr) l i l
                  match bs, eqs with
                    | [], [] => return ((0, 0), mk_true)
                    | _, [] => Prod.mk (bs, 0) <$> mk_exists_lst bs bs
                    | _, _ => Prod.mk (bs, eqs) <$> mk_exists_lst bs (mk_and_lst eqs)
            let shape := intros Prod.fst
            let intros := intros Prod.snd
            Prod.mk shape <$> mk_local_def (mkSimpleName <| "h_" ++ pd) (((pd pd).imp (mk_or_lst intros)).pis pd)
      let shape := rules Prod.fst
      let rules := rules Prod.snd
      let h ← mk_local_def `h <| pd pd
      pd (pd ++ "corec_on") ((pd <| pd).pis <| params ++ fs₁ ++ pd ++ [h] ++ rules) do
          let ps ← intro_lst <| params local_pp_name
          let fs ← intro_lst <| fs₁ local_pp_name
          let ls ← intro_lst <| pd local_pp_name
          let h ← intro `h
          let rules ← intro_lst <| rules local_pp_name
          eapply <| pd <| ps ++ fs
          (pds <| rules shape).mmap fun ⟨pd, hr, s⟩ =>
              solve1 <| do
                let ls ← intro_lst <| pd local_pp_name
                let h' ← intro `h
                let h' ← note `h' none <| hr ls h'
                match s with
                  | 0 => induction h' >> skip
                  |-- h' : false
                      n +
                      1 =>
                    do
                    let hs ← elim_gen_sum n h'
                    (hs <| pd s).mmap' fun ⟨h, r, n_bs, n_eqs⟩ =>
                        solve1 <| do
                          let (as, h, _) ← elim_gen_prod (n_bs - if n_eqs = 0 then 1 else 0) h [] []
                          if n_eqs > 0 then do
                              let (eqs, eq', _) ← elim_gen_prod (n_eqs - 1) h [] []
                              (eqs ++ [eq']).mmap' subst
                            else skip
                          eapply ((const r u_params).app_of_list <| ps ++ fs)
                          iterate assumption
          exact h
  -- prove constructors
      pds
      fun pd =>
      pd fun r =>
        pd r (r params) <| do
          let ps ← intro_lst <| params local_pp_name
          let bs ← intros
          eapply <| pd
          exact <| (const r u_params).app_of_list <| (ps ++ pds fun pd => pd ps) ++ bs
  pds fun pd : coind_pred => set_basic_attribute `irreducible pd
  try triv

-- we setup a trivial goal for the tactic framework
setup_tactic_parser

@[user_command]
unsafe def coinductive_predicate (meta_info : decl_meta_info) (_ : parse <| tk "coinductive") : lean.parser Unit := do
  let decl ← inductive_decl.parse meta_info
  add_coinductive_predicate decl decl <| decl fun d => (d, d)
  decl fun d => do
      get_env >>= fun env => set_env <| env d
      meta_info d
      d d
      let some doc_string ← pure meta_info | skip
      add_doc_string d doc_string

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `hs
/-- Prepares coinduction proofs. This tactic constructs the coinduction invariant from
the quantifiers in the current goal.

Current version: do not support mutual inductive rules -/
unsafe def coinduction (rule : expr) (ns : List Name) : tactic Unit :=
  focus1 <| do
    let ctxts' ← intros
    let ctxts ← ctxts'.mmap fun v => local_const v.local_uniq_name v.local_pp_name v.local_binding_info <$> infer_type v
    let mvars ← apply_core rule { approx := false, NewGoals := NewGoals.all }
    let g
      ←-- analyse relation
          List.headₓ <$>
          get_goals
    let List.cons _ m_is ← return <| mvars.dropWhile fun v => v.2 ≠ g
    let tgt ← target
    let (is, ty) ← open_pis tgt
    let-- construct coinduction predicate
      (bs, eqs)
      ← compact_relation ctxts <$> (is.zip m_is).mmap fun ⟨i, m⟩ => Prod.mk i <$> instantiate_mvars m.2
    solve1 do
        let eqs ←
          (mk_and_lst <$> eqs fun ⟨i, m⟩ => mk_app `eq [m, i] >>= instantiate_mvars) <|> do
              let x ← mk_psigma (eqs Prod.fst)
              let y ← mk_psigma (eqs Prod.snd)
              let t ← infer_type x
              mk_mapp `eq [t, x, y]
        let rel ← mk_exists_lst bs eqs
        exact (rel is)
    -- prove predicate
        solve1
        do
        target >>= instantiate_mvars >>= change
        -- TODO: bug in existsi & constructor when mvars in hyptohesis
            bs
            existsi
        iterate' (econstructor >> skip)
    -- clean up remaining coinduction steps
        all_goals'
        do
        ctxts' clear
        target >>= instantiate_mvars >>= change
        let is
          ←-- TODO: bug in subst when mvars in hyptohesis
              intro_lst <|
              is expr.local_pp_name
        let h ← intro1
        let (_, h, ns) ← elim_gen_prod (bs - if eqs = 0 then 1 else 0) h [] ns
        match eqs with
          | [] => clear h
          | e :: eqs => do
            let (hs, h, ns) ← elim_gen_prod eqs h [] ns
            (h :: hs hs.reverse : List _).mfoldl
                (fun (hs : List Name) (h : expr) => do
                  let [(_, hs', σ)] ← cases_core h hs
                  clear (h σ)
                  pure <| hs hs')
                ns
            skip

namespace Interactive

open Interactive Interactive.Types Expr Lean.Parser

-- mathport name: «expr ?»
local postfix:1024 "?" => optionalₓ

-- mathport name: «expr *»
local postfix:1024 "*" => many

unsafe def coinduction (corec_name : parse ident) (ns : parse with_ident_list)
    (revert : parse <| (tk "generalizing" *> ident*)?) : tactic Unit := do
  let rule ← mk_const corec_name
  let locals ← mmapₓ tactic.get_local <| revert.getOrElse []
  revert_lst locals
  tactic.coinduction rule ns
  skip

end Interactive

end Tactic


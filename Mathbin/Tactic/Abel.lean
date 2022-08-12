/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Tactic.NormNum

/-!
# The `abel` tactic

Evaluate expressions in the language of additive, commutative monoids and groups.


-/


namespace Tactic

namespace Abel

/-- The `context` for a call to `abel`.

Stores a few options for this call, and caches some common subexpressions
such as typeclass instances and `0 : α`.
-/
unsafe structure context where
  red : Transparency
  α : expr
  Univ : level
  α0 : expr
  is_group : Bool
  inst : expr

/-- Populate a `context` object for evaluating `e`, up to reducibility level `red`. -/
unsafe def mk_context (red : Transparency) (e : expr) : tactic context := do
  let α ← infer_type e
  let c ← mk_app `` AddCommMonoidₓ [α] >>= mk_instance
  let cg ← try_core (mk_app `` AddCommGroupₓ [α] >>= mk_instance)
  let u ← mk_meta_univ
  infer_type α >>= unify (expr.sort (level.succ u))
  let u ← get_univ_assignment u
  let α0 ← expr.of_nat α 0
  match cg with
    | some cg => return ⟨red, α, u, α0, tt, cg⟩
    | _ => return ⟨red, α, u, α0, ff, c⟩

/-- Apply the function `n : ∀ {α} [inst : add_whatever α], _` to the
implicit parameters in the context, and the given list of arguments. -/
unsafe def context.app (c : context) (n : Name) (inst : expr) : List expr → expr :=
  (@expr.const true n [c.Univ] c.α inst).mk_app

/-- Apply the function `n : ∀ {α} [inst α], _` to the implicit parameters in the
context, and the given list of arguments.

Compared to `context.app`, this takes the name of the typeclass, rather than an
inferred typeclass instance.
-/
unsafe def context.mk_app (c : context) (n inst : Name) (l : List expr) : tactic expr := do
  let m ← mk_instance ((expr.const inst [c.Univ] : expr) c.α)
  return <| c n m l

/-- Add the letter "g" to the end of the name, e.g. turning `term` into `termg`.

This is used to choose between declarations taking `add_comm_monoid` and those
taking `add_comm_group` instances.
-/
unsafe def add_g : Name → Name
  | Name.mk_string s p => Name.mk_string (s ++ "g") p
  | n => n

/-- Apply the function `n : ∀ {α} [add_comm_{monoid,group} α]` to the given
list of arguments.

Will use the `add_comm_{monoid,group}` instance that has been cached in the context.
-/
unsafe def context.iapp (c : context) (n : Name) : List expr → expr :=
  c.app (if c.is_group then add_g n else n) c.inst

def term {α} [AddCommMonoidₓ α] (n : ℕ) (x a : α) : α :=
  n • x + a

def termg {α} [AddCommGroupₓ α] (n : ℤ) (x a : α) : α :=
  n • x + a

/-- Evaluate a term with coefficient `n`, atom `x` and successor terms `a`. -/
unsafe def context.mk_term (c : context) (n x a : expr) : expr :=
  c.iapp `` term [n, x, a]

/-- Interpret an integer as a coefficient to a term. -/
unsafe def context.int_to_expr (c : context) (n : ℤ) : tactic expr :=
  expr.of_int (if c.is_group then quote.1 ℤ else quote.1 ℕ) n

unsafe inductive normal_expr : Type
  | zero (e : expr) : normal_expr
  | nterm (e : expr) (n : expr × ℤ) (x : expr) (a : normal_expr) : normal_expr

unsafe def normal_expr.e : normal_expr → expr
  | normal_expr.zero e => e
  | normal_expr.nterm e _ _ _ => e

unsafe instance : Coe normal_expr expr :=
  ⟨normal_expr.e⟩

unsafe instance : CoeFun normal_expr fun _ => expr → expr :=
  ⟨fun e => ⇑(e : expr)⟩

unsafe def normal_expr.term' (c : context) (n : expr × ℤ) (x : expr) (a : normal_expr) : normal_expr :=
  normal_expr.nterm (c.mk_term n.1 x a) n x a

unsafe def normal_expr.zero' (c : context) : normal_expr :=
  normal_expr.zero c.α0

unsafe def normal_expr.to_list : normal_expr → List (ℤ × expr)
  | normal_expr.zero _ => []
  | normal_expr.nterm _ (_, n) x a => (n, x) :: a.toList

open NormalExpr

unsafe def normal_expr.to_string (e : normal_expr) : Stringₓ :=
  " + ".intercalate <| (to_list e).map fun ⟨n, e⟩ => toString n ++ " • (" ++ toString e ++ ")"

unsafe def normal_expr.pp (e : normal_expr) : tactic format := do
  let l ←
    (to_list e).mmap fun ⟨n, e⟩ => do
        let pe ← pp e
        return (to_fmt n ++ " • (" ++ pe ++ ")")
  return <| format.join <| l ↑" + "

unsafe instance : has_to_tactic_format normal_expr :=
  ⟨normal_expr.pp⟩

unsafe def normal_expr.refl_conv (e : normal_expr) : tactic (normal_expr × expr) := do
  let p ← mk_eq_refl e
  return (e, p)

theorem const_add_term {α} [AddCommMonoidₓ α] (k n x a a') (h : k + a = a') : k + @term α _ n x a = term n x a' := by
  simp [← h.symm, ← term] <;> ac_rfl

theorem const_add_termg {α} [AddCommGroupₓ α] (k n x a a') (h : k + a = a') : k + @termg α _ n x a = termg n x a' := by
  simp [← h.symm, ← termg] <;> ac_rfl

theorem term_add_const {α} [AddCommMonoidₓ α] (n x a k a') (h : a + k = a') : @term α _ n x a + k = term n x a' := by
  simp [← h.symm, ← term, ← add_assocₓ]

theorem term_add_constg {α} [AddCommGroupₓ α] (n x a k a') (h : a + k = a') : @termg α _ n x a + k = termg n x a' := by
  simp [← h.symm, ← termg, ← add_assocₓ]

theorem term_add_term {α} [AddCommMonoidₓ α] (n₁ x a₁ n₂ a₂ n' a') (h₁ : n₁ + n₂ = n') (h₂ : a₁ + a₂ = a') :
    @term α _ n₁ x a₁ + @term α _ n₂ x a₂ = term n' x a' := by
  simp [← h₁.symm, ← h₂.symm, ← term, ← add_nsmul] <;> ac_rfl

theorem term_add_termg {α} [AddCommGroupₓ α] (n₁ x a₁ n₂ a₂ n' a') (h₁ : n₁ + n₂ = n') (h₂ : a₁ + a₂ = a') :
    @termg α _ n₁ x a₁ + @termg α _ n₂ x a₂ = termg n' x a' := by
  simp [← h₁.symm, ← h₂.symm, ← termg, ← add_zsmul] <;> ac_rfl

theorem zero_term {α} [AddCommMonoidₓ α] (x a) : @term α _ 0 x a = a := by
  simp [← term, ← zero_nsmul, ← one_nsmul]

theorem zero_termg {α} [AddCommGroupₓ α] (x a) : @termg α _ 0 x a = a := by
  simp [← termg]

unsafe def eval_add (c : context) : normal_expr → normal_expr → tactic (normal_expr × expr)
  | zero _, e₂ => do
    let p ← mk_app `` zero_addₓ [e₂]
    return (e₂, p)
  | e₁, zero _ => do
    let p ← mk_app `` add_zeroₓ [e₁]
    return (e₁, p)
  | he₁@(nterm e₁ n₁ x₁ a₁), he₂@(nterm e₂ n₂ x₂ a₂) =>
    (do
        is_def_eq x₁ x₂ c
        let (n', h₁) ← mk_app `` Add.add [n₁.1, n₂.1] >>= norm_num.eval_field
        let (a', h₂) ← eval_add a₁ a₂
        let k := n₁.2 + n₂.2
        let p₁ := c.iapp `` term_add_term [n₁.1, x₁, a₁, n₂.1, a₂, n', a', h₁, h₂]
        if k = 0 then do
            let p ← mk_eq_trans p₁ (c `` zero_term [x₁, a'])
            return (a', p)
          else return (term' c (n', k) x₁ a', p₁)) <|>
      if expr.lex_lt x₁ x₂ then do
        let (a', h) ← eval_add a₁ he₂
        return (term' c n₁ x₁ a', c `` term_add_const [n₁.1, x₁, a₁, e₂, a', h])
      else do
        let (a', h) ← eval_add he₁ a₂
        return (term' c n₂ x₂ a', c `` const_add_term [e₁, n₂.1, x₂, a₂, a', h])

theorem term_neg {α} [AddCommGroupₓ α] (n x a n' a') (h₁ : -n = n') (h₂ : -a = a') :
    -@termg α _ n x a = termg n' x a' := by
  simp [← h₂.symm, ← h₁.symm, ← termg] <;> ac_rfl

unsafe def eval_neg (c : context) : normal_expr → tactic (normal_expr × expr)
  | zero e => do
    let p ← c.mk_app `` neg_zero `` SubtractionMonoid []
    return (zero' c, p)
  | nterm e n x a => do
    let (n', h₁) ← mk_app `` Neg.neg [n.1] >>= norm_num.eval_field
    let (a', h₂) ← eval_neg a
    return (term' c (n', -n.2) x a', c `` term_neg c [n.1, x, a, n', a', h₁, h₂])

def smul {α} [AddCommMonoidₓ α] (n : ℕ) (x : α) : α :=
  n • x

def smulg {α} [AddCommGroupₓ α] (n : ℤ) (x : α) : α :=
  n • x

theorem zero_smul {α} [AddCommMonoidₓ α] (c) : smul c (0 : α) = 0 := by
  simp [← smul, ← nsmul_zero]

theorem zero_smulg {α} [AddCommGroupₓ α] (c) : smulg c (0 : α) = 0 := by
  simp [← smulg, ← zsmul_zero]

theorem term_smul {α} [AddCommMonoidₓ α] (c n x a n' a') (h₁ : c * n = n') (h₂ : smul c a = a') :
    smul c (@term α _ n x a) = term n' x a' := by
  simp [← h₂.symm, ← h₁.symm, ← term, ← smul, ← nsmul_add, ← mul_nsmul]

theorem term_smulg {α} [AddCommGroupₓ α] (c n x a n' a') (h₁ : c * n = n') (h₂ : smulg c a = a') :
    smulg c (@termg α _ n x a) = termg n' x a' := by
  simp [← h₂.symm, ← h₁.symm, ← termg, ← smulg, ← zsmul_add, ← mul_zsmul]

unsafe def eval_smul (c : context) (k : expr × ℤ) : normal_expr → tactic (normal_expr × expr)
  | zero _ => return (zero' c, c.iapp `` zero_smul [k.1])
  | nterm e n x a => do
    let (n', h₁) ← mk_app `` Mul.mul [k.1, n.1] >>= norm_num.eval_field
    let (a', h₂) ← eval_smul a
    return (term' c (n', k.2 * n.2) x a', c `` term_smul [k.1, n.1, x, a, n', a', h₁, h₂])

theorem term_atom {α} [AddCommMonoidₓ α] (x : α) : x = term 1 x 0 := by
  simp [← term]

theorem term_atomg {α} [AddCommGroupₓ α] (x : α) : x = termg 1 x 0 := by
  simp [← termg]

unsafe def eval_atom (c : context) (e : expr) : tactic (normal_expr × expr) := do
  let n1 ← c.int_to_expr 1
  return (term' c (n1, 1) e (zero' c), c `` term_atom [e])

theorem unfold_sub {α} [SubtractionMonoid α] (a b c : α) (h : a + -b = c) : a - b = c := by
  rw [sub_eq_add_neg, h]

theorem unfold_smul {α} [AddCommMonoidₓ α] (n) (x y : α) (h : smul n x = y) : n • x = y :=
  h

theorem unfold_smulg {α} [AddCommGroupₓ α] (n : ℕ) (x y : α) (h : smulg (Int.ofNat n) x = y) : (n : ℤ) • x = y :=
  h

theorem unfold_zsmul {α} [AddCommGroupₓ α] (n : ℤ) (x y : α) (h : smulg n x = y) : n • x = y :=
  h

theorem subst_into_smul {α} [AddCommMonoidₓ α] (l r tl tr t) (prl : l = tl) (prr : r = tr) (prt : @smul α _ tl tr = t) :
    smul l r = t := by
  simp [← prl, ← prr, ← prt]

theorem subst_into_smulg {α} [AddCommGroupₓ α] (l r tl tr t) (prl : l = tl) (prr : r = tr)
    (prt : @smulg α _ tl tr = t) : smulg l r = t := by
  simp [← prl, ← prr, ← prt]

theorem subst_into_smul_upcast {α} [AddCommGroupₓ α] (l r tl zl tr t) (prl₁ : l = tl) (prl₂ : ↑tl = zl) (prr : r = tr)
    (prt : @smulg α _ zl tr = t) : smul l r = t := by
  simp [prt, ← prl₁, prl₂, ← prr, ← smul, ← smulg]

/-- Normalize a term `orig` of the form `smul e₁ e₂` or `smulg e₁ e₂`.
  Normalized terms use `smul` for monoids and `smulg` for groups,
  so there are actually four cases to handle:
  * Using `smul` in a monoid just simplifies the pieces using `subst_into_smul`
  * Using `smulg` in a group just simplifies the pieces using `subst_into_smulg`
  * Using `smul a b` in a group requires converting `a` from a nat to an int and
    then simplifying `smulg ↑a b` using `subst_into_smul_upcast`
  * Using `smulg` in a monoid is impossible (or at least out of scope),
    because you need a group argument to write a `smulg` term -/
unsafe def eval_smul' (c : context) (eval : expr → tactic (normal_expr × expr)) (is_smulg : Bool) (orig e₁ e₂ : expr) :
    tactic (normal_expr × expr) := do
  let (e₁', p₁) ← norm_num.derive e₁ <|> refl_conv e₁
  match if is_smulg then e₁' else coe <$> e₁' with
    | some n => do
      let (e₂', p₂) ← eval e₂
      if c = is_smulg then do
          let (e', p) ← eval_smul c (e₁', n) e₂'
          return (e', c `` subst_into_smul [e₁, e₂, e₁', e₂', e', p₁, p₂, p])
        else do
          guardb c
          let ic ← mk_instance_cache (quote.1 ℤ)
          let nc ← mk_instance_cache (quote.1 ℕ)
          let (ic, zl) ← ic n
          let (_, _, _, p₁') ← norm_num.prove_nat_uncast ic nc zl
          let (e', p) ← eval_smul c (zl, n) e₂'
          return (e', c `` subst_into_smul_upcast c [e₁, e₂, e₁', zl, e₂', e', p₁, p₁', p₂, p])
    | none => eval_atom c orig

unsafe def eval (c : context) : expr → tactic (normal_expr × expr)
  | quote.1 ((%%ₓe₁) + %%ₓe₂) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← eval_add c e₁' e₂'
    let p ← c.mk_app `` NormNum.subst_into_add `` Add [e₁, e₂, e₁', e₂', e', p₁, p₂, p']
    return (e', p)
  | quote.1 ((%%ₓe₁) - %%ₓe₂) => do
    let e₂' ← mk_app `` Neg.neg [e₂]
    let e ← mk_app `` Add.add [e₁, e₂']
    let (e', p) ← eval e
    let p' ← c.mk_app `` unfold_sub `` SubtractionMonoid [e₁, e₂, e', p]
    return (e', p')
  | quote.1 (-%%ₓe) => do
    let (e₁, p₁) ← eval e
    let (e₂, p₂) ← eval_neg c e₁
    let p ← c.mk_app `` NormNum.subst_into_neg `` Neg [e, e₁, e₂, p₁, p₂]
    return (e₂, p)
  | quote.1 (AddMonoidₓ.nsmul (%%ₓe₁) (%%ₓe₂)) => do
    let n ← if c.is_group then mk_app `` Int.ofNat [e₁] else return e₁
    let (e', p) ← eval <| c.iapp `` smul [n, e₂]
    return (e', c `` unfold_smul [e₁, e₂, e', p])
  | quote.1 (SubNegMonoidₓ.zsmul (%%ₓe₁) (%%ₓe₂)) => do
    guardb c
    let (e', p) ← eval <| c.iapp `` smul [e₁, e₂]
    return (e', c `` unfold_zsmul c [e₁, e₂, e', p])
  | e@(quote.1 (@HasSmul.smul Nat _ AddMonoidₓ.hasSmulNat (%%ₓe₁) (%%ₓe₂))) => eval_smul' c eval false e e₁ e₂
  | e@(quote.1 (@HasSmul.smul Int _ SubNegMonoidₓ.hasSmulInt (%%ₓe₁) (%%ₓe₂))) => eval_smul' c eval true e e₁ e₂
  | e@(quote.1 (smul (%%ₓe₁) (%%ₓe₂))) => eval_smul' c eval false e e₁ e₂
  | e@(quote.1 (smulg (%%ₓe₁) (%%ₓe₂))) => eval_smul' c eval true e e₁ e₂
  | e@(quote.1 (@Zero.zero _ _)) =>
    mcond (succeeds (is_def_eq e c.α0)) (mk_eq_refl c.α0 >>= fun p => pure (zero' c, p)) (eval_atom c e)
  | e => eval_atom c e

unsafe def eval' (c : context) (e : expr) : tactic (expr × expr) := do
  let (e', p) ← eval c e
  return (e', p)

inductive NormalizeMode
  | raw
  | term
  deriving has_reflect

instance : Inhabited NormalizeMode :=
  ⟨NormalizeMode.term⟩

unsafe def normalize (red : Transparency) (mode := NormalizeMode.term) (e : expr) : tactic (expr × expr) := do
  let pow_lemma ← simp_lemmas.mk.add_simp `` pow_oneₓ
  let lemmas :=
    match mode with
    | normalize_mode.term =>
      [`` term.equations._eqn_1, `` termg.equations._eqn_1, `` add_zeroₓ, `` one_nsmul, `` one_zsmul, `` zsmul_zero]
    | _ => []
  let lemmas ← lemmas.mfoldl simp_lemmas.add_simp simp_lemmas.mk
  let (_, e', pr) ←
    ext_simplify_core () {  } simp_lemmas.mk (fun _ => failed)
        (fun _ _ _ _ e => do
          let c ← mk_context red e
          let (new_e, pr) ←
            (match mode with
                | normalize_mode.raw => eval' c
                | normalize_mode.term =>
                  trans_conv (eval' c) fun e => do
                    let (e', prf, _) ← simplify lemmas [] e
                    return (e', prf))
                e
          guardₓ ¬expr.alpha_eqv new_e e
          return ((), new_e, some pr, ff))
        (fun _ _ _ _ _ => failed) `eq e
  return (e', pr)

end Abel

namespace Interactive

open Tactic.Abel

setup_tactic_parser

/-- Tactic for solving equations in the language of
*additive*, commutative monoids and groups.
This version of `abel` fails if the target is not an equality
that is provable by the axioms of commutative monoids/groups.

`abel1!` will use a more aggressive reducibility setting to identify atoms.
This can prove goals that `abel` cannot, but is more expensive.
-/
unsafe def abel1 (red : parse (tk "!")?) : tactic Unit := do
  let quote.1 ((%%ₓe₁) = %%ₓe₂) ← target
  let c ← mk_context (if red.isSome then semireducible else reducible) e₁
  let (e₁', p₁) ← eval c e₁
  let (e₂', p₂) ← eval c e₂
  is_def_eq e₁' e₂'
  let p ← mk_eq_symm p₂ >>= mk_eq_trans p₁
  tactic.exact p

unsafe def abel.mode : lean.parser Abel.NormalizeMode :=
  with_desc "(raw|term)?" <| do
    let mode ← ident ?
    match mode with
      | none => return abel.normalize_mode.term
      | some `term => return abel.normalize_mode.term
      | some `raw => return abel.normalize_mode.raw
      | _ => failed

/-- Evaluate expressions in the language of *additive*, commutative monoids and groups.
It attempts to prove the goal outright if there is no `at`
specifier and the target is an equality, but if this
fails, it falls back to rewriting all monoid expressions into a normal form.
If there is an `at` specifier, it rewrites the given target into a normal form.

`abel!` will use a more aggressive reducibility setting to identify atoms.
This can prove goals that `abel` cannot, but is more expensive.
```lean
example {α : Type*} {a b : α} [add_comm_monoid α] : a + (b + a) = a + a + b := by abel
example {α : Type*} {a b : α} [add_comm_group α] : (a + b) - ((b + a) + a) = -a := by abel
example {α : Type*} {a b : α} [add_comm_group α] (hyp : a + a - a = b - b) : a = 0 :=
by { abel at hyp, exact hyp }
example {α : Type*} {a b : α} [add_comm_group α] : (a + b) - (id a + b) = 0 := by abel!
```
-/
unsafe def abel (red : parse (tk "!")?) (SOP : parse abel.mode) (loc : parse location) : tactic Unit :=
  (match loc with
    | Interactive.Loc.ns [none] => abel1 red
    | _ => failed) <|>
    do
    let ns ← loc.get_locals
    let red := if red.isSome then semireducible else reducible
    let tt ← tactic.replace_at (normalize red SOP) ns loc.include_goal | fail "abel failed to simplify"
    when loc <| try tactic.reflexivity

add_tactic_doc
  { Name := "abel", category := DocCategory.tactic, declNames := [`tactic.interactive.abel],
    tags := ["arithmetic", "decision procedure"] }

end Interactive

end Tactic


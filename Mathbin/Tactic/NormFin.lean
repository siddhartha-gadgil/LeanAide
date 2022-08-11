/-
Copyright (c) 2021 Yakov Pechersky All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Mario Carneiro
-/
import Mathbin.Tactic.NormNum

/-!
# `norm_fin`

This file defines functions for dealing with `fin n` numbers as expressions.

## Main definitions

* `tactic.norm_fin.eval_ineq` is a `norm_num` plugin for normalizing equalities and inequalities of
  type `fin n`.

* `tactic.interactive.norm_fin` is a standalone tactic like `norm_num` for normalizing `fin n`
  expressions anywhere in the goal.

-/


namespace Tactic

namespace NormFin

open NormNum

/-- `normalize_fin n a b` means that `a : fin n` is equivalent to `b : ℕ` in the modular sense -
that is, `↑a ≡ b (mod n)`. This is used for translating the algebraic operations: addition,
multiplication, zero and one, which use modulo for reduction. -/
def NormalizeFin (n : ℕ) (a : Finₓ n) (b : ℕ) :=
  a.1 = b % n

/-- `normalize_fin_lt n a b` means that `a : fin n` is equivalent to `b : ℕ` in the embedding
sense - that is, `↑a = b`. This is used for operations that treat `fin n` as the subset
`{0, ..., n-1}` of `ℕ`. For example, `fin.succ : fin n → fin (n+1)` is thought of as the successor
function, but it does not lift to a map `zmod n → zmod (n+1)`; this addition only makes sense if
the input is strictly less than `n`.

`normalize_fin_lt n a b` is equivalent to `normalize_fin n a b ∧ b < n`. -/
def NormalizeFinLt (n : ℕ) (a : Finₓ n) (b : ℕ) :=
  a.1 = b

theorem NormalizeFinLt.coe {n} {a : Finₓ n} {b : ℕ} (h : NormalizeFinLt n a b) : ↑a = b :=
  h

theorem normalize_fin_iff {n} [Fact (0 < n)] {a b} : NormalizeFin n a b ↔ a = Finₓ.ofNat' b :=
  Iff.symm (Finₓ.eq_iff_veq _ _)

theorem NormalizeFinLt.mk {n a b n'} (hn : n = n') (h : NormalizeFin n a b) (h2 : b < n') : NormalizeFinLt n a b :=
  h.trans <|
    Nat.mod_eq_of_ltₓ <| by
      rw [hn] <;> exact h2

theorem NormalizeFinLt.lt {n a b} (h : NormalizeFinLt n a b) : b < n := by
  rw [← h.coe] <;> exact a.2

theorem NormalizeFinLt.of {n a b} (h : NormalizeFinLt n a b) : NormalizeFin n a b :=
  h.trans <| Eq.symm <| Nat.mod_eq_of_ltₓ h.lt

theorem NormalizeFin.zero (n) : NormalizeFin (n + 1) 0 0 := by
  rw [normalize_fin]
  norm_num

theorem NormalizeFinLt.zero (n) : NormalizeFinLt (n + 1) 0 0 :=
  refl _

theorem NormalizeFin.one (n) : NormalizeFin (n + 1) 1 1 :=
  refl _

theorem NormalizeFin.add {n} {a b : Finₓ n} {a' b' c' : ℕ} (ha : NormalizeFin n a a') (hb : NormalizeFin n b b')
    (h : a' + b' = c') : NormalizeFin n (a + b) c' := by
  simp only [← normalize_fin, h] at * <;> rw [Nat.add_modₓ, ← ha, ← hb, Finₓ.add_def]

theorem NormalizeFin.mul {n} {a b : Finₓ n} {a' b' c' : ℕ} (ha : NormalizeFin n a a') (hb : NormalizeFin n b b')
    (h : a' * b' = c') : NormalizeFin n (a * b) c' := by
  simp only [← normalize_fin, h] at * <;> rw [Nat.mul_modₓ, ← ha, ← hb, Finₓ.mul_def]

theorem NormalizeFin.bit0 {n} {a : Finₓ n} {a' : ℕ} (h : NormalizeFin n a a') : NormalizeFin n (bit0 a) (bit0 a') :=
  h.add h rfl

theorem NormalizeFin.bit1 {n} {a : Finₓ (n + 1)} {a' : ℕ} (h : NormalizeFin (n + 1) a a') :
    NormalizeFin (n + 1) (bit1 a) (bit1 a') :=
  h.bit0.add (NormalizeFin.one _) rfl

theorem NormalizeFinLt.succ {n} {a : Finₓ n} {a' b : ℕ} (h : NormalizeFinLt n a a') (e : a' + 1 = b) :
    NormalizeFinLt n.succ (Finₓ.succ a) b := by
  simpa [← normalize_fin_lt, e] using h

theorem NormalizeFinLt.cast_lt {n m} {a : Finₓ m} {ha} {a' : ℕ} (h : NormalizeFinLt m a a') :
    NormalizeFinLt n (Finₓ.castLt a ha) a' := by
  simpa [← normalize_fin_lt] using h

theorem NormalizeFinLt.cast_le {n m} {nm} {a : Finₓ m} {a' : ℕ} (h : NormalizeFinLt m a a') :
    NormalizeFinLt n (Finₓ.castLe nm a) a' := by
  simpa [← normalize_fin_lt] using h

theorem NormalizeFinLt.cast {n m} {nm} {a : Finₓ m} {a' : ℕ} (h : NormalizeFinLt m a a') :
    NormalizeFinLt n (Finₓ.cast nm a) a' := by
  simpa [← normalize_fin_lt] using h

theorem NormalizeFin.cast {n m} {nm} {a : Finₓ m} {a' : ℕ} (h : NormalizeFin m a a') :
    NormalizeFin n (Finₓ.cast nm a) a' := by
  convert ← normalize_fin_lt.cast h

theorem NormalizeFinLt.cast_add {n m} {a : Finₓ n} {a' : ℕ} (h : NormalizeFinLt n a a') :
    NormalizeFinLt (n + m) (Finₓ.castAdd m a) a' := by
  simpa [← normalize_fin_lt] using h

theorem NormalizeFinLt.cast_succ {n} {a : Finₓ n} {a' : ℕ} (h : NormalizeFinLt n a a') :
    NormalizeFinLt (n + 1) (Finₓ.castSucc a) a' :=
  NormalizeFinLt.cast_add h

theorem NormalizeFinLt.add_nat {n m m'} (hm : m = m') {a : Finₓ n} {a' b : ℕ} (h : NormalizeFinLt n a a')
    (e : a' + m' = b) : NormalizeFinLt (n + m) (@Finₓ.addNat n m a) b := by
  simpa [← normalize_fin_lt, e, hm] using h

theorem NormalizeFinLt.nat_add {n m n'} (hn : n = n') {a : Finₓ m} {a' b : ℕ} (h : NormalizeFinLt m a a')
    (e : n' + a' = b) : NormalizeFinLt (n + m) (@Finₓ.natAdd n m a) b := by
  simpa [← normalize_fin_lt, e, hn] using h

theorem NormalizeFin.reduce {n} {a : Finₓ n} {n' a' b k nk : ℕ} (hn : n = n') (h : NormalizeFin n a a')
    (e1 : n' * k = nk) (e2 : nk + b = a') : NormalizeFin n a b := by
  rwa [← e2, ← e1, ← hn, normalize_fin, add_commₓ, Nat.add_mul_mod_self_leftₓ] at h

theorem NormalizeFinLt.reduce {n} {a : Finₓ n} {n' a' b k nk : ℕ} (hn : n = n') (h : NormalizeFin n a a')
    (e1 : n' * k = nk) (e2 : nk + b = a') (hl : b < n') : NormalizeFinLt n a b :=
  NormalizeFinLt.mk hn (h.reduce hn e1 e2) hl

theorem NormalizeFin.eq {n} {a b : Finₓ n} {c : ℕ} (ha : NormalizeFin n a c) (hb : NormalizeFin n b c) : a = b :=
  Finₓ.eq_of_veq <| ha.trans hb.symm

theorem NormalizeFin.lt {n} {a b : Finₓ n} {a' b' : ℕ} (ha : NormalizeFin n a a') (hb : NormalizeFinLt n b b')
    (h : a' < b') : a < b := by
  have ha' := normalize_fin_lt.mk rfl ha (h.trans hb.lt) <;> rwa [← hb.coe, ← ha'.coe] at h

theorem NormalizeFin.le {n} {a b : Finₓ n} {a' b' : ℕ} (ha : NormalizeFin n a a') (hb : NormalizeFinLt n b b')
    (h : a' ≤ b') : a ≤ b := by
  have ha' := normalize_fin_lt.mk rfl ha (h.trans_lt hb.lt) <;> rwa [← hb.coe, ← ha'.coe] at h

/-- The monad for the `norm_fin` internal tactics. The state consists of an instance cache for `ℕ`,
and a tuple `(nn, n', p)` where `p` is a proof of `n = n'` and `nn` is `n` evaluated to a natural
number. (`n` itself is implicit.)  It is in an `option` because it is lazily initialized - for many
`n` we will never need this information, and indeed eagerly computing it would make some reductions
fail spuriously if `n` is not a numeral. -/
unsafe def eval_fin_m (α : Type) : Type :=
  StateTₓ (instance_cache × Option (ℕ × expr × expr)) tactic α deriving Monadₓ, Alternativeₓ

/-- Lifts a tactic into the `eval_fin_m` monad. -/
@[inline]
unsafe def eval_fin_m.lift {α} (m : tactic α) : eval_fin_m α :=
  ⟨fun ⟨ic, r⟩ => do
    let a ← m
    pure (a, ic, r)⟩

unsafe instance {α} : Coe (tactic α) (eval_fin_m α) :=
  ⟨eval_fin_m.lift⟩

/-- Lifts an `instance_cache` tactic into the `eval_fin_m` monad. -/
@[inline]
unsafe def eval_fin_m.lift_ic {α} (m : instance_cache → tactic (instance_cache × α)) : eval_fin_m α :=
  ⟨fun ⟨ic, r⟩ => do
    let (ic, a) ← m ic
    pure (a, ic, r)⟩

/-- Evaluates a monadic action with a fresh `n` cache, and restore the old cache on completion of
the action. This is used when evaluating a tactic in the context of a different `n` than the parent
context. For example if we are evaluating `fin.succ a`, then `a : fin n` and
`fin.succ a : fin (n+1)`, so the parent cache will be about `n+1` and we need a separate cache for
`n`. -/
@[inline]
unsafe def eval_fin_m.reset {α} (m : eval_fin_m α) : eval_fin_m α :=
  ⟨fun ⟨ic, r⟩ => do
    let (a, ic, _) ← m.run ⟨ic, none⟩
    pure (a, ic, r)⟩

/-- Given `n`, returns a tuple `(nn, n', p)` where `p` is a proof of `n = n'` and `nn` is `n`
evaluated to a natural number. The result of the evaluation is cached for future references.
Future calls to this function must use the same value of `n`, unless it is in a sub-context
created by `eval_fin_m.reset`. -/
unsafe def eval_fin_m.eval_n (n : expr) : eval_fin_m (ℕ × expr × expr) :=
  ⟨fun ⟨ic, r⟩ =>
    match r with
    | none => do
      let (n', p) ← or_refl_conv norm_num.derive n
      let nn ← n'.toNat
      let np := (nn, n', p)
      pure (np, ic, some np)
    | some np => pure (np, ic, some np)⟩

/-- Run an `eval_fin_m` action with a new cache and discard the cache after evaluation. -/
@[inline]
unsafe def eval_fin_m.run {α} (m : eval_fin_m α) : tactic α := do
  let ic ← mk_instance_cache (quote.1 ℕ)
  let (a, _) ← StateTₓ.run m (ic, none)
  pure a

/-- The expression constructors recognized by the `eval_fin` evaluator. This is used instead of a
direct expr pattern match because expr pattern matches generate very large terms under the
hood so going via an intermediate inductive type like this is more efficient. -/
unsafe inductive match_fin_result
  | zero (n : expr)-- `(0 : fin (n+1))`

  | one (n : expr)-- `(1 : fin (n+1))`

  | add (n a b : expr)-- `(a + b : fin n)`

  | mul (n a b : expr)-- `(a * b : fin n)`

  | bit0 (n a : expr)-- `(bit0 a : fin n)`

  | bit1 (n a : expr)-- `(bit1 a : fin (n+1))`

  | succ (n a : expr)-- `(fin.succ a : fin n.succ)`

  | cast_lt (n m i h : expr)-- `(fin.cast_lt (i : fin m) (h : i.val < n) : fin n)`

  | cast_le (n m h a : expr)-- `(fin.cast_le (h : n ≤ m) (a : fin n) : fin m)`

  | cast (n m h a : expr)-- `(fin.cast_le (h : n = m) (a : fin n) : fin m)`

  | cast_add (n m a : expr)-- `(fin.cast_add m (a : fin n) : fin (n + m))`

  | cast_succ (n a : expr)-- `(fin.cast_succ (a : fin n) : fin (n + 1))`

  | add_nat (n m a : expr)-- `(fin.add_nat m (a : fin n) : fin (n + m))`

  | nat_add (n m a : expr)

-- `(fin.nat_add n (a : fin m) : fin (n + m))`
section

open MatchFinResult

/-- Match a fin expression of the form `(coe_fn f a)` where `f` is some fin function. Several fin
functions are written this way: for example `cast_le : n ≤ m → fin n ↪o fin m` is not actually a
function but rather an order embedding with a coercion to a function. -/
unsafe def match_fin_coe_fn (a : expr) : expr → Option match_fin_result
  | quote.1 (@Finₓ.castLe (%%ₓn) (%%ₓm) (%%ₓh)) => some (cast_le n m h a)
  | quote.1 (@Finₓ.cast (%%ₓm) (%%ₓn) (%%ₓh)) => some (cast n m h a)
  | quote.1 (@Finₓ.castAdd (%%ₓn) (%%ₓm)) => some (cast_add n m a)
  | quote.1 (@Finₓ.castSucc (%%ₓn)) => some (cast_succ n a)
  | quote.1 (@Finₓ.addNat (%%ₓn) (%%ₓm)) => some (add_nat n m a)
  | quote.1 (@Finₓ.natAdd (%%ₓn) (%%ₓm)) => some (nat_add n m a)
  | _ => none

/-- Match a fin expression to a `match_fin_result`, for easier pattern matching in the
evaluator. -/
unsafe def match_fin : expr → Option match_fin_result
  | quote.1 (@Zero.zero _ (@Finₓ.hasZero (%%ₓn))) => some (zero n)
  | quote.1 (@One.one _ (@Finₓ.hasOne (%%ₓn))) => some (one n)
  | quote.1 (@Add.add (Finₓ (%%ₓn)) _ (%%ₓa) (%%ₓb)) => some (add n a b)
  | quote.1 (@Mul.mul (Finₓ (%%ₓn)) _ (%%ₓa) (%%ₓb)) => some (mul n a b)
  | quote.1 (@bit0 (Finₓ (%%ₓn)) _ (%%ₓa)) => some (bit0 n a)
  | quote.1 (@bit1 _ (@Finₓ.hasOne (%%ₓn)) _ (%%ₓa)) => some (bit1 n a)
  | quote.1 (@Finₓ.succ (%%ₓn) (%%ₓa)) => some (succ n a)
  | quote.1 (@Finₓ.castLt (%%ₓn) (%%ₓm) (%%ₓa) (%%ₓh)) => some (cast_lt n m a h)
  | expr.app (quote.1 (@coeFn _ _ _ (%%ₓf))) a => match_fin_coe_fn a f
  | _ => none

end

/-- `reduce_fin lt n a (a', pa)` expects that `pa : normalize_fin n a a'` where `a'`
is a natural numeral, and produces `(b, pb)` where `pb : normalize_fin n a b` if `lt` is false, or
`pb : normalize_fin_lt n a b` if `lt` is true. In either case, `b` will be chosen to be less than
`n`, but if `lt` is true then we also prove it. This requires that `n` can be evaluated to a
numeral. -/
unsafe def reduce_fin' : Bool → expr → expr → expr × expr → eval_fin_m (expr × expr)
  | lt, n, a, (a', pa) => do
    let (nn, n', pn) ← eval_fin_m.eval_n n
    let na ← expr.to_nat a'
    if na < nn then
        if lt then do
          let p ← eval_fin_m.lift_ic fun ic => prove_lt_nat ic a' n'
          pure (a', (quote.1 @NormalizeFinLt.mk).mk_app [n, a, a', n', pn, pa, p])
        else pure (a', pa)
      else
        let nb := na % nn
        let nk := (na - nb) / nn
        eval_fin_m.lift_ic fun ic => do
          let (ic, k) ← ic nk
          let (ic, b) ← ic nb
          let (ic, nk, pe1) ← prove_mul_nat ic n' k
          let (ic, pe2) ← prove_add_nat ic nk b a'
          if lt then do
              let (ic, p) ← prove_lt_nat ic b n'
              pure (ic, b, (quote.1 @NormalizeFinLt.reduce).mk_app [n, a, n', a', b, k, nk, pn, pa, pe1, pe2, p])
            else pure (ic, b, (quote.1 @NormalizeFin.reduce).mk_app [n, a, n', a', b, k, nk, pn, pa, pe1, pe2])

/-- `eval_fin_lt' eval_fin n a` expects that `a : fin n`, and produces `(b, p)` where
`p : normalize_fin_lt n a b`. (It is mutually recursive with `eval_fin` which is why it takes the
function as an argument.) -/
unsafe def eval_fin_lt' (eval_fin : expr → eval_fin_m (expr × expr)) : expr → expr → eval_fin_m (expr × expr)
  | n, a => do
    let e ← match_fin a
    match e with
      | match_fin_result.succ n a => do
        let (a', pa) ← (eval_fin_lt' n a).reset
        let (b, pb) ← eval_fin_m.lift_ic fun ic => prove_succ' ic a'
        pure (b, (quote.1 @NormalizeFinLt.succ).mk_app [n, a, a', b, pa, pb])
      | match_fin_result.cast_lt _ m a h => do
        let (a', pa) ← (eval_fin_lt' m a).reset
        pure (a', (quote.1 @NormalizeFinLt.cast_lt).mk_app [n, m, a, h, a', pa])
      | match_fin_result.cast_le _ m nm a => do
        let (a', pa) ← (eval_fin_lt' m a).reset
        pure (a', (quote.1 @NormalizeFinLt.cast_le).mk_app [n, m, nm, a, a', pa])
      | match_fin_result.cast m _ nm a => do
        let (a', pa) ← (eval_fin_lt' m a).reset
        pure (a', (quote.1 @NormalizeFinLt.cast).mk_app [n, m, nm, a, a', pa])
      | match_fin_result.cast_add n m a => do
        let (a', pa) ← (eval_fin_lt' m a).reset
        pure (a', (quote.1 @NormalizeFinLt.cast_add).mk_app [n, m, a, a', pa])
      | match_fin_result.cast_succ n a => do
        let (a', pa) ← (eval_fin_lt' n a).reset
        pure (a', (quote.1 @NormalizeFinLt.cast_succ).mk_app [n, a, a', pa])
      | match_fin_result.add_nat n m a => do
        let (a', pa) ← (eval_fin_lt' n a).reset
        let (m', pm) ← or_refl_conv norm_num.derive m
        let (b, pb) ← eval_fin_m.lift_ic fun ic => prove_add_nat' ic a' m'
        pure (b, (quote.1 @NormalizeFinLt.add_nat).mk_app [n, m, m', pm, a, a', b, pa, pb])
      | match_fin_result.nat_add n m a => do
        let (a', pa) ← (eval_fin_lt' m a).reset
        let (n', pn) ← or_refl_conv norm_num.derive n
        let (b, pb) ← eval_fin_m.lift_ic fun ic => prove_add_nat' ic n' a'
        pure (b, (quote.1 @NormalizeFinLt.nat_add).mk_app [n, m, n', pn, a, a', b, pa, pb])
      | _ => do
        let (_, n', pn) ← eval_fin_m.eval_n n
        let (a', pa) ← eval_fin a >>= reduce_fin' tt n a
        let p ← eval_fin_m.lift_ic fun ic => prove_lt_nat ic a' n'
        pure (a', (quote.1 @NormalizeFinLt.mk).mk_app [n, a, a', n', pn, pa, p])

/-- Get `n` such that `a : fin n`. -/
unsafe def get_fin_type (a : expr) : tactic expr := do
  let quote.1 (Finₓ (%%ₓn)) ← infer_type a
  pure n

/-- Given `a : fin n`, `eval_fin a` returns `(b, p)` where `p : normalize_fin n a b`. This function
does no reduction of the numeral `b`; for example `eval_fin (5 + 5 : fin 6)` returns `10`. It works
even if `n` is a variable, for example `eval_fin (5 + 5 : fin (n+1))` also returns `10`. -/
unsafe def eval_fin : expr → eval_fin_m (expr × expr)
  | a => do
    let m ← match_fin a
    match m with
      | match_fin_result.zero n => pure (quote.1 (0 : ℕ), (quote.1 NormalizeFin.zero).mk_app [n])
      | match_fin_result.one n => pure (quote.1 (1 : ℕ), (quote.1 NormalizeFin.one).mk_app [n])
      | match_fin_result.add n a b => do
        let (a', pa) ← eval_fin a
        let (b', pb) ← eval_fin b
        let (c, pc) ← eval_fin_m.lift_ic fun ic => prove_add_nat' ic a' b'
        pure (c, (quote.1 @NormalizeFin.add).mk_app [n, a, b, a', b', c, pa, pb, pc])
      | match_fin_result.mul n a b => do
        let (a', pa) ← eval_fin a
        let (b', pb) ← eval_fin b
        let (c, pc) ← eval_fin_m.lift_ic fun ic => prove_mul_nat ic a' b'
        pure (c, (quote.1 @NormalizeFin.mul).mk_app [n, a, b, a', b', c, pa, pb, pc])
      | match_fin_result.bit0 n a => do
        let (a', pa) ← eval_fin a
        pure ((quote.1 (@bit0 ℕ _)).mk_app [a'], (quote.1 @NormalizeFin.bit0).mk_app [n, a, a', pa])
      | match_fin_result.bit1 n a => do
        let (a', pa) ← eval_fin a
        pure ((quote.1 (@bit1 ℕ _ _)).mk_app [a'], (quote.1 @NormalizeFin.bit1).mk_app [n, a, a', pa])
      | match_fin_result.cast m n nm a => do
        let (a', pa) ← (eval_fin a).reset
        pure (a', (quote.1 @NormalizeFin.cast).mk_app [n, m, nm, a, a', pa])
      | _ => do
        let n ← get_fin_type a
        let (a', pa) ← eval_fin_lt' eval_fin n a
        pure (a', (quote.1 @NormalizeFinLt.of).mk_app [n, a, a', pa])

/-- `eval_fin_lt n a` expects that `a : fin n`, and produces `(b, p)` where
`p : normalize_fin_lt n a b`. -/
unsafe def eval_fin_lt : expr → expr → eval_fin_m (expr × expr) :=
  eval_fin_lt' eval_fin

/-- Given `a : fin n`, `eval_fin ff n a` returns `(b, p)` where `p : normalize_fin n a b`, and
`eval_fin tt n a` returns `p : normalize_fin_lt n a b`. Unlike `eval_fin`, this also does reduction
of the numeral `b`; for example `reduce_fin ff 6 (5 + 5 : fin 6)` returns `4`. As a result, it
fails if `n` is a variable, for example `reduce_fin ff (n+1) (5 + 5 : fin (n+1))` fails. -/
unsafe def reduce_fin (lt : Bool) (n a : expr) : eval_fin_m (expr × expr) :=
  eval_fin a >>= reduce_fin' lt n a

/-- If `a b : fin n` and `a'` and `b'` are as returned by `eval_fin`,
then `prove_lt_fin' n a b a' b'` proves `a < b`. -/
unsafe def prove_lt_fin' : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr
  | n, a, b, a', b' => do
    let (a', pa) ← reduce_fin' false n a a'
    let (b', pb) ← reduce_fin' true n b b'
    let p ← eval_fin_m.lift_ic fun ic => prove_lt_nat ic a' b'
    pure ((quote.1 @NormalizeFin.lt).mk_app [n, a, b, a', b', pa, pb, p])

/-- If `a b : fin n` and `a'` and `b'` are as returned by `eval_fin`,
then `prove_le_fin' n a b a' b'` proves `a ≤ b`. -/
unsafe def prove_le_fin' : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr
  | n, a, b, a', b' => do
    let (a', pa) ← reduce_fin' false n a a'
    let (b', pb) ← reduce_fin' true n b b'
    let p ← eval_fin_m.lift_ic fun ic => prove_le_nat ic a' b'
    pure ((quote.1 @NormalizeFin.le).mk_app [n, a, b, a', b', pa, pb, p])

/-- If `a b : fin n` and `a'` and `b'` are as returned by `eval_fin`,
then `prove_eq_fin' n a b a' b'` proves `a = b`. -/
unsafe def prove_eq_fin' : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr
  | n, a, b, (a', pa), (b', pb) =>
    if expr.alpha_eqv a' b' then do
      pure ((quote.1 @NormalizeFin.eq).mk_app [n, a, b, a', pa, pb])
    else do
      let (a', pa) ← reduce_fin' false n a (a', pa)
      let (b', pb) ← reduce_fin' false n b (b', pb)
      guardₓ (expr.alpha_eqv a' b')
      pure ((quote.1 @NormalizeFin.eq).mk_app [n, a, b, a', pa, pb])

/-- Given a function with the type of `prove_eq_fin'`, evaluates it with the given `a` and `b`. -/
unsafe def eval_prove_fin (f : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr) (a b : expr) :
    tactic expr := do
  let n ← get_fin_type a
  eval_fin_m.run <| eval_fin a >>= fun a' => eval_fin b >>= f n a b a'

/-- If `a b : fin n`, then `prove_eq_fin a b` proves `a = b`. -/
unsafe def prove_eq_fin : expr → expr → tactic expr :=
  eval_prove_fin prove_eq_fin'

/-- If `a b : fin n`, then `prove_lt_fin a b` proves `a < b`. -/
unsafe def prove_lt_fin : expr → expr → tactic expr :=
  eval_prove_fin prove_lt_fin'

/-- If `a b : fin n`, then `prove_le_fin a b` proves `a ≤ b`. -/
unsafe def prove_le_fin : expr → expr → tactic expr :=
  eval_prove_fin prove_le_fin'

section

open NormNum.MatchNumeralResult

/-- Given expressions `n` and `m` such that `n` is definitionally equal to `m.succ`, and
a natural numeral `a`, proves `(b, ⊢ normalize_fin n b a)`, where `n` and `m` are both used
in the construction of the numeral `b : fin n`. -/
unsafe def mk_fin_numeral (n m : expr) : expr → Option (expr × expr)
  | a =>
    match match_numeral a with
    | zero =>
      some
        (expr.app (quote.1 (@Zero.zero (Finₓ (%%ₓn)))) (quote.1 (@Finₓ.hasZero (%%ₓm))),
          expr.app (quote.1 NormalizeFin.zero) m)
    | one =>
      some
        (expr.app (quote.1 (@One.one (Finₓ (%%ₓn)))) (quote.1 (@Finₓ.hasOne (%%ₓm))),
          expr.app (quote.1 NormalizeFin.one) m)
    | bit0 a => do
      let (a', p) ← mk_fin_numeral a
      some (quote.1 (bit0 (%%ₓa') : Finₓ (%%ₓn)), (quote.1 @NormalizeFin.bit0).mk_app [n, a', a, p])
    | bit1 a => do
      let (a', p) ← mk_fin_numeral a
      some
          ((quote.1 (@bit1 (Finₓ (%%ₓn)))).mk_app [quote.1 (@Finₓ.hasOne (%%ₓm)), quote.1 (@Finₓ.hasAdd (%%ₓn)), a'],
            (quote.1 @NormalizeFin.bit1).mk_app [m, a', a, p])
    | _ => none

end

/-- The common prep work for the cases in `eval_ineq`. Given inputs `a b : fin n`, it calls
`f n a' b' na nb` where `a'` and `b'` are the result of `eval_fin` and `na` and `nb` are
`a' % n` and `b' % n` as natural numbers. -/
unsafe def eval_rel {α} (a b : expr) (f : expr → expr × expr → expr × expr → ℕ → ℕ → eval_fin_m α) : tactic α := do
  let n ← get_fin_type a
  eval_fin_m.run <| do
      let (nn, n', pn) ← eval_fin_m.eval_n n
      let (a', pa) ← eval_fin a
      let (b', pb) ← eval_fin b
      let na ← eval_fin_m.lift a'
      let nb ← eval_fin_m.lift b'
      f n (a', pa) (b', pb) (na % nn) (nb % nn)

/-- Given `a b : fin n`, proves either `(n, tt, p)` where `p : a < b` or
`(n, ff, p)` where `p : b ≤ a`. -/
unsafe def prove_lt_ge_fin : expr → expr → tactic (expr × Bool × expr)
  | a, b =>
    (eval_rel a b) fun n a' b' na nb =>
      if na < nb then Prod.mk n <$> Prod.mk true <$> prove_lt_fin' n a b a' b'
      else Prod.mk n <$> Prod.mk false <$> prove_le_fin' n b a b' a'

/-- Given `a b : fin n`, proves either `(n, tt, p)` where `p : a = b` or
`(n, ff, p)` where `p : a ≠ b`. -/
unsafe def prove_eq_ne_fin : expr → expr → tactic (expr × Bool × expr)
  | a, b =>
    (eval_rel a b) fun n a' b' na nb =>
      if na = nb then Prod.mk n <$> Prod.mk true <$> prove_eq_fin' n a b a' b'
      else
        if na < nb then do
          let p ← prove_lt_fin' n a b a' b'
          pure (n, ff, (quote.1 (@ne_of_ltₓ (Finₓ (%%ₓn)) _)).mk_app [a, b, p])
        else do
          let p ← prove_lt_fin' n b a b' a'
          pure (n, ff, (quote.1 (@ne_of_gtₓ (Finₓ (%%ₓn)) _)).mk_app [a, b, p])

/-- A `norm_num` extension that evaluates equalities and inequalities on the type `fin n`.

```
example : (5 : fin 7) = fin.succ (fin.succ 3) := by norm_num
```
-/
@[norm_num]
unsafe def eval_ineq : expr → tactic (expr × expr)
  | quote.1 ((%%ₓa) < %%ₓb) => do
    let (n, lt, p) ← prove_lt_ge_fin a b
    if lt then true_intro p else false_intro ((quote.1 (@not_lt_of_geₓ (Finₓ (%%ₓn)) _)).mk_app [a, b, p])
  | quote.1 ((%%ₓa) ≤ %%ₓb) => do
    let (n, lt, p) ← prove_lt_ge_fin b a
    if lt then false_intro ((quote.1 (@not_le_of_gtₓ (Finₓ (%%ₓn)) _)).mk_app [a, b, p]) else true_intro p
  | quote.1 ((%%ₓa) = %%ₓb) => do
    let (n, Eq, p) ← prove_eq_ne_fin a b
    if Eq then true_intro p else false_intro p
  | quote.1 ((%%ₓa) > %%ₓb) => mk_app `` LT.lt [b, a] >>= eval_ineq
  | quote.1 ((%%ₓa) ≥ %%ₓb) => mk_app `` LE.le [b, a] >>= eval_ineq
  | quote.1 ((%%ₓa) ≠ %%ₓb) => do
    let (n, Eq, p) ← prove_eq_ne_fin a b
    if Eq then false_intro (quote.1 (not_not_intro (%%ₓp : (%%ₓa : Finₓ (%%ₓn)) = %%ₓb))) else true_intro p
  | _ => failed

/-- Evaluates `e : fin n` to a natural number less than `n`. Returns `none` if it is not a natural
number or greater than `n`. -/
unsafe def as_numeral (n e : expr) : eval_fin_m (Option ℕ) :=
  match e.toNat with
  | none => pure none
  | some Ne => do
    let (nn, _) ← eval_fin_m.eval_n n
    pure <| if Ne < nn then some Ne else none

/-- Given `a : fin n`, returns `(b, ⊢ a = b)` where `b` is a normalized fin numeral. Fails if `a`
is already normalized. -/
unsafe def eval_fin_num (a : expr) : tactic (expr × expr) := do
  let n ← get_fin_type a
  eval_fin_m.run <| do
      as_numeral n a >>= fun o => guardb o
      let (a', pa) ← eval_fin a
      let (a', pa) ← reduce_fin' ff n a (a', pa) <|> pure (a', pa)
      let (nm + 1, _) ← eval_fin_m.eval_n n | failure
      let m' ← eval_fin_m.lift_ic fun ic => ic nm
      let n' ← eval_fin_m.lift_ic fun ic => ic (nm + 1)
      let (b, pb) ← mk_fin_numeral n' m' a'
      pure (b, (quote.1 @NormalizeFin.eq).mk_app [n, a, b, a', pa, pb])

end NormFin

namespace Interactive

setup_tactic_parser

/-- Rewrites occurrences of fin expressions to normal form anywhere in the goal.
The `norm_num` extension will only rewrite fin expressions if they appear in equalities and
inequalities. For example if the goal is `P (2 + 2 : fin 3)` then `norm_num` will not do anything
but `norm_fin` will reduce the goal to `P 1`.

(The reason this is not part of `norm_num` is because evaluation of fin numerals uses a top down
evaluation strategy while `norm_num` works bottom up; also determining whether a normalization
will work is expensive, meaning that unrelated uses of `norm_num` would be slowed down with this
as a plugin.) -/
unsafe def norm_fin (hs : parse simp_arg_list) : tactic Unit :=
  try (simp_top_down tactic.norm_fin.eval_fin_num) >> try (norm_num hs (Loc.ns [none]))

/-- Rewrites occurrences of fin expressions to normal form anywhere in the goal.
The `norm_num` extension will only rewrite fin expressions if they appear in equalities and
inequalities. For example if the goal is `P (2 + 2 : fin 3)` then `norm_num` will not do anything
but `norm_fin` will reduce the goal to `P 1`.

```lean
example : (5 : fin 7) = fin.succ (fin.succ 3) := by norm_num
example (P : fin 7 → Prop) (h : P 5) : P (fin.succ (fin.succ 3)) := by norm_fin; exact h
```
-/
add_tactic_doc
  { Name := "norm_fin", category := DocCategory.tactic, declNames := [`tactic.interactive.norm_fin],
    tags := ["arithmetic", "decision procedure"] }

end Interactive

end Tactic


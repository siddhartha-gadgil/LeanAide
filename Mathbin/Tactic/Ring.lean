/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Tactic.NormNum

/-!
# `ring`

Evaluate expressions in the language of commutative (semi)rings.
Based on <http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf> .
-/


namespace Tactic

namespace Ringₓ

/-- The normal form that `ring` uses is mediated by the function `horner a x n b := a * x ^ n + b`.
The reason we use a definition rather than the (more readable) expression on the right is because
this expression contains a number of typeclass arguments in different positions, while `horner`
contains only one `comm_semiring` instance at the top level. See also `horner_expr` for a
description of normal form. -/
def hornerₓ {α} [CommSemiringₓ α] (a x : α) (n : ℕ) (b : α) :=
  a * x ^ n + b

/-- This cache contains data required by the `ring` tactic during execution. -/
unsafe structure cache where
  α : expr
  Univ : level
  comm_semiring_inst : expr
  red : Transparency
  ic : ref instance_cache
  nc : ref instance_cache
  atoms : ref (Buffer expr)

/-- The monad that `ring` works in. This is a reader monad containing a mutable cache (using `ref`
for mutability), as well as the list of atoms-up-to-defeq encountered thus far, used for atom
sorting. -/
unsafe def ring_m (α : Type) : Type :=
  ReaderTₓ cache tactic α deriving Monadₓ, Alternativeₓ

/-- Get the `ring` data from the monad. -/
unsafe def get_cache : ring_m cache :=
  ReaderTₓ.read

/-- Get an already encountered atom by its index. -/
unsafe def get_atom (n : ℕ) : ring_m expr :=
  ⟨fun c => do
    let es ← read_ref c.atoms
    pure (es n)⟩

/-- Get the index corresponding to an atomic expression, if it has already been encountered, or
put it in the list of atoms and return the new index, otherwise. -/
unsafe def add_atom (e : expr) : ring_m ℕ :=
  ⟨fun c => do
    let red := c.red
    let es ← read_ref c.atoms
    (es failed fun n e' t => t <|> is_def_eq e e' red $> n) <|> es <$ write_ref c (es e)⟩

/-- Lift a tactic into the `ring_m` monad. -/
@[inline]
unsafe def lift {α} (m : tactic α) : ring_m α :=
  ReaderTₓ.lift m

/-- Run a `ring_m` tactic in the tactic monad. This version of `ring_m.run` uses an external
atoms ref, so that subexpressions can be named across multiple `ring_m` calls. -/
unsafe def ring_m.run' (red : Transparency) (atoms : ref (Buffer expr)) (e : expr) {α} (m : ring_m α) : tactic α := do
  let α ← infer_type e
  let u ← mk_meta_univ
  infer_type α >>= unify (expr.sort (level.succ u))
  let u ← get_univ_assignment u
  let ic ← mk_instance_cache α
  let (ic, c) ← ic.get `` CommSemiringₓ
  let nc ← mk_instance_cache (quote.1 ℕ)
  (using_new_ref ic) fun r => (using_new_ref nc) fun nr => ReaderTₓ.run m ⟨α, u, c, red, r, nr, atoms⟩

/-- Run a `ring_m` tactic in the tactic monad. -/
unsafe def ring_m.run (red : Transparency) (e : expr) {α} (m : ring_m α) : tactic α :=
  (using_new_ref mkBuffer) fun atoms => ring_m.run' red atoms e m

/-- Lift an instance cache tactic (probably from `norm_num`) to the `ring_m` monad. This version
is abstract over the instance cache in question (either the ring `α`, or `ℕ` for exponents). -/
@[inline]
unsafe def ic_lift' (icf : cache → ref instance_cache) {α} (f : instance_cache → tactic (instance_cache × α)) :
    ring_m α :=
  ⟨fun c => do
    let r := icf c
    let ic ← read_ref r
    let (ic', a) ← f ic
    a <$ write_ref r ic'⟩

/-- Lift an instance cache tactic (probably from `norm_num`) to the `ring_m` monad. This uses
the instance cache corresponding to the ring `α`. -/
@[inline]
unsafe def ic_lift {α} : (instance_cache → tactic (instance_cache × α)) → ring_m α :=
  ic_lift' cache.ic

/-- Lift an instance cache tactic (probably from `norm_num`) to the `ring_m` monad. This uses
the instance cache corresponding to `ℕ`, which is used for computations in the exponent. -/
@[inline]
unsafe def nc_lift {α} : (instance_cache → tactic (instance_cache × α)) → ring_m α :=
  ic_lift' cache.nc

/-- Apply a theorem that expects a `comm_semiring` instance. This is a special case of
`ic_lift mk_app`, but it comes up often because `horner` and all its theorems have this assumption;
it also does not require the tactic monad which improves access speed a bit. -/
unsafe def cache.cs_app (c : cache) (n : Name) : List expr → expr :=
  (@expr.const true n [c.Univ] c.α c.comm_semiring_inst).mk_app

/-- Every expression in the language of commutative semirings can be viewed as a sum of monomials,
where each monomial is a product of powers of atoms. We fix a global order on atoms (up to
definitional equality), and then separate the terms according to their smallest atom. So the top
level expression is `a * x^n + b` where `x` is the smallest atom and `n > 0` is a numeral, and
`n` is maximal (so `a` contains at least one monomial not containing an `x`), and `b` contains no
monomials with an `x` (hence all atoms in `b` are larger than `x`).

If there is no `x` satisfying these constraints, then the expression must be a numeral. Even though
we are working over rings, we allow rational constants when these can be interpreted in the ring,
so we can solve problems like `x / 3 = 1 / 3 * x` even though these are not technically in the
language of rings.

These constraints ensure that there is a unique normal form for each ring expression, and so the
algorithm is simply to calculate the normal form of each side and compare for equality.

To allow us to efficiently pattern match on normal forms, we maintain this inductive type that
holds a normalized expression together with its structure. All the `expr`s in this type could be
removed without loss of information, and conversely the `horner_expr` structure and the `ℕ` and
`ℚ` values can be recovered from the top level `expr`, but we keep both in order to keep proof
 producing normalization functions efficient. -/
unsafe inductive horner_expr : Type
  | const (e : expr) (coeff : ℚ) : horner_expr
  | xadd (e : expr) (a : horner_expr) (x : expr × ℕ) (n : expr × ℕ) (b : horner_expr) : horner_expr

/-- Get the expression corresponding to a `horner_expr`. This can be calculated recursively from
the structure, but we cache the exprs in all subterms so that this function can be computed in
constant time. -/
unsafe def horner_expr.e : horner_expr → expr
  | horner_expr.const e _ => e
  | horner_expr.xadd e _ _ _ _ => e

/-- Is this expr the constant `0`? -/
unsafe def horner_expr.is_zero : horner_expr → Bool
  | horner_expr.const _ c => c = 0
  | _ => false

unsafe instance : Coe horner_expr expr :=
  ⟨horner_expr.e⟩

unsafe instance : CoeFun horner_expr fun _ => expr → expr :=
  ⟨fun e => ⇑(e : expr)⟩

/-- Construct a `xadd` node, generating the cached expr using the input cache. -/
unsafe def horner_expr.xadd' (c : cache) (a : horner_expr) (x : expr × ℕ) (n : expr × ℕ) (b : horner_expr) :
    horner_expr :=
  horner_expr.xadd (c.cs_app `` horner [a, x.1, n.1, b]) a x n b

open HornerExpr

/-- Pretty printer for `horner_expr`. -/
unsafe def horner_expr.to_string : horner_expr → Stringₓ
  | const e c => toString (e, c)
  | xadd e a x (_, n) b => "(" ++ a.toString ++ ") * (" ++ toString x.1 ++ ")^" ++ toString n ++ " + " ++ b.toString

/-- Pretty printer for `horner_expr`. -/
unsafe def horner_expr.pp : horner_expr → tactic format
  | const e c => pp (e, c)
  | xadd e a x (_, n) b => do
    let pa ← a.pp
    let pb ← b.pp
    let px ← pp x.1
    return <| "(" ++ pa ++ ") * (" ++ px ++ ")^" ++ toString n ++ " + " ++ pb

unsafe instance : has_to_tactic_format horner_expr :=
  ⟨horner_expr.pp⟩

/-- Reflexivity conversion for a `horner_expr`. -/
unsafe def horner_expr.refl_conv (e : horner_expr) : ring_m (horner_expr × expr) := do
  let p ← lift <| mk_eq_refl e
  return (e, p)

theorem zero_hornerₓ {α} [CommSemiringₓ α] (x n b) : @hornerₓ α _ 0 x n b = b := by
  simp [← horner]

theorem horner_hornerₓ {α} [CommSemiringₓ α] (a₁ x n₁ n₂ b n') (h : n₁ + n₂ = n') :
    @hornerₓ α _ (hornerₓ a₁ x n₁ 0) x n₂ b = hornerₓ a₁ x n' b := by
  simp [← h.symm, ← horner, ← pow_addₓ, ← mul_assoc]

/-- Evaluate `horner a n x b` where `a` and `b` are already in normal form. -/
unsafe def eval_horner : horner_expr → expr × ℕ → expr × ℕ → horner_expr → ring_m (horner_expr × expr)
  | ha@(const a coeff), x, n, b => do
    let c ← get_cache
    if coeff = 0 then return (b, c `` zero_horner [x.1, n.1, b]) else (xadd' c ha x n b).refl_conv
  | ha@(xadd a a₁ x₁ n₁ b₁), x, n, b => do
    let c ← get_cache
    if x₁.2 = x.2 ∧ b₁ = some 0 then do
        let (n', h) ← nc_lift fun nc => norm_num.prove_add_nat' nc n₁.1 n.1
        return (xadd' c a₁ x (n', n₁.2 + n.2) b, c `` horner_horner [a₁, x.1, n₁.1, n.1, b, n', h])
      else (xadd' c ha x n b).refl_conv

theorem const_add_hornerₓ {α} [CommSemiringₓ α] (k a x n b b') (h : k + b = b') :
    k + @hornerₓ α _ a x n b = hornerₓ a x n b' := by
  simp [← h.symm, ← horner] <;> cc

theorem horner_add_constₓ {α} [CommSemiringₓ α] (a x n b k b') (h : b + k = b') :
    @hornerₓ α _ a x n b + k = hornerₓ a x n b' := by
  simp [← h.symm, ← horner, ← add_assocₓ]

theorem horner_add_horner_ltₓ {α} [CommSemiringₓ α] (a₁ x n₁ b₁ a₂ n₂ b₂ k a' b') (h₁ : n₁ + k = n₂)
    (h₂ : (a₁ + hornerₓ a₂ x k 0 : α) = a') (h₃ : b₁ + b₂ = b') :
    @hornerₓ α _ a₁ x n₁ b₁ + hornerₓ a₂ x n₂ b₂ = hornerₓ a' x n₁ b' := by
  simp [← h₂.symm, ← h₃.symm, ← h₁.symm, ← horner, ← pow_addₓ, ← mul_addₓ, ← mul_comm, ← mul_left_commₓ] <;> cc

theorem horner_add_horner_gtₓ {α} [CommSemiringₓ α] (a₁ x n₁ b₁ a₂ n₂ b₂ k a' b') (h₁ : n₂ + k = n₁)
    (h₂ : (hornerₓ a₁ x k 0 + a₂ : α) = a') (h₃ : b₁ + b₂ = b') :
    @hornerₓ α _ a₁ x n₁ b₁ + hornerₓ a₂ x n₂ b₂ = hornerₓ a' x n₂ b' := by
  simp [← h₂.symm, ← h₃.symm, ← h₁.symm, ← horner, ← pow_addₓ, ← mul_addₓ, ← mul_comm, ← mul_left_commₓ] <;> cc

theorem horner_add_horner_eqₓ {α} [CommSemiringₓ α] (a₁ x n b₁ a₂ b₂ a' b' t) (h₁ : a₁ + a₂ = a') (h₂ : b₁ + b₂ = b')
    (h₃ : hornerₓ a' x n b' = t) : @hornerₓ α _ a₁ x n b₁ + hornerₓ a₂ x n b₂ = t := by
  simp [← h₃.symm, ← h₂.symm, ← h₁.symm, ← horner, ← add_mulₓ, ← mul_comm (x ^ n)] <;> cc

/-- Evaluate `a + b` where `a` and `b` are already in normal form. -/
unsafe def eval_add : horner_expr → horner_expr → ring_m (horner_expr × expr)
  | const e₁ c₁, const e₂ c₂ =>
    ic_lift fun ic => do
      let n := c₁ + c₂
      let (ic, e) ← ic.of_rat n
      let (ic, p) ← norm_num.prove_add_rat ic e₁ e₂ e c₁ c₂ n
      return (ic, const e n, p)
  | he₁@(const e₁ c₁), he₂@(xadd e₂ a x n b) => do
    let c ← get_cache
    if c₁ = 0 then
        ic_lift fun ic => do
          let (ic, p) ← ic `` zero_addₓ [e₂]
          return (ic, he₂, p)
      else do
        let (b', h) ← eval_add he₁ b
        return (xadd' c a x n b', c `` const_add_horner [e₁, a, x.1, n.1, b, b', h])
  | he₁@(xadd e₁ a x n b), he₂@(const e₂ c₂) => do
    let c ← get_cache
    if c₂ = 0 then
        ic_lift fun ic => do
          let (ic, p) ← ic `` add_zeroₓ [e₁]
          return (ic, he₁, p)
      else do
        let (b', h) ← eval_add b he₂
        return (xadd' c a x n b', c `` horner_add_const [a, x.1, n.1, b, e₂, b', h])
  | he₁@(xadd e₁ a₁ x₁ n₁ b₁), he₂@(xadd e₂ a₂ x₂ n₂ b₂) => do
    let c ← get_cache
    if x₁.2 < x₂.2 then do
        let (b', h) ← eval_add b₁ he₂
        return (xadd' c a₁ x₁ n₁ b', c `` horner_add_const [a₁, x₁.1, n₁.1, b₁, e₂, b', h])
      else
        if x₁.2 ≠ x₂.2 then do
          let (b', h) ← eval_add he₁ b₂
          return (xadd' c a₂ x₂ n₂ b', c `` const_add_horner [e₁, a₂, x₂.1, n₂.1, b₂, b', h])
        else
          if n₁.2 < n₂.2 then do
            let k := n₂.2 - n₁.2
            let (ek, h₁) ←
              nc_lift fun nc => do
                  let (nc, ek) ← nc k
                  let (nc, h₁) ← norm_num.prove_add_nat nc n₁.1 ek n₂.1
                  return (nc, ek, h₁)
            let α0 ← ic_lift fun ic => ic `` Zero.zero []
            let (a', h₂) ← eval_add a₁ (xadd' c a₂ x₁ (ek, k) (const α0 0))
            let (b', h₃) ← eval_add b₁ b₂
            return
                (xadd' c a' x₁ n₁ b',
                  c `` horner_add_horner_lt [a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, ek, a', b', h₁, h₂, h₃])
          else
            if n₁.2 ≠ n₂.2 then do
              let k := n₁.2 - n₂.2
              let (ek, h₁) ←
                nc_lift fun nc => do
                    let (nc, ek) ← nc k
                    let (nc, h₁) ← norm_num.prove_add_nat nc n₂.1 ek n₁.1
                    return (nc, ek, h₁)
              let α0 ← ic_lift fun ic => ic `` Zero.zero []
              let (a', h₂) ← eval_add (xadd' c a₁ x₁ (ek, k) (const α0 0)) a₂
              let (b', h₃) ← eval_add b₁ b₂
              return
                  (xadd' c a' x₁ n₂ b',
                    c `` horner_add_horner_gt [a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, ek, a', b', h₁, h₂, h₃])
            else do
              let (a', h₁) ← eval_add a₁ a₂
              let (b', h₂) ← eval_add b₁ b₂
              let (t, h₃) ← eval_horner a' x₁ n₁ b'
              return (t, c `` horner_add_horner_eq [a₁, x₁.1, n₁.1, b₁, a₂, b₂, a', b', t, h₁, h₂, h₃])

theorem horner_neg {α} [CommRingₓ α] (a x n b a' b') (h₁ : -a = a') (h₂ : -b = b') :
    -@hornerₓ α _ a x n b = hornerₓ a' x n b' := by
  simp [← h₂.symm, ← h₁.symm, ← horner] <;> cc

/-- Evaluate `-a` where `a` is already in normal form. -/
unsafe def eval_neg : horner_expr → ring_m (horner_expr × expr)
  | const e coeff => do
    let (e', p) ← ic_lift fun ic => norm_num.prove_neg ic e
    return (const e' (-coeff), p)
  | xadd e a x n b => do
    let c ← get_cache
    let (a', h₁) ← eval_neg a
    let (b', h₂) ← eval_neg b
    let p ← ic_lift fun ic => ic.mk_app `` horner_neg [a, x.1, n.1, b, a', b', h₁, h₂]
    return (xadd' c a' x n b', p)

theorem horner_const_mulₓ {α} [CommSemiringₓ α] (c a x n b a' b') (h₁ : c * a = a') (h₂ : c * b = b') :
    c * @hornerₓ α _ a x n b = hornerₓ a' x n b' := by
  simp [← h₂.symm, ← h₁.symm, ← horner, ← mul_addₓ, ← mul_assoc]

theorem horner_mul_constₓ {α} [CommSemiringₓ α] (a x n b c a' b') (h₁ : a * c = a') (h₂ : b * c = b') :
    @hornerₓ α _ a x n b * c = hornerₓ a' x n b' := by
  simp [← h₂.symm, ← h₁.symm, ← horner, ← add_mulₓ, ← mul_right_commₓ]

/-- Evaluate `k * a` where `k` is a rational numeral and `a` is in normal form. -/
unsafe def eval_const_mul (k : expr × ℚ) : horner_expr → ring_m (horner_expr × expr)
  | const e coeff => do
    let (e', p) ← ic_lift fun ic => norm_num.prove_mul_rat ic k.1 e k.2 coeff
    return (const e' (k.2 * coeff), p)
  | xadd e a x n b => do
    let c ← get_cache
    let (a', h₁) ← eval_const_mul a
    let (b', h₂) ← eval_const_mul b
    return (xadd' c a' x n b', c `` horner_const_mul [k.1, a, x.1, n.1, b, a', b', h₁, h₂])

theorem horner_mul_horner_zeroₓ {α} [CommSemiringₓ α] (a₁ x n₁ b₁ a₂ n₂ aa t) (h₁ : @hornerₓ α _ a₁ x n₁ b₁ * a₂ = aa)
    (h₂ : hornerₓ aa x n₂ 0 = t) : hornerₓ a₁ x n₁ b₁ * hornerₓ a₂ x n₂ 0 = t := by
  rw [← h₂, ← h₁] <;> simp [← horner, ← mul_addₓ, ← mul_comm, ← mul_left_commₓ, ← mul_assoc]

theorem horner_mul_hornerₓ {α} [CommSemiringₓ α] (a₁ x n₁ b₁ a₂ n₂ b₂ aa haa ab bb t)
    (h₁ : @hornerₓ α _ a₁ x n₁ b₁ * a₂ = aa) (h₂ : hornerₓ aa x n₂ 0 = haa) (h₃ : a₁ * b₂ = ab) (h₄ : b₁ * b₂ = bb)
    (H : haa + hornerₓ ab x n₁ bb = t) : hornerₓ a₁ x n₁ b₁ * hornerₓ a₂ x n₂ b₂ = t := by
  rw [← H, ← h₂, ← h₁, ← h₃, ← h₄] <;> simp [← horner, ← mul_addₓ, ← mul_comm, ← mul_left_commₓ, ← mul_assoc]

/-- Evaluate `a * b` where `a` and `b` are in normal form. -/
unsafe def eval_mul : horner_expr → horner_expr → ring_m (horner_expr × expr)
  | const e₁ c₁, const e₂ c₂ => do
    let (e', p) ← ic_lift fun ic => norm_num.prove_mul_rat ic e₁ e₂ c₁ c₂
    return (const e' (c₁ * c₂), p)
  | const e₁ c₁, e₂ =>
    if c₁ = 0 then do
      let c ← get_cache
      let α0 ← ic_lift fun ic => ic.mk_app `` Zero.zero []
      let p ← ic_lift fun ic => ic.mk_app `` zero_mul [e₂]
      return (const α0 0, p)
    else
      if c₁ = 1 then do
        let p ← ic_lift fun ic => ic.mk_app `` one_mulₓ [e₂]
        return (e₂, p)
      else eval_const_mul (e₁, c₁) e₂
  | e₁, he₂@(const e₂ c₂) => do
    let p₁ ← ic_lift fun ic => ic.mk_app `` mul_comm [e₁, e₂]
    let (e', p₂) ← eval_mul he₂ e₁
    let p ← lift <| mk_eq_trans p₁ p₂
    return (e', p)
  | he₁@(xadd e₁ a₁ x₁ n₁ b₁), he₂@(xadd e₂ a₂ x₂ n₂ b₂) => do
    let c ← get_cache
    if x₁.2 < x₂.2 then do
        let (a', h₁) ← eval_mul a₁ he₂
        let (b', h₂) ← eval_mul b₁ he₂
        return (xadd' c a' x₁ n₁ b', c `` horner_mul_const [a₁, x₁.1, n₁.1, b₁, e₂, a', b', h₁, h₂])
      else
        if x₁.2 ≠ x₂.2 then do
          let (a', h₁) ← eval_mul he₁ a₂
          let (b', h₂) ← eval_mul he₁ b₂
          return (xadd' c a' x₂ n₂ b', c `` horner_const_mul [e₁, a₂, x₂.1, n₂.1, b₂, a', b', h₁, h₂])
        else do
          let (aa, h₁) ← eval_mul he₁ a₂
          let α0 ← ic_lift fun ic => ic `` Zero.zero []
          let (haa, h₂) ← eval_horner aa x₁ n₂ (const α0 0)
          if b₂ then return (haa, c `` horner_mul_horner_zero [a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, aa, haa, h₁, h₂])
            else do
              let (ab, h₃) ← eval_mul a₁ b₂
              let (bb, h₄) ← eval_mul b₁ b₂
              let (t, H) ← eval_add haa (xadd' c ab x₁ n₁ bb)
              return
                  (t, c `` horner_mul_horner [a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, aa, haa, ab, bb, t, h₁, h₂, h₃, h₄, H])

theorem horner_powₓ {α} [CommSemiringₓ α] (a x n m n' a') (h₁ : n * m = n') (h₂ : a ^ m = a') :
    @hornerₓ α _ a x n 0 ^ m = hornerₓ a' x n' 0 := by
  simp [← h₁.symm, ← h₂.symm, ← horner, ← mul_powₓ, ← pow_mulₓ]

theorem pow_succ {α} [CommSemiringₓ α] (a n b c) (h₁ : (a : α) ^ n = b) (h₂ : b * a = c) : a ^ (n + 1) = c := by
  rw [← h₂, ← h₁, pow_succ'ₓ]

/-- Evaluate `a ^ n` where `a` is in normal form and `n` is a natural numeral. -/
unsafe def eval_pow : horner_expr → expr × ℕ → ring_m (horner_expr × expr)
  | e, (_, 0) => do
    let c ← get_cache
    let α1 ← ic_lift fun ic => ic.mk_app `` One.one []
    let p ← ic_lift fun ic => ic.mk_app `` pow_zeroₓ [e]
    return (const α1 1, p)
  | e, (_, 1) => do
    let p ← ic_lift fun ic => ic.mk_app `` pow_oneₓ [e]
    return (e, p)
  | const e coeff, (e₂, m) =>
    ic_lift fun ic => do
      let (ic, e', p) ← norm_num.prove_pow e coeff ic e₂
      return (ic, const e' (coeff ^ m), p)
  | he@(xadd e a x n b), m => do
    let c ← get_cache
    match b with
      | some 0 => do
        let (n', h₁) ← nc_lift fun nc => norm_num.prove_mul_rat nc n.1 m.1 n.2 m.2
        let (a', h₂) ← eval_pow a m
        let α0 ← ic_lift fun ic => ic `` Zero.zero []
        return (xadd' c a' x (n', n.2 * m.2) (const α0 0), c `` horner_pow [a, x.1, n.1, m.1, n', a', h₁, h₂])
      | _ => do
        let e₂ ← nc_lift fun nc => nc (m.2 - 1)
        let (tl, hl) ← eval_pow he (e₂, m.2 - 1)
        let (t, p₂) ← eval_mul tl he
        return (t, c `` pow_succₓ [e, e₂, tl, t, hl, p₂])

theorem horner_atomₓ {α} [CommSemiringₓ α] (x : α) : x = hornerₓ 1 x 1 0 := by
  simp [← horner]

/-- Evaluate `a` where `a` is an atom. -/
unsafe def eval_atom (e : expr) : ring_m (horner_expr × expr) := do
  let c ← get_cache
  let i ← add_atom e
  let α0 ← ic_lift fun ic => ic.mk_app `` Zero.zero []
  let α1 ← ic_lift fun ic => ic.mk_app `` One.one []
  return (xadd' c (const α1 1) (e, i) (quote.1 1, 1) (const α0 0), c `` horner_atom [e])

/-- Evaluate `a` where `a` is an atom. -/
unsafe def eval_norm_atom (norm_atom : expr → tactic (expr × expr)) (e : expr) : ring_m (horner_expr × expr) := do
  let o ← lift <| try_core (guardₓ (e.get_app_args.length > 0) >> norm_atom e)
  match o with
    | none => eval_atom e
    | some (e', p) => do
      let (e₂, p₂) ← eval_atom e'
      Prod.mk e₂ <$> lift (mk_eq_trans p p₂)

theorem subst_into_powₓ {α} [Monoidₓ α] (l r tl tr t) (prl : (l : α) = tl) (prr : (r : ℕ) = tr) (prt : tl ^ tr = t) :
    l ^ r = t := by
  rw [prl, prr, prt]

theorem unfold_sub {α} [AddGroupₓ α] (a b c : α) (h : a + -b = c) : a - b = c := by
  rw [sub_eq_add_neg, h]

theorem unfold_div {α} [DivisionRing α] (a b c : α) (h : a * b⁻¹ = c) : a / b = c := by
  rw [div_eq_mul_inv, h]

/-- Evaluate a ring expression `e` recursively to normal form, together with a proof of
equality. -/
unsafe def eval (norm_atom : expr → tactic (expr × expr)) : expr → ring_m (horner_expr × expr)
  | quote.1 ((%%ₓe₁) + %%ₓe₂) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← eval_add e₁' e₂'
    let p ← ic_lift fun ic => ic.mk_app `` NormNum.subst_into_add [e₁, e₂, e₁', e₂', e', p₁, p₂, p']
    return (e', p)
  | e@(quote.1 (@Sub.sub (%%ₓα) (%%ₓinst) (%%ₓe₁) (%%ₓe₂))) =>
    mcond (succeeds (lift <| mk_app `` CommRingₓ [α] >>= mk_instance))
      (do
        let e₂' ← ic_lift fun ic => ic.mk_app `` Neg.neg [e₂]
        let e ← ic_lift fun ic => ic.mk_app `` Add.add [e₁, e₂']
        let (e', p) ← eval e
        let p' ← ic_lift fun ic => ic.mk_app `` unfold_sub [e₁, e₂, e', p]
        return (e', p'))
      (eval_norm_atom norm_atom e)
  | quote.1 (-%%ₓe) => do
    let (e₁, p₁) ← eval e
    let (e₂, p₂) ← eval_neg e₁
    let p ← ic_lift fun ic => ic.mk_app `` NormNum.subst_into_neg [e, e₁, e₂, p₁, p₂]
    return (e₂, p)
  | quote.1 ((%%ₓe₁) * %%ₓe₂) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← eval_mul e₁' e₂'
    let p ← ic_lift fun ic => ic.mk_app `` NormNum.subst_into_mul [e₁, e₂, e₁', e₂', e', p₁, p₂, p']
    return (e', p)
  | e@(quote.1 (Inv.inv (%%ₓ_))) =>
    (do
        let (e', p) ← lift <| norm_num.derive e <|> refl_conv e
        let n ← lift <| e'.to_rat
        return (const e' n, p)) <|>
      eval_norm_atom norm_atom e
  | e@(quote.1 (@Div.div _ (%%ₓinst) (%%ₓe₁) (%%ₓe₂))) =>
    mcond
      (succeeds do
        let inst' ← ic_lift fun ic => ic.mk_app `` DivInvMonoidₓ.toHasDiv []
        lift <| is_def_eq inst inst')
      (do
        let e₂' ← ic_lift fun ic => ic.mk_app `` Inv.inv [e₂]
        let e ← ic_lift fun ic => ic.mk_app `` Mul.mul [e₁, e₂']
        let (e', p) ← eval e
        let p' ← ic_lift fun ic => ic.mk_app `` unfold_div [e₁, e₂, e', p]
        return (e', p'))
      (eval_norm_atom norm_atom e)
  | e@(quote.1 (@Pow.pow _ _ (%%ₓP) (%%ₓe₁) (%%ₓe₂))) => do
    let (e₂', p₂) ← lift <| norm_num.derive e₂ <|> refl_conv e₂
    match e₂', P with
      | some k, quote.1 Monoidₓ.hasPow => do
        let (e₁', p₁) ← eval e₁
        let (e', p') ← eval_pow e₁' (e₂, k)
        let p ← ic_lift fun ic => ic `` subst_into_pow [e₁, e₂, e₁', e₂', e', p₁, p₂, p']
        return (e', p)
      | _, _ => eval_norm_atom norm_atom e
  | e =>
    match e.toNat with
    | some n => (const e (Rat.ofInt n)).refl_conv
    | none => eval_norm_atom norm_atom e

/-- Evaluate a ring expression `e` recursively to normal form, together with a proof of
equality. -/
unsafe def eval' (red : Transparency) (atoms : ref (Buffer expr)) (norm_atom : expr → tactic (expr × expr)) (e : expr) :
    tactic (expr × expr) :=
  ring_m.run' red atoms e <| do
    let (e', p) ← eval norm_atom e
    return (e', p)

theorem horner_def' {α} [CommSemiringₓ α] (a x n b) : @hornerₓ α _ a x n b = x ^ n * a + b := by
  simp [← horner, ← mul_comm]

theorem mul_assoc_rev {α} [Semigroupₓ α] (a b c : α) : a * (b * c) = a * b * c := by
  simp [← mul_assoc]

theorem pow_add_rev {α} [Monoidₓ α] (a : α) (m n : ℕ) : a ^ m * a ^ n = a ^ (m + n) := by
  simp [← pow_addₓ]

theorem pow_add_rev_right {α} [Monoidₓ α] (a b : α) (m n : ℕ) : b * a ^ m * a ^ n = b * a ^ (m + n) := by
  simp [← pow_addₓ, ← mul_assoc]

theorem add_neg_eq_sub {α} [AddGroupₓ α] (a b : α) : a + -b = a - b :=
  (sub_eq_add_neg a b).symm

/-- If `ring` fails to close the goal, it falls back on normalizing the expression to a "pretty"
form so that you can see why it failed. This setting adjusts the resulting form:

  * `raw` is the form that `ring` actually uses internally, with iterated applications of `horner`.
    Not very readable but useful if you don't want any postprocessing.
    This results in terms like `horner (horner (horner 3 y 1 0) x 2 1) x 1 (horner 1 y 1 0)`.
  * `horner` maintains the Horner form structure, but it unfolds the `horner` definition itself,
    and tries to otherwise minimize parentheses.
    This results in terms like `(3 * x ^ 2 * y + 1) * x + y`.
  * `SOP` means sum of products form, expanding everything to monomials.
    This results in terms like `3 * x ^ 3 * y + x + y`. -/
inductive NormalizeMode
  | raw
  | SOP
  | horner
  deriving has_reflect, DecidableEq

instance : Inhabited NormalizeMode :=
  ⟨NormalizeMode.horner⟩

/-- A `ring`-based normalization simplifier that rewrites ring expressions into the specified mode.
See `normalize`. This version takes a list of atoms to persist across multiple calls.

* `atoms`: a mutable reference containing the atom set from the previous call
* `red`: the reducibility setting to use when comparing atoms for defeq
* `mode`: the normalization style (see `normalize_mode`)
* `recursive`: if true, atoms will be reduced recursively using `normalize'`
* `e`: the expression to normalize
* `inner`: This should be set to `ff`. It is used internally to disable normalization
  at the top level when called from `eval` in order to prevent an infinite loop
  `eval' -> eval_atom -> normalize' -> eval'` when called on something that can't
  be simplified like `x`.
-/
unsafe def normalize' (atoms : ref (Buffer expr)) (red : Transparency) (mode := NormalizeMode.horner)
    (recursive := true) : expr → optParam _ false → tactic (expr × expr)
  | e, inner => do
    let pow_lemma ← simp_lemmas.mk.add_simp `` pow_oneₓ
    let lemmas :=
      match mode with
      | normalize_mode.SOP =>
        [`` horner_def', `` add_zeroₓ, `` mul_oneₓ, `` mul_addₓ, `` mul_sub, `` mul_assoc_rev, `` pow_add_rev,
          `` pow_add_rev_right, `` mul_neg, `` add_neg_eq_sub]
      | normalize_mode.horner =>
        [`` horner.equations._eqn_1, `` add_zeroₓ, `` one_mulₓ, `` pow_oneₓ, `` neg_mul, `` add_neg_eq_sub]
      | _ => []
    let lemmas ← lemmas.mfoldl simp_lemmas.add_simp simp_lemmas.mk
    trans_conv
        (fun e => do
          guardₓ (mode ≠ normalize_mode.raw)
          let (e', pr, _) ← simplify simp_lemmas.mk [] e
          pure (e', pr))
        (fun e => do
          let a ← read_ref atoms
          let norm_rec := if recursive then fun e => normalize' e tt else fun _ => failed
          let (a, e', pr) ←
            ext_simplify_core a {  } simp_lemmas.mk (fun _ => failed)
                (fun a _ _ p e => do
                  guardₓ (inner → p)
                  write_ref atoms a
                  let (new_e, pr) ← eval' red atoms norm_rec e
                  let (new_e, pr) ←
                    (match mode with
                        | normalize_mode.raw => fun _ => pure (new_e, pr)
                        | normalize_mode.horner =>
                          trans_conv (fun _ => pure (new_e, pr)) fun e => do
                            let (e', prf, _) ← simplify lemmas [] e
                            pure (e', prf)
                        | normalize_mode.SOP =>
                          (trans_conv fun _ => pure (new_e, pr)) <|
                            (trans_conv fun e => do
                                let (e', prf, _) ← simplify lemmas [] e
                                pure (e', prf)) <|
                              simp_bottom_up' fun e => norm_num.derive e <|> pow_lemma e)
                        e
                  guardₓ ¬expr.alpha_eqv new_e e
                  let a ← read_ref atoms
                  pure (a, new_e, some pr, ff))
                (fun _ _ _ _ _ => failed) `eq e
          write_ref atoms a
          pure (e', pr))
        e

/-- A `ring`-based normalization simplifier that rewrites ring expressions into the specified mode.

  * `raw` is the form that `ring` actually uses internally, with iterated applications of `horner`.
    Not very readable but useful if you don't want any postprocessing.
    This results in terms like `horner (horner (horner 3 y 1 0) x 2 1) x 1 (horner 1 y 1 0)`.
  * `horner` maintains the Horner form structure, but it unfolds the `horner` definition itself,
    and tries to otherwise minimize parentheses.
    This results in terms like `(3 * x ^ 2 * y + 1) * x + y`.
  * `SOP` means sum of products form, expanding everything to monomials.
    This results in terms like `3 * x ^ 3 * y + x + y`. -/
unsafe def normalize (red : Transparency) (mode := NormalizeMode.horner) (recursive := true) (e : expr) :
    tactic (expr × expr) :=
  (using_new_ref mkBuffer) fun atoms => normalize' atoms red mode recursive e

/-- Configuration for `ring_nf`.

  * `recursive`: if true, atoms inside ring expressions will be reduced recursively
-/
structure RingNfCfg where
  recursive := true
  deriving Inhabited

end Ringₓ

namespace Interactive

open Tactic.Ring

setup_tactic_parser

/-- Tactic for solving equations in the language of *commutative* (semi)rings.
  This version of `ring` fails if the target is not an equality
  that is provable by the axioms of commutative (semi)rings. -/
unsafe def ring1 (red : parse (tk "!")?) : tactic Unit :=
  let transp := if red.isSome then semireducible else reducible
  do
  let quote.1 ((%%ₓe₁) = %%ₓe₂) ← target >>= instantiate_mvars
  let ((e₁', p₁), (e₂', p₂)) ←
    ring_m.run transp e₁ <| Prod.mk <$> eval (fun _ => failed) e₁ <*> eval (fun _ => failed) e₂
  is_def_eq e₁' e₂'
  let p ← mk_eq_symm p₂ >>= mk_eq_trans p₁
  tactic.exact p

/-- Parser for `ring_nf`'s `mode` argument, which can only be the "keywords" `raw`, `horner` or
`SOP`. (Because these are not actually keywords we use a name parser and postprocess the result.)
-/
unsafe def ring.mode : lean.parser Ring.NormalizeMode :=
  with_desc "(SOP|raw|horner)?" <| do
    let mode ← ident ?
    match mode with
      | none => pure ring.normalize_mode.horner
      | some `horner => pure ring.normalize_mode.horner
      | some `SOP => pure ring.normalize_mode.SOP
      | some `raw => pure ring.normalize_mode.raw
      | _ => failed

/-- Simplification tactic for expressions in the language of commutative (semi)rings,
which rewrites all ring expressions into a normal form. When writing a normal form,
`ring_nf SOP` will use sum-of-products form instead of horner form.
`ring_nf!` will use a more aggressive reducibility setting to identify atoms.
-/
unsafe def ring_nf (red : parse (tk "!")?) (SOP : parse ring.mode) (loc : parse location) (cfg : RingNfCfg := {  }) :
    tactic Unit := do
  let ns ← loc.get_locals
  let transp := if red.isSome then semireducible else reducible
  let tt ←
    (using_new_ref mkBuffer) fun atoms =>
        tactic.replace_at (normalize' atoms transp SOP cfg.recursive) ns loc.include_goal |
    fail "ring_nf failed to simplify"
  when loc <| try tactic.reflexivity

/-- Tactic for solving equations in the language of *commutative* (semi)rings.
`ring!` will use a more aggressive reducibility setting to identify atoms.

If the goal is not solvable, it falls back to rewriting all ring expressions
into a normal form, with a suggestion to use `ring_nf` instead, if this is the intent.
See also `ring1`, which is the same as `ring` but without the fallback behavior.

Based on [Proving Equalities in a Commutative Ring Done Right
in Coq](http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf) by Benjamin Grégoire
and Assia Mahboubi.
-/
unsafe def ring (red : parse (tk "!")?) : tactic Unit :=
  ring1 red <|> ring_nf red NormalizeMode.horner (Loc.ns [none]) >> trace "Try this: ring_nf"

add_hint_tactic ring

add_tactic_doc
  { Name := "ring", category := DocCategory.tactic, declNames := [`` Ringₓ, `` ring_nf, `` ring1],
    inheritDescriptionFrom := `` Ringₓ, tags := ["arithmetic", "simplification", "decision procedure"] }

end Interactive

end Tactic

namespace Conv.Interactive

open Conv Interactive

open Tactic

open Tactic.Interactive (ring.mode ring1)

open Tactic.Ring (normalize normalize_mode.horner)

-- mathport name: «expr ?»
local postfix:1024 "?" => optionalₓ

/-- Normalises expressions in commutative (semi-)rings inside of a `conv` block using the tactic `ring`.
-/
unsafe def ring_nf (red : parse (lean.parser.tk "!")?) (SOP : parse ring.mode) (cfg : Ring.RingNfCfg := {  }) :
    conv Unit :=
  let transp := if red.isSome then semireducible else reducible
  replace_lhs (normalize transp SOP cfg.recursive) <|> fail "ring_nf failed to simplify"

/-- Normalises expressions in commutative (semi-)rings inside of a `conv` block using the tactic `ring`.
-/
unsafe def ring (red : parse (lean.parser.tk "!")?) : conv Unit :=
  let transp := if red.isSome then semireducible else reducible
  discharge_eq_lhs (ring1 red) <|>
    replace_lhs (normalize transp NormalizeMode.horner) >> trace "Try this: ring_nf" <|> fail "ring failed to simplify"

end Conv.Interactive


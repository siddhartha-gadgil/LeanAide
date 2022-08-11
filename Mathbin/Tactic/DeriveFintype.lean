/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Fintype.Basic

/-!
# Derive handler for `fintype` instances

This file introduces a derive handler to automatically generate `fintype`
instances for structures and inductives.

## Implementation notes

To construct a fintype instance, we need 3 things:

  1. A list `l` of elements
  2. A proof that `l` has no duplicates
  3. A proof that every element in the type is in `l`

Now fintype is defined as a finset which enumerates all elements, so steps (1) and (2) are
bundled together. It is possible to use finset operations that remove duplicates to avoid the need
to prove (2), but this adds unnecessary functions to the constructed term, which makes it more
expensive to compute the list, and it also adds a dependence on decidable equality for the type,
which we want to avoid.

Because we will rely on fintype instances for constructor arguments, we can't actually build a list
directly, so (1) and (2) are necessarily somewhat intertwined. The inductive types we will be
proving instances for look something like this:

```
@[derive fintype]
inductive foo
| zero : foo
| one : bool → foo
| two : ∀ x : fin 3, bar x → foo
```

The list of elements that we generate is
```
{foo.zero}
∪ (finset.univ : bool).map (λ b, finset.one b)
∪ (finset.univ : Σ' x : fin 3, bar x).map (λ ⟨x, y⟩, finset.two x y)
```
except that instead of `∪`, that is `finset.union`, we use `finset.disj_union` which doesn't
require any deduplication, but does require a proof that the two parts of the union are disjoint.
We use `finset.cons` to append singletons like `foo.zero`.

The proofs of disjointness would be somewhat expensive since there are quadratically many of them,
so instead we use a "discriminant" function. Essentially, we define
```
def foo.enum : foo → ℕ
| foo.zero := 0
| (foo.one _) := 1
| (foo.two _ _) := 2
```
and now the existence of this function implies that foo.zero is not foo.two and so on because they
map to different natural numbers. We can prove that sets of natural numbers are mutually disjoint
more easily because they have a linear order: `0 < 1 < 2` so `0 ≠ 2`.

To package this argument up, we define `finset_above foo foo.enum n` to be a finset `s` together
with a proof that all elements `a ∈ s` have `n ≤ enum a`. Now we only have to prove that
`enum foo.zero = 0`, `enum (foo.one _) = 1`, etc. (linearly many proofs, all `rfl`) in order to
prove that all variants are mutually distinct.

We mirror the `finset.cons` and `finset.disj_union` functions into `finset_above.cons` and
`finset_above.union`, and this forms the main part of the finset construction.

This only handles distinguishing variants of a finset. Now we must enumerate the elements of a
variant, for example `{foo.one ff, foo.one tt}`, while at the same time proving that all these
elements have discriminant `1` in this case. To do that, we use the `finset_in` type, which
is a finset satisfying a property `P`, here `λ a, foo.enum a = 1`.

We could use `finset.bind` many times to construct the finset but it turns out to be somewhat
complicated to get good side goals for a naturally nodup version of `finset.bind` in the same way
as we did with `finset.cons` and `finset.union`. Instead, we tuple up all arguments into one type,
leveraging the `fintype` instance on `psigma`, and then define a map from this type to the
inductive type that untuples them and applies the constructor. The injectivity property of the
constructor ensures that this function is injective, so we can use `finset.map` to apply it. This
is the content of the constructor `finset_in.mk`.

That completes the proofs of (1) and (2). To prove (3), we perform one case analysis over the
inductive type, proving theorems like
```
foo.one a ∈ {foo.zero}
  ∪ (finset.univ : bool).map (λ b, finset.one b)
  ∪ (finset.univ : Σ' x : fin 3, bar x).map (λ ⟨x, y⟩, finset.two x y)
```
by seeking to the relevant disjunct and then supplying the constructor arguments. This part of the
proof is quadratic, but quite simple. (We could do it in `O(n log n)` if we used a balanced tree
for the unions.)

The tactics perform the following parts of this proof scheme:
* `mk_sigma` constructs the type `Γ` in `finset_in.mk`
* `mk_sigma_elim` constructs the function `f` in `finset_in.mk`
* `mk_sigma_elim_inj` proves that `f` is injective
* `mk_sigma_elim_eq` proves that `∀ a, enum (f a) = k`
* `mk_finset` constructs the finset `S = {foo.zero} ∪ ...` by recursion on the variants
* `mk_finset_total` constructs the proof `|- foo.zero ∈ S; |- foo.one a ∈ S; |- foo.two a b ∈ S`
  by recursion on the subgoals coming out of the initial `cases`
* `mk_fintype_instance` puts it all together to produce a proof of `fintype foo`.
  The construction of `foo.enum` is also done in this function.

-/


namespace DeriveFintype

/-- A step in the construction of `finset.univ` for a finite inductive type.
We will set `enum` to the discriminant of the inductive type, so a `finset_above`
represents a finset that enumerates all elements in a tail of the constructor list. -/
def FinsetAbove (α) (enum : α → ℕ) (n : ℕ) :=
  { s : Finset α // ∀, ∀ x ∈ s, ∀, n ≤ enum x }

/-- Construct a fintype instance from a completed `finset_above`. -/
def mkFintype {α} (enum : α → ℕ) (s : FinsetAbove α enum 0) (H : ∀ x, x ∈ s.1) : Fintype α :=
  ⟨s.1, H⟩

/-- This is the case for a simple variant (no arguments) in an inductive type. -/
def FinsetAbove.cons {α} {enum : α → ℕ} (n) (a : α) (h : enum a = n) (s : FinsetAbove α enum (n + 1)) :
    FinsetAbove α enum n := by
  refine' ⟨Finset.cons a s.1 _, _⟩
  · intro h'
    have := s.2 _ h'
    rw [h] at this
    exact Nat.not_succ_le_selfₓ n this
    
  · intro x h'
    rcases Finset.mem_cons.1 h' with (rfl | h')
    · exact ge_of_eq h
      
    · exact Nat.le_of_succ_leₓ (s.2 _ h')
      
    

theorem FinsetAbove.mem_cons_self {α} {enum : α → ℕ} {n a h s} : a ∈ (@FinsetAbove.cons α enum n a h s).1 :=
  Multiset.mem_cons_self _ _

theorem FinsetAbove.mem_cons_of_mem {α} {enum : α → ℕ} {n a h s b} :
    b ∈ (s : FinsetAbove _ _ _).1 → b ∈ (@FinsetAbove.cons α enum n a h s).1 :=
  Multiset.mem_cons_of_mem

/-- The base case is when we run out of variants; we just put an empty finset at the end. -/
def FinsetAbove.nil {α} {enum : α → ℕ} (n) : FinsetAbove α enum n :=
  ⟨∅, by
    rintro _ ⟨⟩⟩

instance (α enum n) : Inhabited (FinsetAbove α enum n) :=
  ⟨FinsetAbove.nil _⟩

/-- This is a finset covering a nontrivial variant (with one or more constructor arguments).
The property `P` here is `λ a, enum a = n` where `n` is the discriminant for the current
variant. -/
@[nolint has_inhabited_instance]
def FinsetIn {α} (P : α → Prop) :=
  { s : Finset α // ∀, ∀ x ∈ s, ∀, P x }

/-- To construct the finset, we use an injective map from the type `Γ`, which will be the
sigma over all constructor arguments. We use sigma instances and existing fintype instances
to prove that `Γ` is a fintype, and construct the function `f` that maps `⟨a, b, c, ...⟩`
to `C_n a b c ...` where `C_n` is the nth constructor, and `mem` asserts
`enum (C_n a b c ...) = n`. -/
def FinsetIn.mk {α} {P : α → Prop} (Γ) [Fintype Γ] (f : Γ → α) (inj : Function.Injective f) (mem : ∀ x, P (f x)) :
    FinsetIn P :=
  ⟨Finset.univ.map ⟨f, inj⟩, fun x h => by
    rcases Finset.mem_map.1 h with ⟨x, _, rfl⟩ <;> exact mem x⟩

theorem FinsetIn.mem_mk {α} {P : α → Prop} {Γ} {s : Fintype Γ} {f : Γ → α} {inj mem a} (b) (H : f b = a) :
    a ∈ (@FinsetIn.mk α P Γ s f inj mem).1 :=
  Finset.mem_map.2 ⟨_, Finset.mem_univ _, H⟩

/-- For nontrivial variants, we split the constructor list into a `finset_in` component for the
current constructor and a `finset_above` for the rest. -/
def FinsetAbove.union {α} {enum : α → ℕ} (n) (s : FinsetIn fun a => enum a = n) (t : FinsetAbove α enum (n + 1)) :
    FinsetAbove α enum n := by
  refine' ⟨Finset.disjUnion s.1 t.1 _, _⟩
  · intro a hs ht
    have := t.2 _ ht
    rw [s.2 _ hs] at this
    exact Nat.not_succ_le_selfₓ n this
    
  · intro x h'
    rcases Finset.mem_disj_union.1 h' with (h' | h')
    · exact ge_of_eq (s.2 _ h')
      
    · exact Nat.le_of_succ_leₓ (t.2 _ h')
      
    

theorem FinsetAbove.mem_union_left {α} {enum : α → ℕ} {n s t a} (H : a ∈ (s : FinsetIn _).1) :
    a ∈ (@FinsetAbove.union α enum n s t).1 :=
  Multiset.mem_add.2 (Or.inl H)

theorem FinsetAbove.mem_union_right {α} {enum : α → ℕ} {n s t a} (H : a ∈ (t : FinsetAbove _ _ _).1) :
    a ∈ (@FinsetAbove.union α enum n s t).1 :=
  Multiset.mem_add.2 (Or.inr H)

end DeriveFintype

namespace Tactic

open DeriveFintype Tactic Expr

namespace DeriveFintype

/-- Construct the term `Σ' (a:A) (b:B a) (c:C a b), unit` from
`Π (a:A) (b:B a), C a b → T` (the type of a constructor). -/
unsafe def mk_sigma : expr → tactic expr
  | expr.pi n bi d b => do
    let p ← mk_local' n bi d
    let e ← mk_sigma (expr.instantiate_var b p)
    tactic.mk_app `` PSigma [d, bind_lambda e p]
  | _ => pure (quote.1 Unit)

/-- Prove the goal `(Σ' (a:A) (b:B a) (c:C a b), unit) → T`
(this is the function `f` in `finset_in.mk`) using recursive `psigma.elim`,
finishing with the constructor. The two arguments are the type of the constructor,
and the constructor term itself; as we recurse we add arguments
to the constructor application and destructure the pi type of the constructor. We return the number
of `psigma.elim` applications constructed, which is the number of constructor arguments. -/
unsafe def mk_sigma_elim : expr → expr → tactic ℕ
  | expr.pi n bi d b, c => do
    refine (pquote.1 (@PSigma.elim (%%ₓd) _ _ _))
    let i ← intro_fresh n
    (· + 1) <$> mk_sigma_elim (expr.instantiate_var b i) (c i)
  | _, c => do
    intro1
    exact c $> 0

/-- Prove the goal `a, b |- f a = f b → g a = g b` where `f` is the function we constructed in
`mk_sigma_elim`, and `g` is some other term that gets built up and eventually closed by
reflexivity. Here `a` and `b` have sigma types so the proof approach is to case on `a` and `b`
until the goal reduces to `C_n a1 ... am = C_n b1 ... bm → ⟨a1, ..., am⟩ = ⟨b1, ..., bm⟩`, at which
point cases on the equality reduces the problem to reflexivity.

The arguments are the number `m` returned from `mk_sigma_elim`, and the hypotheses `a,b` that we
need to case on. -/
unsafe def mk_sigma_elim_inj : ℕ → expr → expr → tactic Unit
  | m + 1, x, y => do
    let [(_, [x1, x2])] ← cases x
    let [(_, [y1, y2])] ← cases y
    mk_sigma_elim_inj m x2 y2
  | 0, x, y => do
    cases x
    cases y
    let is ← intro1 >>= injection
    is cases
    reflexivity

/-- Prove the goal `a |- enum (f a) = n`, where `f` is the function constructed in `mk_sigma_elim`,
and `enum` is a function that reduces to `n` on the constructor `C_n`. Here we just have to case on
`a` `m` times, and then `reflexivity` finishes the proof. -/
unsafe def mk_sigma_elim_eq : ℕ → expr → tactic Unit
  | n + 1, x => do
    let [(_, [x1, x2])] ← cases x
    mk_sigma_elim_eq n x2
  | 0, x => reflexivity

/-- Prove the goal `|- finset_above T enum k`, where `T` is the inductive type and `enum` is the
discriminant function. The arguments are `args`, the parameters to the inductive type (and all
constructors), `k`, the index of the current variant, and `cs`, the list of constructor names.
This uses `finset_above.cons` for basic variants and `finset_above.union` for variants with
arguments, using the auxiliary functions `mk_sigma`, `mk_sigma_elim`, `mk_sigma_elim_inj`,
`mk_sigma_elim_eq` to close subgoals. -/
unsafe def mk_finset (ls : List level) (args : List expr) : ℕ → List Name → tactic Unit
  | k, c :: cs => do
    let e := (expr.const c ls).mk_app args
    let t ← infer_type e
    if is_pi t then do
        to_expr (pquote.1 (FinsetAbove.union (%%ₓreflect k))) tt ff >>= fun c => apply c { NewGoals := new_goals.all }
        let Γ ← mk_sigma t
        to_expr (pquote.1 (FinsetIn.mk (%%ₓΓ))) tt ff >>= fun c => apply c { NewGoals := new_goals.all }
        let n ← mk_sigma_elim t e
        intro1 >>= fun x => intro1 >>= mk_sigma_elim_inj n x
        intro1 >>= mk_sigma_elim_eq n
        mk_finset (k + 1) cs
      else do
        let c ← to_expr (pquote.1 (FinsetAbove.cons (%%ₓreflect k) (%%ₓe))) tt ff
        apply c { NewGoals := new_goals.all }
        reflexivity
        mk_finset (k + 1) cs
  | k, [] => applyc `` finset_above.nil

/-- Prove the goal `|- Σ' (a:A) (b: B a) (c:C a b), unit` given a list of terms `a, b, c`. -/
unsafe def mk_sigma_mem : List expr → tactic Unit
  | x :: xs => (fconstructor >> exact x) >> mk_sigma_mem xs
  | [] => fconstructor $> ()

/-- This function is called to prove `a : T |- a ∈ S.1` where `S` is the `finset_above` constructed
by `mk_finset`, after the initial cases on `a : T`, producing a list of subgoals. For each case,
we have to navigate past all the variants that don't apply (which is what the `tac` input tactic
does), and then call either `finset_above.mem_cons_self` for trivial variants or
`finset_above.mem_union_left` and `finset_in.mem_mk` for nontrivial variants. Either way the proof
is quite simple. -/
unsafe def mk_finset_total : tactic Unit → List (Name × List expr) → tactic Unit
  | tac, [] => done
  | tac, (_, xs) :: gs => do
    tac
    let b ← succeeds (applyc `` finset_above.mem_cons_self)
    if b then mk_finset_total (tac >> applyc `` finset_above.mem_cons_of_mem) gs
      else do
        applyc `` finset_above.mem_union_left
        applyc `` finset_in.mem_mk { NewGoals := new_goals.all }
        mk_sigma_mem xs
        reflexivity
        mk_finset_total (tac >> applyc `` finset_above.mem_union_right) gs

end DeriveFintype

open Tactic.DeriveFintype

/-- Proves `|- fintype T` where `T` is a non-recursive inductive type with no indices,
where all arguments to all constructors are fintypes. -/
unsafe def mk_fintype_instance : tactic Unit := do
  intros
  let quote.1 (Fintype (%%ₓe)) ← target >>= whnf
  let (const I ls, args) ← pure (get_app_fn_args e)
  let env ← get_env
  let cs := env.constructors_of I
  guardₓ (env I = 0) <|> fail "@[derive fintype]: inductive indices are not supported"
  guardₓ ¬env I <|>
      fail ("@[derive fintype]: recursive inductive types are " ++ "not supported (they are also usually infinite)")
  applyc `` mk_fintype { NewGoals := new_goals.all }
  intro1 >>= cases >>= fun gs => gs fun ⟨i, _⟩ => exact (reflect i)
  mk_finset ls args 0 cs
  intro1 >>= cases >>= mk_finset_total skip

/-- Tries to derive a `fintype` instance for inductives and structures.

For example:
```
@[derive fintype]
inductive foo (n m : ℕ)
| zero : foo
| one : bool → foo
| two : fin n → fin m → foo
```
Here, `@[derive fintype]` adds the instance `foo.fintype`. The underlying finset
definitionally unfolds to a list that enumerates the elements of the inductive in
lexicographic order.

If the structure/inductive has a type parameter `α`, then the generated instance will have an
argument `fintype α`, even if it is not used.  (This is due to the implementation using
`instance_derive_handler`.)
-/
@[derive_handler]
unsafe def fintype_instance : derive_handler :=
  instance_derive_handler `` Fintype mk_fintype_instance

end Tactic


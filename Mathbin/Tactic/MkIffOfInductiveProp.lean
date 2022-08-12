/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Tactic.Core
import Mathbin.Tactic.Lint.Default

/-!
# mk_iff_of_inductive_prop

This file defines a tactic `tactic.mk_iff_of_inductive_prop` that generates `iff` rules for
inductive `Prop`s. For example, when applied to `list.chain`, it creates a declaration with
the following type:

```lean
∀{α : Type*} (R : α → α → Prop) (a : α) (l : list α),
  chain R a l ↔ l = [] ∨ ∃{b : α} {l' : list α}, R a b ∧ chain R b l ∧ l = b :: l'
```

This tactic can be called using either the `mk_iff_of_inductive_prop` user command or
the `mk_iff` attribute.
-/


open Tactic Expr

namespace MkIff

/-- `select m n` runs `tactic.right` `m` times, and then `tactic.left` `(n-m)` times.
Fails if `n < m`. -/
unsafe def select : ℕ → ℕ → tactic Unit
  | 0, 0 => skip
  | 0, n + 1 => left >> skip
  | m + 1, n + 1 => right >> select m n
  | n + 1, 0 => failure

/-- `compact_relation bs as_ps`: Produce a relation of the form:
```lean
R as := ∃ bs, Λ_i a_i = p_i[bs]
```
This relation is user-visible, so we compact it by removing each `b_j` where a `p_i = b_j`, and
hence `a_i = b_j`. We need to take care when there are `p_i` and `p_j` with `p_i = p_j = b_k`.

TODO: this is a variant of `compact_relation` in `coinductive_predicates.lean`, export it there.
-/
unsafe def compact_relation : List expr → List (expr × expr) → List (Option expr) × List (expr × expr)
  | [], ps => ([], ps)
  | b :: bs, ps =>
    match ps.span fun ap : expr × expr => ¬expr.alpha_eqv ap.2 b with
    | (_, []) =>
      let (bs, ps) := compact_relation bs ps
      (b :: bs, ps)
    | (ps₁, (a, _) :: ps₂) =>
      let i := a.instantiate_local b.local_uniq_name
      let (bs, ps) := compact_relation (bs.map i) ((ps₁ ++ ps₂).map fun ⟨a, p⟩ => (a, i p))
      (none :: bs, ps)

-- TODO: document
@[nolint doc_blame]
unsafe def constr_to_prop (univs : List level) (g : List expr) (idxs : List expr) (c : Name) :
    tactic ((List (Option expr) × Sum expr ℕ) × expr) := do
  let e ← get_env
  let decl ← get_decl c
  let some type' ← return <| decl.instantiate_type_univ_params univs
  let type ← drop_pis g type'
  let (args, res) ← open_pis type
  let idxs_inst := res.get_app_args.drop g.length
  let (bs, eqs) := compact_relation args (idxs.zip idxs_inst)
  let bs' := bs.filterMap id
  let eqs ←
    eqs.mmap fun ⟨idx, inst⟩ => do
        let ty := idx.local_type
        let inst_ty ← infer_type inst
        let sort u ← infer_type ty
        is_def_eq ty inst_ty >> return ((const `eq [u] : expr) ty idx inst) <|>
            return ((const `heq [u] : expr) ty idx inst_ty inst)
  let (n, r) ←
    match bs', eqs with
      | [], [] => return (Sum.inr 0, mk_true)
      | _, [] => do
        let t : expr := bs'.ilast.local_type
        let sort l ← infer_type t
        if l = level.zero then do
            let r ← mk_exists_lst bs' t
            return (Sum.inl bs', r)
          else do
            let r ← mk_exists_lst bs' mk_true
            return (Sum.inr 0, r)
      | _, _ => do
        let r ← mk_exists_lst bs' (mk_and_lst eqs)
        return (Sum.inr eqs, r)
  return ((bs, n), r)

-- TODO: document
@[nolint doc_blame]
unsafe def to_cases (s : List <| List (Option expr) × Sum expr ℕ) : tactic Unit := do
  let h ← intro1
  let i ← induction h
  focus
      ((s i).enum.map fun ⟨p, (shape, t), _, vars, _⟩ => do
        let si := (shape vars).filterMap fun ⟨c, v⟩ => c >>= fun _ => some v
        select p (s - 1)
        match t with
          | Sum.inl e => do
            si existsi
            let some v ← return <| vars (shape - 1)
            exact v
          | Sum.inr n => do
            si existsi
            (iterate_exactly (n - 1) ((split >> constructor) >> skip) >> constructor) >> skip
        done)
  done

/-- Iterate over two lists, if the first element of the first list is `none`, insert `none` into the
result and continue with the tail of first list. Otherwise, wrap the first element of the second
list with `some` and continue with the tails of both lists. Return when either list is empty.

Example:
```
list_option_merge [none, some (), none, some ()] [0, 1, 2, 3, 4] = [none, (some 0), none, (some 1)]
```
-/
def listOptionMerge {α : Type _} {β : Type _} : List (Option α) → List β → List (Option β)
  | [], _ => []
  | none :: xs, ys => none :: list_option_merge xs ys
  | some _ :: xs, y :: ys => some y :: list_option_merge xs ys
  | some _ :: xs, [] => []

-- TODO: document
@[nolint doc_blame]
unsafe def to_inductive (cs : List Name) (gs : List expr) (s : List (List (Option expr) × Sum expr ℕ)) (h : expr) :
    tactic Unit :=
  match s.length with
  | 0 => induction h >> skip
  | n + 1 => do
    let r ← elim_gen_sum n h
    focus
        ((cs (r s)).map fun ⟨constr_name, h, bs, e⟩ => do
          let n := (bs id).length
          match e with
            | Sum.inl e => elim_gen_prod (n - 1) h [] [] >> skip
            | Sum.inr 0 => do
              let (hs, h, _) ← elim_gen_prod n h [] []
              clear h
            | Sum.inr (e + 1) => do
              let (hs, h, _) ← elim_gen_prod n h [] []
              let (es, Eq, _) ← elim_gen_prod e h [] []
              let es := es ++ [Eq]
              /- `es.mmap' subst`: fails when we have dependent equalities (`heq`). `subst` will change the
                          dependent hypotheses, so that the `uniq` local names in `es` are wrong afterwards. Instead
                          we revert them and pull them out one-by-one. -/
                  revert_lst
                  es
              es fun _ => intro1 >>= subst
          let ctxt ← local_context
          let gs := ctxt gs
          let hs := (ctxt n).reverse
          let m := gs some ++ list_option_merge bs hs
          let args ←
            m fun a =>
                match a with
                | some v => return v
                | none => mk_mvar
          let c ← mk_const constr_name
          exact (c args)
          done)
    done

end MkIff

namespace Tactic

open MkIff

/-- `mk_iff_of_inductive_prop i r` makes an `iff` rule for the inductively-defined proposition `i`.
The new rule `r` has the shape `∀ps is, i as ↔ ⋁_j, ∃cs, is = cs`, where `ps` are the type
parameters, `is` are the indices, `j` ranges over all possible constructors, the `cs` are the
parameters for each of the constructors, and the equalities `is = cs` are the instantiations for
each constructor for each of the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, `mk_iff_of_inductive_prop` on `list.chain` produces:

```lean
∀ {α : Type*} (R : α → α → Prop) (a : α) (l : list α),
  chain R a l ↔ l = [] ∨ ∃{b : α} {l' : list α}, R a b ∧ chain R b l ∧ l = b :: l'
```
-/
unsafe def mk_iff_of_inductive_prop (i : Name) (r : Name) : tactic Unit := do
  let e ← get_env
  guardₓ (e i)
  let constrs := e.constructors_of i
  let params := e.inductive_num_params i
  let indices := e.inductive_num_indices i
  let rec :=
    match e.recursor_of i with
    | some rec => rec
    | none => i.append `rec
  let decl ← get_decl i
  let type := decl.type
  let univ_names := decl.univ_params
  let univs := univ_names.map level.param
  let/- we use these names for our universe parameters, maybe we should construct a copy of them
        using `uniq_name` -/
    (g, quote.1 Prop)
    ← open_pis type | fail "Inductive type is not a proposition"
  let lhs := (const i univs).mk_app g
  let shape_rhss ← constrs.mmap (constr_to_prop univs (g.take params) (g.drop params))
  let shape := shape_rhss.map Prod.fst
  let rhss := shape_rhss.map Prod.snd
  add_theorem_by r univ_names ((mk_iff lhs (mk_or_lst rhss)).pis g) do
      let gs ← intro_lst (g local_pp_name)
      split
      focus' [to_cases shape, intro1 >>= to_inductive constrs (gs params) shape]
  skip

end Tactic

section

setup_tactic_parser

/-- `mk_iff_of_inductive_prop i r` makes an `iff` rule for the inductively-defined proposition `i`.
The new rule `r` has the shape `∀ps is, i as ↔ ⋁_j, ∃cs, is = cs`, where `ps` are the type
parameters, `is` are the indices, `j` ranges over all possible constructors, the `cs` are the
parameters for each of the constructors, and the equalities `is = cs` are the instantiations for
each constructor for each of the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, `mk_iff_of_inductive_prop` on `list.chain` produces:

```lean
∀ {α : Type*} (R : α → α → Prop) (a : α) (l : list α),
  chain R a l ↔ l = [] ∨ ∃{b : α} {l' : list α}, R a b ∧ chain R b l ∧ l = b :: l'
```

See also the `mk_iff` user attribute.
-/
@[user_command]
unsafe def mk_iff_of_inductive_prop_cmd (_ : parse (tk "mk_iff_of_inductive_prop")) : parser Unit := do
  let i ← ident
  let r ← ident
  tactic.mk_iff_of_inductive_prop i r

add_tactic_doc
  { Name := "mk_iff_of_inductive_prop", category := DocCategory.cmd, declNames := [`` mk_iff_of_inductive_prop_cmd],
    tags := ["logic", "environment"] }

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- Applying the `mk_iff` attribute to an inductively-defined proposition `mk_iff` makes an `iff` rule
`r` with the shape `∀ps is, i as ↔ ⋁_j, ∃cs, is = cs`, where `ps` are the type parameters, `is` are
the indices, `j` ranges over all possible constructors, the `cs` are the parameters for each of the
constructors, and the equalities `is = cs` are the instantiations for each constructor for each of
the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, if we try the following:
```lean
@[mk_iff] structure foo (m n : ℕ) : Prop :=
(equal : m = n)
(sum_eq_two : m + n = 2)
```

Then `#check foo_iff` returns:
```lean
foo_iff : ∀ (m n : ℕ), foo m n ↔ m = n ∧ m + n = 2
```

You can add an optional string after `mk_iff` to change the name of the generated lemma.
For example, if we try the following:
```lean
@[mk_iff bar] structure foo (m n : ℕ) : Prop :=
(equal : m = n)
(sum_eq_two : m + n = 2)
```

Then `#check bar` returns:
```lean
bar : ∀ (m n : ℕ), foo m n ↔ m = n ∧ m + n = 2
```

See also the user command `mk_iff_of_inductive_prop`.
-/
@[user_attribute]
unsafe def mk_iff_attr : user_attribute Unit (Option Name) where
  Name := `mk_iff
  descr := "Generate an `iff` lemma for an inductive `Prop`."
  parser := «expr ?» ident
  after_set :=
    some fun n _ _ => do
      let tgt ← mk_iff_attr.get_param n
      tactic.mk_iff_of_inductive_prop n (tgt (n "_iff"))

add_tactic_doc
  { Name := "mk_iff", category := DocCategory.attr, declNames := [`mk_iff_attr], tags := ["logic", "environment"] }

end


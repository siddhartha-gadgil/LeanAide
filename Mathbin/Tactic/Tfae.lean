/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Simon Hudon
-/
import Mathbin.Data.List.Tfae
import Mathbin.Tactic.Scc

/-!
# The Following Are Equivalent (TFAE)

This file provides the tactics `tfae_have` and `tfae_finish` for proving the pairwise equivalence of
propositions in a set using various implications between them.
-/


namespace Tactic

export List (Tfae)

namespace Tfae

inductive Arrow : Type
  | right : arrow
  | left_right : arrow
  | left : arrow
  deriving has_reflect, Inhabited

unsafe def mk_implication : ∀ (re : Arrow) (e₁ e₂ : expr), pexpr
  | arrow.right, e₁, e₂ => pquote.1 ((%%ₓe₁) → %%ₓe₂)
  | arrow.left_right, e₁, e₂ => pquote.1 ((%%ₓe₁) ↔ %%ₓe₂)
  | arrow.left, e₁, e₂ => pquote.1 ((%%ₓe₂) → %%ₓe₁)

unsafe def mk_name : ∀ (re : Arrow) (i₁ i₂ : Nat), Name
  | arrow.right, i₁, i₂ => ("tfae_" ++ toString i₁ ++ "_to_" ++ toString i₂ : Stringₓ)
  | arrow.left_right, i₁, i₂ => ("tfae_" ++ toString i₁ ++ "_iff_" ++ toString i₂ : Stringₓ)
  | arrow.left, i₁, i₂ => ("tfae_" ++ toString i₂ ++ "_to_" ++ toString i₁ : Stringₓ)

end Tfae

namespace Interactive

setup_tactic_parser

open Tactic.Tfae List

unsafe def parse_list : expr → Option (List expr)
  | quote.1 [] => pure []
  | quote.1 ((%%ₓe) :: %%ₓes) => (· :: ·) e <$> parse_list es
  | _ => none

/-- In a goal of the form `tfae [a₀, a₁, a₂]`,
`tfae_have : i → j` creates the assertion `aᵢ → aⱼ`. The other possible
notations are `tfae_have : i ← j` and `tfae_have : i ↔ j`. The user can
also provide a label for the assertion, as with `have`: `tfae_have h : i ↔ j`.
-/
unsafe def tfae_have (h : parse <| optionalₓ ident <* tk ":") (i₁ : parse (with_desc "i" small_nat))
    (re :
      parse
        ((tk "→" <|> tk "->") *> return Arrow.right <|>
          (tk "↔" <|> tk "<->") *> return Arrow.left_right <|> (tk "←" <|> tk "<-") *> return Arrow.left))
    (i₂ : parse (with_desc "j" small_nat)) : tactic Unit := do
  let quote.1 (Tfae (%%ₓl)) ← target
  let l ← parse_list l
  let e₁ ← List.nth l (i₁ - 1) <|> fail f! "index {i₁ } is not between 1 and {l.length}"
  let e₂ ← List.nth l (i₂ - 1) <|> fail f! "index {i₂ } is not between 1 and {l.length}"
  let type ← to_expr (tfae.mk_implication re e₁ e₂)
  let h := h.getOrElse (mk_name re i₁ i₂)
  tactic.assert h type
  return ()

/-- Finds all implications and equivalences in the context
to prove a goal of the form `tfae [...]`.
-/
unsafe def tfae_finish : tactic Unit :=
  applyc `` tfae_nil <|>
    closure.with_new_closure fun cl => do
      impl_graph.mk_scc cl
      let quote.1 (Tfae (%%ₓl)) ← target
      let l ← parse_list l
      let (_, r, _) ← cl.root l.head
      refine (pquote.1 (tfae_of_forall (%%ₓr) _ _))
      let thm ← mk_const `` forall_mem_cons
      l fun e => do
          rewrite_target thm
          split
          let (_, r', p) ← cl e
          tactic.exact p
      applyc `` forall_mem_nil
      pure ()

end Interactive

end Tactic

/-- The `tfae` tactic suite is a set of tactics that help with proving that certain
propositions are equivalent.
In `data/list/basic.lean` there is a section devoted to propositions of the
form
```lean
tfae [p1, p2, ..., pn]
```
where `p1`, `p2`, through, `pn` are terms of type `Prop`.
This proposition asserts that all the `pi` are pairwise equivalent.
There are results that allow to extract the equivalence
of two propositions `pi` and `pj`.

To prove a goal of the form `tfae [p1, p2, ..., pn]`, there are two
tactics.  The first tactic is `tfae_have`.  As an argument it takes an
expression of the form `i arrow j`, where `i` and `j` are two positive
natural numbers, and `arrow` is an arrow such as `→`, `->`, `←`, `<-`,
`↔`, or `<->`.  The tactic `tfae_have : i arrow j` sets up a subgoal in
which the user has to prove the equivalence (or implication) of `pi` and `pj`.

The remaining tactic, `tfae_finish`, is a finishing tactic. It
collects all implications and equivalences from the local context and
computes their transitive closure to close the
main goal.

`tfae_have` and `tfae_finish` can be used together in a proof as
follows:

```lean
example (a b c d : Prop) : tfae [a,b,c,d] :=
begin
  tfae_have : 3 → 1,
  { /- prove c → a -/ },
  tfae_have : 2 → 3,
  { /- prove b → c -/ },
  tfae_have : 2 ← 1,
  { /- prove a → b -/ },
  tfae_have : 4 ↔ 2,
  { /- prove d ↔ b -/ },
    -- a b c d : Prop,
    -- tfae_3_to_1 : c → a,
    -- tfae_2_to_3 : b → c,
    -- tfae_1_to_2 : a → b,
    -- tfae_4_iff_2 : d ↔ b
    -- ⊢ tfae [a, b, c, d]
  tfae_finish,
end
```
-/
add_tactic_doc
  { Name := "tfae", category := DocCategory.tactic,
    declNames := [`tactic.interactive.tfae_have, `tactic.interactive.tfae_finish], tags := ["logic"],
    inheritDescriptionFrom := `tactic.interactive.tfae_finish }


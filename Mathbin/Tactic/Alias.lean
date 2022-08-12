/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Tactic.Core

/-!
# The `alias` command

This file defines an `alias` command, which can be used to create copies
of a theorem or definition with different names.

Syntax:

```lean
/-- doc string -/
alias my_theorem ← alias1 alias2 ...
```

This produces defs or theorems of the form:

```lean
/-- doc string -/
@[alias] theorem alias1 : <type of my_theorem> := my_theorem

/-- doc string -/
@[alias] theorem alias2 : <type of my_theorem> := my_theorem
```

Iff alias syntax:

```lean
alias A_iff_B ↔ B_of_A A_of_B
alias A_iff_B ↔ ..
```

This gets an existing biconditional theorem `A_iff_B` and produces
the one-way implications `B_of_A` and `A_of_B` (with no change in
implicit arguments). A blank `_` can be used to avoid generating one direction.
The `..` notation attempts to generate the 'of'-names automatically when the
input theorem has the form `A_iff_B` or `A_iff_B_left` etc.
-/


open Lean.Parser Tactic Interactive

namespace Tactic.Alias

/-- An alias can be in one of three forms -/
unsafe inductive target
  | plain : Name → target
  | forward : Name → target
  | backwards : Name → target
  deriving has_reflect

/-- The name underlying an alias target -/
unsafe def target.to_name : target → Name
  | target.plain n => n
  | target.forward n => n
  | target.backwards n => n

/-- The docstring for an alias. Used by `alias` _and_ by `to_additive` -/
unsafe def target.to_string : target → Stringₓ
  | target.plain n => s! "**Alias** of `{n}`."
  | target.forward n => s! "**Alias** of the forward direction of `{n}`."
  | target.backwards n => s! "**Alias** of the reverse direction of `{n}`."

/-- An auxiliary attribute which is placed on definitions created by the `alias` command. -/
@[user_attribute]
unsafe def alias_attr : user_attribute Unit target where
  Name := `alias
  descr := "This definition is an alias of another."
  parser := failed

/-- The core tactic which handles `alias d ← al`. Creates an alias `al` for declaration `d`. -/
unsafe def alias_direct (doc : Option Stringₓ) (d : declaration) (al : Name) : tactic Unit := do
  updateex_env fun env =>
      env
        (match d with
        | declaration.defn n ls t _ _ _ =>
          declaration.defn al ls t (expr.const n (level.param <$> ls)) ReducibilityHints.abbrev tt
        | declaration.thm n ls t _ => declaration.thm al ls t <| task.pure <| expr.const n (level.param <$> ls)
        | _ => undefined)
  let target := target.plain d.to_name
  alias_attr al target tt
  add_doc_string al (doc target)

/-- Given a proof of `Π x y z, a ↔ b`, produces a proof of `Π x y z, a → b` or `Π x y z, b → a`
(depending on whether `iffmp` is `iff.mp` or `iff.mpr`). The variable `f` supplies the proof,
under the specified number of binders. -/
unsafe def mk_iff_mp_app (iffmp : Name) : expr → (ℕ → expr) → tactic expr
  | expr.pi n bi e t, f => expr.lam n bi e <$> mk_iff_mp_app t fun n => f (n + 1) (expr.var n)
  | quote.1 ((%%ₓa) ↔ %%ₓb), f => pure <| @expr.const true iffmp [] a b (f 0)
  | _, f => fail "Target theorem must have the form `Π x y z, a ↔ b`"

/-- The core tactic which handles `alias d ↔ al _` or `alias d ↔ _ al`. `ns` is the current
namespace, and `is_forward` is true if this is the forward implication (the first form). -/
unsafe def alias_iff (doc : Option Stringₓ) (d : declaration) (ns al : Name) (is_forward : Bool) : tactic Unit :=
  if al = `_ then skip
  else
    let al := ns.append_namespace al
    get_decl al >> skip <|> do
      let ls := d.univ_params
      let t := d.type
      let target := if is_forward then target.forward d.to_name else target.backwards d.to_name
      let iffmp := if is_forward then `iff.mp else `iff.mpr
      let v ← mk_iff_mp_app iffmp t fun _ => expr.const d.to_name (level.param <$> ls)
      let t' ← infer_type v
      updateex_env fun env => env (declaration.thm al ls t' <| task.pure v)
      alias_attr al target tt
      add_doc_string al (doc target)

/-- Get the default names for left/right to be used by `alias d ↔ ..`. -/
unsafe def make_left_right : Name → tactic (Name × Name)
  | Name.mk_string s p => do
    let buf : CharBuffer := s.toCharBuffer
    let parts := s.splitOn '_'
    let (left, _ :: right) ← pure <| parts.span (· ≠ "iff")
    let pfx (a b : Stringₓ) := a.toList.isPrefixOf b.toList
    let (suffix', right') ← pure <| right.reverse.span fun s => pfx "left" s ∨ pfx "right" s
    let right := right'.reverse
    let suffix := suffix'.reverse
    pure
        (mkStrName p ("_".intercalate (right ++ "of" :: left ++ suffix)),
          mkStrName p ("_".intercalate (left ++ "of" :: right ++ suffix)))
  | _ => failed

/-- The `alias` command can be used to create copies
of a theorem or definition with different names.

Syntax:

```lean
/-- doc string -/
alias my_theorem ← alias1 alias2 ...
```

This produces defs or theorems of the form:

```lean
/-- doc string -/
@[alias] theorem alias1 : <type of my_theorem> := my_theorem

/-- doc string -/
@[alias] theorem alias2 : <type of my_theorem> := my_theorem
```

Iff alias syntax:

```lean
alias A_iff_B ↔ B_of_A A_of_B
alias A_iff_B ↔ ..
```

This gets an existing biconditional theorem `A_iff_B` and produces
the one-way implications `B_of_A` and `A_of_B` (with no change in
implicit arguments). A blank `_` can be used to avoid generating one direction.
The `..` notation attempts to generate the 'of'-names automatically when the
input theorem has the form `A_iff_B` or `A_iff_B_left` etc.
-/
@[user_command]
unsafe def alias_cmd (meta_info : decl_meta_info) (_ : parse <| tk "alias") : lean.parser Unit := do
  let old ← ident
  let d ←
    (do
          let old ← resolve_constant old
          get_decl old) <|>
        fail ("declaration " ++ toString old ++ " not found")
  let ns ← get_current_namespace
  let doc := meta_info.doc_string
  (do
        tk "←" <|> tk "<-"
        let aliases ← many ident
        ↑(aliases fun al => alias_direct doc d (ns al))) <|>
      do
      tk "↔" <|> tk "<->"
      let (left, right) ←
        mcond (tk ".." >> pure tt <|> pure ff)
            (make_left_right old <|> fail "invalid name for automatic name generation")
            (Prod.mk <$> types.ident_ <*> types.ident_)
      alias_iff doc d ns left tt
      alias_iff doc d ns right ff

add_tactic_doc
  { Name := "alias", category := DocCategory.cmd, declNames := [`tactic.alias.alias_cmd], tags := ["renaming"] }

/-- Given a definition, look up the definition that it is an alias of.
Returns `none` if this defintion is not an alias. -/
unsafe def get_alias_target (n : Name) : tactic (Option target) := do
  let tt ← has_attribute' `alias n | pure none
  let v ← alias_attr.get_param n
  pure <| some v

end Tactic.Alias


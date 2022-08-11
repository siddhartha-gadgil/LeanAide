/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Minchao Wu
-/
import Mathbin.Meta.RbMap
import Mathbin.Tactic.Core

/-!
# `#explode` command

Displays a proof term in a line by line format somewhat akin to a Fitch style
proof or the Metamath proof style.
-/


open Expr Tactic

namespace Tactic

namespace Explode

inductive Status : Type
  | reg
  | intro
  | lam
  | sintro
  deriving Inhabited

/-- A type to distinguish introduction or elimination rules represented as
strings from theorems referred to by their names.
-/
unsafe inductive thm : Type
  | expr (e : expr)
  | Name (n : Name)
  | Stringₓ (s : Stringₓ)

/-- Turn a thm into a string.
-/
unsafe def thm.to_string : thm → Stringₓ
  | thm.expr e => e.toString
  | thm.name n => n.toString
  | thm.string s => s

unsafe structure entry : Type where
  expr : expr
  line : Nat
  depth : Nat
  Status : Status
  thm : thm
  deps : List Nat

unsafe def pad_right (l : List Stringₓ) : List Stringₓ :=
  let n := l.foldl (fun r (s : Stringₓ) => max r s.length) 0
  l.map fun s => Nat.iterate (fun s => s.push ' ') (n - s.length) s

unsafe structure entries : Type where mk' ::
  s : expr_map entry
  l : List entry
  deriving Inhabited

unsafe def entries.find (es : entries) (e : expr) : Option entry :=
  es.s.find e

unsafe def entries.size (es : entries) : ℕ :=
  es.s.size

unsafe def entries.add : entries → entry → entries
  | es@⟨s, l⟩, e => if s.contains e.expr then es else ⟨s.insert e.expr e, e :: l⟩

unsafe def entries.head (es : entries) : Option entry :=
  es.l.head'

unsafe def format_aux : List Stringₓ → List Stringₓ → List Stringₓ → List entry → tactic format
  | line :: lines, dep :: deps, thm :: thms, en :: es => do
    let fmt ←
      do
        let margin := Stringₓ.join (List.repeat " │" en.depth)
        let margin :=
          match en.Status with
          | status.sintro => " ├" ++ margin
          | status.intro => " │" ++ margin ++ " ┌"
          | status.reg => " │" ++ margin ++ ""
          | status.lam => " │" ++ margin ++ ""
        let p ← infer_type en.expr >>= pp
        let lhs := line ++ "│" ++ dep ++ "│ " ++ thm ++ margin ++ " "
        return <| format.of_string lhs ++ (p lhs).group ++ format.line
    (· ++ fmt) <$> format_aux lines deps thms es
  | _, _, _, _ => return format.nil

unsafe instance : has_to_tactic_format entries :=
  ⟨fun es : entries =>
    let lines := pad_right <| es.l.map fun en => toString en.line
    let deps := pad_right <| es.l.map fun en => Stringₓ.intercalate "," (en.deps.map toString)
    let thms := pad_right <| es.l.map fun en => (entry.thm en).toString
    format_aux lines deps thms es.l⟩

unsafe def append_dep (filter : expr → tactic Unit) (es : entries) (e : expr) (deps : List Nat) : tactic (List Nat) :=
  (do
      let ei ← es.find e
      filter ei
      return (ei :: deps)) <|>
    return deps

unsafe def may_be_proof (e : expr) : tactic Bool := do
  let expr.sort u ← infer_type e >>= infer_type
  return <| bnot u

end Explode

open Explode

mutual
  unsafe def explode.core (filter : expr → tactic Unit) : expr → Bool → Nat → entries → tactic entries
    | e@(lam n bi d b), si, depth, es => do
      let m ← mk_fresh_name
      let l := local_const m n bi d
      let b' := instantiate_var b l
      if si then
          let en : entry := ⟨l, es, depth, status.sintro, thm.name n, []⟩
          do
          let es' ← explode.core b' si depth (es en)
          return <| es' ⟨e, es', depth, status.lam, thm.string "∀I", [es, es' - 1]⟩
        else do
          let en : entry := ⟨l, es, depth, status.intro, thm.name n, []⟩
          let es' ← explode.core b' si (depth + 1) (es en)
          let deps'
            ←-- in case of a "have" clause, the b' here has an annotation
                explode.append_dep
                filter es' b' []
          let deps' ← explode.append_dep filter es' l deps'
          return <| es' ⟨e, es', depth, status.lam, thm.string "∀I", deps'⟩
    | e@(elet n t a b), si, depth, es => explode.core (reduce_lets e) si depth es
    | e@(macro n l), si, depth, es => explode.core l.head si depth es
    | e, si, depth, es =>
      filter e >>
        match get_app_fn_args e with
        | (nm@(const n _), args) => explode.args e args depth es (thm.expr nm) []
        | (fn, []) => do
          let en : entry := ⟨fn, es.size, depth, Status.reg, thm.expr fn, []⟩
          return (es en)
        | (fn, args) => do
          let es' ← explode.core fn false depth es
          let deps
            ←-- in case of a "have" clause, the fn here has an annotation
                explode.append_dep
                filter es' fn.erase_annotations []
          explode.args e args depth es' (thm.string "∀E") deps
  unsafe def explode.args (filter : expr → tactic Unit) :
      expr → List expr → Nat → entries → thm → List Nat → tactic entries
    | e, arg :: args, depth, es, thm, deps => do
      let es' ← explode.core arg false depth es <|> return es
      let deps' ← explode.append_dep filter es' arg deps
      explode.args e args depth es' thm deps'
    | e, [], depth, es, thm, deps => return (es.add ⟨e, es.size, depth, Status.reg, thm, deps.reverse⟩)
end

unsafe def explode_expr (e : expr) (hide_non_prop := true) : tactic entries :=
  let filter := if hide_non_prop then fun e => may_be_proof e >>= guardb else fun _ => skip
  tactic.explode.core filter e true 0 default

unsafe def explode (n : Name) : tactic Unit := do
  let const n _ ← resolve_name n | fail "cannot resolve name"
  let d ← get_decl n
  let v ←
    match d with
      | declaration.defn _ _ _ v _ _ => return v
      | declaration.thm _ _ _ v => return v.get
      | _ => fail "not a definition"
  let t ← pp d.type
  explode_expr v <* trace (to_fmt n ++ " : " ++ t) >>= trace

setup_tactic_parser

/-- `#explode decl_name` displays a proof term in a line-by-line format somewhat akin to a Fitch-style
proof or the Metamath proof style.
`#explode_widget decl_name` renders a widget that displays an `#explode` proof.

`#explode iff_true_intro` produces

```lean
iff_true_intro : ∀ {a : Prop}, a → (a ↔ true)
0│   │ a         ├ Prop
1│   │ h         ├ a
2│   │ hl        │ ┌ a
3│   │ trivial   │ │ true
4│2,3│ ∀I        │ a → true
5│   │ hr        │ ┌ true
6│5,1│ ∀I        │ true → a
7│4,6│ iff.intro │ a ↔ true
8│1,7│ ∀I        │ a → (a ↔ true)
9│0,8│ ∀I        │ ∀ {a : Prop}, a → (a ↔ true)
```

In more detail:

The output of `#explode` is a Fitch-style proof in a four-column diagram modeled after Metamath
proof displays like [this](http://us.metamath.org/mpeuni/ru.html). The headers of the columns are
"Step", "Hyp", "Ref", "Type" (or "Expression" in the case of Metamath):
* Step: An increasing sequence of numbers to number each step in the proof, used in the Hyp field.
* Hyp: The direct children of the current step. Most theorems are implications like `A -> B -> C`,
  and so on the step proving `C` the Hyp field will refer to the steps that prove `A` and `B`.
* Ref: The name of the theorem being applied. This is well-defined in Metamath, but in Lean there
  are some special steps that may have long names because the structure of proof terms doesn't
  exactly match this mold.
  * If the theorem is `foo (x y : Z) : A x -> B y -> C x y`:
    * the Ref field will contain `foo`,
    * `x` and `y` will be suppressed, because term construction is not interesting, and
    * the Hyp field will reference steps proving `A x` and `B y`. This corresponds to a proof term
      like `@foo x y pA pB` where `pA` and `pB` are subproofs.
  * If the head of the proof term is a local constant or lambda, then in this case the Ref will
    say `∀E` for forall-elimination. This happens when you have for example `h : A -> B` and
    `ha : A` and prove `b` by `h ha`; we reinterpret this as if it said `∀E h ha` where `∀E` is
    (n-ary) modus ponens.
  * If the proof term is a lambda, we will also use `∀I` for forall-introduction, referencing the
    body of the lambda. The indentation level will increase, and a bracket will surround the proof
    of the body of the lambda, starting at a proof step labeled with the name of the lambda variable
    and its type, and ending with the `∀I` step. Metamath doesn't have steps like this, but the
    style is based on Fitch proofs in first-order logic.
* Type: This contains the type of the proof term, the theorem being proven at the current step.
  This proof layout differs from `#print` in using lots of intermediate step displays so that you
  can follow along and don't have to see term construction steps because they are implicitly in the
  intermediate step displays.

Also, it is common for a Lean theorem to begin with a sequence of lambdas introducing local
constants of the theorem. In order to minimize the indentation level, the `∀I` steps at the end of
the proof will be introduced in a group and the indentation will stay fixed. (The indentation
brackets are only needed in order to delimit the scope of assumptions, and these assumptions
have global scope anyway so detailed tracking is not necessary.)
-/
@[user_command]
unsafe def explode_cmd (_ : parse <| tk "#explode") : parser Unit := do
  let n ← ident
  explode n

add_tactic_doc
  { Name := "#explode / #explode_widget", category := DocCategory.cmd,
    declNames := [`tactic.explode_cmd, `tactic.explode_widget_cmd], inheritDescriptionFrom := `tactic.explode_cmd,
    tags := ["proof display", "widgets"] }

end Tactic


/-
Copyright (c) 2019 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek
-/
import Mathbin.Tactic.Core

/-!
# The `where` command

When working in a Lean file with namespaces, parameters, and variables, it can be confusing to
identify what the current "parser context" is. The command `#where` identifies and prints
information about the current location, including the active namespace, open namespaces, and
declared variables.

It is a bug for `#where` to incorrectly report this information (this was not formerly the case);
please file an issue on GitHub if you observe a failure.
-/


open Lean.Parser Tactic

namespace Where

/-- Assigns a priority to each binder for determining the order in which variables are traced. -/
unsafe def binder_priority : BinderInfo → ℕ
  | BinderInfo.implicit => 1
  | BinderInfo.strict_implicit => 2
  | BinderInfo.default => 3
  | BinderInfo.inst_implicit => 4
  | BinderInfo.aux_decl => 5

/-- The relation on binder priorities. -/
unsafe def binder_less_important (u v : BinderInfo) : Bool :=
  binder_priority u < binder_priority v

/-- Selects the elements of the given `list α` which under the image of `p : α → β × γ` have `β`
component equal to `b'`. Returns the `γ` components of the selected elements under the image of `p`,
and the elements of the original `list α` which were not selected. -/
def selectForWhich {α β γ : Type} (p : α → β × γ) [DecidableEq β] (b' : β) : List α → List γ × List α
  | [] => ([], [])
  | a :: rest =>
    let (cs, others) := select_for_which rest
    let (b, c) := p a
    if b = b' then (c :: cs, others) else (cs, a :: others)

/-- Helper function for `collect_by`. -/
private unsafe def collect_by_aux {α β γ : Type} (p : α → β × γ) [DecidableEq β] : List β → List α → List (β × List γ)
  | [], [] => []
  | [], _ => undefined_core "didn't find every key entry!"
  | b :: rest, as =>
    let (cs, as) := selectForWhich p b as
    (b, cs) :: collect_by_aux rest as

/-- Returns the elements of `l` under the image of `p`, collecting together elements with the same
`β` component, deleting duplicates. -/
unsafe def collect_by {α β γ : Type} (l : List α) (p : α → β × γ) [DecidableEq β] : List (β × List γ) :=
  collect_by_aux p (l.map <| Prod.fst ∘ p).dedup l

/-- Sort the variables by their priority as defined by `where.binder_priority`. -/
unsafe def sort_variable_list (l : List (Name × BinderInfo × expr)) : List (expr × BinderInfo × List Name) :=
  let l := (collect_by l) fun v => (v.2.2, (v.1, v.2.1))
  let l := l.map fun el => (el.1, (collect_by el.2) fun v => (v.2, v.1))
  (List.join <| l.map fun e => Prod.mk e.1 <$> e.2).qsort fun v u => binder_less_important v.2.1 u.2.1

/-- Separate out the names of implicit variables (commonly instances with no name). -/
unsafe def collect_implicit_names : List Name → List Stringₓ × List Stringₓ
  | [] => ([], [])
  | n :: ns =>
    let n := toString n
    let (ns, ins) := collect_implicit_names ns
    if n.front = '_' then (ns, n :: ins) else (n :: ns, ins)

/-- Format an individual variable definition for printing. -/
unsafe def format_variable : expr × BinderInfo × List Name → tactic Stringₓ
  | (e, bi, ns) => do
    let (l, r) := bi.brackets
    let e ← pp e
    let (ns, ins) := collect_implicit_names ns
    let ns := " ".intercalate <| ns.map toString
    let ns := if ns.length = 0 then [] else [s! "{l }{ns } : {e }{r}"]
    let ins := ins.map fun _ => s! "{l }{e }{r}"
    return <| " ".intercalate <| ns ++ ins

/-- Turn a list of triples of variable names, binder info, and types, into a pretty list. -/
unsafe def compile_variable_list (l : List (Name × BinderInfo × expr)) : tactic Stringₓ :=
  " ".intercalate <$> (sort_variable_list l).mmap format_variable

/-- Strips the namespace prefix `ns` from `n`. -/
private unsafe def strip_namespace (ns n : Name) : Name :=
  n.replace_prefix ns Name.anonymous

/-- `get_open_namespaces ns` returns a list of the open namespaces, given that we are currently in
the namespace `ns` (which we do not include). -/
unsafe def get_open_namespaces (ns : Name) : tactic (List Name) := do
  let opens ← List.dedup <$> tactic.open_namespaces
  return <| (opens ns).map <| strip_namespace ns

/-- Give a slightly friendlier name for `name.anonymous` in the context of your current namespace.
-/
private unsafe def explain_anonymous_name : Name → Stringₓ
  | Name.anonymous => "[root namespace]"
  | ns => toString ns

/-- `#where` output helper which traces the current namespace. -/
unsafe def build_str_namespace (ns : Name) : lean.parser Stringₓ :=
  return s! "namespace {explain_anonymous_name ns}"

/-- `#where` output helper which traces the open namespaces. -/
unsafe def build_str_open_namespaces (ns : Name) : tactic Stringₓ := do
  let l ← get_open_namespaces ns
  let str := " ".intercalate <| l.map toString
  if l then return "" else return s! "open {str}"

/-- `#where` output helper which traces the variables. -/
unsafe def build_str_variables : lean.parser Stringₓ := do
  let l ← get_variables
  let str ← compile_variable_list l
  if l then return "" else return s! "variables {str}"

/-- `#where` output helper which traces the includes. -/
unsafe def build_str_includes : lean.parser Stringₓ := do
  let l ← get_included_variables
  let str := " ".intercalate <| l.map fun n => toString n.1
  if l then return "" else return s! "include {str}"

/-- `#where` output helper which traces the namespace end. -/
unsafe def build_str_end (ns : Name) : tactic Stringₓ :=
  return s! "end {explain_anonymous_name ns}"

/-- `#where` output helper which traces newlines. -/
private unsafe def append_nl (s : Stringₓ) (n : ℕ) : tactic Stringₓ :=
  return <| s ++ (List.asStringₓ <| (List.range n).map fun _ => '\n')

/-- `#where` output helper which traces lines, adding a newline if nonempty. -/
private unsafe def append_line (s : Stringₓ) (t : lean.parser Stringₓ) : lean.parser Stringₓ := do
  let v ← t
  return <| s ++ v ++ if v = 0 then "" else "\n"

/-- `#where` output main function. -/
unsafe def build_msg : lean.parser Stringₓ := do
  let msg := ""
  let ns ← get_current_namespace
  let msg ← append_line msg <| build_str_namespace ns
  let msg ← append_nl msg 1
  let msg ← append_line msg <| build_str_open_namespaces ns
  let msg ← append_line msg <| build_str_variables
  let msg ← append_line msg <| build_str_includes
  let msg ← append_nl msg 3
  let msg ← append_line msg <| build_str_end ns
  return msg

open Interactive

/-- When working in a Lean file with namespaces, parameters, and variables, it can be confusing to
identify what the current "parser context" is. The command `#where` identifies and prints
information about the current location, including the active namespace, open namespaces, and
declared variables.

It is a bug for `#where` to incorrectly report this information (this was not formerly the case);
please file an issue on GitHub if you observe a failure.
-/
@[user_command]
unsafe def where_cmd (_ : parse <| tk "#where") : lean.parser Unit := do
  let msg ← build_msg
  trace msg

add_tactic_doc
  { Name := "#where", category := DocCategory.cmd, declNames := [`where.where_cmd], tags := ["environment"] }

end Where


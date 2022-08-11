/-
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers
-/

/-!
# Widgets used for tactic state and term-mode goal display

The vscode extension supports the display of interactive widgets.
Default implementation of these widgets are included in the core
library.  We override them here using `vm_override` so that we can
change them quickly without waiting for the next Lean release.

The function `widget_override.interactive_expression.mk` renders a single
expression as a widget component.  Each goal in a tactic state is rendered
using the `widget_override.tactic_view_goal` function,
a complete tactic state is rendered using
`widget_override.tactic_view_component`.

Lean itself calls the `widget_override.term_goal_widget` function to render
term-mode goals and `widget_override.tactic_state_widget` to render the
tactic state in a tactic proof.
-/


namespace WidgetOverride

open Widget

open TaggedFormat

open Widget.Html Widget.Attr

namespace InteractiveExpression

unsafe instance : HasMem Expr.Coord Expr.Address :=
  List.hasMem

/-- eformat but without any of the formatting stuff like highlighting, groups etc. -/
unsafe inductive sf : Type
  | tag_expr : Expr.Address → expr → sf → sf
  | compose : sf → sf → sf
  | of_string : Stringₓ → sf
  | highlight : Format.Color → sf → sf
  | block : ℕ → sf → sf

/-- Prints a debugging representation of an `sf` object. -/
unsafe def sf.repr : sf → format
  | sf.tag_expr addr e a =>
    format.group <|
      format.nest 2 <|
        "(tag_expr " ++ to_fmt addr ++ format.line ++ "`(" ++ to_fmt e ++ ")" ++ format.line ++ a.repr ++ ")"
  | sf.compose a b => a.repr ++ format.line ++ b.repr
  | sf.of_string s => reprₓ s
  | sf.block i a => "(block " ++ to_fmt i ++ format.line ++ a.repr ++ ")"
  | sf.highlight c a => "(highlight " ++ c.toString ++ a.repr ++ ")"

unsafe instance : has_to_format sf :=
  ⟨sf.repr⟩

unsafe instance : HasToString sf :=
  ⟨fun s => s.repr.toString⟩

unsafe instance : HasRepr sf :=
  ⟨fun s => s.repr.toString⟩

/-- Constructs an `sf` from an `eformat` by forgetting grouping, nesting, etc. -/
unsafe def sf.of_eformat : eformat → sf
  | tag ⟨ea, e⟩ m => sf.tag_expr ea e <| sf.of_eformat m
  | group m => sf.block 0 <| sf.of_eformat m
  | nest i m => sf.block i <| sf.of_eformat m
  | highlight c m => sf.highlight c <| sf.of_eformat m
  | of_format f => sf.of_string <| format.to_string f
  | compose x y => sf.compose (sf.of_eformat x) (sf.of_eformat y)

/-- Flattens an `sf`, i.e. merges adjacent `of_string` constructors. -/
unsafe def sf.flatten : sf → sf
  | sf.tag_expr ea e m => sf.tag_expr ea e <| sf.flatten m
  | sf.compose x y =>
    match sf.flatten x, sf.flatten y with
    | sf.of_string sx, sf.of_string sy => sf.of_string (sx ++ sy)
    | sf.of_string sx, sf.compose (sf.of_string sy) z => sf.compose (sf.of_string (sx ++ sy)) z
    | sf.compose x (sf.of_string sy), sf.of_string sz => sf.compose x (sf.of_string (sy ++ sz))
    | sf.compose x (sf.of_string sy1), sf.compose (sf.of_string sy2) z =>
      sf.compose x (sf.compose (sf.of_string (sy1 ++ sy2)) z)
    | x, y => sf.compose x y
  |
  sf.of_string s =>-- replace newline by space
      sf.of_string
      (s.toList.map fun c => if c = '\n' then ' ' else c).asString
  | sf.block i (sf.block j a) => (sf.block (i + j) a).flatten
  | sf.block i a => sf.block i a.flatten
  | sf.highlight i a => sf.highlight i a.flatten

private unsafe def elim_part_apps : sf → Expr.Address → sf
  | sf.tag_expr ea e m, Acc =>
    if ∀, ∀ c ∈ ea, ∀, c = Expr.Coord.app_fn then elim_part_apps m (Acc ++ ea)
    else sf.tag_expr (Acc ++ ea) e (elim_part_apps m [])
  | sf.compose a b, Acc => (elim_part_apps a Acc).compose (elim_part_apps b Acc)
  | sf.of_string s, _ => sf.of_string s
  | sf.block i a, Acc => sf.block i <| elim_part_apps a Acc
  | sf.highlight c a, Acc => sf.highlight c <| elim_part_apps a Acc

/-- Post-process an `sf` object to eliminate tags for partial applications by
pushing the `app_fn` as far into the expression as possible. The effect is
that clicking on a sub-expression always includes the full argument list in
the popup.

Consider the expression `id id 0`. We push the `app_fn` for the partial
application `id id` inwards and eliminate it.  Before:
```
(tag_expr [app_fn]
  `(id.{1} (nat -> nat) (id.{1} nat))
  (tag_expr [app_fn] `(id.{1} (nat -> nat)) "id")
  "\n"
  (tag_expr [app_arg] `(id.{1} nat) "id"))
"\n"
(tag_expr [app_arg] `(has_zero.zero.{0} nat nat.has_zero) "0")
```
After:
```
"id"
"\n"
(tag_expr [app_fn, app_arg] `(id.{1} nat) "id")
"\n"
(tag_expr [app_arg] `(has_zero.zero.{0} nat nat.has_zero) "0")
```
-/
unsafe def sf.elim_part_apps (s : sf) : sf :=
  elim_part_apps s []

/-- The actions accepted by an expression widget.
-/
unsafe inductive action (γ : Type)
  | on_mouse_enter : subexpr → action
  | on_mouse_leave_all : action
  | on_click : subexpr → action
  | on_tooltip_action : γ → action
  | on_close_tooltip : action
  | effect : widget.effect → action

/-- Render a 'go to definition' button for a given expression.
If there is no definition available, then returns an empty list.
-/
unsafe def goto_def_button {γ} : expr → tactic (List (html (action γ)))
  | e =>
    (do
        let expr.const n _ ← pure <| expr.get_app_fn e
        let env ← tactic.get_env
        let file := environment.decl_olean env n
        let pos ← environment.decl_pos env n
        pure <|
            [h "button"
                [cn "pointer ba br3 mr1", on_click fun _ => action.effect <| widget.effect.reveal_position file Pos,
                  attr.val "title" "go to definition"]
                ["↪"]]) <|>
      pure []

/-- Due to a bug in the webview browser, we have to reduce the number of spans in the expression.
To do this, we collect the attributes from `sf.block` and `sf.highlight` after an expression
boundary. -/
unsafe def get_block_attrs {γ} : sf → tactic (sf × List (attr γ))
  | sf.block i a => do
    let s : attr γ :=
      style
        [("display", "inline-block"), ("padding-left", "1ch"), ("text-indent", "-1ch"), ("white-space", "pre-wrap"),
          ("vertical-align", "top")]
    let (a, rest) ← get_block_attrs a
    pure (a, s :: rest)
  | sf.highlight c a => do
    let (a, rest) ← get_block_attrs a
    pure (a, cn c :: rest)
  | a => pure (a, [])

/-- Renders a subexpression as a list of html elements.
-/
unsafe def view {γ} (tooltip_component : tc subexpr (action γ)) (click_address : Option Expr.Address)
    (select_address : Option Expr.Address) : subexpr → sf → tactic (List (html (action γ)))
  | ⟨ce, current_address⟩, sf.tag_expr ea e m => do
    let new_address := current_address ++ ea
    let select_attrs : List (attr (action γ)) :=
      if some new_address = select_address then [className "highlight"] else []
    let click_attrs : List (attr (action γ)) ←
      if some new_address = click_address then do
          let content ← tc.to_html tooltip_component (e, new_address)
          let efmt : Stringₓ ← format.to_string <$> tactic.pp e
          let gd_btn ← goto_def_button e
          pure
              [tooltip <|
                  h "div" []
                    [h "div" [cn "fr"]
                        (gd_btn ++
                          [h "button"
                              [cn "pointer ba br3 mr1", on_click fun _ => action.effect <| widget.effect.copy_text efmt,
                                attr.val "title" "copy expression to clipboard"]
                              ["📋"],
                            h "button"
                              [cn "pointer ba br3", on_click fun _ => action.on_close_tooltip, attr.val "title" "close"]
                              ["×"]]),
                      content]]
        else pure []
    let (m, block_attrs) ← get_block_attrs m
    let as := [className "expr-boundary", key ea] ++ select_attrs ++ click_attrs ++ block_attrs
    let inner ← view (e, new_address) m
    pure [h "span" as inner]
  | ca, sf.compose x y => pure (· ++ ·) <*> view ca x <*> view ca y
  | ca, sf.of_string s =>
    pure
      [h "span" [on_mouse_enter fun _ => action.on_mouse_enter ca, on_click fun _ => action.on_click ca, key s]
          [html.of_string s]]
  | ca, b@(sf.block _ _) => do
    let (a, attrs) ← get_block_attrs b
    let inner ← view ca a
    pure [h "span" attrs inner]
  | ca, b@(sf.highlight _ _) => do
    let (a, attrs) ← get_block_attrs b
    let inner ← view ca a
    pure [h "span" attrs inner]

/-- Make an interactive expression. -/
unsafe def mk {γ} (tooltip : tc subexpr γ) : tc expr γ :=
  let tooltip_comp :=
    (component.with_should_update fun x y : tactic_state × expr × Expr.Address => x.2.2 ≠ y.2.2) <|
      component.map_action action.on_tooltip_action tooltip
  (component.filter_map_action fun _ (a : Sum γ widget.effect) => Sum.casesOn a some fun _ => none) <|
    (component.with_effects fun _ (a : Sum γ widget.effect) =>
        match a with
        | Sum.inl g => []
        | Sum.inr s => [s]) <|
      tc.mk_simple (action γ) (Option subexpr × Option subexpr) (fun e => pure <| (none, none))
        (fun e ⟨ca, sa⟩ act =>
          pure <|
            match act with
            | action.on_mouse_enter ⟨e, ea⟩ => ((ca, some (e, ea)), none)
            | action.on_mouse_leave_all => ((ca, none), none)
            | action.on_click ⟨e, ea⟩ => if some (e, ea) = ca then ((none, sa), none) else ((some (e, ea), sa), none)
            | action.on_tooltip_action g => ((none, sa), some <| Sum.inl g)
            | action.on_close_tooltip => ((none, sa), none)
            | action.effect e => ((ca, sa), some <| Sum.inr <| e))
        fun e ⟨ca, sa⟩ => do
        let m ← sf.of_eformat <$> tactic.pp_tagged e
        let m := m.elim_part_apps
        let m := m.flatten
        let-- [hack] in pp.cpp I forgot to add an expr-boundary for the root expression.
        m := m.tag_expr [] e
        let v ← view tooltip_comp (Prod.snd <$> ca) (Prod.snd <$> sa) ⟨e, []⟩ m
        pure <| [h "span" [className "expr", key e, on_mouse_leave fun _ => action.on_mouse_leave_all] <| v]

/-- Render the implicit arguments for an expression in fancy, little pills. -/
unsafe def implicit_arg_list (tooltip : tc subexpr Empty) (e : expr) : tactic <| html Empty := do
  let fn ← mk tooltip <| expr.get_app_fn e
  let args ← List.mmapₓ (mk tooltip) <| expr.get_app_args e
  pure <|
      h "div" [style [("display", "flex"), ("flexWrap", "wrap"), ("alignItems", "baseline")]]
        (h "span" [className "bg-blue br3 ma1 ph2 white"] [fn] ::
          List.map (fun a => h "span" [className "bg-gray br3 ma1 ph2 white"] [a]) args)

/-- Component for the type tooltip.
-/
unsafe def type_tooltip : tc subexpr Empty :=
  tc.stateless fun ⟨e, ea⟩ => do
    let y ← tactic.infer_type e
    let y_comp ← mk type_tooltip y
    let implicit_args ← implicit_arg_list type_tooltip e
    pure
        [h "div"
            [style
                [("minWidth", "8rem"),-- [note]: textIndent is inherited, and we might
                  -- be in an expression here where textIndent is set
                  ("textIndent", "0")]]
            [h "div" [cn "pl1"] [y_comp], h "hr" [] [], implicit_args]]

end InteractiveExpression

/-- Supported tactic state filters.
-/
unsafe inductive filter_type
  | none
  | no_instances
  | only_props
  deriving DecidableEq

/-- Filters a local constant using the given filter.
-/
unsafe def filter_local : filter_type → expr → tactic Bool
  | filter_type.none, e => pure true
  | filter_type.no_instances, e => do
    let t ← tactic.infer_type e
    bnot <$> tactic.is_class t
  | filter_type.only_props, e => do
    let t ← tactic.infer_type e
    tactic.is_prop t

/-- Component for the filter dropdown.
-/
unsafe def filter_component : component filter_type filter_type :=
  component.stateless fun lf =>
    [h "label" [] ["filter: "],
      select
        [⟨filter_type.none, "0", ["no filter"]⟩, ⟨filter_type.no_instances, "1", ["no instances"]⟩,
          ⟨filter_type.only_props, "2", ["only props"]⟩]
        lf]

/-- Converts a name into an html element.
-/
unsafe def html.of_name {α : Type} : Name → html α
  | n => html.of_string <| Name.toString n

open Tactic

/-- Component that shows a type.
-/
unsafe def show_type_component : tc expr Empty :=
  tc.stateless fun x => do
    let y ← infer_type x
    let y_comp ← interactive_expression.mk interactive_expression.type_tooltip <| y
    pure y_comp

/-- A group of local constants in the context that should be rendered as one line. -/
unsafe structure local_collection where
  key : Stringₓ
  locals : List expr
  type : expr
  value : Option expr
  deriving DecidableEq

/-- Converts a single local constant into a (singleton) `local_collection` -/
unsafe def to_local_collection (l : expr) : tactic local_collection :=
  tactic.unsafe.type_context.run <| do
    let lctx ← tactic.unsafe.type_context.get_local_context
    let some ldecl ← pure <| lctx.get_local_decl l.local_uniq_name
    pure { key := l, locals := [l], type := ldecl, value := ldecl }

/-- Groups consecutive local collections by type -/
unsafe def group_local_collection : List local_collection → List local_collection
  | a :: b :: rest =>
    if a.type = b.type ∧ a.value = b.value then
      group_local_collection <| { a with locals := a.locals ++ b.locals } :: rest
    else a :: group_local_collection (b :: rest)
  | ls => ls

/-- Component that displays the main (first) goal. -/
unsafe def tactic_view_goal {γ} (local_c : tc local_collection γ) (target_c : tc expr γ) : tc filter_type γ :=
  tc.stateless fun ft => do
    let g@(expr.mvar u_n pp_n y) ← main_goal
    let t ← get_tag g
    let case_tag : List (html γ) :=
      match interactive.case_tag.parse t with
      | some t =>
        [h "li" [key "_case"] <| [h "span" [cn "goal-case b"] ["case"]] ++ t.case_names.bind fun n => [" ", n]]
      | none => []
    let lcs ← local_context
    let lcs ← List.mfilter (filter_local ft) lcs
    let lcs ← lcs.mmap <| to_local_collection
    let lcs := group_local_collection lcs
    let lchs ←
      lcs.mmap fun lc => do
          let lh ← local_c lc
          let ns : List (html γ) :=
            lc.locals.map fun n => h "span" [cn "goal-hyp b pr2", key n.local_uniq_name] [html.of_name n.local_pp_name]
          pure <| h "li" [key lc] (ns ++ [": ", h "span" [cn "goal-hyp-type", key "type"] [lh]])
    let t_comp ← target_c g
    pure <|
        h "ul" [key g, className "list pl0 font-code"] <|
          case_tag ++ lchs ++ [h "li" [key u_n] [h "span" [cn "goal-vdash b"] ["⊢ "], t_comp]]

/-- Actions accepted by the `tactic_view_component`.
-/
unsafe inductive tactic_view_action (γ : Type)
  | out (a : γ) : tactic_view_action
  | filter (f : filter_type) : tactic_view_action

/-- The "goals accomplished 🎉" HTML widget. This can be overridden using:
```lean
meta def my_new_msg {α : Type} : widget.html α := "my message"
attribute [vm_override my_new_msg] widget_override.goals_accomplished_message
```
-/
unsafe def goals_accomplished_message {α} : html α :=
  h "div" [cn "f5"] ["goals accomplished 🎉"]

/-- Component that displays all goals, together with the `$n goals` message. -/
unsafe def tactic_view_component {γ} (local_c : tc local_collection γ) (target_c : tc expr γ) : tc Unit γ :=
  tc.mk_simple (tactic_view_action γ) filter_type (fun _ => pure <| filter_type.none)
    (fun ⟨⟩ ft a =>
      match a with
      | tactic_view_action.out a => pure (ft, some a)
      | tactic_view_action.filter ft => pure (ft, none))
    fun ⟨⟩ ft => do
    let gs ← get_goals
    let hs ←
      gs.mmap fun g => do
          set_goals [g]
          flip tc.to_html ft <| tactic_view_goal local_c target_c
    set_goals gs
    let goal_message : html γ :=
      if gs.length = 0 then goals_accomplished_message
      else if gs.length = 1 then "1 goal" else html.of_string <| toString gs.length ++ " goals"
    let goal_message : html γ := h "strong" [cn "goal-goals"] [goal_message]
    let goals : html γ :=
      h "ul" [className "list pl0"] <|
        (List.mapWithIndex fun i x => h "li" [className <| "lh-copy mt2", key i] [x]) <| goal_message :: hs
    pure
        [h "div" [className "fr"]
            [html.of_component ft <| component.map_action tactic_view_action.filter filter_component],
          html.map_action tactic_view_action.out goals]

/-- Component that displays the term-mode goal. -/
unsafe def tactic_view_term_goal {γ} (local_c : tc local_collection γ) (target_c : tc expr γ) : tc Unit γ :=
  tc.stateless fun _ => do
    let goal ← flip tc.to_html filter_type.none <| tactic_view_goal local_c target_c
    pure
        [h "ul" [className "list pl0"]
            [h "li" [className "lh-copy"] [h "strong" [cn "goal-goals"] ["expected type:"]],
              h "li" [className "lh-copy"] [goal]]]

/-- Component showing a local collection.
-/
unsafe def show_local_collection_component : tc local_collection Empty :=
  tc.stateless fun lc => do
    let l :: _ ← pure lc.locals
    let c ← show_type_component l
    match lc with
      | some v => do
        let v ← interactive_expression.mk interactive_expression.type_tooltip v
        pure [c, " := ", v]
      | none => pure [c]

/-- Renders the current tactic state.
-/
unsafe def tactic_render : tc Unit Empty :=
  component.ignore_action <| tactic_view_component show_local_collection_component show_type_component

/-- Component showing the current tactic state.
-/
unsafe def tactic_state_widget : component tactic_state Empty :=
  tc.to_component tactic_render

/-- Widget used to display term-proof goals.
-/
unsafe def term_goal_widget : component tactic_state Empty :=
  (tactic_view_term_goal show_local_collection_component show_type_component).to_component

end WidgetOverride

attribute [implementedBy widget_override.term_goal_widget] widget.term_goal_widget

attribute [implementedBy widget_override.tactic_state_widget] widget.tactic_state_widget


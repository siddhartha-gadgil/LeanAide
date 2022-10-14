import system.io
import query_api
import parse

open widget tactic
section json
meta def list.lookup_prod {α β} : (list (α × β)) → (α → bool) → option β
| [] _ := none
| (⟨a,b⟩::xs) p := if p a then pure b else xs.lookup_prod p

open except

meta def json.lookup : json → string → except string json
| (json.object kvs) str :=
  match kvs.lookup_prod $ λ k, k = str with
  | some v := except.ok v
  | none := except.error ("no key " ++ str)
  end
| _ _ := except.error "not an object"

meta def json.as_string : json → except string string
  | (json.of_string s) := except.ok s
  | _ := except.error "not a string"

meta def json.as_array : json → except string (list json)
  | (json.array xs) := ok xs
  | _ := error "not an array"

meta def except.liftOption {α}: option α → except string α
  | none := except.error "option was none"
  | (some a ) := except.ok a

end json

meta def text_of_return_json (parsed : json) : except string string := do
  choices_json ← json.lookup parsed "choices",
  head :: _ ← json.as_array choices_json | except.error "empty array",
  t ← json.lookup head "text",
  s ← json.as_string t,
  return s

meta def run_except {α} : except string α → io α
  | (except.ok a) := pure a
  | (except.error e) := io.fail e



@[derive inhabited]
meta structure bubble :=
  (body : string) -- [todo] add formatting etc
  (user : string)

meta def chat_props := unit

meta structure chat_state : Type :=
  (bubbles : list bubble)
  (current_text : string)

/- @zhangir: write your code for getting response from codex here :-) -/
meta def get_response : chat_state → io string
| state := do {
    bubbles@(head :: tail) ← pure $ state.bubbles | io.fail "no chat yet",
    let statement :=
      match tail with
      | [] := head.body
      | tail := (list.reverse tail).head.body
      end,
    let rest_of_context :=
      match tail with
      | [] := ""
      | tail := (string.intercalate "\n" $  list.map bubble.body $ list.tail $ list.reverse $ bubbles) ++ " Try again:\ntheorem"
        -- want this python command: "\n".join([x.body for x in state.bubbles].reverse[1:])
      end,
    let prompt := prompt_of_nl_statement statement few_shot_prompt ++ rest_of_context,
    --io.put_str_ln (prompt ++ "<endoftext>"),
    return_json ← get_completion_of_request {prompt:=prompt},
    (some maybe_return_parsed) ← pure (json.parse return_json) | io.fail "not json",
    t : string ← run_except $ text_of_return_json maybe_return_parsed,
    return (t ++ " :=")
  }

/-- Use when testing formatting etc to avoid having to call api. -/
meta def get_response_dummy : chat_state → io string
  | state := do {
      return "meta def unsafe_perform_io {α} (m : io α) : except io.error α :=
match (cast undefined m : unit → sum α io.error) () with
| sum.inl a := except.ok a
| sum.inr err := except.error err
end"
    }

-- use some @gebner magic here
meta def unsafe_perform_io {α} (m : io α) : except io.error α :=
match (cast undefined m : unit → sum α io.error) () with
| sum.inl a := except.ok a
| sum.inr err := except.error err
end

meta def unsafe_get_response (input : chat_state) : string :=
  match unsafe_perform_io (get_response input) with
  | except.ok a := a
  | except.error e := "error"
  end

meta inductive chat_action
  | submit
  | demo_text
  | text_change (s : string)
  | copy_to_comment (s : string)
  | copy_to_script (s : string)
  | clear

meta def code_content (code : string) : html chat_action :=
  h "div" [] [
    h "code" [className "font-code", attr.style [("white-space", "break-spaces")]] [
      code
    ],
    h "div" [] [
      button "paste" (chat_action.copy_to_script ("theorem " ++ code))
    ]
  ]

meta inductive nlrun
  | math (s : string) : nlrun
  | text (s : string) : nlrun

meta def nlrun.to_html {α : Type} : nlrun → html α
  | (nlrun.math s) := html.element "InlineMath" [attr.val "math" s] []
  | (nlrun.text s) := html.of_string s

meta def to_nlrun_aux : list string → list nlrun
  | (text :: latex :: rest) := (nlrun.text text) :: (nlrun.math latex) :: to_nlrun_aux rest
  | [] := []
  | [text] := [nlrun.text text]

meta def to_nlrun (s : string) : list nlrun :=
  to_nlrun_aux $ string.split_on s '$'

meta def nl_content (s : string) : html chat_action :=
  let nlruns := to_nlrun s in
  h "div" [className "f6"] $ nlruns.map nlrun.to_html

meta def chat_view (props : chat_props) (state : chat_state) : list (html chat_action) :=
  [h "div" [className "f6"] [
    h "div" [className "flex flex-column"] (
      state.bubbles.reverse.map (λ bubble,
        h "div" [className "pa2 ma2 bg-lightest-blue"] [
          h "div" [className "mr2"] [bubble.user, ": "],
          if bubble.user ≠ "self" then
            code_content bubble.body
          else
            nl_content bubble.body
        ]
      )
    ),
    h "div" [] [
      textbox state.current_text chat_action.text_change,
      button "submit" chat_action.submit, -- [todo] how to get it to trigger on enter?
      button "demo" chat_action.demo_text,
      button "clear" chat_action.clear
    ]
  ]]

meta def push_bubble (b : bubble) (s : chat_state) : chat_state := {bubbles := b :: s.bubbles, ..s}


#check tactic.unsafe_run_io
/-- runs the lean parser on the response, if it's good then returns an error message, otherwise returns none.
  I am not proud of this method, this should be considered bad Lean practice.
-/
meta def unsafe_parse_result (response : string) : option string := do
  empty_tactic_state ← except.to_option $ unsafe_perform_io (io.run_tactic tactic.read),
  let t := lean.parser.run_with_input parse_decl response empty_tactic_state,
  match t with
  | result.success a s := none
  | result.exception (some msg) pos s := some (to_string $ msg())
  | result.exception _ _ _ := some "exception with no message!"
  end

meta def chat_update (props : chat_props)  : chat_state → chat_action → (chat_state × option effect)
  | state (chat_action.submit) :=
    let text := state.current_text,
        state := {current_text := "", ..state},
        state := push_bubble {body := text, user := "self"} state,
        response := unsafe_get_response state,
        state := push_bubble {body := response, user := "codex"} state,
        state := push_bubble {
          body := match unsafe_parse_result ("def " ++ response) with
                  | (some msg) := "error:\n" ++ msg
                  | none := "check passes!"
                  end,
          user := "lean"} state
        in
    (state, none)
  | state (chat_action.text_change s) := ({current_text := s, ..state}, none)
  | state (chat_action.copy_to_comment str) := (state, some $ effect.insert_text $ "/--\n" ++ str ++ "\n-/")
  | state (chat_action.copy_to_script str) := (state, some $ effect.insert_text str)
  | state chat_action.demo_text :=
    -- @zhangir add your example here to avoid having to paste it in every time!
    let state := {current_text := "If $x$ is an element of infinite order in $G$, prove that the elements $x^n$, $n\\in\\mathbb{Z}$ are all distinct.", ..state} in
    chat_update state chat_action.submit
  | state (chat_action.clear) := ({current_text:="", bubbles:=[]}, none)

meta def chat_init (props : chat_props) (old_state : option chat_state) : chat_state :=
  let s : chat_state := ({bubbles := [], current_text := ""} <| old_state) in
  s

meta def chat_widget {π α : Type} : component π α :=
component.ignore_props
$ component.ignore_action
$ component.with_effects (λ _ action, [action])
$ component.stateful chat_action _ chat_init  chat_update chat_view

-- @zhangir put your cursor on the #html token!
#html chat_widget ()
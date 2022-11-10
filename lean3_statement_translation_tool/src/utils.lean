import system.io

/-- Displays the input string in the Lean infoview with a "Try this: ..." message.
    Clicking on the suggestion pastes it into the editor. -/
meta def suggest_string {m : Type* → Type*} [monad m] (s : string) : m unit :=
    let f := to_fmt sformat!"Try this: {s}\n" in
      pure $ _root_.trace_fmt f (λ _, ())

/-- A version of `suggest_string` that handles multiple strings. -/
meta def suggest_strings {m : Type* → Type*} [monad m] (l : list string) : m unit :=
  l.mmap suggest_string >>= λ _, pure ()

/-- Attempts to parse a string representing a type as an expression. -/
meta def parse_str (s : string) : tactic expr :=
  lean.parser.run $
    lean.parser.with_input interactive.types.texpr s >>=
      λ x, tactic.to_expr x.fst


def list.lookup_prod {α β} : list (α × β) → (α → bool) → option β
  | [] _ := none
  | (⟨a, b⟩ :: xs) p := if p a then some b else xs.lookup_prod p

def except.of_option {α β} : option α → β → except β α
  | (some a) _ := except.ok a
  | none b := except.error b

namespace json

/-! The code in this section is based on similar code in `Lean Chat`. -/

meta def lookup : json → string → except string json
  | (json.object kvs) str := 
    except.of_option 
      (kvs.lookup_prod $ λ k, k = str)
      ("no key" ++ str)
  | _ _ := except.error "not an object"

meta def as_string : json → except string string
  | (json.of_string s) := except.ok s
  | _ := except.error "not a string"

meta def as_array : json → except string (list json)
  | (json.array xs) := except.ok xs
  | _ := except.error "not an array"

meta def lookup_as {α} : json → string → (json → except string α) → except string α
  | j s φ := do
    v ← j.lookup s,
    φ v

end json

meta def io.of_except {α} : except string α → io α
  | (except.ok a) := pure a
  | (except.error e) := io.fail e

meta def tactic.of_except {α} : except string α → tactic α
  | (except.ok a) := pure a
  | (except.error e) := tactic.fail e
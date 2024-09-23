import Lean
import LeanAide.Aides
import LeanAide.TranslateM
import LeanCodePrompts.SpawnNearestEmbeddings
import Mathlib
open Lean Meta Elab Term

namespace LeanAide.Meta

def clearEmbedQueries : TranslateM Unit := do
  modify fun st => {st with queryEmbeddingCache := HashMap.empty}

def embedQueryCached (s: String)(retry : Bool := false) : TranslateM (Except String Json) := do
  match (← get).queryEmbeddingCache.find? s with
  | some js? =>
    -- IO.eprintln s!"cache hit for {s}"
    if !retry then
      return js?
    else match js? with
      | Except.ok _ => return js?
      | Except.error _ =>
        let js? ← embedQuery s
        modify fun st => {st with queryEmbeddingCache := st.queryEmbeddingCache.insert s js?}
    return js?
  | none =>
    let js? ← embedQuery s
    modify fun st => {st with queryEmbeddingCache := st.queryEmbeddingCache.insert s js?}
    return js?


def fromBlend (n: Nat) (gps : List (List α)) : List α :=
match n, gps with
| _ , [] :: t =>
  fromBlend n t
| 0, _ => []
| _ , [] => []
| k + 1, (h :: hs) :: t =>
  h :: (fromBlend k (t ++ [hs]))
termination_by (gps.length, n)

def blended (gps: List (List α)) : List α :=
  let n := List.sum (gps.map (·.length))
  fromBlend n gps

def useragent : String := "LeanAide"

def getLeanSearchQueryJson (s : String) (num_results : Nat := 6) : CoreM <| Array Json := do
  let apiUrl := "https://leansearch.net/api/search"
  let s' := System.Uri.escapeUri s
  let q := apiUrl ++ s!"?query={s'}&num_results={num_results}"
  let s ← IO.Process.output {cmd := "curl", args := #["-X", "GET", "--user-agent", useragent, q]}
  match Json.parse s.stdout with
  | Except.error e =>
      IO.throwServerError s!"Could not parse JSON from {s.stdout}; error: {e}"
  | Except.ok js =>
      match js.getArr? with
      | Except.ok arr =>
        return arr[0:num_results]
      | Except.error e => IO.throwServerError s!"Could not obtain array from {js}; error: {e}"

def getMoogleQueryJson (s : String) (num_results : Nat := 6) : CoreM <| Array Json := do
  let apiUrl := "https://www.moogle.ai/api/search"
  let data := Json.arr
    #[Json.mkObj [("isFind", false), ("contents", s)]]
  let s ← IO.Process.output {cmd := "curl", args := #[apiUrl, "-H", "content-type: application/json",  "--user-agent", useragent, "--data", data.pretty]}
  match Json.parse s.stdout with
  | Except.error e =>
    IO.throwServerError s!"Could not parse JSON from {s.stdout}; error: {e}"
  | Except.ok js =>
  let result? := js.getObjValAs?  Json "data"
  match result? with
    | Except.ok result =>
        match result.getArr? with
        | Except.ok arr => return arr[0:num_results]
        | Except.error e => IO.throwServerError s!"Could not obtain array from {js}; error: {e}"
    | _ => IO.throwServerError s!"Could not obtain data from {js}"

structure SearchResult where
  name : String
  type? : Option String
  docString? : Option String
  doc_url? : Option String
  kind? : Option String
  deriving Repr

namespace SearchResult

def ofLeanSearchJson? (js : Json) : Option SearchResult :=
  match js.getObjValAs? String "formal_name" with
  | Except.ok name =>
      let type? := js.getObjValAs? String "formal_type" |>.toOption
      let doc? := js.getObjValAs? String "docstring" |>.toOption
      let doc? := doc?.filter fun s => s != ""
      let docurl? := js.getObjValAs? String "doc_url" |>.toOption
      let kind? := js.getObjValAs? String "kind" |>.toOption
      some {name := name, type? := type?, docString? := doc?, doc_url? := docurl?, kind? := kind?}
  | _ => none

def ofMoogleJson? (js : Json) : MetaM <| Option SearchResult :=
  match js.getObjValAs? String "declarationName" with
  | Except.ok name => do
      let type? ←
        try
          let info ←  getConstInfo name.toName
          let fmt ← PrettyPrinter.ppExpr info.type
          pure <| some fmt.pretty
        catch _ =>
          pure none
      let doc? := js.getObjValAs? String "declarationDocString" |>.toOption
      let doc? := doc?.filter fun s => s != ""
      let kind? := js.getObjValAs? String "declarationType" |>.toOption
      return some {name := name, type? := type?, docString? := doc?, doc_url? := none, kind? := kind?}
  | _ => return none

def toJson (res: SearchResult) : Json :=
  let l := [("name", Json.str res.name)]
  let l := match res.docString? with
  | some doc => l ++ [("docString", Json.str doc)]
  | none => l
  let l := match res.type? with
  | some type => l ++ [("type", Json.str type)]
  | none => l
  Json.mkObj l

end SearchResult

inductive PromptExampleBuilder where
| embedSearch (descField : String) (n: Nat) : PromptExampleBuilder
| leansearch (descFields : List String)
  (preferDocs: Bool := false) (n: Nat) : PromptExampleBuilder
| moogle (descFields : List String)
  (preferDocs: Bool := false) (n: Nat) : PromptExampleBuilder
| sequence : List PromptExampleBuilder → PromptExampleBuilder
| blend : List PromptExampleBuilder → PromptExampleBuilder

namespace PromptExampleBuilder

partial def num : PromptExampleBuilder →  Nat
| embedSearch _ n => n
| leansearch _ _ n => n
| moogle _ _ n => n
| sequence ps => (ps.map num).sum
| blend ps => (ps.map num).sum

end PromptExampleBuilder

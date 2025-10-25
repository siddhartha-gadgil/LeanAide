import Lean
import LeanAide.Aides
import LeanAide.TranslateM
import LeanCodePrompts.SimilaritySearch
import LeanCodePrompts.SpawnNearestEmbeddings
import LeanCodePrompts.ChatClient
import LeanAide.PromptExampleBuilder
import LeanAideCore.Translator
import Mathlib
open Lean Meta Elab Term

namespace LeanAide
open Translate

def clearEmbedQueries : TranslateM Unit := do
  modify fun st => {st with queryEmbeddingCache := Std.HashMap.emptyWithCapacity 100000}

def embedQueryCached (s: String)(retry : Bool := false) : TranslateM (Except String Json) := do
  match (← get).queryEmbeddingCache.get? s with
  | some js? =>
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

def getLeanSearchQueryJsonArray (s : String) (num_results : Nat := 6) : CoreM <| Array Json := do
  let apiUrl := "https://leansearch.net/search"
  let js := Json.mkObj [("query", Json.arr #[toJson s]), ("num_results", num_results)]
  let s ← IO.Process.output {cmd := "curl", args := #["-X", "POST", apiUrl, "--user-agent", useragent, "-H", "accept: application/json", "-H", "Content-Type: application/json", "--data", js.pretty]}
  -- IO.eprintln s!"LeanSearch output: {s.stdout}"
  match Json.parse s.stdout with
  | Except.error e =>
      IO.eprintln s!"Could not parse JSON from leansearch output: {s.stdout}; error: {e}"
      return #[]
  | Except.ok js =>
      match js.getArr? with
      | Except.ok arr =>
        return arr[0:num_results]
      | Except.error e => IO.throwServerError s!"Could not obtain array from {js}; error: {e}"

-- #eval getLeanSearchQueryJsonArray "prime numbers" 10

def getMoogleQueryJsonArray (s : String) (num_results : Nat := 6) : CoreM <| Array Json := do
  let apiUrl := "https://www.moogle.ai/api/search"
  let data := Json.arr
    #[Json.mkObj [("isFind", false), ("contents", s)]]
  let s ← IO.Process.output {cmd := "curl", args := #[apiUrl, "-H", "Content-Type: application/json",  "--user-agent", useragent, "--data", data.pretty]}
  match Json.parse s.stdout with
  | Except.error e =>
    IO.eprintln s!"Could not parse JSON from Moogle output: {s.stdout}; error: {e}"
    return #[]
  | Except.ok js =>
  let result? := js.getObjValAs?  Json "data"
  match result? with
    | Except.ok result =>
        match result.getArr? with
        | Except.ok arr => return arr[0:num_results]
        | Except.error e => IO.throwServerError s!"Could not obtain array from {js}; error: {e}"
    | _ => IO.throwServerError s!"Could not obtain data from {js}"

--#eval getMoogleQueryJsonArray "prime numbers are prime" 10

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

def withDoc? (res: SearchResult) (descFields: List String)
    (preferDocs : Bool) : TranslateM (Option <| String × Json) := do
  let data? ← getDescriptionData res.name.toName
  data?.bindM  fun data => do
  let data := data.mergeObj res.toJson
  match res.docString? with
  | some doc =>
    if preferDocs then return some (doc, data)
    else
      let fromField? := data?.bind fun data =>
      descFields.findSome? fun descField =>
        data.getObjValAs? String descField |>.toOption
      return some <| (fromField?.getD doc, data)
  | none =>
      let fromField? := data?.bind fun data =>
      descFields.findSome? fun descField =>
        data.getObjValAs? String descField |>.toOption
      return fromField?.map fun s => (s, data)

end SearchResult

local instance : Hashable Float where
  hash f := hash (f * 100).toUInt32

namespace PromptExampleBuilder

partial def num : PromptExampleBuilder →  Nat
| similarSearch _ n => n
| embedSearch _ n _ => n
| leansearch _ _ n => n
| moogle _ _ n => n
| generic _ _ _ n => n
| fixed ps => ps.size
| sequence ps => (ps.map num).sum
| blend ps => (ps.map num).sum

def pairsFromEmbeddingJson (js: String) :
    CoreM <| Except String (Array (String × Json)) := do
  match Json.parse js with
  | Except.error e => return Except.error e
  | Except.ok js =>
      match js.getArr? with
      | Except.error e => return Except.error e
      | Except.ok jsArr  =>
        let mut pairs : Array <| String × Json := #[]
        for js in jsArr do
          match js.getObjValAs? String "docString" with
          | Except.error e => return Except.error e
          | Except.ok doc =>
            pairs := pairs.push (doc, js)
        return Except.ok pairs

def pairsFromSearchResults (srs: Array SearchResult)(descFields: List String)
    (preferDocs : Bool) : TranslateM <| (Array (String × Json)) := do
    srs.filterMapM fun sr =>
      sr.withDoc? descFields preferDocs

partial def getPromptPairsOrderedAux (pb: PromptExampleBuilder)
  (query: String) : TranslateM ((Array (String × Json))) := do
  let dataMap ← getEmbedMap
  match pb with
  | similarSearch descField n =>
      IO.eprintln s!"similarSearch on {descField} with query: {query}"
      let outJs ← callSimilaritySearch query descField n
      match ← pairsFromEmbeddingJson outJs with
      | Except.ok jsArr => return jsArr
      | Except.error e =>
        IO.eprintln s!"Could not parse JSON from embedding output: {outJs}; error: {e}"
        throwError e
  | embedSearch descField n p =>
      IO.eprintln s!"embedSearch on {descField} with query: {query}"
      let outJs ←
        getNearestEmbeddingsFull query (← embedQueryCached query) n p (descField := descField) (dataMap := dataMap)
      match ← pairsFromEmbeddingJson outJs with
      | Except.ok jsArr => return jsArr
      | Except.error e =>
        IO.eprintln s!"Could not parse JSON from embedding output: {outJs}; error: {e}"
        throwError e
  | leansearch descFields preferDocs n =>
    let jsArr ← getLeanSearchQueryJsonArray query n
    let srs := jsArr.filterMap SearchResult.ofLeanSearchJson?
    pairsFromSearchResults srs descFields preferDocs
  | moogle descFields preferDocs n =>
    let jsArr ← getMoogleQueryJsonArray query n
    let srs ←  jsArr.filterMapM fun js =>
       SearchResult.ofMoogleJson? js
    pairsFromSearchResults srs descFields preferDocs
  | fixed ps => return ps
  | generic url baseData headers n =>
    if n = 0 then return #[]
    let data := Json.mkObj [("input", Json.str query), ("n", n)]
    let data := data.mergeObj baseData
    let mut httpHeaders := #["-X", "POST", "-H", "Content-Type: application/json"]
    for header in headers do
      httpHeaders := httpHeaders ++ #["-H", header]
    let s ← IO.Process.output {cmd := "curl", args := #[url] ++ httpHeaders ++ #["--user-agent", useragent, "--data", data.pretty]}
    match Json.parse s.stdout with
    | Except.error e =>
      IO.eprintln s!"Could not parse JSON from generic output: {s.stdout}; error: {e}"
      IO.eprintln s!"curl {#[url] ++ httpHeaders ++ #["--user-agent", useragent, "--data", data.pretty]}"
      return #[]
    | Except.ok js =>
      -- IO.eprintln s!"curl {#[url] ++ httpHeaders ++ #["--user-agent", useragent, "--data", data.pretty]}"
      let result? := js.getObjVal?  "data"
      match result? with
      | Except.ok result =>
        match result.getArr? with
        | Except.ok arr =>
          return arr.filterMap fun js =>
            (js.getObjValAs? String "docString" |>.toOption
            |>.orElse (fun _ => js.getObjValAs? String "doc_string" |>.toOption) |>.orElse (fun _ => js.getObjValAs? String "doc" |>.toOption))
            |>.map fun doc => (doc, js)
        | Except.error e => IO.throwServerError s!"Could not obtain array from {js}; error: {e}"
      | _ => IO.throwServerError s!"Could not obtain data from {js}"
  | sequence ps => do
    let offspringGps ← ps.mapM fun pb => getPromptPairsOrderedAux pb query
    return offspringGps.toArray.flatten
  | blend ps =>
    let offspringGps ← ps.mapM fun pb => getPromptPairsOrderedAux pb query
    let offSpringGps := offspringGps.map fun l => l.toList
    return blended offSpringGps |>.toArray

def getPromptPairsOrdered (pb: PromptExampleBuilder)
  (query: String) : TranslateM ((Array (String × Json))) := do
    let file : System.FilePath :=
      (← cachePath) / "prompt" / s!"{hash pb}_{hash query}.json"
    if (← file.pathExists) then
      -- IO.eprintln s!"Getting prompt pairs from cache: {file}"
      let js ← IO.FS.readFile file
      match Json.parse js with
      | Except.error e =>
        IO.eprintln s!"Could not parse JSON from file {file}; error: {e}"
        let pairs ← getPromptPairsOrderedAux pb query
        let js := toJson pairs
        IO.FS.writeFile file js.compress
        return pairs
      | Except.ok js =>
        match (fromJson? js : Except String (Array (String × Json))) with
        | Except.error e =>
          IO.eprintln s!"Could not parse JSON from file {file}; error: {e}"
          let pairs ← getPromptPairsOrderedAux pb query
          let js := toJson pairs
          IO.FS.writeFile file js.compress
          return pairs
        | Except.ok pairs  =>
          return pairs
    else do
      -- IO.eprintln s!"Getting prompt pairs, no cache"
      let pairs ← getPromptPairsOrderedAux pb query
      let js := toJson pairs
      IO.FS.writeFile file js.compress
      return pairs

/--
Obtain prompt pairs from a builder given a target sentence.
-/
def getPromptPairs (pb: PromptExampleBuilder)
    (query: String)(bound: Nat := 600) : TranslateM ((Array (String × Json))) := do
  let pairs ← getPromptPairsOrdered pb query
  let pairs := pairs.filter fun (doc, _) => doc.length < bound
  return pairs.reverse

partial def usedEmbeddings : PromptExampleBuilder → List String
| .similarSearch d _ => [d]
| .embedSearch d _ _ => [d]
| .blend pbs => pbs.map usedEmbeddings |>.flatten
| .sequence pbs => pbs.map usedEmbeddings |>.flatten
| _ => []

partial def simplify? (pb : PromptExampleBuilder): Option (PromptExampleBuilder) :=
match pb with
| .similarSearch _ n => if n > 0 then some pb else none
| .embedSearch _ _ n => if n > 0 then some pb else none
| .leansearch _ _ n => if n > 0 then some pb else none
| .moogle _ _ n => if n > 0 then some pb else none
| .fixed ps => if ps.size > 0 then some pb else none
| .generic  _ _ _ n => if n > 0 then some pb else none
| .sequence pbs =>
  match pbs.filterMap simplify? with
  | [] => none
  | [pb] => some pb
  | simpPbs => some <| .sequence simpPbs
| .blend pbs =>
  match pbs.filterMap simplify? with
  | [] => none
  | [pb] => some pb
  | simpPbs => some <| .blend simpPbs

def simplify (pb : PromptExampleBuilder): PromptExampleBuilder :=
  (simplify? pb).getD <| .blend []

-- #eval toJson (embedBuilder 3 4 5) |>.compress
-- #eval toJson (searchBuilder 3 4) |>.compress

partial def signature (pb: PromptExampleBuilder) : String := match pb with
| .similarSearch descField n => s!"{descField}${n}"
| .embedSearch descField n _ => s!"{descField}${n}"
| .leansearch _ _  n => s!"leansearch${n}"
| .moogle _ _ n => s!"moogle${n}"
| .fixed ps => s!"fixed${ps.size}"
| .generic url _ _ n =>
    s!"generic${url}_${n}"
| .sequence pbs => (pbs.map signature).foldl (· ++ "-" ++ ·) "" |>.drop 1
| .blend pbs => (pbs.map signature).foldl (· ++ "~" ++ ·) "" |>.drop 1

-- #eval signature <| searchBuilder 3 4

/--
Fixed prompts with names from Lean Chat
-/
def fixedPromptTriples:= #[("If $z_1, \\dots, z_n$ are complex, then $|z_1 + z_2 + \\dots + z_n|\\leq |z_1| + |z_2| + \\dots + |z_n|$.", "(n : ℕ) (f : ℕ → ℂ) :\n Complex.abs (∑ i in Finset.range n, f i) ≤ ∑ i in Finset.range n, Complex.abs (f i)", "abs_sum_leq_sum_abs"), ("If x and y are in $\\mathbb{R}^n$, then $|x+y|^2 + |x-y|^2 = 2|x|^2 + 2|y|^2$.", "(n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :\n ‖x + y‖^2 + ‖x - y‖^2 = 2*‖x‖ ^2 + 2*‖y‖^2", "sum_add_square_sub_square_eq_sum_square"), ("If $x$ is an element of infinite order in $G$, prove that the elements $x^n$, $n\\in\\mathbb{Z}$ are all distinct.", "(G : Type*) [Group G] (x : G) (hx : x ≠ 1) (hx_inf : ∀ n : ℕ, x ^ n ≠ 1) : ∀ m n : ℤ, m ≠ n → x ^ m ≠ x ^ n", "distinct_powers_of_infinite_order_element"), ("Let $X$ be a topological space; let $A$ be a subset of $X$. Suppose that for each $x\\in A$ there is an open set $U$ containing $x$ such that $U\\subset A$. Show that $A$ is open in $X$.", "(X : Type*) [TopologicalSpace X]\n (A : Set X) (hA : ∀ x ∈ A, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ A):\n IsOpen A", "subset_of_open_subset_is_open")]

/--
Fixed prompts with names from Lean Chat in JSON format
-/
def fixedPromptsJson : Array <| String × Json :=
  fixedPromptTriples.map (fun (ds, thm, name) =>
    (ds,
    Json.mkObj [("docString", ds), ("type", thm), ("name", name)]))

def proofNetPromptBuilder : PromptExampleBuilder :=
  .fixed fixedPromptsJson

end PromptExampleBuilder


/--
Just collecting for now. Should add selectors if these grow.
-/
def tips :=
  #["Multiplication is usually denoted `*` in Lean, not `⬝`",
  "Within quantifiers `∀` and `∃`, do not use typeclasses, use anonymous variables with types instead. For example, NOT: `∃ (G: Type) [Group G], ...` USE: `∃ G : Type, (_ : Group G), ...`"]


end LeanAide

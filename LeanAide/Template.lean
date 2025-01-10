import Lean

open Lean Meta System

def llmDir := FilePath.mk "llm_data"
def resources := FilePath.mk "resources"

def promptTemplates : IO Json := do
  let path : System.FilePath := resources / "templates.json"
  let path ← if (← path.pathExists) then
    pure path
    else
      let p : System.FilePath :=
        ".lake" / "packages" / "leanaide" / "resources" / "templates.json"
      pure p
  let js ← IO.FS.readFile path
  match Json.parse js with
  | Except.ok j => return j
  | Except.error e =>
    IO.throwServerError s!"Error parsing JSON: {e}; source: {js}"

def componentTemplates : IO Json := do
  let path := resources / "component_templates.json"
  let path ← if (← path.pathExists) then
    pure path
    else
      let p : System.FilePath :=
        ".lake" / "packages" / "leanaide" / "resources" / "component_templates.json"
      pure p
  let js ← IO.FS.readFile path
  match Json.parse js with
  | Except.ok j => return j
  | Except.error e =>
    IO.throwServerError s!"Error parsing JSON: {e}; source: {js}"

def getTemplate (name: String) : IO String := do
  let js ← promptTemplates
  match js.getObjValAs? String name with
  | Except.ok s => return s
  | _ =>
    IO.throwServerError s!"Template {name} not found"

def getComponentTemplate (name: String) : IO String := do
  let js ← componentTemplates
  match js.getObjValAs? String name with
  | Except.ok s => return s
  | _ =>
    IO.throwServerError s!"Component template {name} not found"

def fillTemplate (template: String)(args: List <| String × String) :
    String :=
  args.foldl (fun s (x, y) => s.replace ("${" ++ x ++ "}") y) template

def fromTemplate (name: String)(args: List <| String × String) :
    IO String := do
  let template ← getTemplate name
  return fillTemplate template args

def proofJson : IO String := do
  let path := resources / "ProofJson.md"
  IO.FS.readFile path

def jsonProofTemplateFull  : IO String := do
  let path := resources / "JsonTemplate.md"
  IO.FS.readFile path

def jsonProofInstructions : IO String := do
  let path := resources / "ProofJsonShorter.md"
  IO.FS.readFile path

def structuredProofQueryFull (pf: String) : IO String := do
  let template ← jsonProofTemplateFull
  return fillTemplate template [("proof", pf)]

def jsonField (json: Json) (field : String) : String :=
  json.getObjValAs? String field |>.toOption.getD ""

def jsonField? (json: Json) (field : String) : Option String :=
  json.getObjValAs? String field |>.toOption

def jsonFieldPairs (json: Json) (fields: List String) :
    List (String × String) :=
  fields.map (fun f => (f, jsonField json f))

def jsonFieldPairs' (json: Json) (fields: List String) :
    List (String × String) :=
  fields.filterMap (fun f =>
    let field? := jsonField? json f
    field?.map (fun field => (f, field)))


def fieldsFromTemplate (template: String) : List String :=
  let pieces := template.splitOn "${"
  let piecesOpt? := pieces.tail?.map
    (fun tail => tail.map fun s => (s.splitOn "}").head!)
  piecesOpt?.getD []


def fillTemplateJson (template: String)(json: Json)
     : String :=
  fillTemplate template <| jsonFieldPairs json (fieldsFromTemplate template)

def fillTemplateJson? (template: String)(json: Json)
     : Option String :=
  let fields := fieldsFromTemplate template
  let filled := jsonFieldPairs' json fields
  if filled.length = fields.length then
    some <| fillTemplate template filled
  else none

def fromComponentTemplate (name: String)(json: Json)
    : IO String := do
  let template ← getComponentTemplate name
  return fillTemplateJson template json

def fromComponentTemplates (names: List String)(json: Json)
    : IO (Option String) := do
  match names with
  | [] =>
    IO.eprintln s!"No component templates filled from {json}"
    return none
  | name :: names => do
    let template ← getComponentTemplate name
    match fillTemplateJson? template json with
    | some filled => return some filled
    | none => fromComponentTemplates names json


-- #eval fieldsFromTemplate "The matrix $A$ satisfies the polynomial equation $p(x) = x^3 - 1$ by ${proof}."

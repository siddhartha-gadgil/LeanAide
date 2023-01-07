import Lean
import Lean.Elab
import Lean.Parser
import StatementAutoformalisation.Utils

/-- A structure for storing details of Lean declarations such as `theorem`s or `def`s in `String` format. -/
structure Declaration where
  /-- Records whether the declaration is a `theorem`, `def`, `example`, `axiom`, `abbrev`, etc. -/
  kind : String
  /-- An optional name for the declaration. -/
  name : Option String := none
  /-- The list of open namespaces that the declaration is contained in. -/
  openNamespaces : Array String := #[]
  /-- The arguments to the declaration (the part before the colon). -/
  args : String := "" -- TODO: Decide whether to make this a list/array
  /-- The type of the declaration (the part after the colon). -/
  type : String
  /-- The value of the declaration (the part after the `:=` - irrelevant for theorems, but useful for definitions). -/
  value : String := "sorry"
deriving Inhabited, Repr

/-- A structure containing a `Declaration` together with its corresponding documentation string. -/
structure DeclarationWithDocstring extends Declaration where
  /-- The documentation string describing the declaration. -/
  docstring : String
  -- TODO eventually include embedding and keyword information
deriving Inhabited, Repr

open Lean in
/-- Convert a `ConstantInfo` in the environment into a `Declaration`. 
  This is used to extract `Declaration`s from the environment by their name. -/
def Declaration.fromConstantInfo (ci : ConstantInfo) (extractValue? := false) : MetaM <| _root_.Declaration := do
  let type ← Format.pretty <$> PrettyPrinter.ppExpr ci.type
  return {
    kind := ci.kind?.getD "def",
    name := ci.name.toString,
    openNamespaces := #[]
    args := "",
    type := type,
    value := (if extractValue? then 
      ← ci.value?.mapM <| Functor.map Format.pretty ∘ PrettyPrinter.ppExpr 
              else none).getD "sorry"
  }

open Lean in
/-- The declaration in the environment with the given name, as a `Declaration`. -/
def Declaration.fromName? (nm : Name) : MetaM <| Option _root_.Declaration := do
  let ci? := (← getEnv).constants.find? nm
  ci?.mapM Declaration.fromConstantInfo

open Lean in
/-- The declaration in the environment with the given name, together with its docstring, as a `DeclarationWithDocstring`. -/
def DeclarationWithDocstring.fromName? (nm : Name) : MetaM <| Option DeclarationWithDocstring := do
  let decl? ← Declaration.fromName? nm
  let doc? ← liftM <| findDocString? (← getEnv) nm
  return do some ⟨← decl?, ← doc?⟩

open Lean in
/-- All declarations from the current environment. -/
def Declaration.envDecls (moduleNames : Array Name := .empty) (useMain? : Bool := true) : MetaM <| Array _root_.Declaration := do
  if moduleNames.isEmpty && !useMain? then 
    return #[]
  
  let env ← getEnv
  let moduleNames := 
    if useMain? then
      moduleNames.push env.mainModule
    else moduleNames
  let moduleIdxs := moduleNames.filterMap env.getModuleIdx?

  env.constants.toArray.filterMapM fun ⟨nm, ci⟩ => do
    let some _ := moduleIdxs.contains <$> env.getModuleIdxFor? nm  | pure none
    Declaration.fromConstantInfo ci

open Lean in
/-- All declarations with documentation from the current environment. -/
def DeclarationWithDocstring.envDecls (moduleNames : Array Name := .empty) (useMain? : Bool := true) : MetaM <| Array DeclarationWithDocstring := do
  if moduleNames.isEmpty && !useMain? then 
    return #[]

  let env ← getEnv
  let moduleNames := 
    if useMain? then
      moduleNames.push env.mainModule
    else moduleNames
  let moduleIdxs := moduleNames.filterMap env.getModuleIdx?

  env.constants.toArray.filterMapM fun ⟨nm, ci⟩ => do
    let some _ := moduleIdxs.contains <$> env.getModuleIdxFor? nm | pure none
    let some docstring ← findDocString? env nm | pure none
    let decl ← Declaration.fromConstantInfo ci
    return some ⟨decl, docstring⟩

/-- The `String` representation of the type of a `Declaration`. -/
def Declaration.toType (decl : Declaration) : String :=
  let ns := if decl.openNamespaces.isEmpty then "" else "open " ++ decl.openNamespaces.joinWith " " ++ " in "
  let type :=
    if decl.args.trim = "" then decl.type
    else s!"∀ {decl.args}, {decl.type}"
  ns ++ type

/-- Render a `Declaration` as a `String`. -/
instance Declaration.toString : ToString Declaration where
  toString := fun ⟨kind, name?, _, args, type, value⟩ =>
      s! "{kind} {name?.getD ""} {args} : {type} := {value}"

/-- Display just the type of a `Declaration`, ignoring other details. -/
instance Declaration.printType : ToString Declaration where
  toString := fun ⟨_, _, _, args, type, _⟩ =>
    s!"{args}{if args.isEmpty then "" else " : "}{type}"

/-- Decorate a `String` with Lean comment or docstring syntax. -/
def printAsComment (doc : String) : String := s!"/-- {doc} -/"

/-- Render a `DeclarationWithDocstring` as a `String`. -/
instance DeclarationWithDocstring.toString : ToString DeclarationWithDocstring where
  toString := fun ⟨decl, doc⟩ => 
    s!"{printAsComment doc}\n{Declaration.toString.toString decl}"

/-- Display just the type of a `DeclarationWithDocstring`, ignoring other details. -/
instance DeclarationWithDocstring.printType : ToString DeclarationWithDocstring where
  toString := fun ⟨decl, _⟩ => Declaration.printType.toString decl

/-- Build a prompt from a list of `DeclarationWithDocstring`s. Note that the declarations are printed in the reverse order. -/
def buildPrompt [ToString DeclarationWithDocstring] (decls : Array DeclarationWithDocstring)
  (suffix : String) : String :=
    decls.foldr
    -- this builds the prompt backwards
    (fun d prompt => s!"{toString d}\n\n{prompt}") 
    suffix

/-- Read a `Declaration` from `JSON` format. -/
def Declaration.fromJson (kind : String := "theorem") (data : Lean.Json) : Except String Declaration := do
  let name ← data.getObjValAs? String "name"
  let args ← data.getObjValAs? String "args"
  let type ← data.getObjValAs? String "type"
  return {
    kind := kind,
    name := name,
    openNamespaces := #[],
    args := args,
    type := type,
    value := "sorry"
  }

/-- Read a `DeclarationWithDocstring` from `JSON` format. -/
def DeclarationWithDocstring.fromJson (kind : String := "theorem") (data : Lean.Json) : Except String DeclarationWithDocstring := do
  let docstr ← data.getObjValAs? String "doc_string"
  let decl ← Declaration.fromJson kind data
  return ⟨decl, docstr⟩

/-- Convert a `Declaration` to a `JSON` object. -/
def Declaration.toJson (decl : Declaration) (verbose? := false) : Lean.Json := .mkObj <| [
  ("kind", decl.kind),
  ("name", decl.name.getD ""),
  ("args", decl.args),
  ("type", decl.type)
] ++ if verbose? then [
  ("open_namespaces", Lean.Json.arr <| decl.openNamespaces.map .str),
  ("value", decl.value)
] else []

/-- Convert a `DeclarationWithDocstring` to a `JSON` object. -/
def DeclarationWithDocstring.toJson : DeclarationWithDocstring → Lean.Json
  | ⟨decl, docstr⟩ => .mergeObj decl.toJson (.mkObj [("doc_string", docstr)])

section Parsing

open Lean Parser

declare_syntax_cat argument
syntax "(" ident+ ":" term ")" : argument
syntax "{" ident+ ":" term "}" : argument
syntax "[" ident+ ":" term "]" : argument
syntax "⦃" ident+ ":" term "⦄" : argument
syntax "(" term+ ")" : argument
syntax "{" term+ "}" : argument
syntax "⦃" term+ "⦄" : argument
syntax "[" term+ "]" : argument

def argument.toString : TSyntax `argument → String :=
  TSyntax.toString!

def arguments.toString : TSyntaxArray `argument → String := 
  Array.joinWith " " ∘ .map argument.toString

declare_syntax_cat kind
syntax "theorem" : kind
syntax "def" : kind
syntax "abbrev" : kind
syntax "axiom" : kind
syntax "opaque" : kind
syntax "example" : kind

def kind.toString : TSyntax `kind → String
  | `(kind| theorem) => "theorem"
  | `(kind| def) => "def"
  | `(kind| abbrev) => "abbrev"
  | `(kind| axiom) => "axiom"
  | `(kind| opaque) => "opaque"
  | `(kind| example) => "example"
  | _ => panic! "Expected `kind`"

declare_syntax_cat openNamespaces
syntax "open" ident+ "in" : openNamespaces

def openNamespaces.toArray : TSyntax `openNamespaces → Array String
  | `(openNamespaces| open $ns:ident* in) => ns.map (·.getId.toString)
  | _ => panic! "Expected `openNamespaces`"

declare_syntax_cat decl
syntax (kind)? (ident)? argument* ":" term (":=" term)? : decl

def decl.toDeclaration : TSyntax `decl → _root_.Declaration
  | `(decl| $[$k?:kind]? $[$nm?:ident]? $args:argument* : $t:term $[:= $val?:term]?) =>
  { kind := k?.eliminate kind.toString "def",
    name := nm? >>= (·.getId.toString),
    openNamespaces := #[]
    args := args |> arguments.toString,
    type := t.toString!,
    value := val?.eliminate TSyntax.toString! "sorry" }
  | _ => panic! "Expected `decl`"

declare_syntax_cat declWithNamespaces
syntax (openNamespaces)? decl : declWithNamespaces

def declWithNamespaces.toDeclaration : TSyntax `declWithNamespaces → _root_.Declaration
  | `(declWithNamespaces| $[$ns?:openNamespaces]? $d:decl) =>
    { decl.toDeclaration d with 
      openNamespaces := ns?.eliminate openNamespaces.toArray .empty }
  | _ => panic! "Expected `declWithNamespaces`"

declare_syntax_cat declWithDocstring
syntax (openNamespaces)? docComment decl : declWithDocstring

def declWithDocstring.toDeclarationWithDocstring : TSyntax `declWithDocstring → MetaM DeclarationWithDocstring
  | `(declWithDocstring| $[$ns?:openNamespaces]? $doc:docComment $d:decl) => 
  do pure <| { 
    toDeclaration := declWithNamespaces.toDeclaration <| 
                  ← `(declWithNamespaces| $[$ns?:openNamespaces]? $d:decl),
    docstring := ← getDocStringText doc }
  | _ => panic! "Expected `declWithDocstring`"

end Parsing


/-- Read a `Declaration` from a `String`. -/
def Declaration.fromString? (stmt : String) : Lean.MetaM <| Except String Declaration := do
  let env ← Lean.getEnv
  let stx? := Lean.Parser.runParserCategory env `decl stmt
  return stx?.map (decl.toDeclaration {raw := ·})

/-- Read a `DeclarationWithDocstring` from a `String`. -/
def DeclarationWithDocstring.fromString? (stmt : String) : Lean.MetaM <| Except String DeclarationWithDocstring := do
  let env ← Lean.getEnv
  let stx? := Lean.Parser.runParserCategory env `declWithDocstring stmt
  match stx? with
    | .error e => return .error e
    | .ok stx => .ok <$> declWithDocstring.toDeclarationWithDocstring ⟨stx⟩

open Lean Elab Term in
/-- Check whether a `Declaration` represents a type-correct `Lean` declaration. -/
def Declaration.typeCheck (env : MetaM Environment := getEnv) (decl : _root_.Declaration) : TermElabM <| Except String Unit := do
  let type := decl.toType
  let stx? := Lean.Parser.runParserCategory (← env) `term type
  match stx? with
    | .error e => return .error e
    | .ok stx => try 
      let _ := Term.withAutoBoundImplicit <| 
                Term.withoutErrToSorry <| 
                  elabType stx
      return .ok ()
    catch e => return .error <| ← e.toMessageData.toString
      
/-- Perform the type-checking of a `Declaration` with a given list of imports. -/
def Declaration.typeCheckWithImports (ns : List Lean.Name) (decl : Declaration) := do
  let env := liftM <| Lean.importModules (ns.map ({module := ·})) {}
  decl.typeCheck env

/-- Check whether a `DeclarationWithDocstring` represents a type-correct `Lean` declaration. -/
def DeclarationWithDocstring.typeCheck (env : Lean.MetaM Lean.Environment := Lean.getEnv) : DeclarationWithDocstring → Lean.Elab.Term.TermElabM (Except String Unit) :=
  Declaration.typeCheck env ∘ toDeclaration

/-- Perform the type-checking of a `DeclarationWithDocstring` with a given list of imports. -/
def DeclarationWithDocstring.typeCheckWithImports (ns : List Lean.Name) :=
  Declaration.typeCheckWithImports ns ∘ DeclarationWithDocstring.toDeclaration
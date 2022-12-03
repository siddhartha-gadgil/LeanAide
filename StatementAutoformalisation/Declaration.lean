import Lean

/-- A structure for storing details of Lean declarations such as `theorem`s or `def`s in `String` format. -/
structure Declaration where
  /-- Records whether the declaration is a `theorem`, `def`, `example`, `axiom`, `abbrev`, etc. -/
  kind : String
  /-- An optional name for the declaration. -/
  name : Option String := none
  /-- The list of open namespaces that the declaration is contained in. -/
  openNamespaces : List String := []
  /-- The arguments to the declaration (the part before the colon). -/
  args : String := "" -- TODO: Decide whether to make this a list/array
  /-- The type of the declaration (the part after the colon). -/
  type : String
  /-- The value of the declaration (the part after the `:=` - irrelevant for theorems, but useful for definitions). -/
  value : String := "sorry"

/-- A structure containing a `Declaration` together with its corresponding documentation string. -/
structure DeclarationWithDocstring extends Declaration where
  /-- The documentation string describing the declaration. -/
  docstring : String
  -- TODO eventually include embedding and keyword information

/-- The `kind` of a `ConstantInfo` term (`axiom`/`def`/`theorem`/...) as a `String`.-/
def Lean.ConstantInfo.kind? : Lean.ConstantInfo → Option String
  | axiomInfo  _ => "axiom"
  | defnInfo   _ => "def"
  | thmInfo    _ => "theorem"
  | opaqueInfo _ => "opaque"
  | quotInfo   _ =>  none
  | inductInfo _ => "inductive"
  | ctorInfo   _ =>  none
  | recInfo    _ => "rec"

open Lean in
/-- The declaration in the environment with the given name, as a `Declaration`. -/
def Declaration.fromName? (nm : Name) : MetaM <| Option _root_.Declaration := do
  let ci? := (← getEnv).constants.find? nm
  let type? ← display? <| ConstantInfo.type <$> ci?
  let value? ← display? <| ci? >>= ConstantInfo.value?
  return do some { 
      kind := ← ci? >>= ConstantInfo.kind?,
      name := some nm.toString,
      args := "",
      type := ← type?,
      value := value?.getD "sorry" }
where
  display? : Option Expr → MetaM (Option String)
  | none => return none
  | some e => (·.pretty) <$> Lean.PrettyPrinter.ppExpr e

open Lean in
/-- The declaration in the environment with the given name, together with its docstring, as a `DeclarationWithDocstring`. -/
def DeclarationWithDocstring.fromName? (nm : Name) : MetaM <| Option DeclarationWithDocstring := do
  let decl? ← Declaration.fromName? nm
  let doc? ← liftM <| findDocString? (← getEnv) nm
  return do some ⟨← decl?, ← doc?⟩

-- theorem test (n : Nat) : n = n := sorry
-- #eval do return Declaration.type <$> (← Declaration.fromName? `test)

open Lean in
/-- All declarations from the current environment. -/
def Declaration.envDecls : MetaM <| Array _root_.Declaration := sorry

open Lean in
/-- All declarations with documentation from the current environment. -/
def DeclarationWithDocstring.envDecls : MetaM <| Array DeclarationWithDocstring := sorry

/-- Render a `Declaration` as a `String`. -/
instance Declaration.toString : ToString Declaration where
  toString := fun ⟨kind, name?, _, args, type, value⟩ =>
      s! "{kind} {name?.getD ""} {args} : {type} := {value}"

/-- Decorate a `String` with Lean comment or docstring syntax. -/
def printComment (doc : String) : String := s!"/-- {doc} -/"

/-- Render a `DeclarationWithDocstring` as a `String`. -/
instance DeclarationWithDocstring.toString 
    [printDecl : ToString Declaration] :
    ToString DeclarationWithDocstring where
  toString := fun ⟨decl, doc⟩ => 
    s!"{printComment doc}\n{printDecl.toString decl}"

/-- Build a prompt from a list of `DeclarationWithDocstring`s. Note that the declarations are printed in the reverse order. -/
def buildPrompt [ToString Declaration] (decls : Array DeclarationWithDocstring)
  (suffix : String) : String :=
    decls.foldr
    -- this builds the prompt backwards
    (fun d prompt => s!"{toString d}\n\n{prompt}") 
    suffix

/-- Checks whether a `Declaration` represents a type-correct Lean declaration. -/
def Declaration.typeCheck : Declaration → Lean.MetaM Bool := sorry

/-- Checks whether a `DeclarationWithDocstring` represents a type-correct Lean declaration. -/
def DeclarationWithDocstring.typeCheck : DeclarationWithDocstring → Lean.MetaM Bool := sorry

/-- Read a `Declaration` from `JSON` format. -/
def Declaration.fromJson : Lean.Json → Except String Declaration := sorry

/-- Read a `DeclarationWithDocstring` from `JSON` format. -/
def DeclarationWithDocstring.fromJson : Lean.Json → Except String DeclarationWithDocstring := sorry

/-- Convert a `Declaration` to a `JSON` object. -/
def Declaration.toJson : Declaration → Lean.Json := sorry

/-- Convert a `DeclarationWithDocstring` to a `JSON` object. -/
def DeclarationWithDocstring.toJson : Declaration → Lean.Json := sorry

/-- Read a `Declaration` from a `String`. -/
def Declaration.fromString : String → Declaration := sorry

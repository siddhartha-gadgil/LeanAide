import Lean.Data.Json.FromToJson
import Lean.Syntax
import Lean.Elab
import Lean.Parser
import Init.Prelude

/-YAML-like syntax for Lean-/
namespace Lean.YAML

/-YAML syntactic category-/
declare_syntax_cat yaml

/-YAML null syntax-/
syntax "null" : yaml

/-YAML true syntax-/
syntax "true" : yaml

/-YAML false syntax-/
syntax "false" : yaml

/-YAML string syntax-/
syntax str : yaml

/-YAML keys can be identifiers or strings-/
syntax yamlIdent := ident <|> str

/-YAML key-value pairs-/
syntax manyIndent(yamlIdent":" yaml linebreak): yaml

/-YAML syntax for lists-/
syntax manyIndent("-" yaml linebreak): yaml

/-Alternative YAML syntax for lists-/
syntax "[" yaml,* "]": yaml


syntax "yaml%" yaml : term


macro_rules
  | `(yaml% "null") => `(Lean.Json.null)
  | `(yaml% "true") => `(Lean.Json.bool Bool.true)
  | `(yaml% "false") => `(Lean.Json.bool Bool.false)
  | `(yaml% $n:str) => `(Lean.Json.str $n)
  |`(yaml% $[$keys: yamlIdent : $values: yaml
    ]*)=> do
    let keys: Array (TSyntax `term) ← keys.mapM fun
    |`(yamlIdent| $key:ident) => pure (key.getId |> toString |> quote)
    |`(yamlIdent| $key:str )  => pure (key)
    | _                       => Macro.throwUnsupported
    `(Lean.Json.mkObj [$[($keys, yaml% $values)],*])
  |`(yaml% $[- $items:yaml
    ]*) => `(Lean.Json.arr #[$[yaml% $items],*])
  |`(yaml% [$[$obj],*]) => `(Lean.Json.arr #[$[yaml% $obj],*])

end Lean.YAML

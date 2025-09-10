import LeanAideCore.Syntax

namespace LeanAide

open Meta

/--
## Testing Quote Command

This is the basic form of the quote command syntax
-/
#quote test_quote

#eval test_quote

/--
Quote command *without* identifier
-/
#quote

/--
# General quote command

We can apply any function with domain `String`, for example the constructor of a type.
-/
#quote fn_test <| fun s ↦ "Hello, world!\n" ++ s ;

#eval fn_test

import LeanAideCore.Syntax
import LeanAideCore
import LeanAide.Responses
namespace LeanAide

open Meta

/--
## Testing Quote Command

This is the basic form of the quote command syntax
-/
#quote test_quote

#eval test_quote -- "## Testing Quote Command\n\nThis is the basic form of the quote command syntax"

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

-- Generation
open LeanAide.Discussion


-- #eval generateM "There are infinitely many odd numbers." Document

/-- There are infinitely many odd numbers. -/
#theorem_code infinitely_many_odd_numbers.theorem_code : {n | Odd n}.Infinite

#eval infinitely_many_odd_numbers.theorem_code




#start_chat chatEg

def chatEg₂ := chatEg.mkQuery  {message := "There are infinitely many even numbers."}

#prove chatEg₂ >> Response


#ask "Prove that there are infinitely many odd numbers" << chatEg

/--
Prove that there are infinitely many odd numnbers.
-/
#ask << chatEg

def chatEg₁ := chatEg + (thmText  "There are infinitely many odd numbers.")

#eval chatEg₁

#prove "There are infinitely many odd numbers." >> ProofDocument

namespace long_eg

#prove chatEg₁ >> ProofDocument

end long_eg



end LeanAide

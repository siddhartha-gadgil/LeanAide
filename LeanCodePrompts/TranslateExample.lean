import Mathbin.All
import Lean.Meta
import LeanCodePrompts.Translate
-- import LeanCodePrompts.Autocorrect
open Lean Meta Elab Term

example : //- Every prime number is either `2` or even -/  := by      
    sorry 

#eval showLogs 2

example : //- Every field is a ring -/ := by 
       sorry

#eval showLogs 2

example : //- There are infinitely many odd numbers -/ := by
        sorry

#eval showLogs 2

/-!
## Features

* Integrated interface using elaboration; caching, polling.
* Input-dependent prompting:
    - database of doc-strings from Mathlib
    - selected using: sentence similarity, keywords
* Post-processing:
    - Lean 3 to Lean 4 translation, auto-correction.
        - based on case-transformations, adding/dropping "is" and "has"
    - filtering by elaboration
    - selection by detected equality groups

## Possible improvements

* Interface: code actions
* Prompting:
    - better selection of prompts
    - better/larger database of prompts
    - use proximate prompts
* Post-processing
    - expand auto-correction
    - suggest imports
    - expand equality detection for selection
    - improve selections: round-trips
* Codex improvements:
    - hyper-parameters
    - fine-tuning
-/

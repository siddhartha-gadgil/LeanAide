# LeanAide: Recent and Next steps; Updates for: September 2025

We are moving to a new setup, to allow over the next couple of years multiple interfaces for LeanAide. Currently, the focus is on allowing all the capabilities of LeanAide to be usable:

* From within LeanAide (or with LeanAide as a dependency): For testing and development at least this is essential.
* From another Lean project via functions and a DSL by having `LeanAideCore` as a dependency (replacing `LeanAideTools` which had this role).
* Using an API.
* Via a Python interface.

## Connecting

* To use the Python interface, run from the root of LeanAide `python3 leanaide_server.py --ui` after installing the dependencies in `server/requirements.txt` (say in a virtual environment).
* The same way without the "--ui" label and without dependencies sets up just a web server for the API.
* To use LeanAide in a Lean project, add `LeanAideCore` and `Mathlib` as dependencies. The project `LeanAideCore` is a directory within `LeanAide`, and lake now supports such dependencies. Once you have done this, start the server as above in the LeanAide directory. Then you can use LeanAide by having the following at the top of your file:

```lean
import LeanAideCore
import Mathlib

open LeanAide
universe u v w u_1 u_2 u_3 u₁ u₂ u₃

#leanaide_connect
```

## Multi-stage proving

When proving a result, the approach we take in `LeanAide` is to:

* Ask an LLM to generate a *formalization friendly* proof, giving detailed instructions on the structure of the document to generate.
* From a document ask an LLM to generate a structured proof in a customized JSON schema.
* Generate Lean code from the structured JSON proof using:
  * Translation of statements and definitions in LeanAide.
  * Automation via `simp`, `hammer`, `grind` etc to finish the proof if possible.

This has been in the work for months. The immediate task is to make it convenient to use.

## Syntax (DSL)

At present we have commands like `#theorem`, `#def`, `#doc` and `#prove`. We will instead have clear inputs and outputs, with input auto-detected in some cases. Also, we have a new `#quote` syntax to allow highlighting and editing large blocks of text.

### Quote syntax

This is essentially equivalent to `def`, but allowing Markdown syntax highlighting and not needing strings to be escaped. For example, in the following the string `test_quote` is defined.

```lean
/--
## Testing Quote Command

This is the basic form of the quote command syntax
-/
#quote test_quote

#eval test_quote -- "## Testing Quote Command\n\nThis is the basic form of the quote command syntax"
```

### Modified `#theorem` and `#def`

In place of the fiddly rule of ending with "." or "?", we will have new syntax like:

```lean
#theorem "There are infinitely many odd numbers." --lean
```

For the convenience of the user, if the trailing `--lean` is not present a code action is offered to add it.

### Proofs

Since there are multiple stages of proving, the user needs to specify what they want. For example, consider the following command

```lean
#prove "There are infinitely many primes." --doc
```

This asks for a formalization-friendly proof document. The result will be a code action that replaces this by a "#quote" that defines a variable whose value is the document.

## Internals

### Dual setup

The dual setup allowing the functions of LeanAide to be used both directly and via http are based on a *typeclass* `Kernel` which has functions for the core capabilities. An instance of this is directly implemented in LeanAide but not in the core: specifically in `Responses.lean` soon after the corresponding function for the http server.

Another instance is defined in the `LeanAideCore` in `Kernel.lean` depending on another typeclass `LeanAidePipe`, which wraps a single function doing an http JSON query to an API. The syntax `#leanaide_connect` just defines an instance of this class given a url (which defaults to "http://localhost:7654"). 

A client thus needs to include LeanAideCore and run `#leanaide_connect` to "connect" to the server. The server needs to be running. On the other hand, within LeanAide (or with LeanAide as a dependency) we import `Responses.lean` so that an instance of the `Kernel` is in scope.

## Proving and History

We will implement types for Documents, Lean code etc, many of which are just wrappers (for instance wrapping `String`). For a conversation, proving session etc we define an (indexed) inductive type which allows appending to the previous elements of the conversation, editing etc.
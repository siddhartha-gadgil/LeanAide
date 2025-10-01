# RenPhil grant plans: October 2025

The previous plan `PlanSept25.md` has been implemented. This note is to internally collect things to do, especially in the first phase of the two year project.

The work we need to do is broadly:

* Improve core technology: mainly Autoformalization.
* Interfaces: For Lean users (DSL, server, Zulip Bot) and for Mathematicians (no code environment).
* Development tools: testing, logging etc to make development easier and more robust.

## Phase I goals

Those without checkboxes are not immediate goals.

### Testing

We need complete tests. In many of these cases, we can temporarily add traces in some trace class and use `#guard_msgs`. In the longer run we switch to our new logging framework.

* [ ] Parsing different allowed formats for theorems: just type, statement with/without name etc.
* [ ] The `SimpleFrontend`, including definitions extracted.
* [ ] All the cases of code generation, using Lean code so translation is not needed.
* [ ] Check that the context is picked up correctly, both in text and in Lean code.
* [ ] Nearest embeddings: check that the few best ones are always picked up.
* [ ] Definitions/Theorems used in a statement.
* [ ] The DSL, both in server and client.

### Logging

Some of the ways we want to log stuff:

* `trace` - Lean already has this.
* `IO.eprintln` - to log to stderr
* Log to a log file.

So the following scheme seems fine to me for now:

* We use the same names as Lean's trace classes. So these should be initiated by registering the trace class as usual.
* [ ] In the file `LeanAide.Config`have `def logToStdErr: Array Name := #[...]` and `def logToFile: Array Name := #[...]` which list the trace classes that will be logged using `IO.eprintln` and by writing to a file (maybe both a common file and one with name based on the trace class).
* [ ] To allow future abstraction (such as inheritance), have functions `isLoggedToFile: Name -> Bool` etc and only call these.
* [ ] Have a single function `logTrace (cls: Name) (msg: MessageData) : CoreM Unit` that:
* [ ] runs `Lean.trace cls msg`.
* [ ] writes to stderr and/or file based on whether the class name is in the lists in the config.

There are many improvements, but for a start we should

* [ ] Implement the function `logTrace`
* [ ] Replace all the current logging: `trace`, `appendLog`, `IO.eprintln` and `logTimed` with calls to `logTrace`. 
* [ ] To do this sensible classes are created and registered.

#### Looking ahead

* The main improvements should come indirectly, through better configuration.
* We may want to add more information to the logs, such as timestamps, calling function and module and `IO.monoMsNow` (for relative times).

### Prompts

* [ ] Refactor so that generation of a prompt is not inside another function.
* [ ] Have a different style of prompting with the examples inlined in a single query along with other information.
* [ ] Allow prompts to include definitions.
* [ ] In general, have composable and extensible prompt generation.

### Embeddings

* The current complicated setup was before the server-client model, and is unnecessary now.
* [ ] We should switch to FAISS or something like that.
* [ ] We should also not require OpenAI embeddings - especially for use for people in China.

### Extending "local" Autoformalization

Currently, autoformalization is done for statements of theorems as well as for definitions. On a larger scale these are put together. However, we need more *local* autoformalization:

* Instances: say a group structures.
* Structures and Classes
* Inductive types

The first step is the following:

* [ ] When parsing definition/theorem translations, also allow parsing commands and extracting the new expressions by running in the frontend.

### Caching

* [ ] Add caching for elaboration in the Frontend.
* Figure out the best way to store and share caches.
* A good option when we have a hosted server may be to let it add to the cache.

### Monads

* Currently, these are just stacked, with `TranslateM` on top.
* We can consider having `TranslateT` also, for example, to allow the state to be more modular.
* Capabilities can be introduced analogous to `MonadError` etc.

### Code Generation

* [ ] Loosely couple the code generation with local translation, to allow drop-in replacements such as Goedel Autoformalizer. May need (or benefit from) Monad refactoring.

### Server-Worker setup

* The motivation is that it is easy to run a server for LeanAide, say Drongo, but this will not have an external IP.
* [ ] We have a light-weight server on *App Engine* (for example) which stores task requests and passes them on when polled.
* [ ] We should be able to start `leanaide_process` using polling over https instead of stdio.
* [ ] The polling model can (and should) be tested locally.

### Extensible JSON schema

* [ ] We should allow the schema for a document to be extensible, specifically:
  * [ ] Adding cases for `anyOf`
  * [ ] Adding definitions in the definitions block.
* [ ] We may want to implement a specialized structure *schema* rather than JSON in general, separating out `description`, `type` etc.

### Plausible

* This is the tactic that finds counterexamples. Currently it only logs and does not give expressions.
* This is a goal unless Lean FRO starts working on it sooner than me.

## Larger goals

### Project using LeanAide

* We should work on interactively formalizing using LeanAide, with detailed feedback as we go along.

### Interfaces

* A no-code environment for Mathematicians. They should be able to see the code if they like.
* Lean server with LeanAide.
* Zulip Bot.

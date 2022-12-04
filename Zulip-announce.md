We have been working on a tool for AI based translation from natural language to Lean 4 with a convenient interface. 

* A quick demo of this in action: [leanaide-translation.gif](/user_uploads/3121/BAItBkvXHl43narE21FBKT7Y/leanaide-translation.gif) 
* A brief video: https://youtu.be/_NMquXd0Qos

The code is at https://github.com/siddhartha-gadgil/LeanAide.  The Lean code was written by @**Anand Rao** and myself, and is part of a collaboration with @**Ayush Agrawal** @**Ashvni Narayanan** and Navin Goyal.

## Quickstart

Our translation is based on Codex, to use which you need an OpenAI key. We also use a server for *sentence similarity*. To get started please configure environment variables using the following bash commands or equivalent in your shell:

```bash
export LEANAIDE_IP="34.100.184.111:5000"
export OPENAI_API_KEY=<your-open-ai-key>
```

Build this repository with the following commands

```bash
lake build mathlib
lake build
```

After this open the folder in VS code (or equivalent) with Lean 4 and go to the file `LeanCodePrompts/TranslateExample.lean`. Place the cursor anywhere on one of the comments below and invoke the _code action_ to translate by clicking on the _lightbulb_ or using `ctrl-.`

You can add your own comments and try to translate using the same method. In general, you can `import LeanCodePrompts.CodeActions` in a lean file and use the code-action to translate. You should usually also include `import Mathbin.All` to include the (partly broken) binary port of `mathlib`. 

In case translation fails please look at the troubleshooting section in the  [README](https://github.com/siddhartha-gadgil/LeanAide#readme) or message us here.

## How this works

The translation is based on **Codex** with *input-dependent prompting* and *post-processing*. Our steps are:

* given a natural language statement to be translated we find similar doc-strings in `mathlib` and build a *prompt* roughly with these and the corresponding code, with the natural language statement to be translated appended in the guise of a doc-string.
* the prompt is sent to the Codex server, which returns a bunch of *completions* (which we specify terminate with `:=`).
* these are then post-processed: we (attempt to) translate identifiers from Lean 3 to Lean 4, do some auto-correction, and filter out those that fail to *elaborate*.

More details are in a [note](https://mathai2022.github.io/papers/17.pdf) at the [2nd Math AI workshop](https://mathai2022.github.io/papers/) and in more detail (along with related work) in a [preprint](https://arxiv.org/abs/2211.07524).

## Limitations and road-map

We have a reasonable success rate with typical doc-strings with translations that are valid for the present state of the *binary port* of `mathlib`. We plan to work on many improvements, including

* translating to definitions as well as theorems,
* handling more complex mathematical idioms,
* more generally improving our success rate,
* using the info-panel to offer many choices to the user,
* using the translation of identifiers from mathlib3port and Lean's fuzzy finder in place of (or in addition to) our (hacky) translation and auto-correction.

We further plan to migrate to `mathlib4` as the target once its coverage is adequate. So suggestions, feature requests, contributions are most welcome over the next few months as we hope this tool moves to practical usability.

## Thanks

This work was only possible because of a lot of help we got here from the Lean community. We also got help from a few collaborators at Microsoft Research and Microsoft. Support to host the sentence similarity server comes from Google cloud research credits.
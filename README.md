# LeanAide 

LeanAide or Lean**AI**de (accidental pun) is work in progress to build AI based tools to help development with the Lean Theorem Prover. For now it has one tool under development, which translates statements written in natural language in a doc-string like format to Lean types (including theorem statements).

![leanaide-mathlib4](https://github.com/siddhartha-gadgil/LeanAide/assets/18333981/23de9912-5a60-4fd9-a99e-d9835629b4ca)

## Quickstart: translation to Lean statements

Our translation is based on GPT 3.5-turbo/GPT 4, to use which you need an OpenAI key. To get started please configure environment variables using the following bash commands or equivalent in your system:

```bash
export OPENAI_API_KEY=<your-open-ai-key>
```

Build this repository with the following commands:

```bash
lake exe cache get # download prebuilt mathlib binaries
lake build mathlib
lake build
```

After this open the folder in VS code (or equivalent) with Lean 4 and go to the file `LeanCodePrompts/TranslateExample.lean` or the file `LeanCodePrompts/TranslateDemo.lean`. Any statement written using syntax 
similar to `l!"There are infinitely many primes"` will be translated into Lean code. You will see examples of this in the demo files. Once the translation is done, a `Try this` hyperlink and code-action will appear. Clicking on this will add the translated code to the file.


To use in your own project, include this project as a dependency in `lakefile.lean` using the following.

```lean
require LeanCodePrompts from git "https://github.com/siddhartha-gadgil/LeanAide"@"main
```

If you import `LeanAide` and `Mathlib` to a file, the translation will be available.

## Contributions and details

This is joint work by our team, 

* Siddhartha Gadgil
* Anand Rao Tadipatri
* Ayush Agrawal
* Ashvni Narayanan
* Navin Goyal

with a lot of help from the Lean community and from collaborators at Microsoft Research. Our server is hosted with support from research credits from Google.

Our work is described in a [note](https://mathai2022.github.io/papers/17.pdf) at the [2nd Math AI workshop](https://mathai2022.github.io/papers/) and in more detail (along with related work) in a [preprint](https://arxiv.org/abs/2211.07524).



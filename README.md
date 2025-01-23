# LeanAide 

LeanAide or Lean**AI**de (accidental pun) is work in progress to build AI based tools to help development with the Lean Theorem Prover. For now it has one tool under development, which translates statements written in natural language in a doc-string like format to Lean types (including theorem statements).

![leanaide-mathlib4](https://github.com/siddhartha-gadgil/LeanAide/assets/18333981/23de9912-5a60-4fd9-a99e-d9835629b4ca)

## Quickstart: translation to Lean statements

Build this repository and fetch pre-loaded embeddings with the following commands:

```bash
lake exe cache get # download prebuilt mathlib binaries
lake build mathlib
lake build
lake exe fetch_embeddings
```

Our translation is based on GPT 3.5-turbo/GPT 4, to use which you need an OpenAI key. To get started please configure environment variables using the following bash commands or equivalent in your system at the base of the repository (the angle brackets are **not** to be included in the command), and then launch VS code. 

```bash
export OPENAI_API_KEY=<your-open-ai-key>
code .
```

Alternatively, you can create a file with path `rawdata/OPENAI_API_KEY` (relative to the root of LeanAIDE) containing your key.


After this open the folder in VS code (or equivalent) with Lean 4 and go to the file `LeanCodePrompts/TranslateDemo.lean`. Any statement written using syntax 
similar to `#theorem "There are infinitely many primes"` will be translated into Lean code. You will see examples of this in the demo files. Once the translation is done, a `Try this` hyperlink and code-action will appear. Clicking on this will add the translated code to the file.

Alternatively, you can translate a statement using the following command in the Lean REPL:

```lean
lake exe translate "There are infinitely many primes"
```

### Using as a dependency

Using in your own project still involves some issues, for example it is slow. 

As we use precompiled embeddings, we must have toolchains matching. For using with `v4.15.0` (so far the only version supported), include this project as a dependency in `lakefile.lean` using the following (or use the equivalent in `lakefile.toml`):

```lean
require LeanCodePrompts from git "https://github.com/siddhartha-gadgil/LeanAide"@"4.15.0"
```

The run from a terminal the following to download the prebuilt embeddings.

```bash
lake exe fetch_embeddings
```

If you import `LeanAide` and `Mathlib` to a file, the translation will be available.

## Contributions and details

The principal author of this repository is [Siddhartha Gadgil](https://math.iisc.ac.in/~gadgil/).

The first phase of this work (roughly June 2022-October 2023) was done in collaboration with:

* Anand Rao Tadipatri
* Ayush Agrawal
* Ashvni Narayanan
* Navin Goyal

We had a lot of help from the Lean community and from collaborators at Microsoft Research. Our server is hosted with support from research credits from Google.

More recently (since about October 2024) the work has been done in collaboration with:

* Anirudh Gupta
* Vaishnavi Shirsath
* Ajay Kumar Nair
* Malhar Patel
* Sushrut Jog

This is supported by ARCNet, ART-PARK, IISc.

Our work is described in a [note](https://mathai2022.github.io/papers/17.pdf) at the [2nd Math AI workshop](https://mathai2022.github.io/papers/) and in more detail (along with related work) in a [preprint](https://arxiv.org/abs/2211.07524).



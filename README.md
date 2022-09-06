# LeanAide 

LeanAide or LeanAIde (accidental pun) is work in progress to build AI based tools to help development with the Lean Theorem Prover. For now it has one tool under development, which translates statements written in natural language is a doc-string like format to Lean types (including theorem statements).

## Setup

The code uses `mathlib` as well as `mathlib3port` (i.e., "binport") in Lean and involves meta-programming. Getting all components working together is currently fiddly (though has been done successfully with fresh clones a few times). It also needs some Python code and some Python embedding data to be generated (embeddings are precomputed for efficiency).

### Lean Setup

The code has to be built using `lake build`, and `mathlib` and `mathlib3port` have to be built separately. Ideally the following sequences of commands should suffice.

* `lake build`
* `lake build mathlib`
* `lake build mathlib3port`

However, in practice one may have to do some combination of the following:

* change the directory to `lean_packages/mathlib` and run `lake build` from there.
* change the directory to `lean_packages/mathlib3port` and run lake build from there.
* change the directory to `lean_packages/mathlib3port` and run lake build from there after deleting the subdirectory `lean_packages` (i.e., the directory `lean_packages/mathlib3port/lean_packages` relative to the base of this repository).
* Rerun `lake build`.

For `lean 4/lake` experts any help with streamlining this will be appreciated.

### Python Setup

Some Python code is needed for the prompt engineering. The following installation steps may be needed before running (you may need to use `pip3` instead of `pip`).

```
pip install -U sentence-transformers

pip install flask

pip install yake
```

In addition, embeddings for mathlib prompts are precomputed. To do this, from the base directory, run the following.

```
cd SentenceSimilarityTask
python
```

and from Python, run the following
```
from sentence_similarity import *
save_corpus_embeddings()
```

Hopefully this should complete the setup. If not please ask the maintainers for help (the setup has not been thoroughly tested).

### Running

The Lean code assumes that a Python server is running. To start this, from the base directory run the following.

```
cd web_serv
flask run
```

Then open `code` from the base directory. Navigate to the file `TranslateExample.lean` to see an example translation (which will run automatically after compilation). More examples are in the comments.
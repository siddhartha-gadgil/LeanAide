# LeanAide 

LeanAide or Lean**AI**de (accidental pun) is work in progress to build AI based tools to help development with the Lean Theorem Prover. For now it has one tool under development, which translates statements written in natural language is a doc-string like format to Lean types (including theorem statements).

## Setup

The main code we use is in `Lean 4`. It also needs some Python code and some Python embedding data to be generated (embeddings are precomputed for efficiency).

### Lean Setup

The following sequences of commands should suffice for building the lean code.

* `lake build mathlib`
* `lake build`

### Troubleshooting

The present configuration seems to work reliably with the above instructions. If the above does not suffice, running the following command may be needed.

* `lake build mathlib3port`

However, since there are compatibility issues in the porting of `Lean`, if the above does not work one may have to do some combination of the following:

* change the directory to `lean_packages/mathlib` and run `lake build` from there.
* change the directory to `lean_packages/mathlib3port` and run lake build from there.
* change the directory to `lean_packages/mathlib3port` and run lake build from there after deleting the subdirectory `lean_packages` (i.e., the directory `lean_packages/mathlib3port/lean_packages` relative to the base of this repository).
* Rerun `lake build`.

### Python Setup

Some Python code is needed for the prompt engineering. The following installation steps may be needed before running (you may need to use `pip3` instead of `pip`).

```bash
pip install -U sentence-transformers

pip install flask

pip install yake
```

In addition, embeddings for mathlib prompts are precomputed. To do this, from the base directory, run the following.

```bash
cd SentenceSimilarityTask
python
```

and from Python, run the following

```python
from sentence_similarity import *
save_corpus_embeddings()
```

Hopefully this should complete the setup. If not please ask the maintainers for help (the setup has not been thoroughly tested).

### Running

The Lean code assumes that a Python server is running. To start this, from the base directory run the following.

```bash
cd web_serv
flask run
```

Then open `code` from the base directory. Navigate to the file `TranslateExample.lean` to see an example translation (which will run automatically after compilation). More examples are in the comments.
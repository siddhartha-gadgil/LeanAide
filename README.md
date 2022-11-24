# LeanAide 

LeanAide or Lean**AI**de (accidental pun) is work in progress to build AI based tools to help development with the Lean Theorem Prover. For now it has one tool under development, which translates statements written in natural language in a doc-string like format to Lean types (including theorem statements).

## Quickstart: translation to Lean statements

Our translation is based on Codex, to use which you need an OpenAI key. We also use a server for _sentence similarity_. To get started please configure environment variables using the following bash commands or equivalent in your shell:

```bash
export LEANAIDE_IP="34.100.184.111:5000"
export OPENAI_API_KEY=<your-open-ai-key>
```

Build this repository with the following commands

```bash
lake build mathlib
lake build
```

After this open the folder in VS code (or equivalent) with Lean 4 and go to the file `LeanCodePrompts/TranslateExample.lean`. Place the cursor to the end of one of the comments below and invoke the _code action_ to translate by clicking on the _lightbulb_ or using `ctrl-.`

You can add your own comments and try to translate using the same method. In general, you can `import LeanCodePrompts.CodeActions` in a lean file and use the code-action to translate. You should usually also include `import Mathbin.All` to include the (partly broken) binary port of `mathlib`. 

In case translation fails please look at the troubleshooting section below and/or message us on the Lean 4 Zulip.

To use in your own project, it should suffice to include this project as a dependency in `lakefile.lean` using the following (but this has not been tested).

```lean
require LeanCodePrompts from git "https://github.com/siddhartha-gadgil/LeanAide"
```

## Full setup instructions

The main code we use is in `Lean 4`. It also needs some Python code and some Python embedding data to be generated (embeddings are precomputed for efficiency). You can bypass the Python setup by using the server we host by configuring as above.

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

Some Python code is needed for the prompt engineering. The following installation steps may be needed before running (you may need to use `pip3` instead of `pip`, or even setup a new virtual environment).

```bash
pip install -r web_serv/requirements.txt
```

In addition, embeddings for mathlib prompts are precomputed. To do this, from the base directory, run the following.

```bash
python setup.py
```

Hopefully this should complete the setup. If not please ask the maintainers for help (the setup has not been thoroughly tested).

### Running

The Lean code assumes that a Python server is running. To start this, from the base directory run the following.

```bash
cd web_serv
flask run
```

Alternatively, to use a production wsgi server, run the following from the base directory.

```bash
cd web_serv
gunicorn -b :5000 wsgi:app
```


Then open `code` from the base directory. Navigate to the file `TranslateExample.lean` to see an example translation (which will run automatically after compilation). More examples are in the comments.

## Elaboration using a docker container

If one wants to just check validity of Lean code for statements, more precisely whether they can be elaborated, one can run a docker container. We can as an argument the statement we want to check or a list of statements as a json array. The standard output is the result as a json line. This can be used by calling from a script and redirecting outputs to a `jsonl` file.

Below are some examples.

```bash
sudo docker pull sgadgil00/leanaide-elaborator:latest # pull the docker image
sudo docker run sgadgil00/leanaide-elaborator:latest '["(p q :  ℕ ) (h : nat.prime  p) : p = q", "(p q: ℕ) : p = q", "(p: ℕ): is_silly p"]'
sudo docker run sgadgil00/leanaide-elaborator:latest '(p q :  ℕ ) (h : nat.prime  p) : p = q'
sudo docker run sgadgil00/leanaide-elaborator:latest '(p q :  ℕ ) -> (h : nat.prime  p) -> p = q'
```

Observe the statement can either consist of arguments followed by the claim (technically a `type`) or just be a claim (`type`). Further, mathlib terms are converted to their Lean 4 equivalents. 

## Lean-chat-IDP
We are developing a version of [Lean-chat](https://github.com/zhangir-azerbayev/lean-chat) with input dependent prompting.
# LeanAide 

LeanAide or Lean**AI**de (accidental pun) is work in progress to build AI based tools to help development with the Lean Theorem Prover. For now it has one tool under development, which translates statements written in natural language in a doc-string like format to Lean types (including theorem statements).

## Quickstart: translation to Lean statements

Our translation is based on Codex, to use which you need an OpenAI key. We also use a server for _sentence similarity_. To get started please configure environment variables using the following bash commands or equivalent in your shell:

```bash
export LEANAIDE_IP="34.100.184.111:5000"
export OPENAI_API_KEY=<your-open-ai-key>
```

Build this repository with the following commands:

```bash
lake build mathlib
lake build
```

Before the first command, it is advisable to download prebuilt `mathlib` binaries by running:

```bash
lake exe cache get
```

though this is not guaranteed to work. If it does not work, you can delete the `build` directory and build `mathlib` from source by running `lake build mathlib` instead.


After this open the folder in VS code (or equivalent) with Lean 4 and go to the file `LeanCodePrompts/TranslateExample.lean`. Place the cursor anywhere on one of the comments below and invoke the _code action_ to translate by clicking on the _lightbulb_ or using `ctrl-.`

You can add your own comments and try to translate using the same method. In general, you can `import LeanCodePrompts.CodeActions` in a lean file and use the code-action to translate. You should usually also include `import Mathlib` to include `mathlib`. 

To use in your own project, include this project as a dependency in `lakefile.lean` using the following.

```lean
require LeanCodePrompts from git "https://github.com/siddhartha-gadgil/LeanAide"
```

If you import `LeanAide` and `Mathlib` to a file, the code-action will be available, as in the [example](https://github.com/siddhartha-gadgil/proofs-and-programs-2023/blob/main/PnP2023/Extras/LeanTimes.lean).

A version of the same tool for `Lean3` is available [here](https://github.com/0art0/lean3-statement-translation-tool).

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

__Note:__ The docker container corresponds to the code in the git tag `data_binport` in this repository. This is because the statements are checked using the binary port of mathlib. The binary port has degraded during the porting process but the actual port (mathlib4) has not reached parity with the snapshot of the binary port at that tag.  

## Contributions and details

This is joint work by our team, 

* Siddhartha Gadgil
* Anand Rao Tadipatri
* Ayush Agrawal
* Ashvni Narayanan
* Navin Goyal

with a lot of help from the Lean community and from collaborators at Microsoft Research. Our server is hosted with support from research credits from Google.

Our work is described in a [note](https://mathai2022.github.io/papers/17.pdf) at the [2nd Math AI workshop](https://mathai2022.github.io/papers/) and in more detail (along with related work) in a [preprint](https://arxiv.org/abs/2211.07524).



import LeanSlides
import LeanCodePrompts.Translate

#slides +draft Introduction /-!

% LeanAIde
% A statement autoformalisation tool for Lean
% EuroProofNet Workshop 2023

# Contributors

- Siddhartha Gadgil
- Anand Rao Tadipatri
- Ayush Agrawal
- Ashvni Narayanan
- Navin Goyal

# Overview

- `LeanAIde` is a tool to translate
  mathematical statements from natural language
  to Lean code.
- The tool is itself written in `Lean 4`.
- At its core, `LeanAIde` relies on a 
  large language model for translation.
- Various optimisations to the input and output of
  the language model are used to push up 
  the success rate of translation. 

-/

-- TODO: Demo of the tool

#slides +draft Prompting /-!

# Direct prompting

TODO: Add screenshot

# Few-shot prompting

TODO: Add example

# Input-dependent prompting

TODO: Give details

-/

-- TODO: Demo of mathlib sentence retrieval using embeddings 

#slides +draft Details /-!

# The design

- Receive the input statement from the user through the Lean editor.
- Gather documentation strings from `mathlib` with similar content.
- Assemble a prompt from these doc-strings and query the language model.
- Post-process the outputs and retain only those corresponding to well-formed Lean expressions.
- Pick an output representing the most common translation and display it in the Lean editor.

# Sentence embeddings

Sentence embeddings are numerical representations of text
as vectors of real numbers in a way that captures 
semantic relationships between them.

The embedding of the input statement is computed (using OpenAI embeddings)
and compared with stored embeddings of
`Mathlib` doc-strings to identify the most similar ones.

# Prompting

The prompt to the language model is assembled from the sentence embeddings
as an alternating sequence of doc-strings and their corresponding Lean formal statements.

This is sent as a query to the OpenAI GPT-3.5 Turbo language model via an API call.

Additional configuration options permit adding a few fixed examples to the prompt
and also using theorems with doc-strings from the current editor window.

# Post-processing

A large part of the Lean mathematics library
was developed in the `Lean 3` proof assistant,
before recently transitioning to `Lean 4`.

As `Lean 3` code forms a larger portion of the 
model's training data, we post-process the output
to transform any `Lean 3` syntax into `Lean 4`.

# Elaboration filtering

Additionally, we retain only those
outputs of the language model that correspond to
well-formed Lean expressions.

As `Lean` is a dependently typed language,
this is a very strong condition.

# Output

After post-processing and filtering, the translations
are clustered by proved equivalence using 
the `aesop` automation tool.

A representative of the most common translation is
then presented to the user.

-/

#slides +draft Evaluation /-!

# Evaluation

# Custom Dataset

# ProofNet

-/

-- TODO: Random sampling of silly, false and normal statements.

#slides +draft Conclusion /-! -/
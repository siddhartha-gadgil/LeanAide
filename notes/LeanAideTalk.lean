import LeanSlides

#slides Introduction /-!

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
- The tool is written entirely in `Lean 4`.
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

# Sentence similarity

-- TODO

# Post-processing

-- TODO: Information about `mathlib` port

# Elaboration filtering

-- TODO: Explain elaboration briefly

# Output

-- TODO: Briefly mention `aesop` and its use for clustering
-- TODO: Briefly mention code actions

-/

#slides +draft Evaluation /-!

# Evaluation

# Custom Dataset

# ProofNet

-/

#slides +draft Conclusion /-! -/
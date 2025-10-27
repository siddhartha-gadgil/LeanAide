# A Framework for a Mathematical Reasoning Loop

## List of Tasks

A task has a prompt template and generally an output schema. These are grouped by the phases.

* **Problem Deconstruction & Formalization**
  * Structured Analysis
  * Definition Expansion
  * Rephrasing and Intuition

* **Problem Inspection**
  * Deciding whether to just prove.
  * Deciding whether to first study sources
    * **Branches** either "Source .." or "Problem .."

* **Source Material Analysis**
  * Listing theorems with structure
  * **Loop** through the following:
    * Structural Mapping: Connecting Hypothesis to Conclusion
    * Hypothesis Stress-Testing: The Art of Breaking Things
    * Generalization & Boundary Probing: Pushing the Limits
    * Core Idea Extraction: Finding the "Aha!" Moment

* **Strategy & Plan Generation**
  * Forward reasoning
  * Backward reasoning
  * Technique Brainstorming
  * Simplification & Specialization
  * Proof Sketch & Auxiliary Questions, including labelling auxiliary problems as *easy*, *standard* or *hard*.

* **Step-by-step Execution**
  * Single step execution
    * For a *hard* problem, recursively calls problem solving (with appropriate resource limits).
  * Formal Justification
  * Maintaining State (Summarization)

* **Verification & Critical Analysis**
  * The Skeptic's Hat
  * Sanity Checks and Edge Cases
  * Formalization in Lean and feedback;
    * Itself a many step process, can run in the background.

* **Meta-cognition and loop control**
  * Progress Analysis
  * Identifying Bottlenecks
  * Next Step: one of
    * Refine plan and continue
    * Strategy Pivot to a different plan
    * Changing the main goals (at least for now).

## Implementation

* This is straightforward, using recursion to loop and to branch.
* We have probabilities for triggering expensive tasks, with branches having reduced probabilities.
* The "study source material" is optionally phase 0. One option is to ask for source materials, with the option of skipping.
* There is also **Phase -1** just solve.
* A little work is needed for the interface.

## The loop

The process of solving a hard math problem can be broken down into five (plus 1) key phases. Your loop should be able to invoke tasks from any phase based on the current state of the solution.

## Implementation details from Gemini

This is a comprehensive and well-structured plan. Here are the prompt templates and corresponding JSON schemas for each step in your defined reasoning loop.

Placeholders like `{{problem}}`, `{{context}}`, or `{{source_material}}` are intended to be filled in by your controlling application.

-----

## 1\. Problem Inspection

### 1.1. Deciding whether to just prove / first study sources

This is a single triage step that determines the next phase.

**Prompt Template:**

```md
Analyze the following problem statement:
---
{{problem}}
---
Based on its complexity, terminology, and similarity to known theorems, decide the best initial strategy.

1.  **Direct Proof:** Do we have enough information to proceed directly to deconstruction and proof?
2.  **Source Study:** Must we first consult external sources to understand the terminology, context, or relevant existing proofs?

Provide your recommendation and a brief justification. If you recommend studying sources, suggest specific keywords, theorems, or papers to investigate.
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "ProblemTriageDecision",
  "description": "Initial decision on whether to proceed directly or study sources.",
  "type": "object",
  "properties": {
    "next_action": {
      "description": "The recommended next phase to enter.",
      "type": "string",
      "enum": ["ProblemDeconstruction", "SourceMaterialAnalysis"]
    },
    "justification": {
      "description": "Reasoning for the chosen next action.",
      "type": "string"
    },
    "suggested_sources": {
      "description": "If 'SourceMaterialAnalysis' is chosen, list potential keywords, theorems, or papers to study.",
      "type": "array",
      "items": { "type": "string" }
    }
  },
  "required": ["next_action", "justification"]
}
```

-----

## 2\. Source Material Analysis

This phase involves a loop. First, a step to find the theorems, then a loop over each one.

### 2.1. Listing theorems with structure (Entry Step)

**Prompt Template:**

```md
You have been given the following source material to study in relation to our main goal: '{{goal}}'.
---
Source Full Text:
{{source_material_full_text}}
---
Identify the key theorems, proofs, or sections in this material that are most relevant to our goal.

For each relevant item, provide:
1.  Its name (e.g., "Theorem 4.1").
2.  Its location (e.g., "Page 5, Section 4").
3.  A score (1-10) for its relevance.
4.  The **full, extracted text snippet** of its proof.
```

**JSON Schema (Revised):**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "TheoremExtractor",
  "description": "Identifies, lists, and extracts key theorems and their proofs.",
  "type": "object",
  "properties": {
    "theorems_found": {
      "description": "A list of theorems to be analyzed.",
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "name": { "type": "string", "description": "The name of the theorem or section." },
          "location": { "type": "string", "description": "Page, section, or chapter." },
          "relevance_score": {
            "type": "number",
            "description": "1-10 scale of relevance to the main problem.",
            "minimum": 1,
            "maximum": 10
          },
          "relevance_justification": { "type": "string" },
          "proof_snippet": {
            "type": "string",
            "description": "The full, extracted text of the proof."
          }
        },
        "required": [
          "name",
          "location",
          "relevance_score",
          "relevance_justification",
          "proof_snippet"
        ]
      }
    }
  },
  "required": ["theorems_found"]
}
```

-----

### 2.2. Structural Mapping (Loop Step)

**Prompt Template:**

```md
Analyze the following proof of '{{theorem_name}}' (from '{{location}}'):
---
{{proof_snippet}}
---
Deconstruct the argument into its key logical steps. For each step, create a dependency list specifying which of the theorem's original hypotheses and which previously proven steps are used.
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "ProofStructuralMap",
  "description": "Maps the logical flow of a single proof.",
  "type": "object",
  "properties": {
    "theorem_name": { "type": "string" },
    "original_hypotheses": {
      "type": "array",
      "items": { "type": "string" },
      "description": "List of all initial hypotheses of the theorem."
    },
    "proof_steps": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "step_id": { "type": "string", "description": "A unique ID, e.g., 'Step 1', 'Lemma A'." },
          "claim": { "type": "string", "description": "The statement being proven at this step." },
          "dependencies": {
            "type": "array",
            "items": { "type": "string" },
            "description": "List of original hypotheses or 'step_id's used."
          }
        },
        "required": ["step_id", "claim", "dependencies"]
      }
    }
  },
  "required": ["theorem_name", "original_hypotheses", "proof_steps"]
}
```

### 2.3. Hypothesis Stress-Testing (Loop Step)

**Prompt Template:**

```md
Let's stress-test the hypotheses for '{{theorem_name}}'.
Original hypotheses: {{original_hypotheses}}
Proof structure: {{proof_structural_map}}

For each hypothesis, analyze its necessity:
1.  Construct a simple counterexample that violates *only* this hypothesis.
2.  Trace this counterexample through the proof and identify the *exact* proof step (by step_id) that fails.
3.  Explain *why* it fails.
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "HypothesisStressTest",
  "description": "Analyzes the necessity of each hypothesis.",
  "type": "object",
  "properties": {
    "stress_tests": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "hypothesis_tested": { "type": "string" },
          "counterexample_sketch": { "type": "string" },
          "failed_proof_step_id": { "type": "string" },
          "explanation_of_failure": { "type": "string" }
        },
        "required": ["hypothesis_tested", "counterexample_sketch", "failed_proof_step_id", "explanation_of_failure"]
      }
    }
  },
  "required": ["stress_tests"]
}
```

### 2.4. Generalization & Boundary Probing (Loop Step)

**Prompt Template:**

```md
Analyze the boundaries of '{{theorem_name}}'.
Original hypotheses: {{original_hypotheses}}

For each hypothesis, propose a potential weakening (e.g., 'continuous' -> 'bounded', 'n=3' -> 'n'). Then, analyze if the proof's logic (from {{proof_structural_map}}) could be adapted or if it breaks.
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "GeneralizationProbe",
  "description": "Proposes and analyzes weaker hypotheses.",
  "type": "object",
  "properties": {
    "probes": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "original_hypothesis": { "type": "string" },
          "proposed_weakening": { "type": "string" },
          "analysis": { "type": "string", "description": "Would the theorem still hold? What modifications are needed?" },
          "new_conclusion": { "type": "string", "description": "A weaker conclusion that might hold if the theorem fails." }
        },
        "required": ["original_hypothesis", "proposed_weakening", "analysis"]
      }
    }
  },
  "required": ["probes"]
}
```

### 2.5. Core Idea Extraction (Loop Step)

**Prompt Template:**

```md
After this deep analysis of '{{theorem_name}}' (summarized in {{analysis_so_far}}), what is its single 'core idea' or 'key trick'?

Summarize the central insight in 1-3 sentences. What is the one thing to remember from this proof that could be applied to our main problem?
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "CoreIdeaExtraction",
  "description": "Summarizes the key insight of a proof.",
  "type": "object",
  "properties": {
    "core_idea_summary": {
      "description": "A concise (1-3 sentence) explanation of the 'aha!' moment.",
      "type": "string"
    },
    "key_techniques": {
      "description": "List of the main techniques used (e.g., 'diagonalization', 'pigeonhole principle').",
      "type": "array",
      "items": { "type": "string" }
    },
    "relevance_to_main_problem": {
      "description": "How this core idea might be applied to our main goal.",
      "type": "string"
    }
  },
  "required": ["core_idea_summary", "key_techniques", "relevance_to_main_problem"]
}
```

-----

## 3\. Problem Deconstruction & Formalization

### 3.1. Structured Analysis

**Prompt Template:**

```md
Analyze the following problem statement:
---
{{problem}}
---
Identify and list the following formal components:
1.  **Givens/Data:** All explicit data, variables, and their domains.
2.  **Hypotheses/Premises:** The assumptions or conditions stated to be true.
3.  **Goal/Conclusion:** The precise statement to be proven or the quantity/object to be found.
4.  **Problem Type:** Classify the problem (e.g., Proof, Calculation, Optimization).
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "ProblemStructuredAnalysis",
  "description": "Decomposes the problem into formal components.",
  "type": "object",
  "properties": {
    "givens": {
      "description": "Explicit data, variables, and their domains.",
      "type": "array",
      "items": { "type": "string" }
    },
    "hypotheses": {
      "description": "The assumptions or conditions stated to be true.",
      "type": "array",
      "items": { "type": "string" }
    },
    "goal": {
      "description": "The precise statement to be proven or the object/value to be found.",
      "type": "string"
    },
    "problem_type": {
      "description": "Classification of the problem.",
      "type": "string",
      "enum": ["Proof", "Calculation", "Optimization", "Existence", "Construction", "Other"]
    }
  },
  "required": ["givens", "hypotheses", "goal", "problem_type"]
}
```

### 3.2. Definition Expansion

**Prompt Template:**

```md
From the structured analysis:
{{structured_analysis_output}}

List every mathematical term, symbol, and piece of notation. Provide its precise, formal definition *in the context of this problem*. Identify any potential ambiguities (e.g., does 'log' mean ln or log10?).
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "DefinitionExpansion",
  "description": "Unpacks and defines all terminology.",
  "type": "object",
  "properties": {
    "definitions": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "term": { "type": "string", "description": "The term, symbol, or notation." },
          "definition": { "type": "string", "description": "The precise, formal definition in context." },
          "ambiguities": { "type": "string", "description": "Any potential ambiguities." }
        },
        "required": ["term", "definition"]
      }
    }
  },
  "required": ["definitions"]
}
```

### 3.3. Rephrasing and Intuition

**Prompt Template:**

```md
Given the formal deconstruction of the problem:
{{structured_analysis_output}}
{{definition_expansion_output}}

Rephrase the entire problem in simpler, more intuitive terms, as if explaining it to an undergraduate. What is the core question being asked? Provide an analogy if helpful.
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "ProblemIntuition",
  "description": "Provides an intuitive rephrasing of the problem.",
  "type": "object",
  "properties": {
    "simple_rephrasing": {
      "description": "The problem explained in simple terms.",
      "type": "string"
    },
    "core_question": {
      "description": "The central intuitive question.",
      "type": "string"
    },
    "analogy": {
      "description": "A helpful analogy, if applicable.",
      "type": "string"
    }
  },
  "required": ["simple_rephrasing", "core_question"]
}
```

-----

## 4\. Strategy & Plan Generation

### 4.1. Forward Reasoning

**Prompt Template:**

```md
Let's begin exploring strategies.
Start *only* from the problem's hypotheses:
{{hypotheses}}

What are 5-10 immediate, non-trivial deductions or consequences we can derive? For each, state the justification (e.g., "by definition of compactness", "by Mean Value Theorem").
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "ForwardReasoning",
  "description": "Immediate deductions from the hypotheses.",
  "type": "object",
  "properties": {
    "deductions": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "deduction": { "type": "string", "description": "The new fact or statement." },
          "justification": { "type": "string", "description": "The theorem, definition, or axiom used." }
        },
        "required": ["deduction", "justification"]
      }
    }
  },
  "required": ["deductions"]
}
```

### 4.2. Backward Reasoning

**Prompt Template:**

```md
Now, let's work backward.
Consider the main goal:
{{goal}}

What are 3-5 statements or conditions that, if proven true, would *directly* imply this goal? For each, explain *how* it implies the goal.
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "BackwardReasoning",
  "description": "Statements that would directly imply the conclusion.",
  "type": "object",
  "properties": {
    "penultimate_steps": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "statement": { "type": "string", "description": "The statement to be proven." },
          "justification": { "type": "string", "description": "How this statement implies the main goal." }
        },
        "required": ["statement", "justification"]
      }
    }
  },
  "required": ["penultimate_steps"]
}
```

### 4.3. Technique Brainstorming

**Prompt Template:**

```md
Based on the problem deconstruction:
{{structured_analysis_output}}
And our initial reasoning:
{{forward_reasoning_output}}
{{backward_reasoning_output}}
And any insights from source study:
{{source_analysis_summary_if_any}}

List the top 5 most likely mathematical fields or techniques that could be applicable. For each, provide a one-sentence justification.
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "TechniqueBrainstorm",
  "description": "Lists relevant mathematical techniques.",
  "type": "object",
  "properties": {
    "techniques": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "technique_name": { "type": "string", "description": "e.g., 'Proof by Induction', 'Diagonalization'." },
          "justification": { "type": "string", "description": "Why this technique is relevant." }
        },
        "required": ["technique_name", "justification"]
      }
    }
  },
  "required": ["techniques"]
}
```

### 4.4. Simplification & Specialization

**Prompt Template:**

```md
Let's simplify the main problem:
{{problem}}

Propose three special, concrete cases to analyze. For each, describe the case, provide a quick solution or analysis, and state the potential insight for the general problem.
(Examples: n=1, a finite set, a linear function, an extreme value).
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "ProblemSimplification",
  "description": "Defines and analyzes simpler versions of the problem.",
  "type": "object",
  "properties": {
    "special_cases": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "case_description": { "type": "string", "description": "The simplified version (e.g., 'n=1 case')." },
          "analysis": { "type": "string", "description": "A quick analysis or solution for this case." },
          "potential_insight": { "type": "string", "description": "What this case might teach us for the general problem." }
        },
        "required": ["case_description", "analysis", "potential_insight"]
      }
    }
  },
  "required": ["special_cases"]
}
```

### 4.5. Proof Sketch & Auxiliary Questions

**Prompt Template:**

```md
Synthesize all analysis so far. Generate two distinct proof sketches (Plan A, Plan B) to solve the problem.

For each sketch:
1.  State the overall strategy.
2.  List the major steps as auxiliary problems.
3.  For each step, classify its difficulty as 'easy', 'standard', or 'hard'. A 'hard' problem is a significant lemma that will require a new recursive problem-solving loop.
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "ProofSketch",
  "description": "Generates high-level proof plans with classified steps.",
  "type": "object",
  "properties": {
    "plans": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "plan_name": { "type": "string", "description": "e.g., 'Plan A: Proof by Contradiction'." },
          "strategy_summary": { "type": "string" },
          "steps": {
            "type": "array",
            "items": {
              "type": "object",
              "properties": {
                "step_goal": { "type": "string", "description": "The sub-goal or lemma to prove for this step." },
                "difficulty": {
                  "type": "string",
                  "enum": ["easy", "standard", "hard"],
                  "description": "'hard' spawns a recursive loop."
                }
              },
              "required": ["step_goal", "difficulty"]
            }
          }
        },
        "required": ["plan_name", "strategy_summary", "steps"]
      }
    }
  },
  "required": ["plans"]
}
```

-----

## 5\. Step-by-step Execution

### 5.1. Single step execution

**Prompt Template:**

```md
We are executing '{{plan_name}}'.
Our current state is: {{state_summary}}
The current sub-goal is: '{{step_goal}}' (Difficulty: '{{step_difficulty}}')

Execute this single step. Provide the new fact derived and a brief justification. If this step fails or is blocked, state that clearly.
(Note: 'hard' problems are handled by a recursive call, so this prompt is for 'easy' or 'standard' steps).
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "SingleStepExecution",
  "description": "Executes one step of a proof plan.",
  "type": "object",
  "properties": {
    "status": {
      "type": "string",
      "enum": ["success", "failure", "blocked"],
      "description": "Status of this step execution."
    },
    "new_fact": {
      "description": "The new statement/conclusion from this step (if success).",
      "type": "string"
    },
    "brief_justification": {
      "description": "A brief explanation of how this was derived (if success).",
      "type": "string"
    },
    "failure_reason": {
      "type": "string",
      "description": "If status is 'failure' or 'blocked', explain why."
    }
  },
  "required": ["status"]
}
```

### 5.2. Formal Justification

**Prompt Template:**

```md
You just executed a step, resulting in:
'{{new_fact}}'
You claimed this followed from:
'{{established_facts}}'

Provide a detailed, formal justification for this specific deduction. Cite the specific axioms, definitions, theorems, or lemmas used.
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "FormalJustification",
  "description": "Provides a rigorous justification for a single step.",
  "type": "object",
  "properties": {
    "formal_proof_step": {
      "description": "The detailed, line-by-line justification for this single deduction.",
      "type": "string"
    },
    "citations": {
      "description": "The specific theorems, axioms, or definitions cited.",
      "type": "array",
      "items": { "type": "string" }
    }
  },
  "required": ["formal_proof_step", "citations"]
}
```

### 5.3. Maintaining State (Summarization)

**Prompt Template:**

```md
Let's pause and summarize our progress on '{{plan_name}}'.
Please provide a structured summary of the current proof state, based on all steps executed so far.
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "StateSummary",
  "description": "Summarizes the current state of the proof.",
  "type": "object",
  "properties": {
    "original_hypotheses": {
      "type": "array",
      "items": { "type": "string" }
    },
    "main_goal": {
      "type": "string"
    },
    "established_facts": {
      "description": "All proven intermediate steps and lemmas.",
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "fact_id": { "type": "string" },
          "statement": { "type": "string" }
        },
        "required": ["fact_id", "statement"]
      }
    },
    "current_sub_goal": {
      "description": "The immediate next goal from the plan.",
      "type": "string"
    }
  },
  "required": ["original_hypotheses", "main_goal", "established_facts", "current_sub_goal"]
}
```

-----

## 6\. Verification & Critical Analysis

### 6.1. The Skeptic's Hat

**Prompt Template:**

```md
Act as a skeptical mathematician reviewing our work.
Critically analyze the logical argument from '{{previous_facts}}' to '{{new_facts}}', which was justified by:
---
{{formal_proof_step}}
---
Are there any gaps? Ambiguities? Unstated assumptions? Actively try to find a flaw or a counterexample to this specific step.
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "SkepticalReview",
  "description": "Adversarially checks a proof step for flaws.",
  "type": "object",
  "properties": {
    "is_sound": {
      "type": "boolean",
      "description": "True if no flaws were found in this step."
    },
    "flaws_found": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "potential_flaw": { "type": "string", "description": "The logical gap or unstated assumption." },
          "severity": { "type": "string", "enum": ["minor", "major", "fatal"] },
          "recommendation": { "type": "string", "description": "How to fix this flaw." }
        },
        "required": ["potential_flaw", "severity"]
      }
    }
  },
  "required": ["is_sound", "flaws_found"]
}
```

### 6.2. Sanity Checks and Edge Cases

**Prompt Template:**

```md
We just established the intermediate result:
'{{intermediate_result}}'

Let's do a sanity check. Test this result against the simple/edge cases we identified earlier:
{{special_cases}}

Does the intermediate result hold for all of them? For each case, state 'Holds' or 'Fails' and explain why.
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "SanityCheck",
  "description": "Tests an intermediate result against special cases.",
  "type": "object",
  "properties": {
    "all_passed": {
      "type": "boolean"
    },
    "test_results": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "case": { "type": "string", "description": "The special case being tested." },
          "holds": { "type": "boolean", "description": "Does the result hold for this case?" },
          "explanation": { "type": "string", "description": "Explanation, especially if it fails." }
        },
        "required": ["case", "holds"]
      }
    }
  },
  "required": ["all_passed", "test_results"]
}
```

### 6.3. Formalization in Lean and feedback

**Prompt Template:**

```md
Translate the following mathematical argument into Lean 4 code.
---
Definitions/Imports:
{{lean_definitions_and_imports}}
---
Goal Statement:
{{lean_goal_statement}}
---
Proof Argument:
{{proof_argument_text}}
---
Generate the Lean 4 code for this proof.
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "LeanFormalizationAttempt",
  "description": "Generates Lean 4 code for a proof argument.",
  "type": "object",
  "properties": {
    "lean_code": {
      "description": "The generated Lean 4 proof.",
      "type": "string"
    }
  }
}
```

*(Note: The feedback loop from Lean would then be a new prompt, as described in our previous discussion.)*

-----

## 7\. Meta-cognition and loop control

### 7.1. Progress Analysis

**Prompt Template:**

```md
Let's assess our progress on '{{plan_name}}'.
-   Resources used: {{resource_metric}}
-   Steps completed: {{steps_completed_count}}
-   Current state: {{state_summary}}
-   Known blocks: {{blocks_list}}

On a scale of 1 (dead end) to 10 (highly promising), how viable is this strategy? Justify your score. Is it becoming overly complex or is it on track?
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "ProgressAnalysis",
  "description": "Assesses the viability of the current plan.",
  "type": "object",
  "properties": {
    "promising_score": {
      "description": "Confidence in this plan (1-10).",
      "type": "integer",
      "minimum": 1,
      "maximum": 10
    },
    "analysis": {
      "description": "Justification for the score. Is it getting too complex or is it on track?",
      "type": "string"
    }
  },
  "required": ["promising_score", "analysis"]
}
```

### 7.2. Identifying Bottlenecks

**Prompt Template:**

```md
We are stuck.
-   Current Plan: '{{plan_name}}'
-   Failed Step: '{{failed_step}}'
-   Failure Reason: '{{failure_reason}}'

Analyze this impasse. What is the *single biggest obstacle* preventing progress? Frame this obstacle as a precise, self-contained mathematical question.
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "BottleneckIdentification",
  "description": "Frames the current obstacle as a precise question.",
  "type": "object",
  "properties": {
    "bottleneck_question": {
      "description": "The core problem that needs to be solved.",
      "type": "string"
    },
    "obstacle_type": {
      "type": "string",
      "enum": ["missing_lemma", "flawed_strategy", "complex_calculation", "knowledge_gap", "ambiguous_definition"]
    }
  },
  "required": ["bottleneck_question", "obstacle_type"]
}
```

### 7.3. Next Step

**Prompt Template:**

```md
Given the meta-analysis:
-   Progress Score: {{progress_score}}
-   Bottleneck: '{{bottleneck_question}}'
-   Alternative plans available: {{alternative_plans_list}}

What is the best executive decision for the next step?
-   **Refine plan:** Continue '{{plan_name}}' but modify it to address the bottleneck.
-   **Strategy Pivot:** Abandon '{{plan_name}}' and switch to a different plan.
-   **Change goal:** Modify the main goal (e.g., prove a weaker result).
```

**JSON Schema:**

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "NextStepDecision",
  "description": "Decides the next action for the loop controller.",
  "type": "object",
  "properties": {
    "decision": {
      "type": "string",
      "enum": ["refine_plan", "pivot_to_new_plan", "change_main_goal", "abandon"]
    },
    "justification": {
      "description": "The reasoning for this decision.",
      "type": "string"
    },
    "selected_plan_name": {
      "description": "If pivoting, the name of the new plan to try.",
      "type": "string"
    },
    "new_goal": {
      "description": "If changing goal, the new goal statement.",
      "type": "string"
    },
    "refinement_details": {
      "description": "If refining, the specific changes to make to the plan.",
      "type": "string"
    }
  },
  "required": ["decision", "justification"]
}
```

## Phase 0: Source Material Analysis

### Task: Deep Study of a Reference Proof or Paper

This task is a powerful form of "reconnaissance" 🕵️. It's not about solving *your* problem directly, but about dissecting a related, solved problem to extract its core mechanics, assumptions, and tricks. This is best used when your problem is similar to a known theorem or you've found a relevant paper.

#### Guidelines & Prompts

**Goal:** To move beyond a surface-level understanding of a proof and grasp *why* it is constructed the way it is.

1. **Structural Mapping: Connecting Hypothesis to Conclusion**

   * **Rationale:** A proof is not a monolithic block; it's a directed graph of logical deductions. This step aims to uncover that graph, revealing which parts of the input (hypotheses) are essential for which parts of the output (conclusion).
   * **Prompt Example:**
       > "Analyze the provided proof of the [Theorem Name]. Deconstruct the argument into its key logical steps (lemmas or major deductions). For each step, create a dependency list specifying:
       > 1. **The Claim:** The statement being proven at this step.
       > 2. **Dependencies:** Which of the original hypotheses (e.g., 'compactness', 'continuity') and which of the *previously proven steps* are explicitly or implicitly used to justify this claim."

2. **Hypothesis Stress-Testing: The Art of Breaking Things**

   * **Rationale:** To understand why a condition is necessary, you must see what goes wrong when it's absent. This builds deep intuition and reveals the "load-bearing walls" of the proof.
   * **Prompt Example:**
       > "Let's stress-test the hypotheses of the [Theorem Name]. For each of the following hypotheses, perform this analysis:
       > * **Hypothesis to test:** [e.g., 'The space must be Hausdorff']
       > 1. **Construct a Counterexample:** Provide a simple, concrete mathematical object that violates *this specific hypothesis* but satisfies all the others.
       > 2. **Trace the Failure:** Step-by-step, trace this counterexample through the proof. Identify the *exact first line or deduction* where the proof's logic breaks down.
       > 3. **Explain the Breakdown:** Clearly explain *why* the logic fails at that point for your counterexample."

3. **Generalization & Boundary Probing: Pushing the Limits**

   * **Rationale:** The most insightful discoveries often happen at the boundaries of a theorem. This step explores whether the hypotheses are overly restrictive.
   * **Prompt Example:**
       > "Let's explore the boundaries of the [Theorem Name]. For each hypothesis, propose a potential weakening. Then, analyze the viability of the proof under this new, weaker condition.
       > * **Original Hypothesis:** [e.g., 'The function is $C^1$ (continuously differentiable)']
       > 1. **Proposed Weakening:** [e.g., 'The function is merely continuous', or 'The function is differentiable everywhere except at a single point'].
       > 2. **Impact Analysis:** Would the original conclusion still hold? If so, sketch how the proof might be adapted. If not, identify the obstacle and speculate if a *weaker* conclusion might still be possible."

4. **Core Idea Extraction: Finding the "Aha!" Moment**

   * **Rationale:** Every clever proof has a central trick or insight. This prompt forces the model to distill the essence of the argument, making it a reusable mental tool.
   * **Prompt Example:**
       > "After this deep analysis, what is the 'core idea' or 'key trick' of this proof? Summarize the central insight in 1-3 sentences, as if you were explaining it to a peer to give them the 'aha!' moment without repeating the whole proof."

## Phase 1: Problem Deconstruction & Formalization

   **Goal:** Ensure the model has an unambiguous, deep, and structured understanding of the problem. This is the foundation for everything that follows.

* **1.1. Structured Analysis (Your Prompt)**
  * **Task:** Decompose the problem into its formal components.
  * **Rationale:** Forces a rigorous parse of the input text, separating what's given from what's required.
  * **Prompt Example:** "Analyse the following problem. Identify and list the following components:
           1.  **Givens/Data:** All explicit data, variables, and their domains.
           2.  **Hypothesis/Premises:** The assumptions or conditions that are stated to be true.
           3.  **Goal/Conclusion:** The precise statement to be proven or the quantity/object to be found.
           4.  **Problem Type:** Classify the problem (e.g., Proof, Calculation, Optimization, Existence)."

* **1.2. Definition Expansion**
  * **Task:** Unpack all terminology and notation.
  * **Rationale:** Many errors stem from misunderstanding a term's precise mathematical meaning.
  * **Prompt Example:** "For the problem statement, list every mathematical term and symbol (e.g., 'compact set', 'group homomorphism', '$\int_a^b f(x) dx$') and provide its precise definition in the context of this problem."

* **1.3. Rephrasing and Intuition**
  * **Task:** Ask the model to explain the problem in its own words, perhaps using an analogy.
  * **Rationale:** This is a powerful check for true understanding versus simple pattern-matching of the input text.
  * **Prompt Example:** "Rephrase the entire problem in simpler terms, as if you were explaining it to an undergraduate student. What is the core intuition behind the question being asked?"

## Phase 2: Strategy & Plan Generation

**Goal:** Brainstorm potential paths to a solution without getting bogged down in the details of execution.

* **2.1. Deductive & Abductive Reasoning (Your Prompt)**
  * **Task:** Explore the logical space around the hypothesis and conclusion.
  * **Rationale:** Builds a bridge of potential connections between the start and end points.
  * **Prompt Examples:**
    * **Forward Chaining:** "Starting *only* from the hypothesis, what are 5-10 immediate deductions or consequences we can derive? For each, state the theorem or definition used."
    * **Backward Chaining:** "What are some conditions or statements that, if they were true, would directly imply the conclusion? List at least three distinct 'penultimate steps'."

* **2.2. Technique Brainstorming (Your Prompt)**
  * **Task:** List relevant mathematical fields, theorems, and proof techniques.
  * **Rationale:** Maps the problem's characteristics to the vast library of mathematical tools.
  * **Prompt Example:** "Based on the problem's structure and keywords, list the top 5 most likely mathematical fields or techniques that could be applicable (e.g., Proof by Induction, Diagonalization, Mean Value Theorem, Pigeonhole Principle). For each, provide a one-sentence justification of its relevance."

* **2.3. Simplification and Specialization (Your Prompt)**
  * **Task:** Create simpler, solvable versions of the problem.
  * **Rationale:** Often, the solution to a general problem is an extension of the solution to a simple case. This also helps build intuition.
  * **Prompt Example:** "Let's simplify the problem. Propose and analyze three special cases. For example:
        1.  Consider the case where the dimension $n=1$ or $n=2$.
        2.  What if the function is linear or the set is finite?
        3.  What happens in an extreme or degenerate case (e.g., a value approaches zero or infinity)?"

* **2.4. Proof Sketch & Auxiliary Questions (Your Prompt)**
  * **Task:** Outline high-level plans and identify key sub-problems.
  * **Rationale:** Creates a roadmap for the proof. It's easier to verify a high-level plan than to debug a detailed, incorrect proof.
  * **Prompt Example:** "Generate two distinct proof sketches or solution strategies. For each sketch, list the major steps or milestones. Then, for the most promising sketch, formulate the key lemmas or auxiliary questions we would need to answer to make it work."

**Phase 3: Step-by-Step Execution**
**Goal:** Meticulously execute one of the chosen strategies, ensuring each step is logically sound.

* **3.1. Single Step Execution**
  * **Task:** Execute only the next logical step in the plan.
  * **Rationale:** This is the core of the loop. It prevents the model from rushing ahead and making unverified logical jumps.
  * **Prompt Example:** "We are pursuing proof sketch A. Our last established fact is [insert last fact]. The next step in our plan is to [insert next goal from sketch]. Execute this single step. State the new conclusion and the justification for it."

* **3.2. Formal Justification**
  * **Task:** Force the model to be explicit about the 'why' behind every step.
  * **Rationale:** Enforces rigor and makes the argument verifiable.
  * **Prompt Example:** "You just stated that '$A \implies B$'. Justify this step by citing the specific axiom, definition, theorem, or previously established lemma that makes this deduction valid."

* **3.3. Maintaining State**
  * **Task:** At intervals, ask the model to summarize the current state of the proof.
  * **Rationale:** The context window is finite. This prompt re-establishes the core facts, preventing the model from forgetting earlier parts of the argument.
  * **Prompt Example:** "Let's pause and summarize. Please provide a structured summary of our progress:
        1.  **Initial Hypothesis:** [State it]
        2.  **Goal:** [State it]
        3.  **Established Facts/Lemmas:** [List all proven intermediate steps]
        4.  **Current Sub-Goal:** [What is the immediate next thing we are trying to prove?]"

**Phase 4: Verification & Critical Analysis**
**Goal:** Actively try to break the current line of reasoning to find flaws before proceeding too far.

* **4.1. The Skeptic's Hat**
  * **Task:** Instruct the model to take on an adversarial role.
  * **Rationale:** A powerful way to uncover hidden assumptions or logical fallacies.
  * **Prompt Example:** "Now, act as a skeptical mathematician reviewing our work so far. Critically analyze the argument from [Fact X] to [Fact Y]. Are there any gaps? Ambiguities? Unstated assumptions? Try to formulate a counterexample to our latest claim."

* **4.2. Sanity Checks and Edge Cases**
  * **Task:** Test the latest conclusions against the simple cases identified in Phase 2.
  * **Rationale:** If an intermediate result doesn't hold for a simple case, the general argument is flawed.
  * **Prompt Example:** "Let's check our most recent result: [State the result]. Does this hold for the simple case where $n=1$? Does it make sense intuitively?"

**Phase 5: Metacognition & Loop Control**
**Goal:** Assess the overall progress and make executive decisions about the path forward.

* **5.1. Progress Analysis (Your Prompt)**
  * **Task:** Evaluate the fruitfulness of the current path.
  * **Rationale:** Decides whether to continue, backtrack, or switch strategies.
  * **Prompt Example:** "Let's assess our progress.
        1.  How much closer are we to the final conclusion compared to 5 steps ago?
        2.  Is the current path becoming overly complex or yielding diminishing returns?
        3.  On a scale of 1-10, how promising does this strategy still seem?"

* **5.2. Identifying Bottlenecks**
  * **Task:** Pinpoint the exact reason for being stuck.
  * **Rationale:** A clear problem definition is the first step to solving it. "I'm stuck" is not useful; "I'm stuck because I can't prove that this function is continuous" is.
  * **Prompt Example:** "We seem to be stuck. What is the single biggest obstacle preventing us from reaching the next step in our proof sketch? Frame it as a precise, self-contained mathematical question."

* **5.3. Strategy Pivot**
  * **Task:** Explicitly command a change in strategy.
  * **Rationale:** This is the "backtracking" step in the search algorithm.
  * **Prompt Example:** "This approach seems to have led to a dead end. Let's discard the last N steps and return to our strategy list from Phase 2. Let's now attempt to develop Proof Sketch B. What is the first step of that plan?"

### **Task: Formulate Questions to Overcome Blocks**

This task is a cornerstone of **Phase 5: Metacognition & Loop Control**. When the loop detects a stall (i.e., progress is minimal over several steps), invoking this task is the critical first step to getting "unstuck" 🧠. It transforms a vague "I'm stuck" into a precise, actionable set of questions.

#### **Guidelines & Prompts**

**Goal:** To convert a state of impasse into a set of well-defined sub-problems, research queries, or new strategic directions.

1. **Obstacle Framing: The "Killer" Question**

   * **Rationale:** The most important step in solving a problem is defining it. This prompt forces the model to articulate the *exact* barrier.
   * **Prompt Example (given a bottleneck):**
       > "We are stuck trying to prove [the immediate sub-goal]. Our current approach has failed. Convert this specific obstacle into a single, precise, self-contained mathematical question. This 'killer question' should be such that if we could answer it, we would be immediately unstuck. For example: 'Is the intersection of any two elements from set $S$ also in $S$?'"

2. **Exploratory Questions: The "What If" Scenarios**

   * **Rationale:** When a direct path is blocked, you need to explore the surrounding terrain. These questions generate alternative paths by changing the problem's parameters. This is a direct follow-up to the simplification work in Phase 2.
   * **Prompt Example:**
       > "Our main strategy is stalled. Let's brainstorm new avenues by asking exploratory questions. Formulate three 'what if' questions based on what we've learned so far. Each question should propose a modification to the problem to see if it becomes more tractable. For example:
       > 1. **Simplification:** 'What if we assumed the matrix A was diagonalizable? Could we solve that case?'
       > 2. **Analogy:** 'Is there a similar problem in graph theory that might offer an analogy for our topological problem?'
       > 3. **Exaggeration:** 'What happens to our expression if we let the parameter $n$ go to infinity? Does it reveal any useful asymptotic behavior?'"

3. **Tool-Finding Questions: The "How To" Queries**

   * **Rationale:** You don't need to re-derive all of mathematics. Often, the obstacle is a sub-problem that has a standard name and a standard set of tools to solve it. This prompt formats the obstacle into a query for an external knowledge base (or a more powerful model).
   * **Prompt Example:**
       > "Our current sub-problem is to [show that a given sequence is bounded]. This seems like a standard task. Formulate a question designed to find the right mathematical tool for this job. The question should be structured like a query to a math expert or a search engine. For example:
       > * 'What are the common techniques for proving that a recursively defined sequence is bounded?'
     * 'I am looking for a theorem that connects the convergence of a series with the properties of its Fourier coefficients. What are the key results in this area?'"

### **Putting It All Together: The Loop's Logic**

Your controlling program would orchestrate these prompts. A simplified flow would be:

1. **Start:** Run tasks from **Phase 1** to fully understand the problem.
2. **Strategize:** Run tasks from **Phase 2** to generate multiple plans (A, B, C...).
3. **Select & Execute:**
    * Choose Plan A.
    * Enter a sub-loop:
        * Use **Phase 3** prompts to advance one step.
        * Periodically, use **Phase 4** prompts to check for errors.
        * If an error is found, backtrack and fix it.
4. **Evaluate:** After a set number of steps (or if progress stalls), run **Phase 5** prompts.
    * If the path is promising, go back to step 3.
    * If the path is a dead end, go back to step 2, select Plan B, and start again.
5. **Synthesize:** Once a proof sketch is fully executed and verified, run a final prompt to write up the complete, coherent proof from the successful steps.

This structured approach transforms the LLM from a fallible "answer machine" into a powerful, verifiable "reasoning engine" that you can guide and collaborate with to solve truly difficult problems.

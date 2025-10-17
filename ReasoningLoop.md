# A Framework for a Mathematical Reasoning Loop

## List of Tasks

A task has a prompt template and generally an output schema. These are grouped by the phases.

* **Source Material Analysis**
  * Listing theorems with structure
  * Structural Mapping: Connecting Hypothesis to Conclusion
  * Hypothesis Stress-Testing: The Art of Breaking Things
  * Generalization & Boundary Probing: Pushing the Limits
  * Core Idea Extraction: Finding the "Aha!" Moment

* **Problem Deconstruction & Formalization**
  * Structured Analysis
  * Definition Expansion
  * Rephrasing and Intuition

* **Strategy & Plan Generation**
  * Forward reasoning
  * Backward reasoning
  * Technique Brainstorming
  * Simplification & Specialization
  * Proof Sketch & Auxiliary Questions

* **Step-by-step Execution**
  * Single step execution
  * Formal Justification
  * Maintaining State (Summarization)

* **Verification & Critical Analysis**
  * The Skeptic's Hat
  * Sanity Checks and Edge Cases

* **Meta-cognition and loop control**
  * Progress Analysis
  * Identifying Bottlenecks
  * Strategy Pivot
  * Shifting the goalposts.

## Implementation

* This is straightforward, using recursion to loop and to branch.
* We have probabilities for triggering expensive tasks, with branches having reduced probabilities.
* The "study source material" is optionally phase 0. One option is to ask for source materials, with the option of skipping.
* There is also **Phase -1** just solve.
* A little work is needed for the interface.

## The loop

The process of solving a hard math problem can be broken down into five (plus 1) key phases. Your loop should be able to invoke tasks from any phase based on the current state of the solution.

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

The following is a JSON format for proofs, which we call `ProofJSON`. This format also applies to attempted proofs with errors.

Each JSON object has a "type" field. The possible values for this field are: "define", "assert", "theorem", "problem", "assume", "let", "proof", "cases", "induction", "case", "conclude", "remark". An object can also have a "name" field, which is a string, to be used for reference (for instance it may be the name of a theorem). Use LaTeX when appropriate with formulas enclosed in `$`. The different types of objects and their additional fields are as follows:

* **Let**: For a statement introducing a new variable with given value, type and/or property.
  * Additional fields 
    * **Variable**: the variable being defined (use `<anonymous>` if there is no name, such as `We have a group structure on S`).
    * **Value**: (optional) the value being assigned to the variable.
    * **Kind**: (optional) the type of the variable, such as `real number`, `function from S to T`, `element of G` etc.
    * **Property**: (optional) specific properties of the variable beyond the kind.
* **Assume**: A mathematical assumption being made. In case this is a variable or structure being introduced, use a **let** statement.
  * Additional fields: 
    * **Statement**: the mathematical assumption.
* **Define**: A mathematical definition.
  * Additional fields: 
    * **Statement**: the mathematical definition.
    * **Term**: the term being defined.
* **Assert**: A mathematical statement whose proof is a straightforward consequence of given results following some method.
  * Additional fields: 
    * **Claim**: the mathematical claim being asserted, NOT INCLUDING proofs, justifications or results used. The claim should be purely a logical statement which is the *consequence* obtained.
    * **Deduced_from**: (optional) a JSON object with two (optional) subfields:
      * **From_context**: a JSON list of statements previously proved.
      * **Known_results**: a JSON list of known mathematical results used in the proof.
    * **Proof-method**: (optional) the method of proof for the claim; this should be a single phrase or a fairly simple sentence; if a longer justification is needed break the step into smaller steps. If the method is deduction from a result, use the **deduced_from** field.
    * **Calculation**: (optional) a JSON list of calculation steps, with each step either a JSON string (for an equality, inequality etc) or a JSON object with two fields, **step** (the step) and **justification** (the justification for the step).
    * **Missing**: (optional) a JSON list of **problem** fields which are problems that need to be solved or results that need to be proved to complete the proof. Standard results/criteria may be omitted from the proof: include them in the **deduced_from** field.
    * **Errors**: a list of errors in the proof. Report only actual errors, with missing steps reported in the **missing** field.
* **Theorem**: The statement of a mathematical theorem, lemma or claim.
  * Additional fields: 
    * **Hypothesis**: a JSON list of data and assumptions, **let** and **assume** statements.
    * **Conclusion**: the mathematical theorem as a consequence of the assumptions.
    * **Status**: one of "stated", "recalled", "proved earlier", "proved", "proved later", "wrong statement", "wrong proof" and "incomplete proof".
    * Depending on the status, at most one of:
      * **Proof**: the proof, if the status is "proved".
      * **Ref**: reference to earlier proof, if the status is "proved earlier" or "proved later".
      * **Cite**: reference to literature or external sources, if the status is "recalled"; for well known results, this is omitted.
      * **Missing**: a JSON list of **problem** fields which are problems that need to be solved or results that need to be proved to complete the proof, if the status is "incomplete proof". Standard results/criteria may be omitted from the proof.  
      * **Errors**: the errors in the proof, if the status is "wrong proof". Report only actual errors, with missing steps reported in the **missing** field.
* **Problem**: A mathematical problem that is not a theorem, such as "Find ..."
  * Additional fields: 
    * **Statement**: the problem statement.
    * **Solved**: Boolean field whether the solution is given.
    * **Answer**: (optional) If the "solved" field is true, the answer to the problem (without justification).
    * **Proof**: (optional) If the "solved" field is true, a `ProofJSON` block giving a proof that the answer is correct.
    * **Missing**: (optional) a JSON list of **problem** fields which are problems that need to be solved or results that need to be proved to complete the proof. Standard results/criteria may be omitted from the proof.
    * **Errors**: a list of errors in the proof. Report only actual errors, with missing steps reported in the **missing** field.
* **Proof**: A proof of a theorem, lemma or claim.
  * Additional fields: 
    * **Steps**: a JSON list of steps in the proof.
* **Case**: A case in a proof.
  * Additional fields: 
    * **Condition**: the case statement.
    * **Proof**: a `ProofJSON` block. 
* **Induction**: A proof by induction.
  * Additional fields: 
    * **On**: the variable on which induction is being done.
    * **Proof-cases**: a JSON list of cases in the induction, which are all objects of type **case**.
* **Cases**: A case split in a proof.
  * Additional fields: 
    * **On**: the variable, condition or property on which the case split is being done.
    * **Split-kind**: one of "match" (for pattern matching), "condition" (if based on a condition being true or false) and "groups" (for more complex cases).
    * **Exhaustiveness**: (optional) Proof that the case split is exhaustive for complex splits. 
    * **Proof-cases**: a JSON list of cases in the case split, which are all objects of type **case**.
* **Contradiction**: A proof by contradiction.
  * Additional fields: 
    * **Assumption**: the assumption being made to contradict.
    * **Proof**: a JSON block proving the negation of the assumption.
* **Conclude**: A conclusion in a proof, typically the last statement in a proof block.
  * Additional fields: 
    * **Statement**: the conclusion.
    * **Missing**: a JSON list of **problem** fields which are problems that need to be solved or results that need to be proved to complete the proof, if the status is "incomplete proof". Standard results/criteria may be omitted from the proof.  
    * **Errors**: (optional) an error in the proof so that the conclusion is not justified. Report only actual errors, with missing steps reported in the **missing** field.
* **Remark**: A remark or comment that is NOT MATHEMATICAL, instead being for motivation, attention, sectioning etc.
  * Additional fields: 
    * **Statement**: the remark or comment.

Rewrite the following theorem and proof into `ProofJSON` format. Note that the proof may not be complete and may have some errors, which you should note in the appropriate fields. Output JSON only. The theorem and proof are as follows:

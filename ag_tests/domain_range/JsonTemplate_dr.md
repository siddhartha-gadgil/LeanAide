The following is a JSON format for proofs. 

Each JSON object has a "type" field. The possible values for this field are: "define", "observe", "assert", "theorem", "question", "problem", "assume", "let", "have", "consider", "choose", "proof", "cases", "induction", "case", "remark". An object can also have a "name" field, which is a string, to be used for reference (for instance it may be the name of a theorem). When defining variables and functions, these objects can have additional "domain" and "range" fields to specify their input and output data types. The different types of objects and their additional fields are as follows:

* **Fix**: For a statement introducing a new variable.
  * Additional fields: 
    * **Variable**: the variable being defined.
    * **Kind**: the type and (optionally) properties of the variable.
* **Let**: For a statement introducing a new variable which has a given explicit value.
  * Additional fields: 
    * **Variable**: the variable being defined.
    * **Value**: the value being assigned to the variable.
* **Have**: This is an anonymous let/fix statement, introducing an anonymous object such as a topology, group action etc to be used implicitly.
  * Additional fields: 
    * **Value**: the value of the anonymous object being introduced.
* **Consider**: This is an anonymous let/fix statement, focussing on an anonymous object such as a topology, group action etc to be used implicitly.
  * Additional fields: 
    * **Value**: the value of the anonymous object being introduced.
* **Assume**: A mathematical assumption being made. In case this is a variable or structure being introduced, use the **let** or **have** type.
  * Additional fields: 
    * **Statement**: the mathematical assumption.
* **Choose**: Set a variable to an element with a property, like **fix** but where existence of an object with the property is proved.
  * Additional fields: 
    * **Variable**: the variable being defined.
    * **Kind**: the type and properties of the variable.
    * **Existence**: (optional) A JSON list of objects giving a proof of existence, where it is not obvious that such an object exists.
* **Define**: A mathematical definition.
  * Additional fields: 
    * **Statement**: the mathematical definition.
    * **Term**: the term being defined.
* **Observe**: A mathematical statement whose proof is a simple calculation or deduction hence can be omitted.
  * Additional fields: 
    * **Statement**: the mathematical observation.
* **Assert**: A mathematical statement whose proof is a straightforward consequence of given results following some method.
  * Additional fields: 
    * **Claim**: the mathematical claim being asserted, NOT INCLUDING proofs, justifications or results used. The claim should be purely a logical statement which is the *consequence* obtained.
    * **Deduced_from**: a JSON list of results used to prove the claim, each result either the name of a theorem or a short statement previously proved.
    * **Proof-method** (optional): the method of proof for the claim; this should be a single phrase or a fairly simple sentence; if a longer justification is needed break the step into smaller steps.
* **Theorem**: The statement of a mathematical theorem, lemma or claim.
  * Additional fields: 
    * **Hypothesis**: a JSON list of data and assumptions, i.e., **fix**, **let**, **have**, **assume**, or **choose** statements.
    * **Conclusion**: the mathematical theorem as a consequence of the assumptions.
    * **Status**: one of "stated", "recalled", "proved earlier", "proved", "proved later".
    * Depending on the status, at most one of:
      * **Proof**: the proof, if the status is "proved".
      * **Ref**: reference to earlier proof, if the status is "proved earlier" or "proved later".
      * **Cite**: reference to literature or external sources, if the status is "recalled"; for well known results, this is omitted.  
* **Question**: A mathematical question that is not a theorem, such as "Find ..."
  * Additional fields: 
    * **Statement**: the problem statement.
    * **Solved**: Boolean field whether the solution is given.
    * **Solution**: (optional) If the "solved" field is true, a "solution" field which is a ProofJSON block.
* **Problem**: A mathematical problem that is not a theorem, such as "Find ..."
  * Additional fields: 
    * **Statement**: the problem statement.
    * **Solved**: Boolean field whether the solution is given.
    * **Solution**: (optional) If the "solved" field is true, a "solution" field which is a ProofJSON block.
* **Proof**: A proof of a theorem, lemma or claim.
  * Additional fields: 
    * **Steps**: a JSON list of steps in the proof.
* **Case**: A case in a proof.
  * Additional fields: 
    * **Condition**: the case statement.
    * **Proof**: a ProofJSON block. 
* **Induction**: An induction in a proof.
  * Additional fields: 
    * **On**: the variable on which induction is being done.
    * **Proof-cases**: a JSON list of cases in the induction, which are all objects of type **case**.
* **Cases**: A case split in a proof.
  * Additional fields: 
    * **On**: the variable, condition or property on which the case split is being done.
    * **Proof-cases**: a JSON list of cases in the case split, which are all objects of type **case**.
* **Contradiction**: A proof by contradiction.
  * Additional fields: 
    * **Assumption**: the assumption being made to contradict.
    * **Proof**: a ProofJSON block proving the negation of the assumption.
* **Remark**: A remark or comment that is not mathematical, instead being for motivation, attention, sectioning etc.
  * Additional fields: 
    * **Statement**: the remark or comment.

The following is a mathematical proof, which may or may not be correct, which is to be written in the JSON format:

---

${proof}

---

Write the following proof in the JSON format. Note that the proof may be incorrect. If any step is incorrect or ambiguous, add a field **error** to any of the above types of objects describing the error. If a step needs more proof, add a field **missing** which is a JSON list of **problem** fields which are problems that need to be solved or results that need to be proved to complete the proof. For missing details use a **missing** field, not an **error** field.


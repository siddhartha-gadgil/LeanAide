# ProofJson

We represent mathematical proofs, parts of proofs and groups of statements and proofs as a JSON list of statements in a format we call `ProofJSON`.
Each statement is a JSON object with a **type** field and additional fields depending on the type. In addition, any of the objects can have a **name** field, which is a string, to be used for reference (for instance it may be the name of a theorem). Additional fields may be added in post-processing. The types and the associated fields are as follows:
* **type**: "definition". 
  * A mathematical definition.
  * The definition should be purely a definition, with consequences separated as assertions or observations.
  * Additional fields: 
    * **statement**: the mathematical definition.
    * **term**: the term being defined.
* **type**: "observation".
  * A mathematical statement whose proof is a simple calculation or deduction and can be omitted.
  * Additional fields: 
    * **statement**: the mathematical observation.
* **type**: "assertion".
  * A mathematical statement that can be deduced from the context, easily enough that it need not be stated as a theorem (or lemma). For example: `as H is a subgroup of Z/10Z, the order of H divides 10`. 
  * Additional fields: 
    * **claim**: the mathematical claim being asserted, not including justifications or what is used. In the above example, the claim is `the order of H divides 10`.
    * **deduced-from**: a JSON list of results used to prove the claim, each result either the name of a theorem or a short statement previously proved. In the above example, the list would be `H is a subgroup of Z/10Z` and `Lagrange's theorem` (which is used in the proof of the claim).
      * A member of the list can be an object with fields "result" and "applied-to" to specify to what the result is applied.
      * The "applied-to" field can also be an object if we need to specify more than one variable instantiated in the application.
    * **justification** (optional):a justification for the claim; this should be a single fairly simple sentence; if a longer justification is needed break the step into smaller steps. This can be omitted if the reduction is a logical consequence of the results in the "deduced-from" list.
  * Do not use this type for claims that will be proved later: instead use the type "theorem", "lemma" or "claim". This type is only for assertions that it is expected the reader can deduce at this point. 
* **type**: "theorem".
  * The statement of a mathematical theorem, lemma or claim.
  * We either have just a statement, or a proof may be given here, give earlier or in the literature.
  * The types "lemma", "proposition", "corollary" and "claim" can all be used for theorems in place of "theorem".
  * Additional fields: 
    * **statement**: the mathematical theorem.
    * **status**: one of "stated", "recalled", "proved earlier", "proved", "proved later".
    * Depending on the status, at most one of:
      * **proof**: the proof, if the status is "proved".
        * The proof is a ProofJSON block.
      * **ref**: reference to earlier proof, if the status is "proved earlier" or "proved later".
      * **cite**: reference to literature or external sources, if the status is "recalled"; for well known results, this is omitted.
* **type**: "question".
  * A mathematical question that is not a theorem, such as "Find ..."
  * The problem is either just stated or solved (with proof).
  * Additional fields: 
    * **statement**: the problem statement.
    * **solved**:  Boolean field whether the solution is given.
    * **soution**: (optional) If the "solved" field is true, a "solution" field which is a ProofJSON block.
* **type**: "assumption"
  * A mathematical assumption being made. In case this is a variable or structure being introduced, use the "let" type or "have" type.
  * Additional fields: 
    * **statement**: the mathematical assumption.
* **type**: "let".
  * For a statement introducing a new variable.
  * Additional fields: 
    * **variable**: the variable being defined.
    * **value**: the value being assigned to the variable.
    * If the value is not explicit, we may have proofs of existence, well-defined and uniqueness. Thus, we can have one or more additional fields:
      * **existence**: a ProofJSON block.
      * **well_defined**: a ProofJSON block.
      * **uniqueness**: a ProofJSON block.
* **type**: "have".
  * This is an anonymous let/fix statement, introducing an anonymous object such as a topology, group action etc to be used implicitly.
  * Additional fields: 
    * **value**: the anonymous object being introduced.
    * As with the let statement, we may have proofs of existence, well-defined and uniqueness given by similar additional fields.
* **type**: "choose". 
  * Set a variable to an element with a property, like let but with value not unique in general but given by a property.
  * Additional fields: 
    * **variable**: the variable being defined.
    * **property**: the property being used.
    * Optionally, we may have a proof of existence as an additional field:
      * **existence**: a ProofJSON block.
* **type**: "assumption".
  * Additional fields: 
    * **statement**: the mathematical assumption.
* **type**: "suffices".
  * Reduction of the goal to a given one. This is equivalent to an *assertion* that the new claim implies the old one.
  * Additional fields: 
    * **goal**: the mathematical goal to which the previous goal is reduced.
    * The other fields are the similar to those for an *assertion* except they correspond to *reducing* to the goal instead of justifying the claim.
    * **deduced-from**: a JSON list of results used for the reduction, each result either the name of a theorem or a short statement previously proved. 
      * A member of the list can be an object with fields "result" and "applied-to" to specify to what the result is applied.
      * The "applied-to" field can also be an object if we need to specify more than one variable instantiated in the application.
    * **justification** (optional):a justification for the reduction; this should be a single fairly simple sentence; if a longer justification is needed break the step into smaller steps. This is not needed if the reduction is a logical consequence of the results in the **deduced-from** list.
* **type**: "split_by".
  * Splitting the goal by cases.
  * Additional fields: 
    * **term** or **condition**: the term or condition based on which we split such as `n is prime` or `n`.
    * **cases**: a JSON list of case blocks.
      * Each case block is a JSON object with a *case* field and a *details* field.
        * **case**: the value, range etc for the case.
        * **content**: a ProofJSON block.
* **type**: "use".
  * Using a value for an existentially quantified variable.
  * Additional fields: 
    * **variable**: the variable being used.
    * **value**: the value to which it is set.
* **type**: "example".
  * An example of a mathematical object with some properties.
  * Additional fields: 
    * **description**: the description or definition of the example object.
    * **name**: (optional) the name of the example object.
    * **properties**: a JSON list giving the properties of the example object with proofs that it satisfies the properties.
--------

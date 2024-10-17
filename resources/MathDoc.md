
* **math_document**: A structured math document in a custom JSON format. This is a JSON list, with each element of the list is a JSON object with exactly one key-value pair, with the key one of `let`, `assume`, `def`, `assert`, `theorem`, `problem`, `cases`, `induction`, `contradiction`, `conclude`, `remark`. The descriptions for the choice of key and corresponding values are as follows:
  * **let**: A statement introducing a new variable with given value, type and/or property. This is a JSON object. The keys and corresponding values are as follows.
    * **variable**: The variable being defined (use `<anonymous>` if there is no name such as in `We have a group structure on S`) This is a JSON string.
    * **value**: (OPTIONAL) The value of the variable being defined This is a JSON string.
    * **kind**: (OPTIONAL) The type of the variable, such as `real number`, `function from S to T`, `element of G` etc. This is a JSON string.
    * **properties**: (OPTIONAL) Specific properties of the variable beyond the type. This is a JSON string.
  * **assume**: A mathematical assumption being made. In case this is a variable or structure being introduced, use a **let** statement. This is a JSON string.
  * **def**: A mathematical definition of a term. This is a JSON object. The keys and corresponding values are as follows.
    * **statement**: The mathematical definition. This is a JSON string.
    * **term**: The term being defined. This is a JSON string.
  * **assert**: A mathematical statement whose proof is a straightforward consequence of given and known results following some method. This is a JSON object. The keys and corresponding values are as follows.
    * **claim**: The mathematical claim being asserted, NOT INCLUDING proofs, justifications or results used. The claim should be purely a logical statement which is the *consequence* obtained. This is a JSON string.
    * **proof_method**: (OPTIONAL) The method used to prove the claim. This could be a direct proof, proof by contradiction, proof by induction, etc. this should be a single phrase or a fairly simple sentence; if a longer justification is needed break the step into smaller steps. If the method is deduction from a result, use the 'deduced_using' field This is a JSON string.
    * **deductions**: (OPTIONAL) A list of elements of type `deduction`. Each element of type `deduction` is as follows
      * **deduction**: A deduction of a mathematical result from assumptions or previously known results. This is a JSON object. The keys and corresponding values are as follows.
        * **deduced_from**: The assumptions or previously known results from which the deduction is made. This is a JSON string.
        * **in_context**: Whether the statement from which deduction is made is in the current context. Answer `true` or `false` (answer `false` if a result from the mathematical literature is being invoked). This is a JSON boolean.
        * **instantiations**: (OPTIONAL) A list of elements of type `instantiation`. Each element of type `instantiation` is as follows
          * **instantiation**: The instantiation of the assumption or previously known result to which the result is applied. For example,  `42` if we apply uniqueness of prime factorisation to `42`. This is a JSON string.
    * **calculation**: (OPTIONAL) A list of elements of type `calculation`. Each element of type `calculation` is as follows
      * **calculation**: A step in a calculation or computation. This is a JSON object. The keys and corresponding values are as follows.
        * **calculation**: A series of calculations or computations.
          * **inline**: A simple calculation or computation written as a single line. This is a JSON string.
          * **step**: A step, typically an equality or inequality, in a calculation or computation. This is a JSON string.
          * **continuation**: A continuation of a chain of equalities/inequalities, for example `= x + 3`. Should begin with an operator such as `=` or `≤` and be followed by a term. This is a JSON string.
        * **justification**: (OPTIONAL) The justification for the step in a calculation or computation. This is a JSON string.
    * **missing**: (OPTIONAL) A list of elements of type `missing`. Each element of type `missing` is as follows
      * **missing**: A  problem that need to be solved or results that need to be proved to complete the proof. Standard results/criteria may be omitted from the proof: include them in the 'deduced_from' field. This is a JSON string.
    * **errors**: (OPTIONAL) A list of elements of type `error`. Each element of type `error` is as follows
      * **error**: An error in a proof or calculation. Report only actual errors, with missing steps reported in the 'missing' field. This is a JSON string.
  * **theorem**: A mathematical theorem, with a list of hypotheses and a conclusion. This is a JSON object. The keys and corresponding values are as follows.
    * **hypothesis**: a JSON list of data and assumptions, i.e., **let** and **assume** statements This is a JSON list, with each element of the list is a JSON object with exactly one key-value pair, with the key one of `let`, `assume`.
    * **conclusion**: The conclusion of the theorem. This is a JSON string.
    * **proved**: Whether the theorem has been proved, either here or earlier or by citing the literature. This is a JSON boolean.
    * **proof**: (OPTIONAL) A proof of a lemma, theorem or claim, having the same structure as a `math_document`. This is a JSON list, with each element of the list is a JSON object with exactly one key-value pair, with the key one of `let`, `assume`, `def`, `assert`, `theorem`, `problem`, `cases`, `induction`, `contradiction`, `conclude`, `remark`.
    * **ref**: (OPTIONAL) A reference where the result has been previously proved. This is a JSON string.
    * **cite**: (OPTIONAL) A citation of a result from the mathematical literature which gives the proof. This is a JSON string.
    * **missing**: (OPTIONAL) A list of elements of type `missing`. Each element of type `missing` is as follows
      * **missing**: A  problem that need to be solved or results that need to be proved to complete the proof. Standard results/criteria may be omitted from the proof: include them in the 'deduced_from' field. This is a JSON string.
    * **errors**: (OPTIONAL) A list of elements of type `error`. Each element of type `error` is as follows
      * **error**: An error in a proof or calculation. Report only actual errors, with missing steps reported in the 'missing' field. This is a JSON string.
  * **problem**: A mathematical problem, with a statement and an answer. This is a JSON object. The keys and corresponding values are as follows.
    * **statement**: The statement of the problem. This is a JSON string.
    * **solved**: Whether the problem has been solved. This is a JSON boolean.
    * **answer**: (OPTIONAL) The answer to the problem. This is a JSON string.
    * **proof**: (OPTIONAL) A proof of a lemma, theorem or claim, having the same structure as a `math_document`. This is a JSON list, with each element of the list is a JSON object with exactly one key-value pair, with the key one of `let`, `assume`, `def`, `assert`, `theorem`, `problem`, `cases`, `induction`, `contradiction`, `conclude`, `remark`.
    * **missing**: (OPTIONAL) A list of elements of type `missing`. Each element of type `missing` is as follows
      * **missing**: A  problem that need to be solved or results that need to be proved to complete the proof. Standard results/criteria may be omitted from the proof: include them in the 'deduced_from' field. This is a JSON string.
    * **errors**: (OPTIONAL) A list of elements of type `error`. Each element of type `error` is as follows
      * **error**: An error in a proof or calculation. Report only actual errors, with missing steps reported in the 'missing' field. This is a JSON string.
  * **cases**: A proof by cases or proof by induction, with a list of cases. This is a JSON object. The keys and corresponding values are as follows.
    * **on**: The variable or expression on which the cases are being done. This is a JSON string.
    * **split_kind**: one of 'match' (for pattern matching), 'condition' (if based on a condition being true or false) and 'groups' (for more complex cases)
    * **proof_cases**: A list of elements of type `case`. Each element of type `case` is as follows
      * **case**: A case in a proof by cases or proof by induction. This is a JSON object. The keys and corresponding values are as follows.
        * **condition**: The case condition or pattern; for induction one of 'base' or 'induction-step' This is a JSON string.
        * **proof**: A proof of a lemma, theorem or claim, having the same structure as a `math_document`. This is a JSON list, with each element of the list is a JSON object with exactly one key-value pair, with the key one of `let`, `assume`, `def`, `assert`, `theorem`, `problem`, `cases`, `induction`, `contradiction`, `conclude`, `remark`.
        * **missing**: (OPTIONAL) A list of elements of type `missing`. Each element of type `missing` is as follows
          * **missing**: A  problem that need to be solved or results that need to be proved to complete the proof. Standard results/criteria may be omitted from the proof: include them in the 'deduced_from' field. This is a JSON string.
        * **errors**: (OPTIONAL) A list of elements of type `error`. Each element of type `error` is as follows
          * **error**: An error in a proof or calculation. Report only actual errors, with missing steps reported in the 'missing' field. This is a JSON string.
    * **exhaustiveness**: (OPTIONAL) Proof that the cases are exhaustive. This is a JSON list, with each element of the list is a JSON object with exactly one key-value pair, with the key one of `let`, `assume`, `def`, `assert`, `theorem`, `problem`, `cases`, `induction`, `contradiction`, `conclude`, `remark`.
    * **missing**: (OPTIONAL) A list of elements of type `missing`. Each element of type `missing` is as follows
      * **missing**: A  problem that need to be solved or results that need to be proved to complete the proof. Standard results/criteria may be omitted from the proof: include them in the 'deduced_from' field. This is a JSON string.
    * **errors**: (OPTIONAL) A list of elements of type `error`. Each element of type `error` is as follows
      * **error**: An error in a proof or calculation. Report only actual errors, with missing steps reported in the 'missing' field. This is a JSON string.
  * **induction**: A proof by induction, with a base case and an induction step. This is a JSON object. The keys and corresponding values are as follows.
    * **on**: The variable or expression on which induction is being done. This is a JSON string.
    * **proof_cases**: A list of elements of type `case`. Each element of type `case` is as follows
      * **case**: A case in a proof by cases or proof by induction. This is a JSON object. The keys and corresponding values are as follows.
        * **condition**: The case condition or pattern; for induction one of 'base' or 'induction-step' This is a JSON string.
        * **proof**: A proof of a lemma, theorem or claim, having the same structure as a `math_document`. This is a JSON list, with each element of the list is a JSON object with exactly one key-value pair, with the key one of `let`, `assume`, `def`, `assert`, `theorem`, `problem`, `cases`, `induction`, `contradiction`, `conclude`, `remark`.
        * **missing**: (OPTIONAL) A list of elements of type `missing`. Each element of type `missing` is as follows
          * **missing**: A  problem that need to be solved or results that need to be proved to complete the proof. Standard results/criteria may be omitted from the proof: include them in the 'deduced_from' field. This is a JSON string.
        * **errors**: (OPTIONAL) A list of elements of type `error`. Each element of type `error` is as follows
          * **error**: An error in a proof or calculation. Report only actual errors, with missing steps reported in the 'missing' field. This is a JSON string.
    * **missing**: (OPTIONAL) A list of elements of type `missing`. Each element of type `missing` is as follows
      * **missing**: A  problem that need to be solved or results that need to be proved to complete the proof. Standard results/criteria may be omitted from the proof: include them in the 'deduced_from' field. This is a JSON string.
    * **errors**: (OPTIONAL) A list of elements of type `error`. Each element of type `error` is as follows
      * **error**: An error in a proof or calculation. Report only actual errors, with missing steps reported in the 'missing' field. This is a JSON string.
  * **contradiction**: A proof by contradiction, with an assumption and a proof of the contradiction. This is a JSON object. The keys and corresponding values are as follows.
    * **assumption**: The assumption being made to be contradicted. This is a JSON string.
    * **proof**: The proof of the contradiction given the assumption. This is a JSON list, with each element of the list is a JSON object with exactly one key-value pair, with the key one of `let`, `assume`, `def`, `assert`, `theorem`, `problem`, `cases`, `induction`, `contradiction`, `conclude`, `remark`.
    * **missing**: (OPTIONAL) A list of elements of type `missing`. Each element of type `missing` is as follows
      * **missing**: A  problem that need to be solved or results that need to be proved to complete the proof. Standard results/criteria may be omitted from the proof: include them in the 'deduced_from' field. This is a JSON string.
    * **errors**: (OPTIONAL) A list of elements of type `error`. Each element of type `error` is as follows
      * **error**: An error in a proof or calculation. Report only actual errors, with missing steps reported in the 'missing' field. This is a JSON string.
  * **conclude**: Conclude a claim obtained from the steps so far. This is typically the final statement of a proof giving the conclusion of the theorem. This is a JSON object. The keys and corresponding values are as follows.
    * **claim**: The conclusion of the proof. This is a JSON string.
    * **missing**: (OPTIONAL) A list of elements of type `missing`. Each element of type `missing` is as follows
      * **missing**: A  problem that need to be solved or results that need to be proved to complete the proof. Standard results/criteria may be omitted from the proof: include them in the 'deduced_from' field. This is a JSON string.
    * **errors**: (OPTIONAL) A list of elements of type `error`. Each element of type `error` is as follows
      * **error**: An error in a proof or calculation. Report only actual errors, with missing steps reported in the 'missing' field. This is a JSON string.
  * **remark**: A remark or comment that is NOT MATHEMATICAL, instead being for motivation, attention, sectioning etc. This is a JSON string.
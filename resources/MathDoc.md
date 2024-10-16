## Structure

* We have a labelled JSON-like tree structure for the proof.
* This means we have fields/elements that can be
  * Leaves of different kinds: *String*, *Bool*, *Num* or *Enumeration*.
  * Lists of elements of the same kind or of a group of kinds.
  * Nodes, with fields that can be of different kinds.
    * Fields can be lists and/or optional.
* Each node has a description.
* Enumerations, such as status of proof, are ideally separately specified.
* We refer by name, to allow forward references.
  * A function should check for missing references.
* We can have at most one of a collection of fields (e.g., for a theorem either a proof or a ref). This may depend on other fields.
* To disambiguate, we can use composite names with only the back being referred to in the prompt.
* We can attempt a variant with a single field instead of a type.

### Examples/Remarks

* A document is a list of *blocks*. What is a block is not specfied in advance.
* A `let` statement has an optional list of properties.
* Justifications is an open class, which may have more kinds added.
* `deduced_from` may also have an optional `applied_to` field.
  * `deduced_from` can be split into two groups: `from_context` and `known_results`.
* Error fields may be added at specific nodes.
* Should have an `end_of_source` field to indicate the end of the document.
* The current nesting of steps within proofs is unnecessary.
  * A proof should just be a document.
  * There is also inconsistency in how these are described.
* There is redundancy in the `remark` block having just a statement.
  * We do want a separate type.
  * We can uniformly use the term `content` for different types of strings.
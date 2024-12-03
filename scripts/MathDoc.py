class MathDocTree:
    def __init__(self,
                 name: str,
                 text: str = "",
                 children: list = [],
                 key_value_str: list = [],
                 optional: bool = False,
                 give_json: str = "",
                 post_text: str = ""):
        """Initialise a node in the MathDocTree."""
        self.name = name
        self.desc = text
        self.children = []
        self.optional = optional
        self.give_json = give_json
        self.key_value_str = key_value_str
        self.post_text = post_text
        for child in children:
            self.create_child(child)

    def create_child(self, name_or_node, text: str = ""):
        """Create a new child or assign an existing node as a child."""
        if isinstance(name_or_node, MathDocTree):
            # If the input is an existing node, add it as a child
            child = name_or_node
        else:
            # Otherwise, create a new node
            child = MathDocTree(name_or_node, text)
        self.children.append(child)
        return child

    def add_existing_child(self, existing_child):
        """Add an existing node as a child to this node."""
        self.children.append(existing_child)

    def get_child_names(self):
        """Return a list of names of all children of the current node."""
        return [child.name for child in self.children]


    def _to_markdown(self, depth=0):
        """Helper function to generate Markdown with proper indentation."""

        def key_value_pair_txt(keys: list) -> str:
            if keys == []:
                return ""
            return " with each element of the list is a JSON object with exactly one _key-value pair_, with the _key_ one of " + ", ".join([f"`{key}`" for key in keys]) + "."

        # Children are indented by 2 spaces * depth
        indent = " " * 2 * depth
        optional_text = " (OPTIONAL)" if self.optional else ""
        post_text = f" {self.post_text}" if self.post_text != "" else ""
        give_json_text = f" Give a JSON {self.give_json}" if self.give_json else ""
        key_value_pair_str = key_value_pair_txt(self.key_value_str) 
        if key_value_pair_str == "": 
            punct = "."
        else:
            punct = ","
        # name is bolded
        line = f"{indent}- **{self.name}**:{optional_text} {self.desc}{give_json_text}{punct}{key_value_pair_str}{post_text}"
        lines = [line]

        for child in self.children:
            lines.extend(child._to_markdown(depth + 1))
        return lines

    def to_markdown(self):
        """Generate Markdown representation of the tree."""
        return "\n".join(self._to_markdown())

def node_sequence_txt(node_name: str) -> str:
    return f"A list of elements of type `{node_name}`. Each element of type `{node_name}` is as follows:"

md_blobnames = ["let", "some", "assume", "def", "assert", "theorem", "problem", "cases", "induction", "contradiction", "calculate", "conclude", "remark"]
subkeys_posttext = "The keys and corresponding values are as follows."

root_child = []

var = MathDocTree("variable", "The variable being defined (use `<anonymous>` if there is no name such as in `We have a group structure on S`)", give_json = "string")
value = MathDocTree("value", "The value of the variable being defined", optional = True, give_json = "string")
kind = MathDocTree("kind", "The type of the variable, such as `real number`, `function from S to T`, `element of G` etc.", optional = True, give_json = "string")
properties = MathDocTree("properties", "Specific properties of the variable beyond the type.", optional = True, give_json = "string")

## Let 
let_children = [var, value, kind, properties]
let = MathDocTree("let", "A statement introducing a new variable with given value, type and/or property. For saying that **some** value of the variable is as needed, use a 'some' statement.", children = let_children, give_json = "object", post_text= subkeys_posttext)
root_child.append(let)

## Some
some = MathDocTree("some", "A statement introducing a new variable and saying that **some** value of this variable is as required (i.e., an existence statement). This is possibly with given type and/or property. This corresponds to statements like 'for some integer `n` ...' or 'There exists an integer `n` ....'.", children = [var, kind, properties], give_json = "object", post_text= subkeys_posttext)
root_child.append(some)

## Assume
assume = MathDocTree("assume", "A mathematical assumption being made. In case this is a variable or structure being introduced, use a 'let' statement.", give_json = "string")
root_child.append(assume)

## Define
statement = MathDocTree("statement", "The mathematical definition.", give_json="string")
term = MathDocTree("term", "The term being defined.", give_json="string")
name_field = MathDocTree("name", "The name of the theorem, lemma or claim.", optional = True, give_json="string")

define = MathDocTree("def", "A mathematical term being defined. In case a definition is being used, use 'assert' or 'theorem' instead.", [statement, term, name_field], give_json = "object", post_text= subkeys_posttext)
root_child.append(define)

## Assert

claim = MathDocTree("claim", "The mathematical claim being asserted, NOT INCLUDING proofs, justifications or results used. The claim should be purely a logical statement which is the *consequence* obtained.", give_json="string")
proof_method = MathDocTree("proof_method", "The method used to prove the claim. This could be a direct proof, proof by contradiction, proof by induction, etc. this should be a single phrase or a fairly simple sentence; if a longer justification is needed break the step into smaller steps. If the method is deduction from a result, use the 'deduced_using' field.", optional = True, give_json="string")


instantiation = MathDocTree("instantiation", "Specific numbers, functions etc to which a known result is applied. For example, if we apply uniqueness of prime factorisation to `42` write `{'result_used' : 'uniqueness of prime factorization', 'instantiation': '42'}`.")

### Deduced Using

result_used = MathDocTree("result_used", "An assumption or previously known results from which the deduction is made. If more than one result is used, list them in the 'deductions' field as separate `deduction` objects. If the result used needs justification, have a separate `assert` object earlier.", give_json="string")
in_context = MathDocTree("proved_earlier", "Whether the statement from which deduction has been proved earlier IN THIS DOCUMENT. Answer `true` or `false` (answer `false` if a result from the mathematical literature is being invoked).", give_json="boolean")

deduced_from= MathDocTree("deduced_from", "A deduction of a mathematical result from assumptions or previously known results.", [result_used, in_context], give_json = "object", post_text= subkeys_posttext)

deduced_from_results = MathDocTree("deduced_from_results", node_sequence_txt("deduced_from"), [deduced_from], optional = True)

### Calculate

inline = MathDocTree("inline_calculation", "A simple calculation or computation written as a single line.", give_json="string")
calculation_step = MathDocTree("calculation_step", "A step, typically an equality or inequality, in a calculation or computation.", give_json="string")
calculation_sequence = MathDocTree("calculation_sequence", node_sequence_txt("calculation_step"), [calculation_step]) 

calculate = MathDocTree("calculate", "An equation, inequality, short calculation etc.", [inline, calculation_sequence], optional = True, give_json="object", key_value_str=["inline_calculation", "calculation_sequence"])

### Missing Proofs
missing = MathDocTree("missing", "A  problem that need to be solved or results that need to be proved to complete the proof. Standard results/criteria may be omitted from the proof: include them in the 'deduced_from' field.", give_json="string")
missing_proofs = MathDocTree("missing_proofs", node_sequence_txt("missing"), [missing], optional=True)

### Errors
error = MathDocTree("error", "An error in a proof or calculation. Report only actual errors, with missing steps reported in the 'missing' field.", give_json = "string")
errors = MathDocTree("errors", node_sequence_txt("error"), children = [error], optional=True)

assert_children = [claim, proof_method, deduced_from_results, calculate, missing_proofs, errors]

assert_type = MathDocTree("assert", "A mathematical statement whose proof is a straightforward consequence of given and known results following some method.", assert_children, give_json = "object", post_text= subkeys_posttext) 
root_child.append(assert_type)

## Theorem

hypothesis = MathDocTree("hypothesis", "a JSON list of data and assumptions, i.e., **let** and **assume** statements.", give_json = "list", key_value_str=["let", "some", "assume"])

conclusion = MathDocTree("conclusion", "The conclusion of the theorem.", give_json="string")
proved = MathDocTree("proved", "Whether the theorem has been proved, either here or earlier or by citing the literature.", give_json="boolean")

proof = MathDocTree("proof", "A proof of a lemma, theorem or claim, having the same structure as (the value for) a `math_document`.", optional = True, give_json="list", key_value_str = md_blobnames) 
ref = MathDocTree("ref", "A reference where the result has been previously proved.", optional = True, give_json="string")
cite = MathDocTree("cite", "A citation of a result from the mathematical literature which gives the proof.", optional= True, give_json="string")

theorem = MathDocTree("theorem", "A mathematical theorem, with a list of hypotheses and a conclusion.", children = [hypothesis, conclusion, proved, name_field, proof, ref, cite, missing_proofs, errors], give_json= "object", post_text= subkeys_posttext)
root_child.append(theorem)

## Problem

problem_statement = MathDocTree("statement", "The statement of the problem.", give_json="string")
solved = MathDocTree("solved", "Whether the problem has been solved", give_json="boolean")
answer = MathDocTree("answer", "The answer to the problem.", optional = True, give_json="string")

problem = MathDocTree("problem", "A mathematical problem, with a statement and an answer.", children = [problem_statement, solved, answer, proof, missing_proofs, errors], give_json="object", post_text= subkeys_posttext)
root_child.append(problem)

## Cases

split_kind = MathDocTree("split_kind", "one of 'implication_direction' (for two sides of an 'iff' implication), 'match' (for pattern matching), 'condition' (if based on a condition being true or false) and 'groups' (for more complex cases).")
on = MathDocTree("on", "The variable or expression on which the cases are being done. Write 'implication direction' for an 'iff' statement.", give_json="string")

### Proof Cases
#### Case
condition = MathDocTree("condition", "The case condition or pattern; for induction one of 'base' or 'induction-step'; for a side of an 'iff' statement write the claim being proved (i.e., the statement `P => Q` or `Q => P`).", give_json="string")

case = MathDocTree("case", "A case in a proof by cases or proof by induction.", children = [condition, proof, missing_proofs, errors], give_json="object", post_text= subkeys_posttext)

proof_cases = MathDocTree("proof_cases", node_sequence_txt("case"), [case], optional = True)

exhaustiveness = MathDocTree("exhaustiveness", "Proof that the cases are exhaustive, similar to (the value for) 'math_document'.", optional = True, give_json="list", key_value_str = md_blobnames)

cases = MathDocTree("cases", "A proof by cases or proof by induction, with a list of cases.", children = [split_kind, on, proof_cases, exhaustiveness, missing_proofs, errors], give_json="object", post_text= subkeys_posttext)
root_child.append(cases)

## Induction
induction_on = MathDocTree("on", "The variable or expression on which induction is being done.", give_json="string")

induction = MathDocTree("induction", "The variable or expression on which induction is being done.", children = [induction_on, proof_cases], give_json="object", post_text= subkeys_posttext)
root_child.append(induction)

## Contradiction
assumption = MathDocTree("assumption", "The assumption being made for the contradiction.", give_json="string")
assumption_proof = MathDocTree("proof", "The proof of the contradiction given the assumption.", give_json="list", key_value_str = md_blobnames)

contradiction = MathDocTree("contradiction", "A proof by contradiction, with an assumption and a proof of the contradiction.", children = [assumption, assumption_proof, missing_proofs, errors], give_json="object", post_text= subkeys_posttext)
root_child.append(contradiction)

## Calculate
root_child.append(calculate)

## Conclude
conlusion_claim = MathDocTree("claim", "The conclusion of the proof.", give_json="string")
conclude = MathDocTree("conclude", "conclude a claim obtained from the steps so far. this is typically the final statement of a proof giving the conclusion of the theorem.", children = [ conlusion_claim, missing_proofs, errors], give_json="object", post_text= subkeys_posttext)
root_child.append(conclude)

## Remarks
remark = MathDocTree("remark", "A remark or comment that is NOT MATHEMATICAL, instead being for motivation, attention, sectioning etc.", give_json="string")
root_child.append(remark)

## Root 
# Tree initialisation from root.
root = MathDocTree("math_document", "A structured math document in a custom JSON format.", children=root_child, key_value_str=md_blobnames, give_json="list")
root.post_text = "The descriptions for the choices of _key_ and corresponding _value_ are as follows:"


if __name__ == "__main__":
    # Converting the tree to markdown (Always at the bottom)
    mathdoc = root.to_markdown()

    with open("./MathDoc.md", "w") as f:
        f.write(mathdoc)

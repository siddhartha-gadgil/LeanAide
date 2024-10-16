open Std Lean

/--
Building blocks for structured math documents. Additional data is given as a HashMap from `Name` to `MathPara` for elements in a group.
-/
inductive MathPara where
  | text (name: Name) (description : String := "ToDo")
  | bool (name: Name) (description : String := "ToDo")
  | enum (name: Name) (choices: List String)
      (description : String := "ToDo")
  | list (name: Name) (fieldType: Name) (describeOptions: Bool) (description : String := "ToDo")
  | one_of (name: Name) (choices: List MathPara) (description : String := "ToDo")
  | list_of (name: Name) (type : MathPara)
  | obj (fields: List MathPara) (optFields : List MathPara)
      (description : String := "ToDo")

namespace MathPara

def mathDoc : MathPara :=
  .list `document (fieldType := `mathBlock) (describeOptions := true) "A structured math document. This is a list of math blocks."

namespace let_statement

def var : MathPara := .text `variable ("the variable being defined (use `<anonymous>` if there is no name such as in `We have a group structure on S`)")

def value : MathPara := .text `value ("the value of the variable being defined")

def kind : MathPara := .text `kind ("the type of the variable, such as `real number`, `function from S to T`, `element of G` etc.")

def properties : MathPara := .text `properties "specific properties of the variable beyond the type."

end let_statement

open let_statement in
def let_statement : MathPara :=
  .obj (fields := [var])
    (optFields := [value, kind, properties])
    (description := "A statement introducing a new variable with given value, type and/or property.")

def assume : MathPara :=
  .text `assume "A mathematical assumption being made. In case this is a variable or structure being introduced, use a **let** statement."

namespace define

def statement : MathPara :=
  .text `statement "The mathematical definition."

def term : MathPara :=
  .text `term "The term being defined."

end define

def define : MathPara :=
  .obj (fields := [define.statement, define.term]) (optFields := [])
    (description := "A mathematical definition of a term.")

namespace deduced_using

def deduced_from : MathPara := .text `deduced_from "The assumptions or previously known results from which the deduction is made."

def in_context : MathPara := .bool `in_context "Whether the statement from which deduction is made is in the current context. Answer `true` or `false` (answer `false` if a result from the mathematical literature is being invoked)."

def instantiations : MathPara := .list `instantiations (fieldType := `instantiation) (describeOptions := true) "The instantiations of the assumptions or previously known results."

-- This will be a case of instantiations
def instantiation : MathPara :=  .text `instantiation "The instantiation of the assumption or previously known result to which the result is applied. For example,  `42` if we apply uniqueness of prime factorisation to `42`."

end deduced_using

namespace calculation

def inline : MathPara := .text `inline "A simple calculation or computation written as a single line."

def step : MathPara := .text `step "A step, typically an equality or inequality, in a calculation or computation."

def continuation : MathPara := .text `continuation "A continuation of a chain of equalities/inequalities, for example `= x + 3`. Should begin with an operator such as `=` or `≤` and be followed by a term."

end calculation

def calculation_step.justification : MathPara :=
  .text `justification "The justification for the step in a calculation or computation."

open calculation in
def calculation : MathPara :=
  .one_of `calculation [inline, step, continuation]  "A series of calculations or computations."

def calculation_step : MathPara :=
  .obj (fields := [calculation])
    (optFields := [calculation_step.justification])
    (description := "A step in a calculation or computation.")

namespace assert
open deduced_using in
def deduction : MathPara :=
  .obj (fields := [deduced_from, in_context])
    (optFields := [instantiations])
    (description := "A deduction of a mathematical result from assumptions or previously known results.")

def deductions : MathPara :=
  .list_of `deductions deduction

def claim : MathPara :=
  .text `claim "The mathematical claim being asserted, NOT INCLUDING proofs, justifications or results used. The claim should be purely a logical statement which is the *consequence* obtained."

def proof_method : MathPara :=
  .text `proof_method "The method used to prove the claim. This could be a direct proof, proof by contradiction, proof by induction, etc. this should be a single phrase or a fairly simple sentence; if a longer justification is needed break the step into smaller steps. If the method is deduction from a result, use the **deduced_using** field"

def calculations : MathPara :=
  .list_of `calculation (type := calculation_step)
end assert

def missing_result : MathPara :=
  .text `missing "A  problem that need to be solved or results that need to be proved to complete the proof. Standard results/criteria may be omitted from the proof: include them in the **deduced_from** field."

def missing : MathPara :=
  .list_of `missing missing_result

def error : MathPara :=
  .text `error "An error in a proof or calculation. Report only actual errors, with missing steps reported in the **missing** field."

def errors : MathPara :=
  .list_of `errors error

open assert in
def assert : MathPara :=
  .obj (fields := [claim])
    (optFields := [proof_method, deductions, calculations, missing, errors])
    (description := "A mathematical statement whose proof is a straightforward consequence of given and known results following some method.")

namespace thm

def hypothesis : MathPara :=
  .list `hypothesis (fieldType := `contextBlock) (describeOptions := false)  "a JSON list of data and assumptions, i.e., **let** and **assume** statements"

def conclusion : MathPara :=
  .text `conclusion "The conclusion of the theorem."

def proved : MathPara :=
  .bool `proved "Whether the theorem has been proved, either here or earlier or by citing the literature."


def ref : MathPara :=
  .text `ref "A reference where the result has been previously proved."

def cite : MathPara :=
  .text `cite "A citation of a result from the mathematical literature which gives the proof."

end thm

def proof : MathPara :=
  .list `proof (fieldType := `mathBlock) (describeOptions := false) "A proof of a lemma, theorem or claim. A list of steps each of which is an arbitrary math block (as in a math document)."

open thm in
def thm : MathPara :=
  .obj (fields := [hypothesis, conclusion, proved])
    (optFields := [proof, ref, cite, missing, errors])
    (description := "A mathematical theorem, with a list of hypotheses and a conclusion.")

namespace problem

def statement : MathPara :=
  .text `statement "The statement of the problem."

def solved : MathPara :=
  .bool `solved "Whether the problem has been solved."

def answer : MathPara :=
  .text `answer "The answer to the problem."

end problem

open problem in
def problem : MathPara :=
  .obj (fields := [statement, solved])
    (optFields := [answer, proof, missing, errors])
    (description := "A mathematical problem, with a statement and an answer.")

namespace case

def condition : MathPara :=
  .text `condition "The case condition or pattern; for induction one of 'base' or 'induction-step'"

end case

open case in
def case : MathPara :=
  .obj (fields := [condition, proof])
    (optFields := [missing, errors])
    (description := "A case in a proof by cases or proof by induction.")

namespace cases

def on : MathPara :=
  .text `on "The variable or expression on which the cases are being done."

def split_kind : MathPara :=
  .enum `split_kind ["match", "condition", "groups"] "one of 'match' (for pattern matching), 'condition' (if based on a condition being true or false) and 'groups' (for more complex cases)"

def exhaustiveness : MathPara :=
  .list `exhaustiveness (fieldType := `mathBlock) (describeOptions := false) "Proof that the cases are exhaustive."

end cases

def proof_cases : MathPara :=
  .list_of `proof_cases case

open cases in
def cases : MathPara :=
  .obj (fields := [on, split_kind, proof_cases])
    (optFields := [exhaustiveness, missing, errors])
    (description := "A proof by cases or proof by induction, with a list of cases.")

namespace induction

def on : MathPara :=
  .text `on "The variable or expression on which induction is being done."

end induction

open induction in
def induction : MathPara :=
  .obj (fields := [on, proof_cases])
    (optFields := [missing, errors])
    (description := "A proof by induction, with a base case and an induction step.")

namespace contradiction
def assumption : MathPara :=
  .text `assumption "The assumption being made to be contradicted."

def proof : MathPara :=
  .list `proof (fieldType := `mathBlock) (describeOptions := false) "The proof of the contradiction given the assumption."

end contradiction

open contradiction in
def contradiction : MathPara :=
  .obj (fields := [assumption, contradiction.proof])
    (optFields := [missing, errors])
    (description := "A proof by contradiction, with an assumption and a proof of the contradiction.")

namespace conclusion

def statement : MathPara :=
  .text `statement "The conclusion of the proof."

end conclusion

open conclusion in
def conclusion : MathPara :=
  .obj (fields := [statement])
    (optFields := [missing, errors])
    (description := "A conclusion obtained from the steps so far. This is typically the final statement of a proof giving the conclusion of the theorem.")

def remark : MathPara :=
  .text `remark "A remark or comment that is NOT MATHEMATICAL, instead being for motivation, attention, sectioning etc."

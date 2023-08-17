import Mathlib
import LeanCodePrompts.Translate
import LeanCodePrompts.CodeAction
import LeanCodePrompts.SpawnNearestEmbeddings
-- import LeanAide.CommentCodeAction

/-!
# Translation demo

To see translation in action, place the cursor anywhere on one of the comments below and invoke the code action to translate by clicking on the lightbulb or using `ctrl-.`. 
-/


//- There are infinitely many odd numbers -/

//- Every prime number is either `2` or odd -/

-- set_option trace.Translate.info true 
#eval translateViewM "There are infinitely many odd numbers"

#eval translateViewM "Every prime number is either `2` or odd"

def stats := #[
  "There are infinitely many odd numbers",
  "Every vector space of dimension 2 is finite dimensional",
  "Every subgroup of an Abelian group is Abelian"]

def mainTest : IO Unit := timeit "nearest_embeddings_test" do
  let results ← queryNearestEmbeddingsProcess stats
  IO.println results

#eval mainTest
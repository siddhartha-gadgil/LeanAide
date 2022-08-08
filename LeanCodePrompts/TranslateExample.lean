import Mathbin.All
import LeanCodePrompts.Translate

example : //- Every prime number is either `2` or odd. -//  := by
          
          sorry

-- example : //- Every field is a ring -// := by
                        
--             sorry

example  {K : Type u} [Field K] : Ring K := by sorry


#theorem test : "Every field is a ring" := by
  intro p hp
  sorry

#example "The sum of any two natural numbers is prime" := by admit


#eval checkElabThm "{K : Type u} [Field K] : is_ring K"
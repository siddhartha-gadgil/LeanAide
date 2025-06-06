import Lean
open Lean

instance : BEq (Option ModuleIdx) := inferInstanceAs (BEq (Option Nat))


/- A function for extracting the name and the type out of a `ConstantInfo` term.
It is desgined to work only for theorems, but can be extended to work for definitions too (may cause issues). -/
def Lean.ConstantInfo.extractNameType : ConstantInfo → Option (Name × Expr)
  | .thmInfo ⟨⟨nm, _, typ⟩, _, _⟩ => some ⟨nm, typ⟩
--  | .defnInfo ⟨⟨nm, _, typ⟩, _, _, _, _⟩ => some ⟨nm, typ⟩
  | _ => none


/- Gets all the theorem names and docstrings in the current file -/
def getFileThmInfo : MetaM (List $ Name × Option String) := do

  let env ← getEnv -- getting the current environment
  let mainModuleIdx := env.getModuleIdx? env.mainModule -- the index of the main module (i.e., the current file)

  -- extracting the names and types of the theorems in the current file
  let cnsts : List (Name × Expr) := env.constants |>.toList |>.filterMap
    (λ ⟨nm, ci⟩ => liftOption $ do
      guard $ env.getModuleIdxFor? nm == mainModuleIdx -- ensuring that the constant is in the current file
      ci.extractNameType) -- extracting the name and the type pf the theorem using the function defined above

  -- fetching the docstrings for each of the theorems in the current file
  (liftM : IO _ → MetaM _) $
    cnsts.mapM (λ ⟨nm, _typ⟩ => do
      return ⟨nm, ← findDocString? env nm⟩ )


section Testing

/-- Addition of two on the left is equal to addition of two on the right. -/
theorem add_two_comm : ∀ n : Nat, n + 2 = 2 + n := sorry

/-- Fermat's Last theorem, stated in the special case of `n = 3`. -/
theorem flt3 : a^3 + b^3 = c^3 → a * b * c = 0 := sorry


-- #eval getFileThmInfo

end Testing

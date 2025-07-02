import LeanAide
import Lean

open Lean Meta Elab
open LeanAide Meta CodeGenerator


-- set_option pp.funBinderTypes true in
#check show_sorries (let h₀ : Nat := (sorry : Nat)
  sorry : Nat)

#check show_sorries (sorry : True)

#check purge_lets (let a : Nat := (sorry : Nat)
  sorry : Nat)

#check purge_lets (let a : Nat := (sorry : Nat)
  sorry + a : Nat)

#check purge_lets (let a : Nat := (sorry : Nat)
  3 : Nat)

#check purge_lets (let a : Nat := (sorry : Nat)
  3 + a : Nat)


elab "#exists_vars" type:term : command => do
  Command.liftTermElabM do
  match ← existsVarTypes type with
  | some vars =>
      logInfo s!"Vars: {vars.map (·.1)}"
      return
  | none =>
      logInfo s!"No vars"
      return

#exists_vars ∃ n m : Nat, ∃ k: Nat, n + m  = 3

#exists_vars ∃ (n : Nat) (m: Nat), ∃ k: Nat, n + m  = 3

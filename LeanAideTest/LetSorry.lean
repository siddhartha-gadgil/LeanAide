import LeanAide

open LeanAide Meta

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

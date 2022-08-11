/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Data.Fin.Interval

/-!
# The structure of `fintype (fin n)`

This file contains some basic results about the `fintype` instance for `fin`,
especially properties of `finset.univ : finset (fin n)`.
-/


open Finset

open Fintype

namespace Finₓ

@[simp]
theorem Ioi_zero_eq_map {n : ℕ} : ioi (0 : Finₓ n.succ) = univ.map (Finₓ.succEmbedding _).toEmbedding := by
  ext i
  simp only [← mem_Ioi, ← mem_map, ← mem_univ, ← Function.Embedding.coe_fn_mk, ← exists_true_left]
  constructor
  · refine' cases _ _ i
    · rintro ⟨⟨⟩⟩
      
    · intro j _
      exact ⟨j, rfl⟩
      
    
  · rintro ⟨i, _, rfl⟩
    exact succ_pos _
    

@[simp]
theorem Ioi_succ {n : ℕ} (i : Finₓ n) : ioi i.succ = (ioi i).map (Finₓ.succEmbedding _).toEmbedding := by
  ext i
  simp only [← mem_filter, ← mem_Ioi, ← mem_map, ← mem_univ, ← true_andₓ, ← Function.Embedding.coe_fn_mk, ←
    exists_true_left]
  constructor
  · refine' cases _ _ i
    · rintro ⟨⟨⟩⟩
      
    · intro i hi
      refine' ⟨i, succ_lt_succ_iff.mp hi, rfl⟩
      
    
  · rintro ⟨i, hi, rfl⟩
    simpa
    

end Finₓ


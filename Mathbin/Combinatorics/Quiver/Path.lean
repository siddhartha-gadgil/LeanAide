/-
Copyright (c) 2021 David Wärn,. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Scott Morrison
-/
import Mathbin.Combinatorics.Quiver.Basic

/-!
# Paths in quivers

Given a quiver `V`, we define the type of paths from `a : V` to `b : V` as an inductive
family. We define composition of paths and the action of prefunctors on paths.
-/


universe v v₁ v₂ u u₁ u₂

namespace Quiver

/-- `G.path a b` is the type of paths from `a` to `b` through the arrows of `G`. -/
inductive Path {V : Type u} [Quiver.{v} V] (a : V) : V → Sort max (u + 1) v
  | nil : path a
  | cons : ∀ {b c : V}, path b → (b ⟶ c) → path c

/-- An arrow viewed as a path of length one. -/
def Hom.toPath {V} [Quiver V] {a b : V} (e : a ⟶ b) : Path a b :=
  Path.nil.cons e

namespace Path

variable {V : Type u} [Quiver V]

/-- The length of a path is the number of arrows it uses. -/
def length {a : V} : ∀ {b : V}, Path a b → ℕ
  | _, path.nil => 0
  | _, path.cons p _ => p.length + 1

instance {a : V} : Inhabited (Path a a) :=
  ⟨Path.nil⟩

@[simp]
theorem length_nil {a : V} : (Path.nil : Path a a).length = 0 :=
  rfl

@[simp]
theorem length_cons (a b c : V) (p : Path a b) (e : b ⟶ c) : (p.cons e).length = p.length + 1 :=
  rfl

/-- Composition of paths. -/
def comp {a b : V} : ∀ {c}, Path a b → Path b c → Path a c
  | _, p, path.nil => p
  | _, p, path.cons q e => (p.comp q).cons e

@[simp]
theorem comp_cons {a b c d : V} (p : Path a b) (q : Path b c) (e : c ⟶ d) : p.comp (q.cons e) = (p.comp q).cons e :=
  rfl

@[simp]
theorem comp_nil {a b : V} (p : Path a b) : p.comp Path.nil = p :=
  rfl

@[simp]
theorem nil_comp {a : V} : ∀ {b} (p : Path a b), Path.nil.comp p = p
  | a, path.nil => rfl
  | b, path.cons p e => by
    rw [comp_cons, nil_comp]

@[simp]
theorem comp_assoc {a b c : V} :
    ∀ {d} (p : Path a b) (q : Path b c) (r : Path c d), (p.comp q).comp r = p.comp (q.comp r)
  | c, p, q, path.nil => rfl
  | d, p, q, path.cons r e => by
    rw [comp_cons, comp_cons, comp_cons, comp_assoc]

end Path

end Quiver

namespace Prefunctor

open Quiver

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] (F : Prefunctor V W)

/-- The image of a path under a prefunctor. -/
def mapPathₓ {a : V} : ∀ {b : V}, Path a b → Path (F.obj a) (F.obj b)
  | _, path.nil => Path.nil
  | _, path.cons p e => Path.cons (map_path p) (F.map e)

@[simp]
theorem map_path_nil (a : V) : F.mapPath (Path.nil : Path a a) = path.nil :=
  rfl

@[simp]
theorem map_path_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    F.mapPath (Path.cons p e) = Path.cons (F.mapPath p) (F.map e) :=
  rfl

@[simp]
theorem map_path_comp {a b : V} (p : Path a b) :
    ∀ {c : V} (q : Path b c), F.mapPath (p.comp q) = (F.mapPath p).comp (F.mapPath q)
  | _, path.nil => rfl
  | _, path.cons p e => by
    dsimp'
    rw [map_path_comp]

end Prefunctor


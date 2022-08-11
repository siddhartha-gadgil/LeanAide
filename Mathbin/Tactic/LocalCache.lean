/-
Copyright (c) 2019 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek
-/
import Mathbin.Tactic.NormNum

namespace Tactic

namespace LocalCache

namespace Internal

variable {α : Type} [reflected _ α] [has_reflect α]

unsafe def mk_full_namespace (ns : Name) : Name :=
  `local_cache ++ ns

unsafe def save_data (dn : Name) (a : α) [reflected _ a] : tactic Unit :=
  tactic.add_decl <| mk_definition dn [] (reflect α) (reflect a)

unsafe def load_data (dn : Name) : tactic α := do
  let e ← tactic.get_env
  let d ← e.get dn
  tactic.eval_expr α d

unsafe def poke_data (dn : Name) : tactic Bool := do
  let e ← tactic.get_env
  return (e dn).toBool

unsafe def run_once_under_name {α : Type} [reflected _ α] [has_reflect α] (t : tactic α) (cache_name : Name) :
    tactic α := do
  load_data cache_name <|> do
      let a ← t
      save_data cache_name a
      return a

-- We maintain two separate caches with different scopes:
-- one local to `begin ... end` or `by` blocks, and another
-- for entire `def`/`lemma`s.
unsafe structure cache_scope where
  -- Returns the name of the def used to store the contents of is cache,
  -- making a new one and recording this in private state if neccesary.
  get_name : Name → tactic Name
  -- Same as above but fails instead of making a new name, and never
  -- mutates state.
  try_get_name : Name → tactic Name
  -- Asks whether the namespace `ns` currently has a value-in-cache
  present : Name → tactic Bool
  -- Clear cache associated to namespace `ns`
  clear : Name → tactic Unit

namespace BlockLocal

-- `mk_new` gives a way to generate a new name if no current one
-- exists.
private unsafe def get_name_aux (ns : Name) (mk_new : options → Name → tactic Name) : tactic Name := do
  let o ← tactic.get_options
  let opt := mk_full_namespace ns
  match o opt "" with
    | "" => mk_new o opt
    | s => return <| Name.fromComponents <| s (· = '.')

unsafe def get_name (ns : Name) : tactic Name :=
  (get_name_aux ns) fun o opt => do
    let n ← mk_user_fresh_name
    tactic.set_options <| o opt n
    return n

-- Like `get_name`, but fail if `ns` does not have a cached
-- decl name (we create a new one above).
unsafe def try_get_name (ns : Name) : tactic Name :=
  (get_name_aux ns) fun o opt => fail f! "no cache for "{ns}""

unsafe def present (ns : Name) : tactic Bool := do
  let o ← tactic.get_options
  match o (mk_full_namespace ns) "" with
    | "" => return ff
    | s => return tt

unsafe def clear (ns : Name) : tactic Unit := do
  let o ← tactic.get_options
  set_options <| o (mk_full_namespace ns) ""

end BlockLocal

namespace DefLocal

-- Fowler-Noll-Vo hash function (FNV-1a)
section FnvA1

def fNVOFFSETBASIS :=
  14695981039346656037

def fNVPRIME :=
  1099511628211

def rADIX := by
  apply_normed 2 ^ 64

def hashByte (seed : ℕ) (c : Charₓ) : ℕ :=
  let n : ℕ := c.toNat
  seed.lxor n * FNV_PRIME % RADIX

def hashString (s : Stringₓ) : ℕ :=
  s.toList.foldl hashByte fNVOFFSETBASIS

end FnvA1

unsafe def hash_context : tactic Stringₓ := do
  let ns ← open_namespaces
  let dn ← decl_name
  let flat := ((List.cons dn ns).map toString).foldl Stringₓ.append ""
  return <| toString dn ++ toString (hash_string flat)

unsafe def get_root_name (ns : Name) : tactic Name := do
  let hc ← hash_context
  return <| mk_full_namespace <| hc ++ ns

unsafe def apply_tag (n : Name) (tag : ℕ) : Name :=
  n ++ toString f! "t{tag}"

unsafe def mk_dead_name (n : Name) : Name :=
  n ++ `dead

unsafe def kill_name (n : Name) : tactic Unit :=
  save_data (mk_dead_name n) ()

unsafe def is_name_dead (n : Name) : tactic Bool :=
  (do
      let witness : Unit ← load_data <| mk_dead_name n
      return True) <|>
    return False

-- `get_with_status_tag_aux rn n` fails exactly when `rn ++ to_string n` does
-- not exist.
private unsafe def get_with_status_tag_aux (rn : Name) : ℕ → tactic (ℕ × Bool)
  | tag => do
    let n := apply_tag rn tag
    let present ← poke_data n
    if ¬present then fail f! "{rn} never seen in cache!"
      else do
        let is_dead ← is_name_dead n
        if is_dead then get_with_status_tag_aux (tag + 1) <|> return (tag, False) else return (tag, True)

-- Find the latest tag for the name `rn` and report whether it is alive.
unsafe def get_tag_with_status (rn : Name) : tactic (ℕ × Bool) :=
  get_with_status_tag_aux rn 0

unsafe def get_name (ns : Name) : tactic Name := do
  let rn ← get_root_name ns
  let (tag, alive) ← get_tag_with_status rn <|> return (0, True)
  return <| apply_tag rn <| if alive then tag else tag + 1

unsafe def try_get_name (ns : Name) : tactic Name := do
  let rn ← get_root_name ns
  let (tag, alive) ← get_tag_with_status rn
  if alive then return <| apply_tag rn tag else fail f! "no cache for "{ns}""

unsafe def present (ns : Name) : tactic Bool := do
  let rn ← get_root_name ns
  Prod.snd <$> get_tag_with_status rn <|> return False

unsafe def clear (ns : Name) : tactic Unit :=
  (do
      let n ← try_get_name ns
      kill_name n) <|>
    skip

end DefLocal

end Internal

open Internal

/-- This scope propogates the cache within a `begin ... end` or `by` block
    and its decendants. -/
unsafe def cache_scope.block_local : cache_scope :=
  ⟨block_local.get_name, block_local.try_get_name, block_local.present, block_local.clear⟩

/-- This scope propogates the cache within an entire `def`/`lemma`. -/
unsafe def cache_scope.def_local : cache_scope :=
  ⟨def_local.get_name, def_local.try_get_name, def_local.present, def_local.clear⟩

open CacheScope

/-- Asks whether the namespace `ns` currently has a value-in-cache. -/
unsafe def present (ns : Name) (s : cache_scope := block_local) : tactic Bool :=
  s.present ns

/-- Clear cache associated to namespace `ns`. -/
unsafe def clear (ns : Name) (s : cache_scope := block_local) : tactic Unit :=
  s.clear ns

/-- Gets the (optionally present) value-in-cache for `ns`. -/
unsafe def get (ns : Name) (α : Type) [reflected _ α] [has_reflect α] (s : cache_scope := block_local) :
    tactic (Option α) := do
  let dn ← some <$> s.try_get_name ns <|> return none
  match dn with
    | none => return none
    | some dn => some <$> load_data dn

-- Note: we can't just use `<|>` on `load_data` since it will fail
-- when a cached value is not present *as well as* when the type of
-- `α` is just wrong.
end LocalCache

open LocalCache LocalCache.Internal

/-- Using the namespace `ns` as its key, when called for the first
    time `run_once ns t` runs `t`, then saves and returns the result.
    Upon subsequent invocations in the same tactic block, with the scope
    of the caching being inherited by child tactic blocks) we return the
    cached result directly.

    You can configure the cached scope to be entire `def`/`lemma`s changing
    the optional cache_scope argument to `cache_scope.def_local`.
    Note: the caches backing each scope are different.

    If `α` is just `unit`, this means we just run `t` once each tactic
    block. -/
unsafe def run_once {α : Type} [reflected _ α] [has_reflect α] (ns : Name) (t : tactic α)
    (s : cache_scope := cache_scope.block_local) : tactic α :=
  s.get_name ns >>= run_once_under_name t

end Tactic


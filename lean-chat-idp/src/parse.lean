import system.io
import tactic
import data.nat.basic
import algebra.char_p
import ring_theory.power_series.basic
import combinatorics.partition
import data.nat.parity
import data.finset.nat_antidiagonal
import tactic.interval_cases
import tactic.apply_fun


open finset
open_locale big_operators
open_locale classical


open lean
def test1 := "theorem group_with_all_squares_equal_to_one_is_abelian (G : Type*)
   [group G] (hG : ∀ x : G, x^2 = 1) :
   ∀ x y : G, x * y = y * x := sorry"

def test2 := "theorem binomial_theorem_char_p (F : Type*) [field F] (p : ℕ) (hp : char_p F p)
  (a b : F) : (a + b)^p = ∑ i in finset.range p, (p choose i) * a^i * b^(p - i) := sorry"

-- theorem binomial_theorem_char_p (F : Type*) [field F] (p : ℕ) (hp : char_p F p)
--   (a b : F) : (a + b)^p = ∑ i in finset.range p, (p choose i) * a^i * b^(p - i) := sorry

meta structure decl_parse_result : Type :=
  (name : name)
  (binders : list expr)
  (type : expr)

open lean.parser

meta def binder.to_pi : binder → expr → expr
| b body := expr.pi b.name b.info b.type body

meta def mk_type_mvar : tactic expr :=
do u ← tactic.mk_meta_univ,
   t ← tactic.mk_meta_var (expr.sort u),
   return t

meta def expr.local_binder_info : pexpr → binder_info
  | (expr.local_const _ _ bi _) := bi
  | _ := inhabited.default

meta def pexpr.local_uniq_name : pexpr → name
  | (expr.local_const un _ _ _) := un
  | _ := inhabited.default


meta def pi_intro (b : binder) : tactic expr := do
  (main :: rest) ← tactic.get_goals,
  u ← tactic.mk_meta_univ,
  (new_goal, fvar) ← tactic.unsafe.type_context.run (do
    fvar ← tactic.unsafe.type_context.push_local b.name b.type b.info,
    new_goal ← tactic.unsafe.type_context.mk_mvar `T (expr.sort u),
    let assignment := binder.to_pi b $ expr.mk_delayed_abstraction new_goal [fvar.local_uniq_name],
    tactic.unsafe.type_context.assign main assignment,
    return (new_goal, fvar)
  ),
  tactic.set_goals (new_goal :: rest),
  return fvar

meta def add_binders : list pexpr → parser unit
  | [] := pure ()
  | ((expr.local_const un pn bi t) :: tail) := do
    parser.add_local (expr.local_const un pn bi (inhabited.default)),
    add_binders tail
  | _ := pure ()

meta def parse_decl : parser decl_parse_result := do
  (tk "theorem" <|> tk "def"),
  name ← ident,
  binders ← interactive.parse_binders,
  add_binders binders,
  tk ":",
  smt ← parser.pexpr 0,
  tk ":=",
  (T,fvars) ← parser.of_tactic (do
   T ← mk_type_mvar,
   tactic.set_goals [T],
   fvars : list expr ← binders.mmap (λ b, do
         t ← pure $ b.local_type,
         type ← tactic.i_to_expr ``(%%t : Sort*),
         let b : binder := ⟨b.local_pp_name, b.local_binder_info, type⟩,
         fvar ← pi_intro b,
         pure fvar
   ),
   smt ← tactic.i_to_expr ``(%%smt : Sort*),
   tactic.exact smt,
   T ← tactic.instantiate_mvars T,
   return (T, fvars)
  ),
  _ ← fvars.mmap parser.add_local,
  return {
     name := name,
     binders := fvars,
     type := T,
  }

-- set_option pp.all true

-- run_cmd do {
--    d1 ← parser.run_with_input parse_decl test1,
--    tactic.trace d1.name,
--    tactic.trace d1.type,
--    -- this step errors
--    d2 ← parser.run_with_input parse_decl test2,
--    tactic.trace d2.name,
--    tactic.trace d2.type
-- }


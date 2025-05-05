import Lean
import Lean.Parser
import Lean.Data.Json.Parser
import Mathlib
import LeanAide.VerboseDelabs
import DataGenAide.Premises
import LeanAide.SimpleFrontend
open Lean Meta Elab Parser Json.Parser
-- open Mathlib.Prelude.Rename

#check FiniteDimensional.finrank
#check ContinuousLinearEquiv.preimage_symm_preimage
-- #check homology.map_desc_apply
#check Submodule.equivMapOfInjective.proof_2
#check Submodule.equivMapOfInjective

universe u v

elab "natural:" n:num "only" : term => do
  return Expr.lit (Literal.natVal n.getNat)

#eval natural: 3 only -- 3

def fillIn : ℕ := natural: 3 only

def fillIn' : ℕ := natural: 0 only

#check Elab.runFrontend

def checkElabFront(s: String) : IO Bool := do
  let (_, chk) ← Elab.runFrontend s {} "<input>" `main
  return chk

#eval checkElabFront "def blah : Nat := 1"
#eval checkElabFront "theorem two_le_three : 2 ≤ 3  := by decide"


def checkDefFront(s: String)(n: Name) : IO Bool := do
  let (env, _) ← Elab.runFrontend s {} "<input>" `main
  let seek : Option ConstantInfo :=  env.find? n
  return seek.isSome

def defFrontValue(s: String)(n: Name) : MetaM String := do
  let (env, _) ← Elab.runFrontend s {} "<input>" `main
  let seek? : Option ConstantInfo :=  env.find? n
  let seek := seek?.get!
  let val := seek.value?.get!
  let fmt ←  ppExpr val
  return fmt.pretty

#eval checkDefFront "def blah : Nat := 1" `blah

#eval defFrontValue "def blah : Nat := 1" `blah
#eval defFrontValue
  "theorem two_le_three : 2 ≤ 3  := by decide" `two_le_three

#eval defFrontValue
  "theorem two_le_three : 2 ≤ 3  := by sorry" `two_le_three

#eval defFrontValue
  "theorem two_le_three : 2 ≤ 3  := sorry" `two_le_three


def bb : String := "
theorem two_le_four : 2 ≤ 4  := by decide

def x := unknown

def one : Nat := 1
"

#eval checkElabFrontM "def three := 2"

#eval checkElabFrontM bb


#check sorry
#reduce sorry
#check sorryAx

-- #check SlimCheck.Testable
-- #eval natural: 3 + 4 only -- Error

example :(A B C : Prop) → (f : A → B → C) → (a : A) → (b : B) → C := by
  aesop?


example: ∀ {K : Type u} {V : Type v} [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : Module K V]
  (h : FiniteDimensional.finrank K V = 2), FiniteDimensional K V := by sorry

example (a b c: ℕ) : a + b + c = c + b + a := by
  conv  =>
    congr
    conv =>
      congr
      rw [Nat.add_comm]
  sorry
/-- Subtract `m` and `n` in the presence of a proof that `n ≤ m`. -/
def minus (m n : ℕ)(hyp : n ≤ m) : ℕ :=
  match m, n, hyp with
  | m, 0, _ => m
  | 0, _ +1, pf => nomatch pf
  | m + 1, n + 1 , pf =>
    minus m n (Nat.le_of_succ_le_succ pf)

#eval minus 5 3 (by decide) -- 2

macro n:term "-₀" m:term : term => do
  `(minus $n $m (by decide))

#eval 5 -₀ 3 -- 2

#check Array.zip

-- elab(priority:=high) n:term "-" m:term : term =>
--   Term.withoutErrToSorry do
--   try
--     let n' ← Term.elabTermEnsuringType n (mkConst ``Nat)
--     let m' ← Term.elabTermEnsuringType m (mkConst ``Nat)
--     let inequality ← mkAppM ``LE.le #[m', n']
--     let pf ← Term.elabTermEnsuringType (← `(by decide)) inequality
--     Term.synthesizeSyntheticMVarsNoPostponing
--     mkAppM ``minus #[n', m', pf]
--   catch _ =>
--     let n ← Term.elabTerm n none
--     let m ← Term.elabTerm m none
--     mkAppM ``HSub.hSub #[n, m]

elab(priority:=high) n:term "-" m:term : term =>
  Term.withoutErrToSorry do
  let (n', m') ←
    try
      let n' ← Term.elabTermEnsuringType n (mkConst ``Nat)
      let m' ← Term.elabTermEnsuringType m (mkConst ``Nat)
      pure (n', m')
    catch _ =>
      let n ← Term.elabTerm n none
      let m ← Term.elabTerm m none
      pure (n, m)
  let nType ← inferType n'
  let mType ← inferType m'
  if (← isDefEq nType (mkConst ``Nat)) && (← isDefEq mType (mkConst ``Nat)) then
  let inequality ← mkAppM ``LE.le #[m', n']
  let mvar ← mkFreshExprMVar inequality
  let mvarId := mvar.mvarId!
  let (l, _) ←
  try
    runTactic mvarId (← `(tactic|decide))
  catch _ =>
    pure ([mvarId], {})
  unless l.isEmpty do
    throwError s!"failed to prove inequality {← ppExpr inequality}"
  mkAppM ``minus #[n', m', mvar]
  else
    mkAppM ``HSub.hSub #[n', m']

#check runTactic

#eval (5 : ℤ) - (6 : ℤ)
#eval 6 - 5 -- 1
-- #eval 5 - 6 -- error

#eval Json.parse "1.345345674532" |>.toOption |>.get! |>.getNum?|>.toOption |>.get! |>.toFloat

#eval decide (5 ≤  6)

#check DirectSum.lie_of

def purgeFailEg : MetaM DefData := do
  pure (← DefData.ofNameM? `purgeFailEg).get!

#eval purgeFailEg

open PrettyPrinter in

def delabView (name: Name) : MetaM String :=
    do
    let info ←  getConstInfo name
    let term := info.value?.get!
    let stx ←  delab term
    let fmt ←  ppTerm stx
    return fmt.pretty --stx.raw.reprint.get!

def egComp {α β γ α' : Type} (f : α' → β → γ) (g : (a : α) → α') (a : α) (b : β) :=  f (g a) b

#print egComp

#eval delabView `egComp -- this has the error `f g a b`

def delabSyntax (name: Name) : MetaM Syntax :=
    do
    let info ←  getConstInfo name
    let term := info.value?.get!
    PrettyPrinter.delab term

#eval delabSyntax `egComp

example : ∀ {α : Type u_1} {f : (a : α) → ENNReal} {s : Finset α} (h : Finset.sum s (fun (a : α) ↦ f a) = 1) (h' : ∀ (a : α) (x : ¬ a ∈ s) , f a = 0) {a : α} (ha : ¬ a ∈ s) , f a = 0   := by sorry

def egDel {α : Type u_1} [GeneralizedCoheytingAlgebra α] {a : α} {b : α} {c : α} (h : a ⊔ c ≤ b ⊔ c)  : (a \ c ≤ b \ c) = (a \ c ≤ b \ c) := by sorry

def egChk {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set α} {f : (a : α) → β} (hf : Function.Injective f) (h : f '' s ⊆ f '' t)  : (s ⊆ t) = (s ⊆ t) := by sorry

#check egDel
#check egChk

elab "egDelab" d:term : term => do
  let t ← Term.elabTerm d none
  logInfo m!"term: {t}"
  logInfo m!"purged: {← d.raw.purge}"
  return t

example {α : Type u} {ι : Sort x} {f : (a : ι) → Filter α} {p : (a : ι) → Prop} {l : Filter α} (h : ∀ {s : Set α} , (s ∈ l : Prop) ↔ (∃ (i : ι) , (p i : Prop) ∧ (s ∈ f i : Prop) : Prop)) {x : Set α} (a : ι)  : (p a) = (p a) := by sorry

-- {α : Type u_5} {β : Type u_4} {γ : Type u_3} {a : Option α} {b : Option β} {α' : Type u_1} {δ : Type u_2} {f : (a : α') → (a : β) → γ} {g : (a : α) → α'} {f' : (a : β) → (a : α) → δ} {g' : (a : δ) → γ} (h_left_anticomm : ∀ (a : α) (b : β) , f g a b = g' f' b a) (val : α) (h : a = some val) (val_1 : β) (h : b = some val_1)  : some val_1 = b

def egBind {α : Type u_5} {β : Type u_4} {γ : Type u_3} {a : Option α} {b : Option β} {α' : Type u_1} {δ : Type u_2} {f : (a : α') → (a : β) → γ} {g : (a : α) → α'} {f' : (a : β) → (a : α) → δ} {g' : (a : δ) → γ} (h_left_anticomm : ∀ (a : α) (b : β) , f (g a) b = g' (f' b a)) (val : α) (h : a = some val) (val_1 : β) (h : b = some val_1)  : some val_1 = b := by sorry

def egBind' {α β γ α' : Type}  {f : (a : α') → (a : β) → γ} {g : (a : α) → α'} (_ : ∀ (a : α) (b : β) , f (g a) b = f (g a) b)  : 1 = 1 := rfl



#eval verboseView? `egBind -- this has the error `f g a b` without `(g a)`

#eval delabView `egBind -- this has the error `f g a b` without `(g a)`

#eval delabView `egBind' -- this has the error `f g a b` without `(g a)`

example {α : Type u_1} {ι : Sort u_2} [ConditionallyCompleteLattice α] {f : (a : ι) → α} {g : (a : ι) → α} (B : BddAbove (Set.range g)) (H : ∀ (x : ι) , f x ≤ g x) (h : IsEmpty ι) (h_1 : (isEmpty_or_nonempty ι =: (IsEmpty ι : Prop) ∨ (Nonempty ι : Prop)) = (Or.inl h =: (IsEmpty ι : Prop) ∨ (Nonempty ι : Prop)))  : Or.inl h = isEmpty_or_nonempty ι := by sorry

example {α : Type u_2} {β : Type u_1} {M : Type u_3} [CommMonoid M] {f : (a : α) → M} {s : Set β} {g : (a : β) → α} (hg : Set.InjOn g (s ∩ Function.mulSupport f ∘ g))  : 1 = 1 := by sorry

#check egDelab {α : Type} →  {s : Set α} →  {t : Set α}   →  (s ⊆ t : Prop) = (s ⊆ t : Prop)

universe u_1 u_2 u_3

#check egDelab ({α : Type u_1} →  {β : Type u_2} →  {s : Set α} →  {t : Set α} →  {f : (a : α) → β} →  (hf : Function.Injective f) →  (h : f '' s ⊆ f '' t)  →  (s ⊆ t : Prop) = (s ⊆ t : Prop) : Prop)

#check egDelab ({α : Type u_2} →  {β : Type u_1} →  {M : Type u_3} →  [CommMonoid M] →  {f : (a : α) → M} →  {s : Set β} →  {g : (a : β) → α} →  (hg : Set.InjOn g (s ∩ Function.mulSupport f ∘ g))  →  1 = 1)




#eval Lean.Json.parse "{\"x\" : 3, \"y\" : 4, \"z\" : [\"five\", 6]}"

def gedit : IO String := do
  discard <| IO.Process.spawn { cmd := "gedit"}
  return "done"

def egType := fun (α : Type) ↦ fun [Mul α] ↦ fun x y : α ↦ x * y

#check egType ℕ
#eval egType _ 2 3

#check List.findSome?
#check List.getLast?_isSome
#check zero_mem
#eval (resolveGlobalName `none : MetaM _)
#print AddSubmonoid.zero_mem
example: ∀ {M : Type u_1} [
AddZeroClass M] (S : AddSubmonoid M) , 0 ∈ S  := zero_mem
#check FirstOrder.Language.Term.var.sizeOf_spec
#print false_or
#print Prop.completeLattice.proof_3
#check List.foldl_append
#check List.concat_eq_append
#check List.reverse_append

#check Fintype

structure SplitList (l: List α) where
  l₁ : List α
  a : α
  w : l = l₁ ++ [a]

theorem splitEnd (l: List α)(nontriv : l ≠ []): ∃ (l' : List α) (a : α), l = l' ++ [a] := by
  match c:l.reverse with
  | [] =>
    simp [List.reverse_reverse] at c
    contradiction
  | (a::l') =>
    have c' : l.reverse.reverse = (a::l').reverse := by rw [c]
    simp [List.reverse_reverse] at c'
    use l'.reverse, a


def splitEnd' [DecidableEq α](l: List α)(_ : l ≠ []): SplitList l :=
  match l with
  | h :: t =>
    if p:t = [] then
      ⟨[], h, by simp [p]⟩
    else by
      let ⟨l'', a, w⟩ := splitEnd' t p
      use h :: l'', a
      simp [w]
termination_by l.length

def mockCancel (l₁ l₂ : List ℤ): List ℤ  :=
  if c:l₁ = [] then l₂ else
  let ⟨l₁', a, _⟩ := splitEnd' l₁ c
  match l₂ with
  | [] => l₁
  | h :: t =>
      if h = -a then l₁' ++ t else l₁ ++ l₂

theorem mc_shrink (l₁ l₂ : List ℤ) :
  (mockCancel l₁ l₂).length ≤ l₁.length + l₂.length := by
  rw [mockCancel]
  split
  · simp
  · split
    split
    · simp
    · rename_i h₀' sp l₁' a' w' _ l₂' h' t'
      split
      · rw [w']
        simp [List.length_append]
        linarith
      · simp [List.length_append]


theorem one_is_pos : 0 < 1 := by simp

example : ∀ (x : Set Prop) (x_1 : Prop),
  (∀ (b : Prop), b ∈ x → x_1 ≤ b) → x_1 → ∀ (b : Prop), b ∈ x → b := by aesop

-- example : ∀ (x : Set Prop) (a : Prop), a ∈ x → infₛ x → a  := by aesop


example : 1 ≤3 := by
  have : 1 ≤ 2
  let _ := 3
  simp
  decide


-- #eval gedit
#check or_false_iff
#check MvFunctor
#print Or.intro_left
#check Or.inl

#check  1

#check List.findIdx?

#check List.remove
#print Decidable.recOn_true.proof_1
#check NeZero

instance : NeZero 1 := ⟨by decide⟩

#eval (2 : ZMod 3)

syntax (name:= gedit!) "#gedit" : command

open Command in
@[command_elab gedit!] def elabGedit : CommandElab :=
  fun _ => do
  let _ ← gedit
  return ()

-- #gedit

example : (4 : ℝ) > 0 := by simp
example : (4 : ℝ)⁻¹ > 0 := by simp

def stxPurged : MetaM Syntax := do
  let text := "rw [Nat.zero]\n\n -- a comment"
  let stx? := runParserCategory (← getEnv) `tactic text
  let stx := stx?.toOption.get!
  let stx' := stx.copyHeadTailInfoFrom .missing
  return stx'

def stxPurgedView : MetaM String := do
  let stx ← stxPurged
  return stx.reprint.get!.trim

#eval stxPurgedView

notation:85 x "^" y => Vector x y

instance : HAdd String String Nat :=
  ⟨fun s t ↦ s.length + t.length⟩

#eval "blah" + "Hello"

instance : Zero String where
  zero := "zero"
#eval (0 : String)
#eval (0 : String × Nat)

set_option autoImplicit false

structure IncidenceGeometry  where
   Point : Type
   Line : Type

structure Segment (geom: IncidenceGeometry) where
    p1 : geom.Point
    p2 : geom.Point

structure EuclideanGeometry extends IncidenceGeometry where
   distance : Point → Point → Nat

instance : Coe EuclideanGeometry IncidenceGeometry where
  coe geom := { Point := geom.Point, Line := geom.Line }

def length (geom: EuclideanGeometry) (s: Segment geom) : Nat :=
  geom.distance s.p1 s.p2

def rnd (lo hi: Nat) : Nat := ((IO.rand lo hi).run' ()).get!

#eval rnd 3 20

def a := rnd 0 10

def b := rnd 0 10

#eval a -- 1

#eval b -- 2

example : a = b := by rfl

def scottSyntax (h t: Expr) : MetaM Syntax := do
  let hStx ← PrettyPrinter.delab h
  let tpp ← ppExpr t
  let stx1 ← `(tactic| rw [$hStx:term])
  return stx1.raw.updateTrailing s!"-- {tpp}".toSubstring

elab "test_stx" h:term "hint" t:term  : term => do
  let h ← Term.elabTerm h none
  let t ← Term.elabTerm t none
  let stx ← scottSyntax h t
  logInfo m!"{stx}"
  return h

def egStx : MetaM Syntax := do
  let stx? := runParserCategory (← getEnv) `tactic "rw [Nat.zero]"
  let stx := stx?.toOption.get!
  logInfo m!"{stx}"
  return stx


def imps : CoreM <| Array Name := do
  return (← getEnv).allImportedModuleNames

#eval imps

#eval egStx

#eval test_stx Nat.zero hint 3

#check Lean.Syntax.atom

-- set_option pp.all true
-- example  : a = a := by
--     apply Eq.trans
--     rename_i α
--     exact rfl
--     rename_i β
--     exact rfl

/-
def runParserCategoryPartial  (catName : Name) (input : String) (fileName := "<input>") : MetaM <| Except String Syntax := do
  let env ← getEnv
  let c := mkParserContext (mkInputContext input fileName) { env := env, options := {} }
  let s := mkParserState input
  let s := whitespace c s
  let parser := categoryParser catName 0
  let parserFn := parser.fn
  let s : ParserState := parserFn c s
  let stack := s.stxStack.filter fun s => !s.hasMissing
  -- let s := categoryParserFnImpl catName c s
  if stack.isEmpty &&  s.hasError then
    return    Except.error (s.toErrorMsg c)
  else
    IO.println <| input.extract 0 s.pos
    return Except.ok stack.back

def runParserPartial  (parser : Parser) (input : String) (fileName := "<input>") : MetaM <| Except String Syntax := do
  let env ← getEnv
  let c := mkParserContext (mkInputContext input fileName) { env := env, options := {} }
  let s := mkParserState input
  let s := whitespace c s
  let parserFn := parser.fn
  let s : ParserState := parserFn c s
  -- IO.println s.stxStack
  let stack := s.stxStack.filter fun s => !s.hasMissing
  -- let s := categoryParserFnImpl catName c s
  if stack.isEmpty &&  s.hasError then
    return    Except.error (s.toErrorMsg c)
  else
    IO.println <| input.extract 0 s.pos
    return Except.ok stack.back


#eval runParserCategoryPartial `term "1 + 2  3"

#check Syntax.hasMissing

#eval runParserPartial ident "x y z 3"

#eval runParserCategoryPartial `tactic "repeat (simp [x, Nat]; skip)  1 + 2  3"

open Command

#eval runParserPartial «variable» "variable (x : Nat) [h: Group x] and something else"

variable (x : Nat)

#eval runParserCategoryPartial `tactic "have x : N := 2 := 3 ; simp"

declare_syntax_cat hellotac

declare_syntax_cat defhead
syntax "theorem" : defhead
syntax "def" : defhead
syntax "lemma" : defhead

syntax defhead ident ":" term ":=" "by" tactic : hellotac

declare_syntax_cat sectionHead

syntax "section" (colGt ident)? : sectionHead

#eval runParserCategoryPartial `sectionHead "section blah"

def multiline := "section
lemma x → y := by simp
end"

#eval runParserCategoryPartial `sectionHead multiline

#eval runParserCategoryPartial `hellotac "theorem blah : Nat := by let x : N := 2 := 3 ; simp"

def ml := "theorem blah : Nat := by
let x : N := 2 := 3
simp"

#eval runParserCategoryPartial `hellotac ml

def getName (stx: Syntax) : MetaM Name := do
match stx with
| `(hellotac|theorem $name:ident : $_:term := by $_) => pure name.getId
| _ => throwUnsupportedSyntax

def parseName(s: String) : MetaM Name := do
match ← runParserCategoryPartial `hellotac s with
| Except.ok stx => getName stx
| Except.error msg => throwError msg

#eval parseName "theorem blah : Nat := by let x : N := 2 := 3 ; simp"

def getPieces (stx: Syntax) : MetaM (String × String × String) := do
match stx with
| `(hellotac|theorem $name:ident : $t:term := by $tac) =>
    pure (name.raw.reprint.get!, t.raw.reprint.get!, tac.raw.reprint.get!)
| _ => throwUnsupportedSyntax

def parsePieces(s: String) : MetaM (String × String × String) := do
match ← runParserCategoryPartial `hellotac s with
| Except.ok stx => getPieces stx
| Except.error msg => throwError msg

#eval parsePieces "theorem blah : Nat := by let x : N := 2 := 3 ; simp"

#check IO.FS.readFile

#eval (searchPathRef.get : IO _)

def oleanFiles : IO (Array System.FilePath) := do
  let paths ← searchPathRef.get
  IO.println paths
  Lean.SearchPath.findAllWithExt paths "olean"

#eval oleanFiles

#check System.mkFilePath ["."]

def leanFiles : IO (Array System.FilePath) := do
  Lean.SearchPath.findAllWithExt [System.mkFilePath ["./LeanCodePrompts"]] "lean"

#eval leanFiles

def inducEg := "induction m with
    | zero =>
      simp [zhom]
    | succ k ih =>
      simp [zhom]
      simp [zhom] at ih
      rw [← add_assoc]
      simp
      simp
      let l₂ := gsmul_succ (n + k) x
      simp at l₂
      rw [l₂]
      rw [ih]
      simp
      conv =>
        lhs
        rw [← add_assoc]
        arg 1
        rw [add_comm]
      rw [← add_assoc]"

#eval runParserCategoryPartial `tactic inducEg

def contractInductionStx (induction : Syntax) : MetaM Syntax := do
match induction with
| `(tactic| induction $name $_:inductionAlts) =>
  `(tactic| induction $name)
| `(tactic| cases $name $_:inductionAlts) =>
  `(tactic| cases $name)
| _ => return induction

def contractInduction (s: String) : MetaM String := do
match ← runParserCategoryPartial `tactic s with
| Except.ok stx => do
    let stx ←  contractInductionStx stx
    pure stx.reprint.get!
| Except.error _ => pure s

#eval contractInduction inducEg

def js := Json.mkObj [
  ("a", Json.num 1),
  ("b", Json.str "hello is this going to cause a wrap in the line"),
  ("c", Json.arr #[Json.num 1, Json.str s!"hello {multiline}"])
]

#eval multiline
#eval multiline.quote
#eval js.pretty (10000)
-- #eval IO.FS.writeFile "test.json" (js.pretty (10000))

#check Expr.forallE

open Term

@[term_elab byTactic] def myElabByTactic : TermElab :=
  fun stx expectedType? => do
  mkSyntheticSorry (mkConst ``Nat)

def sillyNat : Nat := by exact 1

example : String := by simp

-/

import LeanCodePrompts.FirstTacticData
import Lean

open Lean Meta Elab Tactic

def getTacticString : TacticM String := do
  let target ← getMainTarget
  let lctx ←  getLCtx
  let decls := lctx.decls
  let mut statement := ""
  for decl in decls do
    match decl with
    | some <| LocalDecl.ldecl _ _ n t .. => 
      statement := statement ++ s!"({n.eraseMacroScopes} : {← t.view}) "
      pure ()
    | some <| LocalDecl.cdecl _ _ n t bi => do
      let core := s!"{n.eraseMacroScopes} : {← t.view}"
      let typeString :=s!"{← t.view}"
      let argString := match bi with
      | BinderInfo.implicit => "{"++ core ++ "}"
      | BinderInfo.strictImplicit => "{{ "++ core ++ "}}"
      | BinderInfo.instImplicit =>
        if (`inst).isPrefixOf n then s!"[{typeString}]"
          else s!"[{core}]"
      | BinderInfo.default => s!"({core})" 
      | _ => ""
      statement := statement ++ argString ++ " " 
      pure ()
    | none => pure ()
  statement := statement ++ ": " ++ (←  target.view)
  return statement.replace "✝" ""


elab "show_goal" : tactic => 
  withMainContext do  
    let view ← getTacticString
    logInfo view
    return ()

def silly {α  : Type}(n m : ℕ)[DecidableEq α] : n + m = n +m := by 
    let a  := n
    show_goal
    rfl


def silly' : (n m : ℕ)  →  n + m = n +m := by
    intros
    show_goal  
    rfl


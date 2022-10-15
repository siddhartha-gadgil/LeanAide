import LeanCodePrompts.FirstTacticData
import Lean

open Lean Meta Elab Tactic Parser

def getTacticString : TacticM String := do
  let s ← saveState
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
  s.restore
  return statement.replace "✝" ""


elab "show_goal" : tactic => 
  withMainContext do  
    let view ← getTacticString
    logInfo view
    return ()

def silly {α  : Type}(n m : ℕ)[DecidableEq α] : n + m = n +m := by 
    show_goal
    let a  := n
    let h : a = a := rfl
    show_goal
    rfl


def silly' : (n m : ℕ)  →  n + m = n +m := by
    intros
    show_goal  
    rfl

structure TacticStateProxy where
  binders: Array <| Name ×  BinderInfo
  letData : Array <| Name × Expr × Expr
  target : Expr 

def getTacticStateProxy : TacticM <| Option TacticStateProxy := 
  withoutModifyingState do
  try 
    let target ← getMainTarget
    let lctx ←  getLCtx
    let decls := lctx.decls
    let mut binders := #[]
    let mut letData := #[]
    let mut fvars : Array Expr := #[]
    for decl in decls do
      match decl with
      | some <| LocalDecl.ldecl _ _ n t b .. => 
        let t ← mkForallFVars fvars t
        let b ← mkLambdaFVars fvars b
        letData := letData.push (n, t, b)
        pure ()
      | some <| LocalDecl.cdecl _ fVarId n _ bi => do
        binders := binders.push  (n, bi)
        fvars := fvars.push <| mkFVar fVarId
        pure ()
      | none => pure ()
    let target ← mkForallFVars fvars target
    return some {binders := binders, letData := letData, target := target}
  catch _ => return none

#check List.allM

def equalStates (s₁ s₂ : TacticStateProxy) : TacticM Bool := 
   withMainContext do
    return s₁.binders == s₂.binders 
            && s₁.letData.size == s₂.letData.size && 
            (← isDefEq s₁.target s₂.target) && 
            (← (List.range s₁.letData.size).allM (fun i => 
              let (n₁, t₁, b₁) := s₁.letData.get! i
              let (n₂, t₂, b₂) := s₂.letData.get! i
              return n₁ == n₂ && (← isDefEq t₁ t₂) && (← isDefEq b₁ b₂)))

def firstEffectiveTactic (tacStrings: List String) : TacticM Unit :=
  withMainContext do
  let env ← getEnv
  let s ← saveState
  -- logInfo m!"Trying tactics {tacStrings}"
  let s₁? ← getTacticStateProxy
  -- logInfo "Saved proxy"
  for tacString in tacStrings do
    -- logInfo m!"Trying tactic {tacString}"
    let tac? := runParserCategory env `tactic tacString
    -- logInfo m!"Trying parsed tactic {tacString}"
    match tac? with
    | Except.ok tac => do
      -- logInfo tacString
      try 
          evalTactic tac
          let check : Bool ← 
          try 
            let s₂? ← getTacticStateProxy  
            match s₁?, s₂? with
            | some s₁, some s₂ => equalStates s₁ s₂          
            | _,_ => pure false
          catch e =>
            logWarning 
              m!"Failed to check state after {tacString}; error : {e.toMessageData}" 
            pure false
          if check then
            logWarning m!"{tacString} did not change the goal"
            s.restore
          else
            logInfo m!"{tacString} changed the goal"
            return 
      catch e =>
        logWarning m!"{tacString} failed with error {e.toMessageData}" 
        s.restore
    | Except.error e => 
        logWarning m!"could not parse{e}"
        pure ()
  logWarning "No tactic in the list was effective" 

 
elab "first_effective_tactic" : tactic => 
  withMainContext do
    firstEffectiveTactic ["intros", "rfl"]


def silly'' (n m : ℕ)  : n + m = n + m := by
    first_effective_tactic

def silly''' : (n m : ℕ)  →  n + m = n + m := by
    first_effective_tactic 
    rfl
import LeanAide.FirstTacticData

import LeanCodePrompts.Translate
import Lean

open Lean Meta Elab Tactic Parser 

initialize cacheTacticJson : IO.Ref (HashMap String Json) ← IO.mkRef (HashMap.empty) 

def getTacticString : TacticM String := do
  let s ← saveState
  let target ← getMainTarget
  let lctx ←  getLCtx
  let decls := lctx.decls.toList.tail!
  let mut statement := ""
  for decl in decls do
    match decl with
    | some <| LocalDecl.ldecl _ _ n t .. => 
      statement := statement ++ s!"({n.eraseMacroScopes} : {← t.view}) "
      pure ()
    | some <| LocalDecl.cdecl _ _ n t bi _ => do
      let core := s!"{n.eraseMacroScopes} : {← t.view}"
      let typeString :=s!"{← t.view}"
      let argString := match bi with
      | BinderInfo.implicit => "{"++ core ++ "}"
      | BinderInfo.strictImplicit => "{{ "++ core ++ "}}"
      | BinderInfo.instImplicit =>
        if (`inst).isPrefixOf n then s!"[{typeString}]"
          else s!"[{core}]"
      | BinderInfo.default => s!"({core})" 
      statement := statement ++ argString ++ " " 
      pure ()
    | none => pure ()
  statement := statement ++ ": " ++ (←  target.view)
  s.restore
  return statement.replace "✝" ""

elab "name_inacessibles" : tactic => do
  withMainContext do
  let lctx ←  getLCtx
  let decls := lctx.decls
  let mut statement := "rename_i"
  for decl in decls do
    match decl with
    | some <| LocalDecl.ldecl _ _ n .. => 
      if n != n.eraseMacroScopes then
        statement := statement ++ s!" {n.eraseMacroScopes}"
      pure ()
    | some <| LocalDecl.cdecl _ _ n .. => do
      if n != n.eraseMacroScopes then
        statement := statement ++ s!" {n.eraseMacroScopes}"
      pure ()
    | none => pure ()
  unless statement == "rename_i" do
    let tac? := runParserCategory (← getEnv) `tactic statement
      match tac? with
      | Except.ok tac => do
        evalTactic tac
      | Except.error e => do
        throwError e     

elab "show_goal" : tactic => 
  withMainContext do  
    let view ← getTacticString
    logInfo view
    return ()

def silly {α  : Type}(n m : Nat)[DecidableEq α] : n + m = n + m := by 
    show_goal
    let a  := n
    let _ : a = a := rfl
    show_goal
    rfl


def silly' : (n m : Nat)  →  n + m = n + m := by
    intros
    show_goal  
    rfl
    done

example : (n m : Nat)  →  n + m = n + m := by
    intros
    name_inacessibles  
    rfl
    done

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
      | some <| LocalDecl.cdecl _ fVarId n _ bi _ => do
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

def firstEffectiveTactic (tacStrings: List String)(warnOnly: Bool := Bool.true) : TacticM Unit :=
  withMainContext do
  let env ← getEnv
  let goal ← getTacticString
  logInfo m!"goal: {goal}"
  logInfo m!"trying tactics: {tacStrings}"
  let s ← saveState
  let s₁? ← getTacticStateProxy
  for tacString in tacStrings do
    -- logInfo m!"Trying tactic {tacString}"
    try
      let tac? := runParserCategory env `tactic tacString
      match tac? with
      | Except.ok tac => do
          Term.withoutErrToSorry do 
            evalTactic tac
          let gs ← getUnsolvedGoals
          if gs.isEmpty then
              logInfo m!"tactic `{tacString}` was effective"
              return 
          else
            let check : Bool ← 
            try 
              let s₂? ← getTacticStateProxy  
              match s₁?, s₂? with
              | some s₁, some s₂ => equalStates s₁ s₂          
              | _,_ => pure Bool.true
            catch _ =>
              -- logWarning 
                -- m!"Failed to check state after {tacString}; error : {e.toMessageData}" 
              pure Bool.true
            if check then
              s.restore
            else
              let checkForSorries : Bool ←
                try
                  let target ← getMainTarget
                  pure target.hasSyntheticSorry
                catch _ => pure Bool.false
              -- logInfo m!"sorries? {checkForSorries}"
              if checkForSorries then
                s.restore
              else
                logInfo m!"tactic `{tacString}` was effective"
                return 
      | Except.error _ => 
        pure ()
    catch _ =>
      s.restore
  unless warnOnly do
    throwError m!"No effective tactic found for {goal} in {tacStrings}"
  logWarning "No tactic in the list was effective" 

 
elab "first_effective_tactic" : tactic => 
  withMainContext do
    firstEffectiveTactic ["unparsable", "exact blah", "intros", "rfl"]

-- proved by reflexivity
def silly'' (n m : Nat)  : n + m = n + m := by
    intros -- legal but no effect
    first_effective_tactic

def silly''' : (n m : Nat)  →  n + m = n + m := by
    first_effective_tactic 
    rfl

def silly'''' : (n m : Nat)  →  n + m = n + m := by
    repeat (first_effective_tactic)

def getTacticPrompts(s: String)(numSim : Nat)
   : TermElabM (Array String) := do
      let jsData := Json.mkObj [
        ("filename", "data/lean4-thms.json"),
        ("field", "core-prompt"),
        ("core-prompt", s),
        ("n", numSim),
        ("model_name", "all-mpnet-base-v2")
      ]
      let simJsonOut ←   
        IO.Process.output {cmd:= "curl", args:= 
          #["-X", "POST", "-H", "Content-type: application/json", "-d", jsData.pretty, s!"{← leanAideIP}/nearest_prompts"]}
      if simJsonOut.exitCode > 0 then
        throwError m!"Failed to get prompts from server: {simJsonOut.stderr}"
      else
        let json := 
          Lean.Json.parse simJsonOut.stdout |>.toOption.get! 
        match json.getArr? with
        | Except.ok arr => 
          let mut prompts := #[]
          for j in arr do
            match j.getObjVal? "tactic-prompt" with
            | Except.ok s =>
              match s.getStr? with
              | Except.ok s => 
                prompts := prompts.push s
              | Except.error e => 
                throwError m!"Failed to parse json {j}; error: {e}"
            | Except.error e =>
              throwError m!"Failed to parse json {j}; error: {e}"
          return prompts
        | Except.error e => 
            throwError m!"Failed to parse json: {e}"



def fourSquaresPrompt := ": ∀ p : Nat, Prime p → (p % 4 = 1) → ∃ a b : Nat, a ^ 2 + b ^ 2 = p"

-- #eval getTacticPrompts fourSquaresPrompt 20 

def makeTacticPrompt (n: Nat)  : TacticM String := do
  let core ← getTacticString
  let prompts ← getTacticPrompts core n
  let prompt := prompts.foldr (fun  p acc => 
s!"{p}

{acc}"
          ) s!"
theorem {core} := by "
  return prompt

def tacticList : TacticM <| List String := do
  let core ← getTacticString
  let prompts ← getTacticPrompts core 5
  let promptPairs := prompts.map (fun p => 
    let arr := p.splitOn ":= by"
    (arr.get! 0++ ":= by", arr.get! 1))
  let prompt := GPT.makePrompt core promptPairs
  -- let prompt ← makeTacticPrompt 20 
  let cache ← cacheTacticJson.get
  let fullJson ←
    match cache.find? prompt.pretty with
    | some json => pure json
    | none =>  
      let res ← gptQuery prompt 5 ⟨8, 1⟩ #[";", "sorry", "\n"]
      cacheTacticJson.set <| cache.insert prompt.pretty res
      pure res
  let outJson := 
        (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
  let arr ← GPT.jsonToExprStrArray outJson
  let arr := arr.map (fun s => 
      if s.endsWith "<" then s.dropRight 1 |>.trim else s.trim)
  return arr.toList.eraseDups

elab "aide?" : tactic =>
  withMainContext do
    let tacStrings ← tacticList
    let tacStrings := tacStrings.filter (fun s => s != "sorry" && s != "admit")
    let tac ← `(tactic|name_inacessibles)
    evalTactic tac
    firstEffectiveTactic tacStrings Bool.true

elab "aide!" : tactic =>
  withMainContext do
    let tacStrings ← tacticList
    let tac ← `(tactic|name_inacessibles)
    evalTactic tac
    let tacStrings := tacStrings.filter (fun s => s != "sorry" && s != "admit")
    firstEffectiveTactic tacStrings Bool.false

macro "aide" : tactic => 
  `(tactic| (aide? ; save))


elab "show_tactic_prompt" : tactic => 
  withMainContext do  
    let view ← makeTacticPrompt 20
    logInfo view
    return ()

elab "lookahead" tac:tactic : tactic => 
  withMainContext do
    let s ← saveState
    try
      evalTactic tac
      s.restore
    catch e =>
      s.restore
      let msg := e.toMessageData
      throwError s!"{← msg.toString}"


def lookaheadTactics (ss: List String) : List String :=
    ss.map (fun s => s!"{s} ; done") ++ 
    ss.map (fun s => s!"({s} <;> (lookahead aide!)) ; done") ++
    ss.map (fun s => s!"{s} <;> (lookahead aide!)") ++ 
    ss

example : 1 = 1 := by
  lookahead rfl
  lookahead rfl
  rfl

elab "aide_aux" : tactic =>
  withMainContext do
    let tacStrings ← tacticList
    let tacStrings := tacStrings.filter (fun s => s != "sorry" && s != "admit")
    let tac ← `(tactic|name_inacessibles)
    evalTactic tac
    let tacStrings := lookaheadTactics tacStrings
    firstEffectiveTactic tacStrings Bool.false

macro "aide_lookahead" : tactic => `(tactic|checkpoint aide_aux)

/-
Copied and modified from Lean 4 `./src/Lean/PrettyPrinter/Delaborator/Builtins.lean`
-/
import Lean
import LeanCodePrompts.Utils
open Lean Meta Elab Term Parser PrettyPrinter

namespace LeanAide.Meta

open Elab Term in
elab (name:=proved_prop) "(" a:term "=:" b:term ")": term => do
    let b ← elabType b 
    let a ← elabTermEnsuringType a (some b)
    guard (← isProof a)
    return a

example :=  ((by decide) =: 1 ≤ 2 )


  

-- delaborator copied from Lean to modify
open Delaborator SubExpr 
def checkExprDepth (e: Expr) : DelabM Unit := do
  let depth ← getDelabBound
  if e.approxDepth > depth then
    failure


def checkDepth : DelabM Unit := do
  let depth ← getDelabBound
  let e ← getExpr
  if e.approxDepth > depth then
    failure




partial def delabVerbose : Delab := do
  checkMaxHeartbeats "delab"
  let e ← getExpr
  -- checkExprDepth e
  let isProof := !e.isAtomic && (← (try Meta.isProof e catch _ => pure false))
  let k ← getExprKind
  let stx ← delabFor k <|> (liftM $ show MetaM _ from throwError "don't know how to delaborate '{k}'")
  if (← getPPOption getPPAnalyzeTypeAscriptions <&&> getPPOption getPPAnalysisNeedsType <&&> pure !e.isMData) then
    let typeStx ← withType delab
    `(($stx : $typeStx)) >>= annotateCurPos
  else if isProof then
    let typeStx ← withType delab
    `(($stx =: $typeStx)) >>= annotateCurPos
  else
    return stx

def wrapInType (e: Expr)(stx: Term) : Delab := do
  let isProof ← (try Meta.isProof e catch _ => pure false)
  if isProof then
    let typeStx ← withType delab
    `(($stx =: $typeStx)) >>= annotateCurPos
  else
    return stx

open Lean.Parser.Term
open TSyntax.Compat

def fvarPrefix : Name := "freeVariable"

@[scoped delab app]
def delabAppExplicitVerbose : Delab := do
  checkDepth
  let paramKinds ← getParamKinds
  let tagAppFn ← getPPOption getPPTagAppFns
  let (fnStx, _, argStxs) ← withAppFnArgs
    (do
      let stx ← withOptionAtCurrPos `pp.tagAppFns tagAppFn delabAppFn
      let needsExplicit := stx.raw.getKind != ``Lean.Parser.Term.explicit
      let stx ← if needsExplicit then `(@$stx) else pure stx
      pure (stx, paramKinds.toList, #[]))
    (fun ⟨fnStx, paramKinds, argStxs⟩ => do
      let isInstImplicit := match paramKinds with
                            | [] => false
                            | param :: _ => param.bInfo == BinderInfo.instImplicit
      let argStx ← if ← getPPOption getPPAnalysisHole then `(_)
                   else if isInstImplicit == true then
                     let stx ← if ← getPPOption getPPInstances then delab else `(_)
                     if ← getPPOption getPPInstanceTypes then
                       let typeStx ← withType delab
                       `(($stx : $typeStx))
                     else pure stx
                   else delabVerbose
      pure (fnStx, paramKinds.tailD [], argStxs.push argStx))
  let stx := Syntax.mkApp fnStx argStxs
  wrapInType (← getExpr) stx


@[scoped delab app]
def delabAppImplicit : Delab := do
  checkDepth
  -- TODO: always call the unexpanders, make them guard on the right # args?
  let paramKinds ← getParamKinds
  if ← getPPOption getPPExplicit then
    if paramKinds.any (fun param => !param.isRegularExplicit) then failure

  -- If the application has an implicit function type, fall back to delabAppExplicit.
  -- This is e.g. necessary for `@Eq`.
  let isImplicitApp ← try
      let ty ← whnf (← inferType (← getExpr))
      pure <| ty.isForall && (ty.binderInfo == BinderInfo.implicit || ty.binderInfo == BinderInfo.instImplicit)
    catch _ => pure false
  if isImplicitApp then failure

  let tagAppFn ← getPPOption getPPTagAppFns
  let (fnStx, _, argStxs) ← withAppFnArgs
    (withOptionAtCurrPos `pp.tagAppFns tagAppFn <|
      return (← delabAppFn, paramKinds.toList, #[]))
    (fun (fnStx, paramKinds, argStxs) => do
      let arg ← getExpr
      let opts ← getOptions
      let mkNamedArg (name : Name) (argStx : Syntax) : DelabM Syntax := do
        `(Parser.Term.namedArgument| ($(mkIdent name) := $argStx))
      let argStx? : Option Syntax ←
        if ← getPPOption getPPAnalysisSkip then pure none
        else if ← getPPOption getPPAnalysisHole then `(_)
        else
          match paramKinds with
          | [] => delabVerbose
          | param :: rest =>
            if param.defVal.isSome && rest.isEmpty then
              let v := param.defVal.get!
              if !v.hasLooseBVars && v == arg then pure none else delabVerbose
            else if !param.isRegularExplicit && param.defVal.isNone then
              if ← getPPOption getPPAnalysisNamedArg <||> (pure (param.name == `motive) <&&> shouldShowMotive arg opts) then some <$> mkNamedArg param.name (← delabVerbose) else pure none
            else delabVerbose
      let argStxs := match argStx? with
        | none => argStxs
        | some stx => argStxs.push stx
      pure (fnStx, paramKinds.tailD [], argStxs))
  let stx := Syntax.mkApp fnStx argStxs
  let stx ← wrapInType (← getExpr) stx
  if ← isRegularApp then
    (guard (← getPPOption getPPNotation) *> unexpandRegularApp stx)
    <|> (guard (← getPPOption getPPStructureInstances) *> unexpandStructureInstance stx)
    <|> pure stx
  else pure stx


/--
  Extract arguments of motive applications from the matcher type.
  For the example below: `#[#[`([])], #[`(a::as)]]` -/
private partial def delabPatterns (st : AppMatchState) : DelabM (Array (Array Term)) :=
  withReader (fun ctx => { ctx with inPattern := true, optionsPerPos := {} }) do
    let ty ← instantiateForall st.matcherTy st.params
    -- need to reduce `let`s that are lifted into the matcher type
    forallTelescopeReducing ty fun params _ => do
      -- skip motive and discriminators
      let alts := Array.ofSubarray params[1 + st.discrs.size:]
      alts.mapIdxM fun idx alt => do
        let ty ← inferType alt
        -- TODO: this is a hack; we are accessing the expression out-of-sync with the position
        -- Currently, we reset `optionsPerPos` at the beginning of `delabPatterns` to avoid
        -- incorrectly considering annotations.
        withTheReader SubExpr ({ · with expr := ty }) $
          usingNames st.varNames[idx]! do
            withAppFnArgs (pure #[]) (fun pats => do pure $ pats.push (← delabVerbose))
where
  usingNames {α} (varNames : Array Name) (x : DelabM α) : DelabM α :=
    usingNamesAux 0 varNames x
  usingNamesAux {α} (i : Nat) (varNames : Array Name) (x : DelabM α) : DelabM α :=
    if i < varNames.size then
      withBindingBody varNames[i]! <| usingNamesAux (i+1) varNames x
    else
      x

/-- Skip `numParams` binders, and execute `x varNames` where `varNames` contains the new binder names. -/
private partial def skippingBinders {α} (numParams : Nat) (x : Array Name → DelabM α) : DelabM α :=
  loop numParams #[]
where
  loop : Nat → Array Name → DelabM α
    | 0,   varNames => x varNames
    | n+1, varNames => do
      let rec visitLambda : DelabM α := do
        let varName := (← getExpr).bindingName!.eraseMacroScopes
        -- Pattern variables cannot shadow each other
        if varNames.contains varName then
          let varName := (← getLCtx).getUnusedName varName
          withBindingBody varName do
            loop n (varNames.push varName)
        else
          withBindingBodyUnusedName fun id => do
            loop n (varNames.push id.getId)
      let e ← getExpr
      if e.isLambda then
        visitLambda
      else
        -- eta expand `e`
        let e ← forallTelescopeReducing (← inferType e) fun xs _ => do
          if xs.size == 1 && (← inferType xs[0]!).isConstOf ``Unit then
            -- `e` might be a thunk create by the dependent pattern matching compiler, and `xs[0]` may not even be a pattern variable.
            -- If it is a pattern variable, it doesn't look too bad to use `()` instead of the pattern variable.
            -- If it becomes a problem in the future, we should modify the dependent pattern matching compiler, and make sure
            -- it adds an annotation to distinguish these two cases.
            mkLambdaFVars xs (mkApp e (mkConst ``Unit.unit))
          else
            mkLambdaFVars xs (mkAppN e xs)
        withTheReader SubExpr (fun ctx => { ctx with expr := e }) visitLambda

/--
  Delaborate applications of "matchers" such as
  ```
  List.map.match_1 : {α : Type _} →
    (motive : List α → Sort _) →
      (x : List α) → (Unit → motive List.nil) → ((a : α) → (as : List α) → motive (a :: as)) → motive x
  ```
-/
@[scoped delab app]
def delabAppMatch : Delab := whenPPOption getPPNotation <| whenPPOption getPPMatch do
  checkDepth
  -- incrementally fill `AppMatchState` from arguments
  let st ← withAppFnArgs
    (do
      let (Expr.const c us) ← getExpr | failure
      let (some info) ← getMatcherInfo? c | failure
      let matcherTy ← instantiateTypeLevelParams (← getConstInfo c) us
      return { matcherTy, info : AppMatchState })
    (fun st => do
      if st.params.size < st.info.numParams then
        return { st with params := st.params.push (← getExpr) }
      else if st.motive.isNone then
        -- store motive argument separately
        let lamMotive ← getExpr
        let piMotive ← lambdaTelescope lamMotive fun xs body => mkForallFVars xs body
        -- TODO: pp.analyze has not analyzed `piMotive`, only `lamMotive`
        -- Thus the binder types won't have any annotations
        let piStx ← withTheReader SubExpr (fun cfg => { cfg with expr := piMotive }) delabVerbose
        let named ← getPPOption getPPAnalysisNamedArg
        return { st with motive := (piStx, lamMotive), motiveNamed := named }
      else if st.discrs.size < st.info.numDiscrs then
        let idx := st.discrs.size
        let discr ← delabVerbose
        if let some hName := st.info.discrInfos[idx]!.hName? then
          -- TODO: we should check whether the corresponding binder name, matches `hName`.
          -- If it does not we should pretty print this `match` as a regular application.
          return { st with discrs := st.discrs.push (← `(matchDiscr| $(mkIdent hName) : $discr)) }
        else
          return { st with discrs := st.discrs.push (← `(matchDiscr| $discr:term)) }
      else if st.rhss.size < st.info.altNumParams.size then
        /- We save the variables names here to be able to implement safe_shadowing.
           The pattern delaboration must use the names saved here. -/
        let (varNames, rhs) ← skippingBinders st.info.altNumParams[st.rhss.size]! fun varNames => do
          let rhs ← delabVerbose
          return (varNames, rhs)
        return { st with rhss := st.rhss.push rhs, varNames := st.varNames.push varNames }
      else
        return { st with moreArgs := st.moreArgs.push (← delabVerbose) })

  if st.discrs.size < st.info.numDiscrs || st.rhss.size < st.info.altNumParams.size then
    -- underapplied
    failure

  match st.discrs, st.rhss with
  | #[discr], #[] =>
    let stx ← `(nomatch $discr)
    return Syntax.mkApp stx st.moreArgs
  | _,        #[] => failure
  | _,        _   =>
    let pats ← delabPatterns st
    let stx ← do
      let (piStx, lamMotive) := st.motive.get!
      let opts ← getOptions
      -- TODO: disable the match if other implicits are needed?
      if ← pure st.motiveNamed <||> shouldShowMotive lamMotive opts then
        `(match (motive := $piStx) $[$st.discrs:matchDiscr],* with $[| $pats,* => $st.rhss]*)
      else
        `(match $[$st.discrs:matchDiscr],* with $[| $pats,* => $st.rhss]*)
    return Syntax.mkApp stx st.moreArgs

/--
  Delaborate applications of the form `(fun x => b) v` as `let_fun x := v; b`
-/
def delabLetFun : Delab := do
  let stxV ← withAppArg delabVerbose
  withAppFn do
    let Expr.lam n _ b _ ← getExpr | unreachable!
    let n ← getUnusedName n b
    let stxB ← withBindingBody n delabVerbose
    if ← getPPOption getPPLetVarTypes <||> getPPOption getPPAnalysisLetVarType then
      let stxT ← withBindingDomain delab
      `(let_fun $(mkIdent n) : $stxT := $stxV; $stxB)
    else
      `(let_fun $(mkIdent n) := $stxV; $stxB)

@[scoped delab mdata]
def delabMData : Delab := do
  -- checkDepth
  if let some _ := inaccessible? (← getExpr) then
    let s ← withMDataExpr delabVerbose
    if (← read).inPattern then
      `(.($s)) -- We only include the inaccessible annotation when we are delaborating patterns
    else
      return s
  else if isLetFun (← getExpr) && getPPNotation (← getOptions) then
    withMDataExpr <| delabLetFun
  else if let some _ := isLHSGoal? (← getExpr) then
    withMDataExpr <| withAppFn <| withAppArg <| delabVerbose
  else
    withMDataOptions delabVerbose

/--
Check for a `Syntax.ident` of the given name anywhere in the tree.
This is usually a bad idea since it does not check for shadowing bindings,
but in the delaborator we assume that bindings are never shadowed.
-/
partial def hasIdent (id : Name) : Syntax → Bool
  | Syntax.ident _ _ id' _ => id == id'
  | Syntax.node _ _ args   => args.any (hasIdent id)
  | _                      => false

/--
Return `true` iff current binder should be merged with the nested
binder, if any, into a single binder group:
* both binders must have same binder info and domain
* they cannot be inst-implicit (`[a b : A]` is not valid syntax)
* `pp.binderTypes` must be the same value for both terms
* prefer `fun a b` over `fun (a b)`
-/
private def shouldGroupWithNext : DelabM Bool := do
  let e ← getExpr
  let ppEType ← getPPOption (getPPBinderTypes e)
  let go (e' : Expr) := do
    let ppE'Type ← withBindingBody `_ $ getPPOption (getPPBinderTypes e)
    pure $ e.binderInfo == e'.binderInfo &&
      e.bindingDomain! == e'.bindingDomain! &&
      e'.binderInfo != BinderInfo.instImplicit &&
      ppEType == ppE'Type &&
      (e'.binderInfo != BinderInfo.default || ppE'Type)
  match e with
  | Expr.lam _ _     e'@(Expr.lam _ _ _ _) _     => go e'
  | Expr.forallE _ _ e'@(Expr.forallE _ _ _ _) _ => go e'
  | _ => pure false
where
  getPPBinderTypes (e : Expr) :=
    if e.isForall then getPPPiBinderTypes else getPPFunBinderTypes

def withBindingBodyUnusedName {α} (d : Syntax → DelabM α) : DelabM α := do
  let n ← getUnusedName (← getExpr).bindingName! (← getExpr).bindingBody!
  -- let n := n.append "domVar"
  let stxN ← annotateCurPos (mkIdent n)
  withBindingBody n $ d stxN


private partial def delabBinders (delabGroup : Array Syntax → Syntax → Delab) : optParam (Array Syntax) #[] → Delab
  -- Accumulate names (`Syntax.ident`s with position information) of the current, unfinished
  -- binder group `(d e ...)` as determined by `shouldGroupWithNext`. We cannot do grouping
  -- inside-out, on the Syntax level, because it depends on comparing the Expr binder types.
  | curNames => do
    -- if ← shouldGroupWithNext then
    --   -- group with nested binder => recurse immediately
    --   withBindingBodyUnusedName fun stxN => delabBinders delabGroup (curNames.push stxN)
    -- else
      -- don't group => delab body and prepend current binder group
      let (stx, stxN) ← withBindingBodyUnusedName fun stxN => return (← delab, stxN)
      delabGroup (curNames.push stxN) stx

@[scoped delab lam]
def delabLam : Delab :=
  delabBinders fun curNames stxBody => do
    let e ← getExpr
    -- checkExprDepth e
    let stxT ← withBindingDomain delab
    let ppTypes := true
    let usedDownstream := curNames.any (fun n => hasIdent n.getId stxBody)

    -- leave lambda implicit if possible
    -- TODO: for now we just always block implicit lambdas when delaborating. We can revisit.
    -- Note: the current issue is that it requires state, i.e. if *any* previous binder was implicit,
    -- it doesn't seem like we can leave a subsequent binder implicit.
    let blockImplicitLambda := true
    /-
    let blockImplicitLambda := expl ||
      e.binderInfo == BinderInfo.default ||
      -- Note: the following restriction fixes many issues with roundtripping,
      -- but this condition may still not be perfectly in sync with the elaborator.
      e.binderInfo == BinderInfo.instImplicit ||
      Elab.Term.blockImplicitLambda stxBody ||
      usedDownstream
    -/

    if !blockImplicitLambda then
      pure stxBody
    else
      let defaultCase (_ : Unit) : Delab := do
        if ppTypes then
          -- "default" binder group is the only one that expects binder names
          -- as a term, i.e. a single `Syntax.ident` or an application thereof
          let stxCurNames ←
            if curNames.size > 1 then
              `($(curNames.get! 0) $(curNames.eraseIdx 0)*)
            else
              pure $ curNames.get! 0;
          `(funBinder| ($stxCurNames : $stxT))
        else
          pure curNames.back  -- here `curNames.size == 1`
      let group ← match e.binderInfo, ppTypes with
        | BinderInfo.default,        _      => defaultCase ()
        | BinderInfo.implicit,       true   => `(funBinder| {$curNames* : $stxT})
        | BinderInfo.implicit,       false  => `(funBinder| {$curNames*})
        | BinderInfo.strictImplicit, true   => `(funBinder| ⦃$curNames* : $stxT⦄)
        | BinderInfo.strictImplicit, false  => `(funBinder| ⦃$curNames*⦄)
        | BinderInfo.instImplicit,   _     =>
          if usedDownstream then `(funBinder| [$curNames.back : $stxT])  -- here `curNames.size == 1`
          else  `(funBinder| [$stxT])
      let (binders, stxBody) :=
        match stxBody with
        | `(fun $binderGroups* => $stxBody) => (#[group] ++ binderGroups, stxBody)
        | _                                 => (#[group], stxBody)
      -- if ← getPPOption getPPUnicodeFun then
      `(fun $binders* ↦ $stxBody)
      -- else
      --   `(fun $binders* => $stxBody)

/--
Similar to `delabBinders`, but tracking whether `forallE` is dependent or not.

See issue #1571
-/
private partial def delabForallBinders (delabGroup : Array Syntax → Bool → Syntax → Delab) (curNames : Array Syntax := #[]) (curDep := false) : Delab := do
  let dep := !(← getExpr).isArrow
  if !curNames.isEmpty && dep != curDep then
    -- don't group
    delabGroup curNames curDep (← delabVerbose)
  else
    let curDep := dep
    if ← shouldGroupWithNext then
      -- group with nested binder => recurse immediately
      withBindingBodyUnusedName fun stxN => delabForallBinders delabGroup (curNames.push stxN) curDep
    else
      -- don't group => delab body and prepend current binder group
      let (stx, stxN) ← withBindingBodyUnusedName fun stxN => return (← delab, stxN)
      delabGroup (curNames.push stxN) curDep stx


@[scoped delab letE]
def delabLetE : Delab := do
  -- checkDepth
  let Expr.letE n t v b _ ← getExpr | unreachable!
  let n ← getUnusedName n b
  let stxV ← descend v 1 delabVerbose
  let stxB ← withLetDecl n t v fun fvar =>
    let b := b.instantiate1 fvar
    descend b 2 delabVerbose
  if ← getPPOption getPPLetVarTypes <||> getPPOption getPPAnalysisLetVarType then
    let stxT ← descend t 0 delab
    `(let $(mkIdent n) : $stxT := $stxV; $stxB)
  else `(let $(mkIdent n) := $stxV; $stxB)



@[scoped delab app.dite]
def delabDIte : Delab := whenPPOption getPPNotation do
  -- Note: we keep this as a delaborator for now because it actually accesses the expression.
  guard $ (← getExpr).getAppNumArgs == 5
  let c ← withAppFn $ withAppFn $ withAppFn $ withAppArg delabVerbose
  let (t, h) ← withAppFn $ withAppArg $ delabBranch none
  let (e, _) ← withAppArg $ delabBranch h
  `(if $(mkIdent h):ident : $c then $t else $e)
where
  delabBranch (h? : Option Name) : DelabM (Syntax × Name) := do
    let e ← getExpr
    guard e.isLambda
    let h ← match h? with
      | some h => return (← withBindingBody h delabVerbose, h)
      | none   => withBindingBodyUnusedName fun h => do
        return (← delabVerbose, h.getId)

@[scoped delab app.cond]
def delabCond : Delab := whenPPOption getPPNotation do
  -- checkDepth
  guard $ (← getExpr).getAppNumArgs == 4
  let c ← withAppFn $ withAppFn $ withAppArg delabVerbose
  let t ← withAppFn $ withAppArg delabVerbose
  let e ← withAppArg delabVerbose
  `(bif $c then $t else $e)

@[scoped delab app.namedPattern]
def delabNamedPattern : Delab := do
  -- checkDepth
  -- Note: we keep this as a delaborator because it accesses the DelabM context
  guard (← read).inPattern
  guard $ (← getExpr).getAppNumArgs == 4
  let x ← withAppFn $ withAppFn $ withAppArg delab
  let p ← withAppFn $ withAppArg delab
  -- TODO: we should hide `h` if it has an inaccessible name and is not used in the rhs
  let h ← withAppArg delab
  guard x.raw.isIdent
  `($x:ident@$h:ident:$p:term)

-- Sigma and PSigma delaborators
def delabSigmaCore (sigma : Bool) : Delab := whenPPOption getPPNotation do
  checkDepth
  guard $ (← getExpr).getAppNumArgs == 2
  guard $ (← getExpr).appArg!.isLambda
  withAppArg do
    let α ← withBindingDomain delab
    let bodyExpr := (← getExpr).bindingBody!
    withBindingBodyUnusedName fun n => do
      let b ← delabVerbose
      if bodyExpr.hasLooseBVars then
        if sigma then `(($n:ident : $α) × $b) else `(($n:ident : $α) ×' $b)
      else
        if sigma then `((_ : $α) × $b) else `((_ : $α) ×' $b)

@[scoped delab app.Sigma]
def delabSigma : Delab := delabSigmaCore (sigma := true)

@[scoped delab app.PSigma]
def delabPSigma : Delab := delabSigmaCore (sigma := false)

partial def delabDoElems : DelabM (List Syntax) := do
  let e ← getExpr
  checkExprDepth e
  if e.isAppOfArity ``Bind.bind 6 then
    -- Bind.bind.{u, v} : {m : Type u → Type v} → [self : Bind m] → {α β : Type u} → m α → (α → m β) → m β
    let α := e.getAppArgs[2]!
    let ma ← withAppFn $ withAppArg delabVerbose
    withAppArg do
      match (← getExpr) with
      | Expr.lam _ _ body _ =>
        withBindingBodyUnusedName fun n => do
          if body.hasLooseBVars then
            prependAndRec `(doElem|let $n:term ← $ma:term)
          else if α.isConstOf ``Unit || α.isConstOf ``PUnit then
            prependAndRec `(doElem|$ma:term)
          else
            prependAndRec `(doElem|let _ ← $ma:term)
      | _ => failure
  else if e.isLet then
    let Expr.letE n t v b _ ← getExpr | unreachable!
    let n ← getUnusedName n b
    let stxT ← descend t 0 delab
    let stxV ← descend v 1 delabVerbose
    withLetDecl n t v fun fvar =>
      let b := b.instantiate1 fvar
      descend b 2 $
        prependAndRec `(doElem|let $(mkIdent n) : $stxT := $stxV)
  else
    let stx ← delabVerbose
    return [← `(doElem|$stx:term)]
  where
    prependAndRec x : DelabM _ := List.cons <$> x <*> delabDoElems

-- @[scoped delab app.Bind.bind]
-- def delabDo : Delab := whenPPOption getPPNotation do
--   guard <| (← getExpr).isAppOfArity ``Bind.bind 6
--   let elems ← delabDoElems
--   let items ← elems.toArray.mapM (`(doSeqItem|$(·):doElem))
--   `(do $items:doSeqItem*)

structure NameGroups where
  constNames : Array <| Name × Nat := #[]
  freeVarNames : Array Name := #[]
  domVarNames : Array Name := #[]
deriving Inhabited, Repr

def NameGroups.append (base: NameGroups) (n: Name)(d: Nat): NameGroups :=
  match n with
  | Name.str p "freeVar"  =>
    match p with
    | Name.str q "domVar"  => ⟨base.constNames, base.freeVarNames.push q, base.domVarNames⟩
    | _ => ⟨base.constNames, base.freeVarNames.push p, base.domVarNames⟩
  | Name.str q "domVar"  => 
      ⟨base.constNames, base.freeVarNames, base.domVarNames.push q⟩
  | _ => ⟨base.constNames.push (n, d), base.freeVarNames, base.domVarNames⟩

def groupedNames (nd : Array <| Name × Nat) : NameGroups :=
  nd.foldl (fun gp (n, d) => gp.append n d) {}

def Name.purgeSuffix: Name → Name
  | Name.str p "freeVar"  =>
    Name.purgeSuffix p
  | Name.str q "domVar"  => 
    Name.purgeSuffix q
  | n => n


def lambdaStx?(stx : Syntax) : MetaM <| Option (Syntax × Array Syntax) := do
  match stx with
  | `(fun $args:funBinder* ↦ $body) =>
    return some (body, args)
  | `((fun $args:funBinder* ↦ $body)) =>
    return some (body, args)
  | _ => return none

#check Parser.mkIdent

def proofWithProp? (stx : Syntax) : MetaM <| Option (Syntax × Syntax) := do
  match stx with
  | `(($stx =: $typeStx)) =>    
    return some (stx, typeStx)
  | _ => return none

def getVar (stx: Syntax) : Option Name := 
match stx with
| `(funBinder|($n:ident)) => some n.getId
| `(funBinder|($n:ident : $_)) => some n.getId
| `(funBinder|{$n:ident : $_}) => some n.getId
| `(funBinder|⦃$n:ident : $_⦄) => some n.getId
| _ => none

def namedArgument? (stx : Syntax) : MetaM <| Option (Syntax × Syntax) := do
  match stx with
  | `(namedArgument|($n:ident := $stx)) =>    
    return some (stx, n)
  | _ => return none

-- @[scoped delab fvar]
-- def delabFVar : Delab := do
-- let Expr.fvar fvarId ← getExpr | unreachable!
-- try
--   let l ← fvarId.getDecl
--   maybeAddBlockImplicit (mkIdent <| l.userName.append "freeVar")
-- catch _ =>
--   -- loose free variable, use internal name
--   maybeAddBlockImplicit <| mkIdent <| fvarId.name.append "freeVar"



end LeanAide.Meta

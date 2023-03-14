import Aesop.Search.Main
import Lean
open Aesop Lean Meta

def applyConstRuleMember (decl: Name)(p: Float) : MetaM RuleSetMember := do
  let type := (← getConstInfo decl).type
  let indexingMode ←  IndexingMode.targetMatchingConclusion type
  let name : RuleName := {
    name := decl
    builder := BuilderName.apply
    phase := PhaseName.«unsafe»
    scope := ScopeName.global
  }
  return RuleSetMember.unsafeRule {
    name:= name
    indexingMode := indexingMode
    usesBranchState := false
    extra:= ⟨⟨p⟩⟩
    tac := .applyConst decl}
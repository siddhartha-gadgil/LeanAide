import Lean
import LeanAide.Config


def resourcesDirCheck : IO Bool := do
 try
  let _ ← resourcesDir
  return true
 catch _ =>
  return false

def searchDataCheck : IO Bool := do
 try
  let _ ← searchData
  return true
 catch _ =>
  return false

/-- info: true -/
#guard_msgs in
#eval resourcesDirCheck

/-- info: true -/
#guard_msgs in
#eval searchDataCheck

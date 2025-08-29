import LeanAide.Responses
import LeanAide.ResponseExt

namespace LeanAide

open Lean Json

/-- info: {"result": "success", "data": {"extra": "payload"}} -/
#guard_msgs in
#eval responseFromTask "echo" {}
  (json% {"extra": "payload"})

/-- info: {"theorem": "{n | Odd n}.Infinite", "result": "success"} -/
#guard_msgs in
#eval responseFromTask "translate_thm" {} (json% {"text": "There are infinitely many odd numbers."})

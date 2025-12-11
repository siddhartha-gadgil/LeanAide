import LeanAide.Responses
import LeanAide.ResponseExt

namespace LeanAide

open Lean Json

/-- info: {"result": "success", "data": {"extra": "payload"}} -/
#guard_msgs in
#eval responseFromTask "echo" {}
  (json% {"extra": "payload"})

/--
info: Querying: {"openAI":{"model":"gpt-5.1","authHeader?":null}}
Reading from cache: /home/gadgil/code/LeanAide/.leanaide_cache/chat/13762311000014589115_17650432015256907884_11050509263652133987.json
---
info: {"theorem": "{n | Odd n}.Infinite", "result": "success"}
-/
#guard_msgs in
#eval responseFromTask "translate_thm" {} (json% {"text": "There are infinitely many odd numbers."})

import LeanCodePrompts
import LeanCodePrompts.CheckParse

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false


def main : IO Unit :=
  IO.println s!"Hello, {hello}!"

import Lean

open Lean Meta Elab Tactic Parser 

#eval 3

#check IO.asTask

-- From Lean 4 source

-- #eval id (α := IO _) do
--   let t1 ← IO.asTask $ Nat.forM 10 fun _ => IO.println "hi";
--   let t2 ← IO.asTask $ Nat.forM 10 fun _ => IO.println "ho";
--   IO.ofExcept t1.get

-- #eval id (α := IO _) do
--   let t1 ← IO.mapTask IO.println (Task.spawn fun _ => "ha");
--   pure ()

-- #eval id (α := IO _) do
--   let t1 ← IO.bindTask (Task.spawn fun _ => "hu") fun s =>
--     IO.asTask (IO.println s);
--   pure ()

-- #eval id (α := IO _) do
--   let t1 ← IO.asTask do {
--     let c ← IO.checkCanceled;
--     IO.println (if c then "canceled!" else "done!")
--   };
--   pure ()

-- #eval id (α := IO _) do
--   let t1 ← IO.asTask do {
--     let c ← IO.checkCanceled;
--     IO.println (if c then "canceled! 2" else "done! 2")
--   };
--   IO.cancel t1;
--   discard $ IO.wait t1;
--   pure ()

#eval IO.waitAny [
  Task.spawn fun _ => dbgSleep 2 fun _ => "A",
  Task.spawn fun _ => dbgSleep 3 fun _ => "B",
  Task.spawn fun _ => dbgSleep 1 fun _ => "C"
]

def slowFibIO : Nat → IO Nat
| 0 => pure 0
| 1 => pure 1
| n + 2 => do return (← slowFibIO (n)) + (←  slowFibIO (n + 1))   

elab "run_io_task" : tactic => do
  let _  ← (IO.asTask <| 
    do IO.FS.writeFile ("rawdata/testIO.txt") s!"Computed: {← slowFibIO 34} at {← IO.monoMsNow}"
    ).toIO
  return ()

example : 5 = 5 := by
  run_io_task
  rfl


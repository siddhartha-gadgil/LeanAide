import Lean
open Lean Std

partial def camelSplitAux (s : String)(accum: List String) : List String :=
  if s.length == 0 then accum
  else 
    let head := s.decapitalize.takeWhile (fun c => 'a' ≤ c)
    if head.length = 0 then accum ++ [s]
    else
      let tail := s.drop (head.length)
      camelSplitAux tail (accum ++ [head])

def camelSplit(s : String) : List String :=
  camelSplitAux s []

#eval camelSplit "CamelCaseWord"

def fullSplit (s : String) : List String :=
  let parts := s.splitOn "_"
  parts.bind (fun s => camelSplit s)

#eval fullSplit "CamelCaseWord"
#eval fullSplit "snake_caseBut_wordWithCamel"

initialize binNamesCache : IO.Ref (Array String) ← IO.mkRef (#[])

initialize binNameMapCache : IO.Ref (HashMap (List String) String) 
  ← IO.mkRef (HashMap.empty)

def binNames : IO (Array String) := do 
  let cacheStr ← binNamesCache.get
  if cacheStr.size > 0 then 
    return cacheStr
  else 
    let all ← 
      IO.FS.lines (System.mkFilePath ["data", "binport_names.txt"])
    let filtered := all.filter (fun s => s.length > 0)
    let filtered := filtered.toList
    binNamesCache.set filtered.toArray
    return all.filter (fun s => !(s.contains  '.'))

def binNameMap : IO (HashMap (List String) String) := do
  let cacheMap ← binNameMapCache.get
  if cacheMap.isEmpty then 
    let names ← binNames
    let res := names.foldl 
      (fun m s => m.insert (fullSplit s) s) (HashMap.empty)
    binNameMapCache.set res
    return res
  else
    return cacheMap

def withoutIs : List String → List String
| x :: ys => if x = "is" || x = "has" then ys else x :: ys
| [] => []

def getBinName(s : String) : IO <| Option String := do
  let all ← binNames
  let split := fullSplit s
  -- let all := #[]
  let res := all.find? (fun s => split = fullSplit s)
  match res with
  | some s => return some s
  | none =>
    match split with
    | x :: ys => 
      if x = "is" || x = "has" 
      then return  all.find? (fun s => ys = withoutIs (fullSplit s))
      else return none
    | _ => return none




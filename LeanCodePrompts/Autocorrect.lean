
partial def camelSplitAux (s : String)(accum: List String) : List String :=
  if s.length == 0 then accum
  else 
    let head := s.decapitalize.takeWhile (fun c => 'a' ≤ c)
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

def binNames : IO (Array String) := do 
  let all ← 
    IO.FS.lines (System.mkFilePath ["data", "binport_names.txt"])
  return all.filter (fun s => !(s.contains  '.'))


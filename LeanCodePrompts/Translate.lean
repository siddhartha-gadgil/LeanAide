import Lean
import Lean.Meta
import Lean.Parser
import Std
import LeanCodePrompts.CheckParse
import LeanCodePrompts.ParseJson
import LeanCodePrompts.Autocorrect
import LeanCodePrompts.KeywordSummary.KeywordExtraction
open Lean Meta Std

open Lean Elab Parser Command

def egJsonSentenceSim : String := "[{'theorem': '{p : ℕ} [fact (nat.prime p)] : p % 2 = 1 ↔ p ≠ 2', 'doc_string': 'A prime `p` satisfies `p % 2 = 1` if and only if `p ≠ 2`.'}, {'theorem': '{n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3', 'doc_string': 'A natural number is odd iff it has residue `1` or `3` mod `4`'}, {'theorem': '{p : ℕ} (hp : nat.prime p) : p.factorization = finsupp.single p 1', 'doc_string': 'The only prime factor of prime `p` is `p` itself, with multiplicity `1`'}, {'theorem': '{m n : ℕ} : even (m ^ n) ↔ even m ∧ n ≠ 0', 'doc_string': ' If `m` and `n` are natural numbers, then the natural number `m^n` is even if and only if `m` is even and `n` is positive.'}]"

def egSen := "[{\"statement\": \"theorem nat.prime.mod_two_eq_one_iff_ne_two {p : ℕ} [fact (nat.prime p)] : p % 2 = 1 ↔ p ≠ 2\", \"doc_string\": \"A prime `p` satisfies `p % 2 = 1` if and only if `p ≠ 2`.\", \"theorem\": \"{p : ℕ} [fact (nat.prime p)] : p % 2 = 1 ↔ p ≠ 2\"}, {\"statement\": \"theorem nat.odd_mod_four_iff {n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3\", \"doc_string\": \"A natural number is odd iff it has residue `1` or `3` mod `4`\", \"theorem\": \"{n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3\"}, {\"statement\": \"theorem nat.factorization_eq_zero_iff (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1\", \"doc_string\": \"The only numbers with empty prime factorization are `0` and `1`\", \"theorem\": \"(n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1\"}, {\"statement\": \"theorem nat.prime.factorization {p : ℕ} (hp : nat.prime p) : p.factorization = finsupp.single p 1\", \"doc_string\": \"The only prime factor of prime `p` is `p` itself, with multiplicity `1`\", \"theorem\": \"{p : ℕ} (hp : nat.prime p) : p.factorization = finsupp.single p 1\"}, {\"statement\": \"theorem nat.even_pow {m n : ℕ} : even (m ^ n) ↔ even m ∧ n ≠ 0\", \"doc_string\": \" If `m` and `n` are natural numbers, then the natural number `m^n` is even if and only if `m` is even and `n` is positive.\", \"theorem\": \"{m n : ℕ} : even (m ^ n) ↔ even m ∧ n ≠ 0\"}, {\"statement\": \"theorem is_prime_pow_iff_unique_prime_dvd {n : ℕ} : is_prime_pow n ↔ ∃! (p : ℕ), nat.prime p ∧ p ∣ n\", \"doc_string\": \" An equivalent definition for prime powers: `n` is a prime power iff there is a unique prime dividing it.\", \"theorem\": \"{n : ℕ} : is_prime_pow n ↔ ∃! (p : ℕ), nat.prime p ∧ p ∣ n\"}, {\"statement\": \"theorem nat.factorization_inj  : set.inj_on nat.factorization {x : ℕ | x ≠ 0}\", \"doc_string\": \"Every nonzero natural number has a unique prime factorization\", \"theorem\": \" : set.inj_on nat.factorization {x : ℕ | x ≠ 0}\"}, {\"statement\": \"theorem nat.mem_factors_mul_left {p a b : ℕ} (hpa : p ∈ a.factors) (hb : b ≠ 0) : p ∈ (a * b).factors\", \"doc_string\": \"If `p` is a prime factor of `a` then `p` is also a prime factor of `a * b` for any `b > 0`\", \"theorem\": \"{p a b : ℕ} (hpa : p ∈ a.factors) (hb : b ≠ 0) : p ∈ (a * b).factors\"}, {\"statement\": \"theorem gaussian_int.prime_iff_mod_four_eq_three_of_nat_prime (p : ℕ) [hp : fact (nat.prime p)] : prime ↑p ↔ p % 4 = 3\", \"doc_string\": \"A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`\", \"theorem\": \"(p : ℕ) [hp : fact (nat.prime p)] : prime ↑p ↔ p % 4 = 3\"}]"

def sentenceSimPairs(s: String) : MetaM  <| Except String (Array (String × String)) := do
  let json ← readJson (s) 
  -- logInfo "obtained json"
  match json.getArr? with
  | Except.ok jsonArr => do
    let pairs ←  jsonArr.mapM fun json => do
      let docstring : String ←  
        match (json.getObjVal? "doc_string") with
        | Except.error e => throwError s!"Error {e} while getting doc_string"
        | Except.ok js => 
          match js.getStr? with
          | Except.error e => throwError s!"Error {e} while processing {js} as string"  
          | Except.ok s => pure s
      let thm ←  match (json.getObjVal? "theorem") with
        | Except.error e => throwError s!"Error {e} while getting doc_string"
        | Except.ok js => 
          match js.getStr? with
          | Except.error e => throwError s!"Error {e} while processing {js} as string"  
          | Except.ok s => pure s
      return (docstring, thm)
    return Except.ok pairs
  | Except.error e => return Except.error e

#eval sentenceSimPairs egSen

def makePrompt(prompt : String)(pairs: Array (String × String)) : String := 
      pairs.foldr (fun  (ds, thm) acc => 
        -- acc ++ "/-- " ++ ds ++" -/\ntheorem" ++ thm ++ "\n" ++ "\n"
s!"/-- {ds} -/
theorem {thm} :=

{acc}"
          ) s!"/-- {prompt} -/
theorem "


def openAIKey : IO (Option String) := IO.getEnv "OPENAI_API_KEY"

def openAIQuery(prompt: String)(n: Nat := 1)(temp : JsonNumber := ⟨2, 1⟩) : MetaM Json := do
  let key? ← openAIKey
  let key := key?.get!
  let dataJs := Json.mkObj [("model", "code-davinci-002"), ("prompt", prompt), ("temperature", Json.num temp), ("n", n), ("max_tokens", 150), ("stop", Json.arr #[":=", "-/"])]
  let data := dataJs.pretty
  let out ←  IO.Process.output {
        cmd:= "curl", 
        args:= #["https://api.openai.com/v1/completions",
        "-X", "POST",
        "-H", "Authorization: Bearer " ++ key,
        "-H", "Content-Type: application/json",
        "--data", data]}
  -- logInfo "OpenAI query answered"
  readJson out.stdout

def egBlob' := "[{ \"text\" : \"{p : ℕ} (hp : Nat.Prime p) :  p = 2 ∨ p % 2 = 1 \"},
   { \"text\" : \"(p : ℕ) :  Nat.Prime p ↔ p = 2 ∨ p % 2 = 1 \"},
   { \"text\" : \"{p : ℕ} (hp : Nat.Prime p) : p = 2 ∨ p % 2 = 1 \"},
   { \"text\" : \"(n : ℕ) (hp : Nat.Prime n) : n = 2 ∨ n % 2 = 1 \"},
   { \"text\" : \"{p : ℕ} (hp : Nat.Prime p) : p = 2 ∨ p % 2 = 1 \"},
   { \"text\" : \"Nonsense output to test filtering\"}]"

def caseMapProc (s: String) : IO String := do
  let tmpFile := System.mkFilePath ["web_serv/tmp.json"]
  IO.FS.writeFile tmpFile s
  let out ← 
    IO.Process.output {cmd:= "./amm", args := #["scripts/simplemap.sc"]}
  return out.stdout

initialize webCache : IO.Ref (HashMap String String) ← IO.mkRef (HashMap.empty)

initialize pendingQueries : IO.Ref (HashSet String) 
    ← IO.mkRef (HashSet.empty)

def getCached? (s: String) : IO (Option String) := do
  let cache ← webCache.get
  return cache.find? s

def cache (s jsBlob: String)  : IO Unit := do
  let cache ← webCache.get
  webCache.set (cache.insert s jsBlob)
  return ()

partial def pollCache (s : String) : IO String := do
  let cache ← webCache.get
  match cache.find? s with
  | some jsBlob => return jsBlob
  | none => do
    IO.sleep 200
    pollCache s

initialize webCacheJson : IO.Ref (HashMap String Json) ← IO.mkRef (HashMap.empty)

initialize pendingJsonQueries : IO.Ref (HashSet String) 
    ← IO.mkRef (HashSet.empty)

def getCachedJson? (s: String) : IO (Option Json) := do
  let cache ← webCacheJson.get
  return cache.find? s

def cacheJson (s: String)(js: Json)  : IO Unit := do
  let cache ← webCacheJson.get
  webCacheJson.set (cache.insert s js)
  return ()

partial def pollCacheJson (s : String) : IO Json := do
  let cache ← webCacheJson.get
  match cache.find? s with
  | some jsBlob => return jsBlob
  | none => do
    IO.sleep 200
    pollCacheJson s

def getCodeJsonBlob (s: String) : TermElabM String := do
  match ← getCached? s with
  | some s => return s
  | none =>    
    let pending ←  pendingQueries.get
    if pending.contains s then
      IO.println "Polling" 
      pollCache s
    else 
      let pending ←  pendingQueries.get
      pendingQueries.set (pending.insert s)
      let out ←  
        IO.Process.output {cmd:= "curl", args:= 
          #["-X", "POST", "-H", "Content-type: application/json", "-d", s, "localhost:5000/post_json"]}
      let res := out.stdout  
          -- ← caseMapProc out.stdout
      let pending ←  pendingQueries.get
      pendingQueries.set (pending.erase s)
      if out.exitCode = 0 then cache s res 
        else throwError m!"Web query error: {out.stderr}"
      return res
  -- return out.stdout

def hasElab (s: String)(limit : Option Nat := none) : TermElabM Bool := do
    -- (elabThmTrans s).map (fun e => e.toBool)
  let elab? ← polyElabThmTrans s limit
  match elab? with
  | Except.error _ => return Bool.false
  | Except.ok els => return !els.isEmpty

def hasElabCore (s: String)(limit : Option Nat := none) : CoreM Bool := 
  (hasElab s limit).run'.run'

def parsedThmsPrompt : IO (Array String) := do
  let file := System.mkFilePath ["data/parsed_thms.txt"]
  IO.FS.lines file


def elabThmSplit(start? size?: Option Nat := none) : TermElabM ((Array String) × (Array String)) := do 
  let deps ← parsedThmsPrompt
  let deps := deps.toList.drop (start?.getD 0)
  let deps := deps.take (size?.getD (deps.length))
  let deps := deps.toArray
  let mut succ: Array String := Array.empty
  let mut fail: Array String := Array.empty
  let mut count := start?.getD 0
  let succFile := System.mkFilePath ["data/elab_thms.txt"]
  let h ← IO.FS.Handle.mk succFile IO.FS.Mode.append Bool.false
  IO.println s!"total: {deps.size}"
  for thm in deps do
    IO.println s!"parsing theorem {thm}"
    let chk ←  hasElab thm (some 25)
    count := count + 1
    if chk then
      succ := succ.push thm
      h.putStrLn thm
    else
      fail := fail.push thm
    IO.println s!"parsed: {count}"
    IO.println s!"elaborated: {succ.size}"
  return (succ, fail)

def elabThmSplitCore(start? size?: Option Nat := none) : CoreM ((Array String) × (Array String)) := 
  (elabThmSplit start? size?).run'.run'

def getCodeJson (s: String)(numSim : Nat:= 10)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM Json := do
  -- IO.println s!"initially pending : {(← pendingJsonQueries.get).size}"
  match ← getCachedJson? s with
  | some js => return js
  | none =>    
    -- IO.println s!"poll-check pending : {(← pendingJsonQueries.get).size}"
    let pending ←  pendingJsonQueries.get
    if pending.contains s then pollCacheJson s 
    else 
      let pending ←  pendingJsonQueries.get
      pendingJsonQueries.set (pending.insert s)
      let (pairs, IOOut) ← getPairs
      let prompt := makePrompt s pairs
      dbg_trace prompt
      -- IO.println s!"pending : {(← pendingJsonQueries.get).size}"
      let fullJson ← openAIQuery prompt 5 
      let outJson := (fullJson.getObjVal? "choices").toOption.get!
      -- logInfo s!"query gave: {outJson}"
      let pending ←  pendingJsonQueries.get
      pendingJsonQueries.set (pending.erase s)
      if IOOut.exitCode = 0 then cacheJson s outJson 
        else throwError m!"Web query error: {IOOut.stderr}"
      return outJson
  where getPairs : TermElabM (Array (String × String) × IO.Process.Output) := do
      let simJsonOut ←  
        IO.Process.output {cmd:= "curl", args:= 
          #["-X", "POST", "-H", "Content-type: application/json", "-d", s ++ s!" top_K {numSim}", "localhost:5000/similar_json"]}
      let pairs? ← sentenceSimPairs simJsonOut.stdout
      let allPairs := pairs?.toOption.get!
      let kwPairs ←  keywordBasedPrompts docPair s scoreBound matchBound
      let allPairs := (allPairs ++ kwPairs).toList.eraseDups.toArray
      let pairs -- := allPairs -- 
        ←  allPairs.filterM (fun (_, s) => do
            isElabPrompt s )
      let kwPairs ←  keywordBasedPrompts docPair s
      return (
          (pairs ++ kwPairs).toList.eraseDups.toArray, simJsonOut)



def arrayToExpr (output: Array String) : TermElabM Expr := do
  let output := output.toList.eraseDups.toArray
  let mut elaborated : Array String := Array.empty
  -- let mut failed: Nat := 0
  for out in output do
    let ployElab? ← polyElabThmTrans out
    match ployElab? with
      | Except.error _ => pure ()
      | Except.ok es =>
        for (_, s) in es do
          elaborated := elaborated.push s 
  -- let elaborated ← output.filterMapM (
  --   fun s => do 
  --     return (← elabThmTrans s).toOption.map (fun (_, s) => s))
  -- logInfo m!"elaborated: {elaborated.size} out of {output.size}, failed {failed}"
  if elaborated.isEmpty then do
    logWarning m!"No valid output from Codex; outputs below"
    for out in output do
      let polyOut ←  polyStrThmTrans out
      for str in polyOut do
        logWarning m!"{str}"
    mkSyntheticSorry (mkSort levelZero)
  else    
    let groupSorted ← groupFuncStrs elaborated
    let topStr := groupSorted[0]![0]!
    let thmExc ← elabFuncTyp topStr
    match thmExc with
    | Except.ok thm => return thm
    | Except.error s => throwError s

def arrayToExpr? (output: Array String) : TermElabM (Option (Expr× (Array String))) := do
  -- erase duplicates before calling
  let mut elaborated : Array String := Array.empty
  for out in output do
    let ployElab? ← polyElabThmTrans out
    match ployElab? with
      | Except.error _ => pure ()
      | Except.ok es =>
        for (_, s) in es do
          elaborated := elaborated.push s 
  if elaborated.isEmpty then return none
  else    
    let groupSorted ← groupFuncStrs elaborated
    let topStr := groupSorted[0]![0]!
    let thmExc ← elabFuncTyp topStr
    match thmExc with
    | Except.ok thm => return some (thm, elaborated)
    | Except.error s => throwError s


def textToExpr (s: String) : TermElabM Expr := do
  let json ← readJson s
  let outArr : Array String ← 
    match json.getArr? with
    | Except.ok arr => 
        let parsedArr : Array String ← 
          arr.filterMapM <| fun js =>
          match js.getStr? with
          | Except.ok str => pure (some str)
          | Except.error e => 
            throwError m!"json string expected but got {js}, error: {e}"
        pure parsedArr
    | Except.error e => throwError m!"json parsing error: {e}"
  let output := outArr
  arrayToExpr output

def textToExpr' (s: String) : TermElabM Expr := do
  let json ← readJson s
  let outArr : Array String ← 
    match json.getArr? with
    | Except.ok arr => 
        let parsedArr : Array String ← 
          arr.filterMapM <| fun js =>
            match js.getObjVal? "text" with
              | Except.ok jsstr =>
                match jsstr.getStr? with
                | Except.ok str => pure (some str)
                | Except.error e => 
                  throwError m!"json string expected but got {js}, error: {e}"
              | Except.error _ =>
                throwError m!"no text field"
        pure parsedArr
    | Except.error e => throwError m!"json parsing error: {e}"
  let output := outArr
  arrayToExpr output

def jsonToExprStrArray (json: Json) : TermElabM (Array String) := do
  let outArr : Array String ← 
    match json.getArr? with
    | Except.ok arr => 
        let parsedArr : Array String ← 
          arr.filterMapM <| fun js =>
            match js.getObjVal? "text" with
              | Except.ok jsstr =>
                match jsstr.getStr? with
                | Except.ok str => pure (some str)
                | Except.error e => 
                  throwError m!"json string expected but got {js}, error: {e}"
              | Except.error _ =>
                throwError m!"no text field"
        pure parsedArr
    | Except.error e => throwError m!"json parsing error: {e}"
  return outArr

def jsonToExpr' (json: Json) : TermElabM Expr := do
  let output ← jsonToExprStrArray json
  -- logInfo s!"output: {output}"
  arrayToExpr output


def textToExprStx' (s : String) : TermElabM (Expr × TSyntax `term) := do
  let e ← textToExpr' s
  let (stx : Term) ← (PrettyPrinter.delab e)
  return (e, stx)

elab "//-" cb:commentBody  : term => do
  let s := cb.raw.getAtomVal!
  let s := (s.dropRight 2).trim  
  let js ← getCodeJson  s
  let e ← jsonToExpr' js
  logInfo m!"{e}"
  return e

def promptToExpr? (s: String) : 
  TermElabM (Option (Expr × (Array String) )) := do
  let js ← getCodeJson  s
  let output ← jsonToExprStrArray js
  let output := output.toList.eraseDups.toArray
  let res ← arrayToExpr? output
  return res
  

elab "#theorem" name:ident " : " stmt:str ":=" prf:term : command => do
  let (fmlstmt, fmlstx) ← liftTermElabM none $ textToExprStx' egBlob' -- stmt.getString
  logInfoAt stmt m!"{fmlstmt}"
  elabCommand $ ← `(theorem $name:ident : $fmlstx:term := $prf:term)

elab "#example" stmt:str ":=" prf:term : command => do
  let (fmlstmt, fmlstx) ← liftTermElabM none $ textToExprStx' egBlob' -- stmt.getString
  logInfoAt stmt m!"{fmlstmt}"
  elabCommand $ ← `(example : $fmlstx:term := $prf:term)

-- #eval getCodeJsonBlob egPrompt
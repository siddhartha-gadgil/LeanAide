import $ivy.`com.lihaoyi::requests:0.7.0`
import $ivy.`com.lihaoyi::upickle:1.6.0`

val key = sys.env("OPENAI_API_KEY")

def postCode(prompt: String, stopTokens: List[String] = List(":=", "-/"), temp: Float = 0.2F) = 
    requests.post("https://api.openai.com/v1/completions", data=ujson.Obj("model" -> "code-davinci-002", "prompt" -> prompt, "temperature" -> temp, "max_tokens" -> 150, "stop" -> stopTokens), headers = Map("content-type" -> "application/json", "authorization" -> s"Bearer $key"))

def responseText(r: requests.Response) : String = {
    val js = upickle.default.read[ujson.Obj](r.data.array)
    val text = js("choices")(0)("text").str
    text
}

// An example for code generation
val pp = 
"""/-- A prime `p` satisfies `p % 2 = 1` if and only if `p ≠ 2`.-/
theorem {p : ℕ} [fact (nat.prime p)] : p % 2 = 1 ↔ p ≠ 2 :=

/-- A natural number is odd iff it has residue `1` or `3` mod `4`-/
theorem {n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3 := 

/-- The only numbers with empty prime factorization are `0` and `1`-/
theorem (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 := 

/-- The only prime factor of prime `p` is `p` itself, with multiplicity `1` -/
theorem {p : ℕ} (hp : nat.prime p) : p.factorization = finsupp.single p 1 := 

/-- Every prime number is either `2` or odd.-/
theorem """ 

// The example for code generation reversed for doc generation
val ppp = """theorem {p : ℕ} [fact (nat.prime p)] : p % 2 = 1 ↔ p ≠ 2 :=
  /- A prime `p` satisfies `p % 2 = 1` if and only if `p ≠ 2`.-/
  
  theorem {n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3 := 
  /- A natural number is odd iff it has residue `1` or `3` mod `4`-/
  
  theorem (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 :=
  /- The only numbers with empty prime factorization are `0` and `1`-/
  
  theorem {p : ℕ} (hp : nat.prime p) : p.factorization = finsupp.single p 1 :=
  /- The only prime factor of prime `p` is `p` itself, with multiplicity `1` -/
  
  theorem {p : ℕ} (hp : nat.prime p) : p = 2 ∨ p % 2 = 1 :=
  /-"""
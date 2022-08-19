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

val freeGroupPrompt = """/--Subgroups of torsion-free groups are torsion-free.-/
theorem {G : Type u_1} [group G] (tG : monoid.is_torsion_free G) (H : subgroup G) : monoid.is_torsion_free ↥H :=


/--Quotienting a group by its torsion subgroup yields a torsion free group.-/
theorem (G : Type u_1) [comm_group G] : monoid.is_torsion_free (G ⧸ torsion G) :=


/--Subgroups of additive torsion-free groups are additively torsion-free.-/
theorem {G : Type u_1} [add_group G] (tG : add_monoid.is_torsion_free G) (H : add_subgroup G) : add_monoid.is_torsion_free ↥H :=


/--The canonical injection from the type to the free group is an injection.-/
theorem {α : Type u} : function.injective free_group.of :=

/--  If two words correspond to the same element in the free group, then they have a common maximal reduction. This is the proof that the function that sends an element of the free group to its maximal reduction is well-defined. -/
theorem {α : Type u} {L₁ L₂ : list (α × bool)} [decidable_eq α] (H : free_group.mk L₁ = free_group.mk L₂) : free_group.reduce L₁ = free_group.reduce L₂ :=

/-- A word and its maximal reduction correspond to the same element of the free group.-/
theorem {α : Type u} {L : list (α × bool)} [decidable_eq α] : free_group.mk (free_group.reduce L) = free_group.mk L :=

/--  If two words have a common maximal reduction, then they correspond to the same element in the free group.-/
theorem {α : Type u} {L₁ L₂ : list (α × bool)} [decidable_eq α] (H : free_group.reduce L₁ = free_group.reduce L₂) : free_group.mk L₁ = free_group.mk L₂

/-- Every subgroup of a free group is a free group -/
theorem """


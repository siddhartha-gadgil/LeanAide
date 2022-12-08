from transformers import AutoTokenizer, AutoModelForCausalLM

print("loading model")

tokenizer = AutoTokenizer.from_pretrained("hoskinson-center/proofGPT-v0.1")

model = AutoModelForCausalLM.from_pretrained("hoskinson-center/proofGPT-v0.1").cuda()

print("loaded model")

prompt = "/--  If `m` and `n` are natural numbers, then the natural number `m^n` is even if and only if `m` is even and `n` is positive. -/\ntheorem {m n : ℕ} : even (m ^ n) ↔ even m ∧ n ≠ 0 :=\n\n/-- Odd Bernoulli numbers (greater than 1) are zero. -/\ntheorem {n : ℕ} (h_odd : odd n) (hlt : 1 < n) : bernoulli' n = 0 :=\n\n/-- A natural number is odd iff it has residue `1` or `3` mod `4` -/\ntheorem {n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3 :=\n\n/--  Euclid's theorem on the **infinitude of primes**. Here given in the form: for every `n`, there exists a prime number `p ≥ n`. -/\ntheorem (n : ℕ) : ∃ (p : ℕ), n ≤ p ∧ nat.prime p :=\n\n/-- **Cantor's theorem** -/\ntheorem (a : cardinal) : a < 2 ^ a :=\n\n/-- The cardinality of the antidiagonal of `n` is `n+1`. -/\ntheorem (n : ℕ) : ⇑multiset.card (multiset.nat.antidiagonal n) = n + 1 :=\n\n/-- The golden ratio is irrational. -/\ntheorem  : irrational golden_ratio :=\n\n/-- There are no perfect squares strictly between m² and (m+1)² -/\ntheorem {n m : ℕ} (hl : m * m < n) (hr : n < (m + 1) * (m + 1)) : ¬∃ (t : ℕ), t * t = n :=\n\n/-- Two natural numbers are equal if and only if the have the same multiples. -/\ntheorem {m n : ℕ} : (∀ (a : ℕ), m ∣ a ↔ n ∣ a) ↔ m = n :=\n\n/-- For any natural numbers n, a, and b, one of the following holds: 1. n < a 2. n ≥ b 3. n ∈ Ico a b -/\ntheorem (n a b : ℕ) : n < a ∨ b ≤ n ∨ n ∈ list.Ico a b :=\n\n/-- If `s.nth n = some aₙ` for some value `aₙ`, then there is also some value `aₘ` such that `s.nth = some aₘ` for `m ≤ n`. -/\ntheorem {α : Type u} (s : seq α) {aₙ : α} {n m : ℕ} (m_le_n : m ≤ n) (s_nth_eq_some : s.nth n = option.some aₙ) : ∃ (aₘ : α), s.nth m = option.some aₘ :=\n\n/-- The only numbers with empty prime factorization are `0` and `1` -/\ntheorem (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 :=\n\n/-- There are infinitely many odd natural numbers. -/\ntheorem "

input_ids = tokenizer.encode(prompt, return_tensors='pt').to('cuda')

colEq = tokenizer(":=").input_ids[0]

gen_tokens = model.generate(
    input_ids,
    do_sample=True,
    temperature=0.8,
    num_return_sequences=15,
    eos_token_id=colEq,
    max_length=1000,
)

print("Text computed")

gen_text = tokenizer.batch_decode(gen_tokens)
statement_text = ["theorem " + (s[len(prompt):].split(":=")[0]) for s in gen_text]
for s in statement_text:
    print(s)
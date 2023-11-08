# Note: you need to be using OpenAI Python v0.27.0 for the code below to work
import openai
import os

openai.api_key = os.getenv("AZURE_OPENAI_KEY")
openai.api_base = os.getenv("AZURE_OPENAI_ENDPOINT") 
openai.api_type = 'azure'
openai.api_version = '2023-05-15' # this might change in the future

deployment_name='leanaide-gpt4'

completion = openai.ChatCompletion.create(
  engine=deployment_name,
  n= 5,
  temperature=0.8,
  messages=[
        {"role": "system", "content": "You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. Follow EXACTLY the examples given"},
        {"role": "user", "content": "/-- The cardinality of the antidiagonal of `n` is `n+1`. -/"},
        {"role": "assistant", "content": "theorem (n : ℕ) : ⇑multiset.card (multiset.nat.antidiagonal n) = n + 1 :="},
        {"role": "user", "content": "/-- The golden ratio is irrational. -/"},
        {"role": "assistant", "content": "theorem  : irrational golden_ratio :="},
        {"role": "user", "content": "/-- There are no perfect squares strictly between m² and (m+1)² -/"},
        {"role": "user", "content": "/-- The only numbers with empty prime factorization are `0` and `1` -/"},        
        {"role": "assistant", "content": "theorem (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 :="},
        {"role": "user", "content": "/--  If `m` and `n` are natural numbers, then the natural number `m^n` is even if and only if `m` is even and `n` is positive. -/"},
        {"role": "assistant", "content": "theorem {m n : ℕ} : even (m ^ n) ↔ even m ∧ n ≠ 0 :="},
        {"role": "user", "content": "/-- Odd Bernoulli numbers (greater than 1) are zero. -/"},
        {"role": "assistant", "content": "theorem {n : ℕ} (h_odd : odd n) (hlt : 1 < n) : bernoulli' n = 0 :="},
        {"role": "user", "content": "/-- A natural number is odd iff it has residue `1` or `3` mod `4` -/"},
        {"role": "assistant", "content": "theorem {n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3 :="},
        {"role": "user", "content": "/--  Euclid's theorem on the **infinitude of primes**. Here given in the form: for every `n`, there exists a prime number `p ≥ n`. -/"},
        {"role": "assistant", "content": "theorem (n : ℕ) : ∃ (p : ℕ), n ≤ p ∧ nat.prime p :="},
        {"role": "user", "content": "/-- There are infinitely many odd numbers. -/"}
    ]
)

import sys
sys.stdout.reconfigure(encoding='utf-8')
print([choice.message['content'].encode().decode('unicode-escape').encode('latin1').decode('utf-8') for choice in completion.choices])

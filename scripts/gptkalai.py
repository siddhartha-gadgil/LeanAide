# Note: you need to be using OpenAI Python v0.27.0 for the code below to work
import openai

completion = openai.ChatCompletion.create(
  model="gpt-3.5-turbo",
  n= 7,
  temperature=1.5,
  messages=[
        {"role": "system", "content": "You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. Follow EXACTLY the examples given"},
        {"role": "user", "content": "Complete the following theorem:\ntheorem {m n : ℕ} :"},
        {"role": "assistant", "content": "theorem {m n : ℕ} : even (m ^ n) ↔ even m ∧ n ≠ 0 :="},
        {"role": "user", "content": "Complete the following theorem:\ntheorem {n : ℕ} (h_odd : odd n) (hlt : 1 < n) :"},
        {"role": "assistant", "content": "theorem {n : ℕ} (h_odd : odd n) (hlt : 1 < n) : bernoulli' n = 0 :="},
        {"role": "user", "content": "Complete the following theorem:\ntheorem {n : ℕ} (h : n % 2 = 1) :"},
         {"role": "assistant", "content": "theorem {n : ℕ} (h : n % 2 = 1) : n % 4 = 1 ∨ n % 4 = 3 :="},
        {"role": "user", "content": "Complete the following theorem:\ntheorem (n : ℕ) :"},
        {"role": "assistant", "content": "theorem (n : ℕ) : ∃ (p : ℕ), n ≤ p ∧ nat.prime p :="},
        {"role": "user", "content": "Complete the following theorem:\ntheorem {n : ℕ} (h : n > 0) :"},
        {"role": "assistant", "content": "theorem (a : cardinal) : a < 2 ^ a :="},
        {"role": "user", "content": "Complete the following theorem:\ntheorem {α : Type u} [DecidableEq α] {a : α} {l : List α} (hyp : a ∈ l) :"},
        {"role": "assistant", "content": "theorem {α :  Type u} [DecidableEq α]{a : α } {l : List α} (hyp : a ∈ l) : (List.remove a l).length < l.length :="},
        {"role": "user", "content": "Complete the following theorem:\ntheorem {α : Type u} [DecidableEq α] {a : α} {l : List α} (hyp : a ∈ l) :"},
        {"role": "assistant", "content": "theorem (a b c : ℤ) (h : ∃ x : ℤ, ∃ y : ℤ,  a * x + b * y = c) :  ↑(Int.gcd a b) ∣ c ="},
        {"role": "user", "content": "Complete the following theorem:\ntheorem {α : Type u} [DecidableEq α] {a : α} {l : List α} (hyp : a ∈ l) :"},      
        {"role": "assistant", "content": "theorem (a b: Int)(h : b ∣ a) : {q : Int // a = b * q} :="},
        {"role": "user", "content": "Complete the following theorem:\ntheorem (n m : ℕ) [Nat.Prime n] :"},
    ]
)

import sys
sys.stdout.reconfigure(encoding='utf-8')
print([choice.message['content'].encode().decode('unicode-escape').encode('latin1').decode('utf-8') for choice in completion.choices])

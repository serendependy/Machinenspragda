open import Data.Nat

module Parity where

data Parity : ℕ → Set where
  even : (n : ℕ) → Parity (n * 2)
  odd  : (n : ℕ) → Parity (1 + n * 2)

parity : ∀ n → Parity n
parity 0 = even zero
parity 1 = odd zero
parity (suc (suc n)) with parity n
parity (suc (suc .(n' * 2)))       | even n' = even (suc n')
parity (suc (suc .(1 + (n' * 2)))) | odd  n' = odd (suc n')

pow₂ : ℕ → ℕ
pow₂ 0 = 1
pow₂ (suc n) = 2 * pow₂ n

pow₂-1 : ℕ → ℕ
pow₂-1 0 = 0
pow₂-1 (suc n) = pow₂ n + pow₂-1 n
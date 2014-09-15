open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

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


pow₂≡sk : ∀ n → Σ[ k ∈ ℕ ] pow₂ n ≡ suc k
pow₂≡sk zero = zero , refl
pow₂≡sk (suc n) with pow₂≡sk n 
...   | k' , prf rewrite prf = k' + suc (k' + zero) , refl

curry' : {A B C : Set} → (A → B → C) → (A × B) → C
curry' f (a , b) = f a b

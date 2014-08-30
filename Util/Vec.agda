open import Data.Nat
open import Data.Vec
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Function

open import Algebra.Structures
open IsCommutativeSemiringWithoutOne ⊔-⊓-0-isCommutativeSemiringWithoutOne
  renaming (*-comm to ⊓-comm)
  hiding (sym)

module Util.Vec where

vec-resize : ∀ {n} {α} {A : Set α} → Vec A n → A → (m : ℕ) → Vec A m
vec-resize {n = n} xs a m with compare n m
vec-resize xs a .(suc (n + k)) | less n k rewrite sym $ +-suc n k = xs ++ (tabulate $ const a)
vec-resize xs a n | equal .n = xs
vec-resize xs a m | greater .m k rewrite sym $ +-suc m k = take m xs

vec-⊓ : ∀ {m} {α} {A : Set α} → 
        Vec A m → (n : ℕ) → Vec A (m ⊓ n)
vec-⊓ [] zero = []
vec-⊓ [] (suc n) = []
vec-⊓ (x ∷ as) zero = []
vec-⊓ (x ∷ as) (suc n₁) = x ∷ vec-⊓ as n₁


-- todo rewrite in terms of above
vec-⊓₂ : ∀ {m n} {α β} {A : Set α} {B : Set β} →
        Vec A m → Vec B n → Vec A (m ⊓ n) × Vec B (m ⊓ n)
vec-⊓₂ {m = m} {n = n} as bs with vec-⊓ as n | vec-⊓ bs m
...  | as⊓ | bs⊓ rewrite ⊓-comm n m = as⊓ , bs⊓

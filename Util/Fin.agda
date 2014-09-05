open import Data.Nat
open import Data.Fin
  renaming (_+_ to _Fin+_)

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties.Simple

open import Parity

module Util.Fin where

_+⊔_ : ∀ {n m} → Fin n → Fin m → Fin (n + m)
_+⊔_ {.(suc n)} {m} (zero {n = n}) j = raise (suc n) j
_+⊔_ {.(suc n)} {m} (suc {n = n} i) j = suc (i +⊔ j)

_*ℕF_ : ∀ {m n} → (m' : ℕ) → ⦃ prf : m' ≡ suc m ⦄ → Fin n → Fin (m' * n)
_*ℕF_ {zero} {n} .1 ⦃ refl ⦄ i rewrite +-right-identity n = i
_*ℕF_ {suc m} .(suc (suc m)) {{refl}} i = i +⊔ ((suc m) *ℕF i)

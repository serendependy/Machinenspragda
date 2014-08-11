open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Data.Product hiding (map)
open import Function using (_$_ ; _∘_)

open import Parity

module BitPrimitives where

Bit : Set
Bit = Bool

Bits : ℕ → Set
Bits n = Vec Bit n

Byte : Set
Byte = Bits 8

bits-0 : ∀ {n} → Bits n
bits-0 {n} = tabulate (λ _ → false)

bits-tabulate : ∀ n → Vec (Bits n) (pow₂ n)
bits-tabulate zero = [ [] ]
bits-tabulate (suc n) with bits-tabulate n
...         | tab = (_∷_ false) ∷ [ _∷_ true ] ⊛* tab


-- fit two sets of bits to the same size (glb)

bits-⊓ : ∀ {n m} → Bits n → Bits m → (Bits (n ⊓ m) × Bits (n ⊓ m))
bits-⊓ [] [] = [] , []
bits-⊓ [] (x ∷ b2) = [] , []
bits-⊓ (x ∷ b1) [] = [] , []
bits-⊓ (x ∷ b1) (x₁ ∷ b2) with bits-⊓ b1 b2
...  | b1⊓ , b2⊓ = (x ∷ b1⊓) , x₁ ∷ b2⊓

-- bit operations for bytes

BitOp : ℕ → Set
BitOp zero = Bit
BitOp (suc n) = Bit → BitOp n

BitsOp : ℕ → Set
BitsOp n = ∀ {l} → helper l n
  where
    helper : ℕ → ℕ → Set
    helper l 0 = Bits l
    helper l (suc n) = Bits l → helper l n

~_ : BitsOp 1
~ b = map not b

_&_ : BitsOp 2
b1 & b2 = zipWith _∧_ b1 b2

_∣_ : BitsOp 2
b1 ∣ b2 = zipWith _∨_ b1 b2

_^_ : BitsOp 2
b1 ^ b2 = zipWith _xor_ b1 b2

-- bits equality
eq-0 : ∀ {n} → Bits n → Bit
eq-0 bits = not (foldr₁ _∨_ $ false ∷ bits)

-- bit-parity
bit-parity : ∀ {n} → Bits (suc n) → Bit
bit-parity = head

bit-parity-extend : ∀ {n} → Bits (suc n) → Bits (suc (suc n))
bit-parity-extend bits = bit-parity bits ∷ bits

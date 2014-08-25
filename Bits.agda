open import Data.Nat
open import Data.Bool
open import Data.Vec
open import Data.Product hiding (map)
open import Function using (_$_ ; _∘_ ; const)

open import Parity

module Bits where

Bit : Set
Bit = Bool

Bits : ℕ → Set
Bits n = Vec Bit n

Byte : Set
Byte = Bits 8


module Conversions where
  open import BitView
  open import Data.Fin
    renaming (toℕ to Fin-toℕ)
    hiding (_+_)

  Bit-toℕ : Bit → ℕ
  Bit-toℕ true  = 1
  Bit-toℕ false = 0

  Bit-toBitView : (x : Bit) → BitView (Bit-toℕ x) 1
  Bit-toBitView true  = ₂#1
  Bit-toBitView false = ₂#0


  bin-placevals : ∀ n → Vec ℕ n
  bin-placevals n = reverse $ map (pow₂ ∘ Fin-toℕ) (allFin n)

  Bits-toℕ' : ∀ {n} → Bits n → ℕ
  Bits-toℕ' [] = 0
  Bits-toℕ' .{suc n} (_∷_ {n} x bits) = Bit-toℕ x * pow₂ n + Bits-toℕ' bits

  -- the 'J' way to compute the value
  -- +/ (|. 2 ^ i. n) * bits
  -- Bits-toℕ' [] = 0
  -- Bits-toℕ' (b ∷ bits) = foldr₁ _+_ $ 
  --   zipWith _*_ (bin-placevals _)
  --               (map Bit-toℕ (b ∷ bits))

  Bits×Carry-toℕ' : ∀ {n} → (Bits n × Bit) → ℕ
  Bits×Carry-toℕ' (bits , c) = Bits-toℕ' (c ∷ bits)

  -- the 'Agda' way to compute the value
  Bits-toBitView : ∀ {l} → (bits : Bits (suc l)) → Σ[ n ∈ ℕ ] BitView n (suc l)
  Bits-toBitView (x ∷ []) = _ , Bit-toBitView x
  Bits-toBitView (x ∷ x₁ ∷ bits) = _ , proj₂ (Bit-toBitView x #ˡ proj₂ (Bits-toBitView $ x₁ ∷ bits))

  Bits-toℕ : ∀ {n} → Bits n → ℕ
  Bits-toℕ [] = 0
  Bits-toℕ (x ∷ bits) = proj₁ $ Bits-toBitView (x ∷ bits)

  Bits-fromBitView : ∀ {n l} → BitView n l → Bits l
  Bits-fromBitView ₂#0 = [ false ]
  Bits-fromBitView ₂#1 = [ true  ]
  Bits-fromBitView (bv #0) = Bits-fromBitView bv ∷ʳ false
  Bits-fromBitView (bv #1) = Bits-fromBitView bv ∷ʳ true

  Bits-fromℕ : ℕ → Σ[ n ∈ ℕ ] Bits n
  Bits-fromℕ n with bitView n
  ...      | l , bv = l , Bits-fromBitView bv

  Byte-toℕ : Byte → ℕ
  Byte-toℕ byte = Bits-toℕ' byte


module Primitives where

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

  bit-parity-extend : ∀ {n} → Bits n → Bits (suc n)
  bit-parity-extend [] = [ false ]
  bit-parity-extend (x ∷ bits) = x ∷ x ∷ bits

  open import Data.Nat.Properties.Simple

  _⟪ℕ_ : ∀ {n} → Bits n → ℕ → Bits n
  _⟪ℕ_ {n} bits shift = drop shift $ bits++0s
    where
      bits++0s : Bits (shift + n)
      bits++0s rewrite +-comm shift n = bits ++ tabulate (const false)

  _⟫ℕₗ_ : ∀ {n} → Bits n → ℕ → Bits n
  _⟫ℕₗ_ {n} bits shift = take n $ 0s++bits
    where
      0s++bits : Bits (n + shift)
      0s++bits rewrite +-comm n shift = tabulate {shift} (const false) ++ bits

  -- _⟪₁ : ∀ {n} → Bits n → Bits n
  -- _⟪₁ {n} bits = drop 1 $ bits ∷ʳ false

  -- _⟪_ : ∀ {n m} → Bits n → Bits m → Bits n
  -- bᵥ ⟪ bₛ with Conversions.Bits-toℕ' bₛ
  -- bᵥ ⟪ bₛ | shift = helper bᵥ shift
  --   where
  --     helper : ∀ {n} → Bits n → ℕ → Bits n
  --     helper b zero = b
  --     helper b (suc s) = helper (b ⟪₁) s

  -- _⟫₁ₗ : ∀ {n} → Bits n → Bits n
  -- _⟫₁ₗ {n} bits = take n $ false∷bits
  --   where
  --     open import Data.Nat.Properties.Simple
  --     false∷bits : Bits (n + 1)
  --     false∷bits rewrite +-comm n 1 = false ∷ bits
   
  -- _⟫₁ₐ : ∀ {n} → Bits n → Bits n
  -- _⟫₁ₐ {n} bits = take n $ parity∷bits
  --   where
  --     open import Data.Nat.Properties.Simple
  --     parity∷bits : Bits (n + 1)
  --     parity∷bits rewrite +-comm n 1 = bit-parity-extend bits
 

open Primitives public

private
  temp = false ∷ true ∷ true ∷ true ∷ [ false ]
  shft = false ∷ false ∷ false ∷ true ∷ [ false ]
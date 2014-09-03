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
    renaming (toℕ to Fin-toℕ ; _+_ to _Fin+_)

  open import Data.Nat.Properties.Simple
  open import Relation.Binary.PropositionalEquality
    renaming ([_] to ⟦_⟧)
  open import Data.Fin.Properties
    hiding (reverse)

  open import Function

  Bit-toFin : Bit → Fin 2
  Bit-toFin true = suc zero
  Bit-toFin false = zero

  Bit-toℕ : Bit → ℕ
  Bit-toℕ = Fin-toℕ ∘ Bit-toFin

  Bit-toBitView : (x : Bit) → BitView (Bit-toℕ x) 1
  Bit-toBitView true  = ₂#1
  Bit-toBitView false = ₂#0

  bin-placevals : ∀ n → Vec ℕ n
  bin-placevals n = reverse $ map (pow₂ ∘ Fin-toℕ) (allFin n)

  Bits-toFin : ∀ {n} → Bits n → Fin (pow₂ n)
  Bits-toFin [] = zero
  Bits-toFin (_∷_ {n} true bits) rewrite +-right-identity (pow₂ n) =
             raise (pow₂ n) (Bits-toFin bits)
  Bits-toFin (_∷_ {n} false bits) rewrite +-right-identity (pow₂ n) =
             inject+ (pow₂ n) (Bits-toFin bits)

  -- Bits-fromFin : ∀ {n} → Fin (pow₂ n) → Bits n
  -- Bits-fromFin i = {!!}

  Bits-toℕ' : ∀ {n} → Bits n → ℕ
  Bits-toℕ' [] = 0
  Bits-toℕ' .{suc n} (_∷_ {n} x bits) = Bit-toℕ x * pow₂ n + Bits-toℕ' bits

  Bits-toℕ'' : ∀ {n} → Bits n → ℕ
  Bits-toℕ'' = Fin-toℕ ∘ Bits-toFin

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

  Bits-fromℕΣ : ℕ → Σ[ n ∈ ℕ ] Bits n
  Bits-fromℕΣ n with bitView n
  ...      | l , bv = l , Bits-fromBitView bv

  open import Util.Vec
  Bits-fromℕ : ∀ n → ℕ → Bits n
  Bits-fromℕ n m = vec-resizeₗ (proj₂ (Bits-fromℕΣ m)) false n

  Byte-toℕ : Byte → ℕ
  Byte-toℕ byte = Bits-toℕ' byte


module Primitives where
  open import Util.Vec

-- promote a bit to bits
  bit-extend : ∀ {n} → Bit → Bits n
  bit-extend b = tabulate (const b)

  bits-0 : ∀ {n} → Bits n
  bits-0 = bit-extend false

-- little bit of meta-bit-programming here
  bits-tabulate : ∀ n → Vec (Bits n) (pow₂ n)
  bits-tabulate zero = [ [] ]
  bits-tabulate (suc n) = (_∷_ false) ∷ [ _∷_ true ] ⊛* (bits-tabulate n)

  mux-resize : ∀ {#bits} {#inputs} #mux → Vec (Bits #bits) (suc #inputs) →
                 Vec (Bits #bits) (pow₂ #mux)
  mux-resize #mux inputs = vec-resize inputs (last inputs) (pow₂ #mux)

  bits-⊓ : ∀ {n m} → Bits n → Bits m → (Bits (n ⊓ m) × Bits (n ⊓ m))
  bits-⊓ = vec-⊓₂

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

  -- BitsOp-curried : ℕ → Set
  -- BitsOp-curried n = ∀ {len} → Vec (Bits len) n → Bits len

  BitsOp-curried : ℕ → ℕ → Set
  BitsOp-curried #bits #inputs = Vec (Bits #bits) #inputs → Bits #bits

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
  bit-parity : ∀ {n} → Bits n → Bit
  bit-parity [] = false
  bit-parity (x ∷ bits) = x

  bit-parity-extend : ∀ {n} → Bits n → Bits (suc n)
  bit-parity-extend bits = bit-parity bits ∷ bits

  -- helper functions for shift
  private
      open import Data.Nat.Properties.Simple

      _⟪ℕ_ : ∀ {n} → Bits n → ℕ → Bits n
      _⟪ℕ_ {n} bits shift = drop shift $ bits++0s
        where
          bits++0s : Bits (shift + n)
          bits++0s rewrite +-comm shift n =
            bits ++ tabulate (const false)

      _⟫ℕₗ_ : ∀ {n} → Bits n → ℕ → Bits n
      _⟫ℕₗ_ {n} bits shift = take n $ 0s++bits
        where
          0s++bits : Bits (n + shift)
          0s++bits rewrite +-comm n shift =
            tabulate {shift} (const false) ++ bits

      _⟫ℕₐ_ : ∀ {n} → Bits n → ℕ → Bits n
      _⟫ℕₐ_ {n} bits shift = take n $ sigs++bits
        where
          sigs++bits : Bits (n + shift)
          sigs++bits rewrite +-comm n shift =
            tabulate {shift} (const $ bit-parity bits) ++ bits

  _⟪_ : ∀ {n m} → Bits n → Bits m → Bits n
  _⟪_ {m = m} bₙ bₘ = bₙ ⟪ℕ (Conversions.Bits-toℕ' bₘ)

  _⟫ₗ_ : ∀ {n m} → Bits n → Bits m → Bits n
  _⟫ₗ_ {m = m} bₙ bₘ = bₙ ⟫ℕₗ (Conversions.Bits-toℕ' bₘ)

  _⟫ₐ_ : ∀ {n m} → Bits n → Bits m → Bits n
  _⟫ₐ_ {m = m} bₙ bₘ = bₙ ⟫ℕₐ (Conversions.Bits-toℕ' bₘ)

open Primitives public

private
  temp = false ∷ true ∷ true ∷ true ∷ [ false ]
  shft = false ∷ false ∷ false ∷ true ∷ [ false ]

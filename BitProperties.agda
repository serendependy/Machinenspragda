open import Data.Bool
open import Data.Nat
open import Data.Vec
open import Data.Product
  hiding (map)
open import Data.Fin
  renaming (toℕ to Fin-toℕ)
  hiding   (_+_)

open import Function

open import Parity
open import BitPrimitives
open import BitView
open import Machine

module BitProperties where

Bit-toℕ : Bit → ℕ
Bit-toℕ true  = 1
Bit-toℕ false = 0

Bit-toBitView : (x : Bit) → BitView (Bit-toℕ x) 1
Bit-toBitView true  = ₂#1
Bit-toBitView false = ₂#0


bin-placevals : ∀ n → Vec ℕ n
bin-placevals n = reverse $ map (pow₂ ∘ Fin-toℕ) (allFin n)

-- the 'J' way to compute the value
-- +/ (|. 2 ^ i. n) * bits
Bits-toℕ' : ∀ {n} → Bits n → ℕ
Bits-toℕ' [] = 0
Bits-toℕ' (b ∷ bits) = foldr₁ _+_ $ 
  zipWith _*_ (bin-placevals _)
              (map Bit-toℕ (b ∷ bits))

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


-- ambitious

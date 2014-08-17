open import Data.Bool
open import Data.Nat
open import Data.Vec
open import Data.Product
  hiding (map)
open import Data.Fin
  renaming (toℕ to Fin-toℕ)
  hiding   (_+_)

open import Relation.Binary.PropositionalEquality
  renaming ([_] to ⟦_⟧)
open Relation.Binary.PropositionalEquality.≡-Reasoning

import Data.Nat.Properties
open Data.Nat.Properties.SemiringSolver
  using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)
open import Data.Nat.Properties.Simple

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
Bits-toℕ' .{suc n} (_∷_ {n} x bits) = Bit-toℕ x * pow₂ n + Bits-toℕ' bits
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


-- ambitious
bit-adder-correct : ∀ {n} → (b₁ b₂ : Bits n) → 
                      (Bits-toℕ' b₁ + Bits-toℕ' b₂) ≡ Bits×Carry-toℕ' (b₁ +ₙ b₂)
bit-adder-correct [] [] = refl
bit-adder-correct (x ∷ b₁) (x₁ ∷ b₂) with bit-adder-correct b₁ b₂
bit-adder-correct (true  ∷ b₁) (true  ∷ b₂) | prf = {!!}
bit-adder-correct (true  ∷ b₁) (false ∷ b₂) | prf = {!!}
bit-adder-correct (_∷_ {n} false b₁) (true  ∷ b₂) | prf with b₁ +ₙ b₂
...             | bitsum , true  = 
  let b₁' = Bits-toℕ' b₁
      b₂' = Bits-toℕ' b₂
      bitsum' = Bits-toℕ' bitsum
      2ⁿ = pow₂ n
  in begin b₁' + (pow₂ n + zero + b₂') 
               ≡⟨ cong (_+_ b₁') (+-comm (pow₂ n + zero) b₂') ⟩ 
           b₁' + (b₂' + (pow₂ n + zero)) 
               ≡⟨ sym (+-assoc b₁' b₂' (pow₂ n + zero)) ⟩ 
           b₁' + b₂' + (pow₂ n + zero)
               ≡⟨ cong (λ x → x + (pow₂ n + zero)) prf ⟩
           pow₂ n + zero + bitsum' + (pow₂ n + zero)
               ≡⟨ +-assoc (pow₂ n + zero) bitsum'  (pow₂ n + zero) ⟩
           pow₂ n + zero + (bitsum' + (pow₂ n + zero))
               ≡⟨ +-assoc (pow₂ n) 0 (bitsum' + (pow₂ n + 0)) ⟩ 
           pow₂ n + (bitsum' + (pow₂ n + 0))
               ≡⟨ cong (λ x → pow₂ n + x) (+-comm bitsum' (pow₂ n + 0)) ⟩
           pow₂ n + (pow₂ n + zero + bitsum')
               ≡⟨ sym (+-assoc (pow₂ n) (pow₂ n + 0) bitsum') ⟩
           pow₂ n + (pow₂ n + zero) + bitsum'
               ≡⟨ cong (λ x → pow₂ n + x + bitsum') (sym (+-right-identity (pow₂ n + 0))) ⟩
           pow₂ n + (pow₂ n + zero + zero) + bitsum'
               ≡⟨ cong (λ x → x + bitsum') (sym (+-assoc (pow₂ n) (pow₂ n + 0) 0)) ⟩
           (pow₂ n + (pow₂ n + zero) + zero + bitsum' ∎)
...             | bitsum , false = {!!}
bit-adder-correct (false ∷ b₁) (false ∷ b₂) | prf = prf


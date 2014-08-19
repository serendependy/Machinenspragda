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
open import Reflection

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
bit-adder-correct (_∷_ {n} x₁ b₁) (_∷_ .{n} x₂ b₂)
  rewrite +-right-identity (pow₂ n)
  with Bits-toℕ' b₁ | Bits-toℕ' b₂ | pow₂ n | (b₁ +ₙ b₂) | bit-adder-correct b₁ b₂
... | b₁' | b₂' | 2ⁿ | bₛ , c | prf with Bits-toℕ' bₛ 
bit-adder-correct (true ∷ b₁) (true ∷ b₂) | b₁' | b₂' | 2ⁿ | bₛ , true | prf | bₛ' 
  rewrite +-right-identity 2ⁿ | +-right-identity (2ⁿ + 2ⁿ) = 
   begin 2ⁿ + b₁' + (2ⁿ + b₂')       ≡⟨ +-assoc 2ⁿ b₁' (2ⁿ + b₂') ⟩
         2ⁿ + (b₁' + (2ⁿ + b₂'))     ≡⟨ cong (λ x → 2ⁿ + x) (+-comm b₁' (2ⁿ + b₂')) ⟩
         2ⁿ + (2ⁿ + b₂' + b₁')       ≡⟨ cong (λ x → 2ⁿ + x) (+-assoc 2ⁿ b₂' b₁') ⟩
         2ⁿ + (2ⁿ + (b₂' + b₁'))     ≡⟨ sym (+-assoc 2ⁿ 2ⁿ (b₂' + b₁')) ⟩
         2ⁿ + 2ⁿ + (b₂' + b₁')       ≡⟨ cong (λ x → 2ⁿ + 2ⁿ + x) (+-comm b₂' b₁') ⟩
         2ⁿ + 2ⁿ + (b₁' + b₂')       ≡⟨ cong (λ x → 2ⁿ + 2ⁿ + x) prf ⟩
         2ⁿ + 2ⁿ + (2ⁿ + bₛ')        ∎
bit-adder-correct (true ∷ b₁) (true ∷ b₂) | b₁' | b₂' | 2ⁿ | bₛ , false | prf | bₛ' 
  rewrite +-right-identity 2ⁿ | +-right-identity (2ⁿ + 2ⁿ) = 
   begin 2ⁿ + b₁' + (2ⁿ + b₂')       ≡⟨ +-assoc 2ⁿ b₁' (2ⁿ + b₂') ⟩
         2ⁿ + (b₁' + (2ⁿ + b₂'))     ≡⟨ cong (_+_ 2ⁿ) (sym (+-assoc b₁' 2ⁿ b₂')) ⟩
         2ⁿ + (b₁' + 2ⁿ + b₂')       ≡⟨ cong (λ x → 2ⁿ + (x + b₂')) (+-comm b₁' 2ⁿ) ⟩
         2ⁿ + (2ⁿ + b₁' + b₂')       ≡⟨ cong (_+_ 2ⁿ) (+-assoc 2ⁿ b₁' b₂') ⟩
         2ⁿ + (2ⁿ + (b₁' + b₂'))     ≡⟨ sym (+-assoc 2ⁿ 2ⁿ (b₁' + b₂')) ⟩
         2ⁿ + 2ⁿ + (b₁' + b₂')       ≡⟨ cong (_+_ (2ⁿ + 2ⁿ)) prf ⟩
         2ⁿ + 2ⁿ + bₛ'               ∎
bit-adder-correct (true ∷ b₁) (false ∷ b₂) | b₁' | b₂' | 2ⁿ | bₛ , true | prf | bₛ'
  rewrite +-right-identity 2ⁿ | +-right-identity (2ⁿ + 2ⁿ) =
   begin 2ⁿ + b₁' + b₂'              ≡⟨ +-assoc 2ⁿ b₁' b₂' ⟩
         2ⁿ + (b₁' + b₂')            ≡⟨ cong (_+_ 2ⁿ) prf ⟩
         2ⁿ + (2ⁿ + bₛ')             ≡⟨ sym (+-assoc 2ⁿ 2ⁿ bₛ') ⟩
         2ⁿ + 2ⁿ + bₛ'               ∎
bit-adder-correct (true ∷ b₁) (false ∷ b₂) | b₁' | b₂' | 2ⁿ | bₛ , false | prf | bₛ'
  rewrite +-right-identity 2ⁿ =
    begin 2ⁿ + b₁' + b₂'             ≡⟨ +-assoc 2ⁿ b₁' b₂' ⟩
          2ⁿ + (b₁' + b₂')           ≡⟨ cong (_+_ 2ⁿ) prf ⟩
          2ⁿ + bₛ'                   ∎
bit-adder-correct (false ∷ b₁) (true ∷ b₂) | b₁' | b₂' | 2ⁿ | bₛ , true | prf | bₛ' 
  rewrite +-right-identity 2ⁿ | +-right-identity (2ⁿ + 2ⁿ) =
   begin b₁' + (2ⁿ + b₂')            ≡⟨ sym (+-assoc b₁' 2ⁿ b₂') ⟩
         b₁' + 2ⁿ + b₂'              ≡⟨ cong (λ x → x + b₂') (+-comm b₁' 2ⁿ) ⟩
         2ⁿ + b₁' + b₂'              ≡⟨ +-assoc 2ⁿ b₁' b₂' ⟩ 
         2ⁿ + (b₁' + b₂')            ≡⟨ cong (λ x → 2ⁿ + x) prf ⟩
         2ⁿ + (2ⁿ + bₛ')             ≡⟨ sym (+-assoc 2ⁿ 2ⁿ bₛ') ⟩
         2ⁿ + 2ⁿ + bₛ'               ∎
bit-adder-correct (false ∷ b₁) (true ∷ b₂) | b₁' | b₂' | 2ⁿ | bₛ , false | prf | bₛ'
  rewrite +-right-identity 2ⁿ =
   begin b₁' + (2ⁿ + b₂')            ≡⟨ sym (+-assoc b₁' 2ⁿ b₂') ⟩
         b₁' + 2ⁿ + b₂'              ≡⟨ cong (λ x → x + b₂') (+-comm b₁' 2ⁿ) ⟩
         2ⁿ + b₁' + b₂'              ≡⟨ +-assoc 2ⁿ b₁' b₂' ⟩
         2ⁿ + (b₁' + b₂')            ≡⟨ cong (λ x → 2ⁿ + x) prf ⟩
         2ⁿ + bₛ'                    ∎
bit-adder-correct (false ∷ b₁) (false ∷ b₂) | b₁' | b₂' | 2ⁿ | bₛ , true | prf | bₛ'
  rewrite +-right-identity 2ⁿ = prf
bit-adder-correct (false ∷ b₁) (false ∷ b₂) | b₁' | b₂' | 2ⁿ | bₛ , false | prf | bₛ' = prf

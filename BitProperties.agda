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
open import Bits
open Bits.Conversions

open import BitView
open import Machine

module BitProperties where

-- if I tabulate all the bits of a given size, any bit of that size is contained in it.
bits-tabulate-covers : ∀ {n} → (bits : Bits n) → bits ∈ (bits-tabulate n)
bits-tabulate-covers {zero} [] = here
bits-tabulate-covers {suc n} (x ∷ bits) with bits-tabulate n 
...                | all-bits-n with bits-tabulate-covers bits 
...                | prf = {!!}
-- bits-tabulate-covers {suc zero} (true ∷ .[])  | [] ∷ [] | here = there here
-- bits-tabulate-covers {suc zero} (false ∷ .[]) | [] ∷ [] | here = here
-- bits-tabulate-covers {suc zero} (x ∷ [])      | [] ∷ [] | there ()
-- bits-tabulate-covers {suc (suc n)} (x ∷ bits) | all-bits-n | prf with bits-tabulate n 
-- ...                | all-bits-n' = {!!}



-- bit adder
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

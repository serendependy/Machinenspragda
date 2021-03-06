open import Data.Bool
open import Data.Nat
open import Data.Vec
open import Data.Product
  hiding (map)
open import Data.Fin
  renaming (toℕ to Fin-toℕ ; compare to compareFin)
  hiding   (_+_ ; pred)

open import Relation.Binary.PropositionalEquality
  renaming ([_] to ⟦_⟧)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Data.Nat.Properties
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
open import Util.Vec

module BitProperties where

-- if I tabulate all the bits of a given size, any bit of that size is contained in it.
-- it ends up being easier to write out the raw subterms then to try to create aliases for them...
module Relations where
  open import Data.Empty
  open import Relation.Nullary

  infix 4 _≤₂_
  data _≤₂_ : ∀ {n} → (b c : Bits n) → Set where
    null  : [] ≤₂ []
    zeroₙ : ∀ {n} → (b₁ b₂ : Bits n) → (false ∷ b₁ ≤₂ true ∷ b₂)
    sucₙ  : ∀ {n} → ∀ x → {b₁ b₂ : Bits n} → b₁ ≤₂ b₂ → x ∷ b₁ ≤₂ x ∷ b₂

module Decisions where
  open import Relation.Binary
  open import Relation.Nullary
  open Relations

  _≟₂_ : ∀ {n} → Decidable {A = Bits n} _≡_
  _≟₂_ = vec-Dec-≡

  _≤₂?_ : ∀ {n} → Decidable {A = Bits n} _≤₂_
  [] ≤₂? [] = yes null
  (true ∷ b₁) ≤₂? (true ∷ b₂) with b₁ ≤₂? b₂ 
  (true ∷ b₁) ≤₂? (true ∷ b₂) | yes p = yes (sucₙ true p)
  (true ∷ b₁) ≤₂? (true ∷ b₂) | no ¬p = no (λ { (sucₙ .true x) → ¬p x })
  (true ∷ b₁) ≤₂? (false ∷ b₂) = no (λ ())
  (false ∷ b₁) ≤₂? (true ∷ b₂) = yes (zeroₙ b₁ b₂)
  (false ∷ b₁) ≤₂? (false ∷ b₂) with b₁ ≤₂? b₂ 
  (false ∷ b₁) ≤₂? (false ∷ b₂) | yes p = yes (sucₙ false p)
  (false ∷ b₁) ≤₂? (false ∷ b₂) | no ¬p = no (λ { (sucₙ .false x) → ¬p x })

bits-tabulate-covers : ∀ {n} → (bits : Bits n) → bits ∈ (bits-tabulate n)
bits-tabulate-covers {zero} [] = here
bits-tabulate-covers {suc n} (x ∷ bits) with bits-tabulate n | inspect bits-tabulate n
...                | all-bits | ⟦ eq ⟧  with subst (_∈_ bits) eq (bits-tabulate-covers bits) 
bits-tabulate-covers {suc n} (true ∷ bits)  | all-bits | ⟦ _ ⟧ | prf = 
                     vec-∈-++ᵣ (vec-∈-++[] (vec-∈-map-cons prf _)) (map (_∷_ false) all-bits)
bits-tabulate-covers {suc n} (false ∷ bits) | all-bits | ⟦ _ ⟧ | prf = 
                     vec-∈-++ₗ (vec-∈-map-cons prf false) $ (map (_∷_ true) all-bits) ++ []

import Data.Vec.Equality
open Data.Vec.Equality.Equality (setoid Bit)
  renaming (refl to ≈₂-refl)
  hiding (sym) 
import Util.Fin
open Util.Fin.HetEquality
  renaming (_≈_ to _≈Fin_)

open import Data.Vec.Properties

bits-tabulate-correct : ∀ {n} → (i : Fin (pow₂ n)) → (Bits-toℕ' $ lookup i (bits-tabulate n)) ≡ Fin-toℕ i
bits-tabulate-correct {zero} zero = refl
bits-tabulate-correct {zero} (suc ())
bits-tabulate-correct {suc n} i = {!!}
  where
    reflection-lemma = solve 1 (λ x → (x :+ (x :+ (con 0))) := (x :+ x)) refl (pow₂ n)

    i' = subst Fin reflection-lemma i
    bt' = subst (Vec (Bits (suc n))) reflection-lemma (bits-tabulate (suc n))
    
    i=i' : i ≈Fin i'
    i=i' = subst≈ i reflection-lemma

    open Data.Vec.Equality.Equality (setoid (Bits (suc n)))
      renaming (refl to ≈ₙ-refl ; _≈_ to _≈ₙ_)
    import Util.Vec
    open Util.Vec.Equality (Bits (suc n))
    bt=bt' : (bits-tabulate (suc n)) ≈ₙ bt'
    bt=bt' = ≈-subst reflection-lemma (bits-tabulate (suc n))

    lookup-eq = lookup-cong i=i' bt=bt'
    -- bt' = map (_∷_ false) (bits-tabulate n) ++ map (_∷_ true) (bits-tabulate n)
    -- -- bt' = subst (Vec (Bits (suc n))) reflection-lemma (bits-tabulate (suc n))


    -- open Equality (setoid (Bits (suc n)))
    --   renaming (_≈_ to _≈ₙ_ ; _++-cong_ to ++-cong₂ ; refl to ≈ₙ-refl)
    -- open UsingVectorEquality (setoid (Bits (suc n)))
    -- bt-eq : bits-tabulate (suc n) ≈ₙ (map (_∷_ false) (bits-tabulate n)) ++ (map (_∷_ true) (bits-tabulate n))
    -- bt-eq = ++-cong₂ (≈ₙ-refl (map ((_∷_ false)) (bits-tabulate n))) (xs++[]=xs _)

    -- hole = {!!}
                           

-- bits-tabulate-in-order : ∀ {n} → (i : Fin (pred $ pow₂ n)) →
--                            let (k , prf) = pow₂≡sk n
--                                all-bits = subst (Vec (Bits n)) prf $ bits-tabulate n
--                                i' = subst Fin (cong pred prf) i
--                            in ((suc ∘′ Bits-toℕ') $ lookup (raise 1 i') all-bits) ≡
--                               (Bits-toℕ' $ lookup (inject₁ i') all-bits)
-- bits-tabulate-in-order {n} i with pow₂≡sk n
-- ...  | (k , prf) with subst (Vec (Bits n)) prf $ bits-tabulate n |
--                       subst Fin (cong pred prf) i
-- bits-tabulate-in-order {zero} () | k , prf | all-bits' | i'
-- bits-tabulate-in-order {suc n} i | ._ , prf | all-bits' | zero 
--   rewrite +-right-identity (pow₂ n) | prf = {!!}
-- bits-tabulate-in-order {suc n} i | ._ , prf | all-bits' | suc i' = {!!}


mux-curried-correct : ∀ {#bits} {#mux} →
                        (inputs : Vec (Bits #bits) (pow₂ #mux)) → (mux : Bits #mux) → 
                        muxₙ-curried inputs mux ≡ lookup (Bits-toFin mux) inputs
mux-curried-correct inputs mux = {!!}

-- bit adder is correct
private
  reflection-lemma₁ = solve 3 (λ a b c → ((a :+ b) :+ (a :+ c)) :=
                                          (a :+ a) :+ (b :+ c)) refl
  reflection-lemma₂ = solve 3 (λ a b c → b :+ (a :+ c) := 
                                         a :+ (b :+ c)) refl

bit-adder-correct : ∀ {n} → (b₁ b₂ : Bits n) → 
                      (Bits-toℕ' b₁ + Bits-toℕ' b₂) ≡ Bits×Carry-toℕ' (b₁ +ₙ b₂)
bit-adder-correct [] [] = refl
bit-adder-correct (_∷_ {n} x₁ b₁) (_∷_ .{n} x₂ b₂)
  rewrite +-right-identity (pow₂ n)
  with Bits-toℕ' b₁ | Bits-toℕ' b₂ | pow₂ n | (b₁ +ₙ b₂) | bit-adder-correct b₁ b₂
... | b₁' | b₂' | 2ⁿ | bₛ , c | prf with Bits-toℕ' bₛ 
bit-adder-correct (true ∷ b₁) (true ∷ b₂) | b₁' | b₂' | 2ⁿ | bₛ , true | prf | bₛ' 
  rewrite +-right-identity 2ⁿ | +-right-identity (2ⁿ + 2ⁿ) = 
   begin 2ⁿ + b₁' + (2ⁿ + b₂')       ≡⟨ reflection-lemma₁ 2ⁿ b₁' b₂' ⟩
         2ⁿ + 2ⁿ + (b₁' + b₂')       ≡⟨ cong (λ x → 2ⁿ + 2ⁿ + x) prf ⟩
         2ⁿ + 2ⁿ + (2ⁿ + bₛ')        ∎
bit-adder-correct (true ∷ b₁) (true ∷ b₂) | b₁' | b₂' | 2ⁿ | bₛ , false | prf | bₛ' 
  rewrite +-right-identity 2ⁿ | +-right-identity (2ⁿ + 2ⁿ) = 
   begin 2ⁿ + b₁' + (2ⁿ + b₂')       ≡⟨ reflection-lemma₁ 2ⁿ b₁' b₂' ⟩ -- 
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
   begin b₁' + (2ⁿ + b₂')            ≡⟨ reflection-lemma₂ 2ⁿ b₁' b₂' ⟩
         2ⁿ + (b₁' + b₂')            ≡⟨ cong (λ x → 2ⁿ + x) prf ⟩
         2ⁿ + (2ⁿ + bₛ')             ≡⟨ sym (+-assoc 2ⁿ 2ⁿ bₛ') ⟩
         2ⁿ + 2ⁿ + bₛ'               ∎
bit-adder-correct (false ∷ b₁) (true ∷ b₂) | b₁' | b₂' | 2ⁿ | bₛ , false | prf | bₛ'
  rewrite +-right-identity 2ⁿ =
   begin b₁' + (2ⁿ + b₂')            ≡⟨ reflection-lemma₂ 2ⁿ b₁' b₂' ⟩
         2ⁿ + (b₁' + b₂')            ≡⟨ cong (λ x → 2ⁿ + x) prf ⟩
         2ⁿ + bₛ'                    ∎
bit-adder-correct (false ∷ b₁) (false ∷ b₂) | b₁' | b₂' | 2ⁿ | bₛ , true | prf | bₛ'
  rewrite +-right-identity 2ⁿ = prf
bit-adder-correct (false ∷ b₁) (false ∷ b₂) | b₁' | b₂' | 2ⁿ | bₛ , false | prf | bₛ' = prf

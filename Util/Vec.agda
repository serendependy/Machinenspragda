open import Data.Nat
open import Data.Vec
open import Data.Product
  hiding (map)

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Vec.Properties
open import Function

open import Algebra.Structures
open IsCommutativeSemiringWithoutOne ⊔-⊓-0-isCommutativeSemiringWithoutOne
  renaming (*-comm to ⊓-comm)
  hiding (sym ; +-comm)

open import Relation.Binary
open import Relation.Nullary

module Util.Vec where

vec-resize : ∀ {n} {α} {A : Set α} → Vec A n → A → (m : ℕ) → Vec A m
vec-resize {n = n} xs a m with compare n m
vec-resize xs a .(suc (n + k)) | less n k rewrite sym $ +-suc n k = xs ++ (tabulate $ const a)
vec-resize xs a n | equal .n = xs
vec-resize xs a m | greater .m k rewrite sym $ +-suc m k = take m xs

vec-resizeₗ : ∀ {n} {α} {A : Set α} → Vec A n → A → (m : ℕ) → Vec A m
vec-resizeₗ {n = n} xs a m with compare n m
vec-resizeₗ xs a .(suc (n + k)) | less n k rewrite +-comm n k = (tabulate {suc k} (const a)) ++ xs
vec-resizeₗ xs a n | equal .n = xs
vec-resizeₗ xs a m | greater .m k rewrite sym $ +-suc m k = take m xs

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

vec-∈-++ₗ : ∀ {m n} {α} {A : Set α} → {xs₁ : Vec A m} → {x : A} → 
             x ∈ xs₁ → (xs₂ : Vec A n) → x ∈ (xs₁ ++ xs₂)
vec-∈-++ₗ here xs₂ = here
vec-∈-++ₗ (there prf) xs₂ = there (vec-∈-++ₗ prf xs₂)

vec-∈-++ᵣ : ∀ {m n} {α} {A : Set α} → {xs₁ : Vec A m} → {x : A} → 
              x ∈ xs₁ → (xs₂ : Vec A n) → x ∈ (xs₂ ++ xs₁)
vec-∈-++ᵣ prf [] = prf
vec-∈-++ᵣ prf (x₁ ∷ xs₂) = there (vec-∈-++ᵣ prf xs₂)

vec-∈-++[] : ∀ {m} {α} {A : Set α} → {x : A} → {xs : Vec A m} → x ∈ xs → x ∈ xs ++ []
vec-∈-++[] here = here
vec-∈-++[] (there prf) = there (vec-∈-++[] prf)

vec-∈-map-cons : ∀ {#outer #inner} {α} {A : Set α} {xs} →
                  {xss : Vec (Vec A #inner) #outer} → 
                  xs ∈ xss → (a : A) → (a ∷ xs) ∈ (map (_∷_ a) xss)
vec-∈-map-cons here a = here
vec-∈-map-cons (there prf) a = there (vec-∈-map-cons prf a)

vec-Dec-≡ : ∀ {α} {A : Set α} {n} → ⦃ dec-eq : Decidable {A = A} _≡_ ⦄ →
              Decidable {A = Vec A n} _≡_
vec-Dec-≡ [] [] = yes _≡_.refl
vec-Dec-≡ ⦃ de ⦄ (x ∷ xs) (y ∷ ys) with de x y
...     | yes x≡y with vec-Dec-≡ xs ys 
vec-Dec-≡ (x ∷ xs) (.x ∷ .xs) | yes _≡_.refl | yes _≡_.refl = yes _≡_.refl
vec-Dec-≡ (x ∷ xs) (y ∷ ys) | yes p | no ¬p = no (λ x∷xs≡y∷ys →
          let x≡y , xs≡ys = ∷-injective x∷xs≡y∷ys in ¬p xs≡ys)
vec-Dec-≡ (x ∷ xs) (y ∷ ys) | no ¬p = no (λ x∷xs≡y∷ys →
          let x≡y , xs≡ys = ∷-injective x∷xs≡y∷ys in ¬p x≡y)
                  

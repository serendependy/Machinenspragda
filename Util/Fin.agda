open import Data.Nat
  renaming (compare to compareℕ ; pred to ℕpred)
open import Data.Fin
  renaming (_+_ to _Fin+_)
  hiding (_≤_ ; _<_)
open import Data.Product

open import Function

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties.Simple

open import Parity

module Util.Fin where

refine-+ : ∀ {m n} → (i : Fin (m + n)) → (toℕ i < m) → Fin m
refine-+ i i<m = fromℕ≤ i<m

from-l+m≡nₗ : ∀ l r {n} → suc l + r ≡ n → Fin n
from-l+m≡nₗ zero r refl = zero
from-l+m≡nₗ (suc l) r refl = suc (from-l+m≡nₗ l r refl)

to-≤ : ∀ {n} → (i : Fin n) → toℕ i ≤ n
to-≤ {zero} ()
to-≤ {suc n} zero = z≤n
to-≤ {suc n} (suc i) = s≤s (to-≤ i)

_+⊔_ : ∀ {n m} → Fin n → Fin m → Fin (n + m)
_+⊔_ {.(suc n)} {m} (zero {n = n}) j
  rewrite +-comm (suc n) m = inject+ (suc n) j
_+⊔_ {.(suc n)} {m} (suc {n = n} i) j = suc (i +⊔ j)

_*ℕF_ : ∀ {m n} → (m' : ℕ) → ⦃ prf : m' ≡ suc m ⦄ → Fin n → Fin (m' * n)
_*ℕF_ {zero} {n} .1 ⦃ refl ⦄ i
  rewrite +-right-identity n = i
_*ℕF_ {suc m} .(suc (suc m)) {{refl}} i = i +⊔ ((suc m) *ℕF i)

-- *ℕF-0ᵣ : ∀ {m n} → (m' : ℕ) → ⦃ m'=sm : m' ≡ suc m ⦄ → toℕ (m' *ℕF zero {n}) ≡ 0
-- *ℕF-0ᵣ {zero} {n} .1 {{refl}} rewrite +-right-identity n = refl
-- *ℕF-0ᵣ {suc m} {n} .(suc (suc m)) {{refl}} with *ℕF-0ᵣ {n = n} (suc m)
-- ...  | rec = {!!}

_∸Fℕ_ : ∀ {n} m → (Fin (m + (suc n))) → Fin (suc n)
zero ∸Fℕ i = i
_∸Fℕ_ {n} (suc m) zero = zero
suc m ∸Fℕ suc i = m ∸Fℕ i

/2F : ∀ {m} → Fin (suc (2 * m)) → Fin (suc m)
/2F zero = zero
/2F {zero} (suc i) = zero
/2F {suc m} (suc zero) = zero
/2F {suc m} (suc (suc i)) rewrite +-suc m (m + 0) = suc (/2F {m} i)

%2F : ∀ {m} → Fin (suc (2 * m)) → Fin 2
%2F zero = zero
%2F {zero} (suc ())
%2F {suc m} (suc zero) = (suc zero)
%2F {suc m} (suc (suc i)) with m + suc (m + 0) | +-suc m (m + 0) 
%2F {suc m} (suc (suc zero))    | ._ | refl = zero
%2F {suc m} (suc (suc (suc i))) | ._ | refl = %2F {m} (suc i)

module Properties where
  open import Data.Nat.Properties
  from-l+m≡nₗ-toℕ :  ∀ l r {n} → (l+r≡n : suc l + r ≡ n) →
                       (toℕ $ from-l+m≡nₗ l r l+r≡n) ≡ l
  from-l+m≡nₗ-toℕ zero r refl = refl
  from-l+m≡nₗ-toℕ (suc l) r refl = cong suc (from-l+m≡nₗ-toℕ l r refl)

  reduce≥-≡ : ∀ {m n} → (i : Fin (m + n)) → (i≥m : toℕ i ≥ m) →
                raise m (reduce≥ i i≥m) ≡ i
  reduce≥-≡ {zero} i i≥m = refl
  reduce≥-≡ {suc m} zero ()
  reduce≥-≡ {suc m} (suc i) (s≤s i≥m) = cong suc (reduce≥-≡ i i≥m)

  -- misplaced
  +≡-to-≤ₗ : ∀ m n l → m + n ≡ l → m ≤ l
  +≡-to-≤ₗ m n .(m + n) refl = m≤m+n m n

  +≡-to-≤ᵣ : ∀ m n l → m + n ≡ l → n ≤ l
  +≡-to-≤ᵣ m n .(m + n) refl = n≤m+n m n

  extract-+≤ : ∀ m {n l} → m + n ≤ m + l → n ≤ l
  extract-+≤ zero m+n≤m+l = m+n≤m+l
  extract-+≤ (suc m) (s≤s m+n≤m+l) = extract-+≤ m m+n≤m+l

module HetEquality where

  infix 4 _≈_
  data _≈_ : ∀ {n₁ n₂} → Fin n₁ → Fin n₂ → Set where
    0-cong  : ∀ {n₁ n₂} → zero {n₁} ≈ zero {n₂}
    +1-cong : ∀ {n₁ n₂} → {i : Fin n₁} → {j : Fin n₂} →
                i ≈ j → suc i ≈ suc j

  to≡ : ∀ {n} → {i j : Fin n} → (i ≈ j) → i ≡ j
  to≡ 0-cong = refl
  to≡ (+1-cong eq) = cong suc (to≡ eq)

  reflFin : ∀ {n} → (i : Fin n) → i ≈ i
  reflFin zero = 0-cong
  reflFin (suc i) = +1-cong (reflFin i)

  toℕrefl : ∀ {n m} → (i : Fin n) → (j : Fin m) → toℕ i ≡ toℕ j → i ≈ j
  toℕrefl zero zero i≡j = 0-cong
  toℕrefl zero (suc j) ()
  toℕrefl (suc i) zero ()
  toℕrefl (suc i) (suc j) i≡j = +1-cong (toℕrefl i j (cong ℕpred i≡j))

  toℕ≡ : ∀ {n₁ n₂} → {i : Fin n₁} → {j : Fin n₂} → i ≈ j → toℕ i ≡ toℕ j
  toℕ≡ 0-cong = refl
  toℕ≡ (+1-cong eq) = cong suc $ toℕ≡ eq

  subst≈ : ∀ {n₁ n₂} → (i : Fin n₁) → (n₁≡n₂ : n₁ ≡ n₂) → i ≈ subst Fin n₁≡n₂ i
  subst≈ i refl = reflFin i

  -- /2F≡ : ∀ {m} → (i : Fin (suc (2 * m))) → i ≈ %2F {m} i Fin+ (2 *ℕF (/2F {m} i))
  -- /2F≡ zero = {!!}
  -- /2F≡ (suc i) = {!!}


  -- /2F≡ zero = 0-cong
  -- /2F≡ {zero} (suc ())
  -- /2F≡ {suc m} (suc zero) = +1-cong 0-cong
  -- /2F≡ {suc m} (suc (suc i)) with m + suc (m + 0) | +-suc m (m + 0)
  -- /2F≡ {suc m} (suc (suc zero)) | .(suc (m + (m + 0))) | refl = {!!}
  -- /2F≡ {suc m} (suc (suc (suc i))) | .(suc (m + (m + 0))) | refl = {!!}

private
  i : Fin 11
  i = inject+ 3 (fromℕ 7)

  i/2 : Fin 6
  i/2 = /2F {5} i

  i%2 : Fin 2
  i%2 = %2F {5} i

  2*i/2 : Fin 12
  2*i/2 = 2 *ℕF i/2

  -- [/2]≡ : ∀ {m} → (i : Fin (suc (2 * m))) → i ≈ [ i %2F] Fin+ (2 *ℕF )
  -- [/2]≡ i = {!!}

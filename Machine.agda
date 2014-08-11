open import Data.Bool

open import Data.Nat
  renaming (_≟_ to _ℕ≟_)
open import Data.Fin
  hiding (fromℕ ; _+_ ; _≤_)
  renaming (toℕ to Fin-toℕ)

open import Data.Vec
open import Data.List
  using (List)

open import Data.Product
  hiding (zip ; map)

open import Relation.Nullary
open import Function
  using (_$_ ; _∘_)

open import Parity
open import BitView
open import BitPrimitives

module Machine where

_==_ : ∀ {n} → Bits n → Bits n → Bit
b1 == b2 = eq-0 (~ (b1 ^ (~ b2)))

-- mux
mux₂ : BitOp 3
mux₂ bₘ b₀ b₁ = (not bₘ ∧ b₀) ∨ (bₘ ∧ b₁)
-- mux₂ true  b₀ b₁ = b₁
-- mux₂ false b₀ b₁ = b₀

muxₙ : ∀ {m n} → Bits (suc m) → Bits (suc n) → Bit
muxₙ {m = mux-len} mux bits = 
  let all-mux = bits-tabulate (suc mux-len)    -- tabulate all possible mux configurations
      sel-mux = map (_==_ mux) all-mux         -- find the given mux configuration
      (bits⊓ , sel-mux⊓) = bits-⊓ bits sel-mux -- fit input to common size
  in not (eq-0 $ bits⊓ & sel-mux⊓)

-- addition
_+₂ʰ_ : Bit → Bit → (Bit × Bit)
bit₁ +₂ʰ bit₂ = (bit₁ ∧ bit₂) , (bit₁ xor bit₂)

_+₂_carry_ : Bit → Bit → (carry : Bit) → (Bit × Bit)
bit₁ +₂ bit₂ carry r =
  let (c' , s') = bit₁ +₂ʰ bit₂
      (c'' , s'') = s' +₂ʰ r
  in  (c' ∨ c'' , s'')

_+₂_ : Bit → Bit → (Bit × Bit)
bit₁ +₂ bit₂ = bit₁ +₂ bit₂ carry false

_-₂_ : Bit → Bit → (Bit × Bit)
bit₁ -₂ bit₂ = bit₁ +₂ bit₂ carry true

{-
  The workhorse here is foldMe, which takes the bits
at the same position of each byte, computes a bit sum and carry,
adds the bit sum to the sum-in-progress and passes along this and
the new carry.
-}

_+ₙ_carry_ : ∀ {n} → Bits n → Bits n → Bit → (Bits n × Bit)
b₁ +ₙ b₂ carry c = (foldr (λ n → (Bits n) × Bit) foldMe ([] , c) (zip b₁ b₂))
  where
    foldMe : ∀ {n} →  Bit × Bit → (Bits n) × Bit → (Bits (suc n) × Bit)
    foldMe (bit₁ , bit₂) (bits , c) = 
      let (c' , sum) = bit₁ +₂ bit₂ carry c
      in (sum ∷ bits , c')

_+ₙ_ : ∀ {n} → Bits n → Bits n → (Bits n × Bit)
b₁ +ₙ b₂ = b₁ +ₙ b₂ carry false

_-ₙ_carry_ : ∀ {n} → Bits n → Bits n → Bit → (Bits n × Bit)
b₁ -ₙ b₂ carry c = b₁ +ₙ ~ b₂ carry c

_-ₙ_ : ∀ {n} → Bits n → Bits n → (Bits n × Bit)
b₁ -ₙ b₂ = b₁ -ₙ b₂ carry true

-- comparisons
-- feels a bit hacky do create hardware with one extra bit
bit-signed-gt : ∀ {n} → Bits (suc n) → Bits (suc n) → Bit
bit-signed-gt b1 b2 = bit-parity $ proj₁ $ (false ∷ b1) -ₙ (false ∷ b2)

bit-unsigned-gt : ∀ {n} → Bits (suc n) → Bits (suc n) → Bit
bit-unsigned-gt b1 b2 = bit-parity $ proj₁ $ bit-parity-extend b1 -ₙ bit-parity-extend b2

private
  module _ where
    b1 : Byte -- 85
    b1 = false ∷ true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ [ true ]

    b2 : Byte -- 171
    b2 = true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ true ∷ [ true ]

open import Relation.Binary.PropositionalEquality
  hiding ([_])




--sym (lem₁ (pow₂ l)) = lshift¹ l #0

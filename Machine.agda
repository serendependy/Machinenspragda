open import Data.Bool

open import Data.Nat
  renaming (_≟_ to _ℕ≟_)
open import Data.Fin
  hiding (fromℕ ; _+_ ; _≤_)
  renaming (toℕ to Fin-toℕ)

import Data.Nat.Properties
open Data.Nat.Properties.SemiringSolver
    using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)

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

module Machine where

Bit : Set
Bit = Bool

Bits : ℕ → Set
Bits n = Vec Bit n

Byte : Set
Byte = Bits 8

bits-0 : ∀ {n} → Bits n
bits-0 {n} = tabulate (λ _ → false)

bits-tabulate : ∀ n → Vec (Bits n) (pow₂ n)
bits-tabulate zero = [ [] ]
bits-tabulate (suc n) with bits-tabulate n
...         | tab = (_∷_ false) ∷ [ _∷_ true ] ⊛* tab

-- conversion functions

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

-- fit two sets of bits to the same size (glb)

Bits-⊓ : ∀ {n m} → Bits n → Bits m → (Bits (n ⊓ m) × Bits (n ⊓ m))
Bits-⊓ [] [] = [] , []
Bits-⊓ [] (x ∷ b2) = [] , []
Bits-⊓ (x ∷ b1) [] = [] , []
Bits-⊓ (x ∷ b1) (x₁ ∷ b2) with Bits-⊓ b1 b2
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

-- more complex operations

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
      (bits⊓ , sel-mux⊓) = Bits-⊓ bits sel-mux -- fit input to common size
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

  Overflow is discarded
-}

_+ₙ_carry_ : ∀ {n} → Bits n → Bits n → Bit → Bits n
b₁ +ₙ b₂ carry c = proj₁ (foldr (λ n → (Bits n) × Bit) foldMe ([] , c) (zip b₁ b₂))
  where
    foldMe : ∀ {n} →  Bit × Bit → (Bits n) × Bit → (Bits (suc n) × Bit)
    foldMe (bit₁ , bit₂) (bits , c) = 
      let (c' , sum) = bit₁ +₂ bit₂ carry c
      in (sum ∷ bits , c')

_+ₙ_ : BitsOp 2
b₁ +ₙ b₂ = b₁ +ₙ b₂ carry false

_-ₙ_carry_ : ∀ {n} → Bits n → Bits n → Bit → Bits n
b₁ -ₙ b₂ carry c = b₁ +ₙ ~ b₂ carry c

_-ₙ_ : BitsOp 2
b₁ -ₙ b₂ = b₁ -ₙ b₂ carry true

private
  module _ where
    b1 : Byte
    b1 = false ∷ true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ [ true ]

    b2 : Byte
    b2 = true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ true ∷ [ true ]

open import Relation.Binary.PropositionalEquality
  hiding ([_])


-- experimenting with ring solver
private
  lem₁ : (x : ℕ) → x * 2 ≡ x + 1 * x
  lem₁ = (solve 1 (λ x' → x' :* con 2 := x' :+ con 1 :* x') refl)

-- 1 followed by l zeros
lshift¹ : (l : ℕ) → BitView (pow₂ l) (suc l)
lshift¹ 0 = ₂#1
lshift¹ (suc l) rewrite sym $ lem₁ $ pow₂ l = lshift¹ l #0
--sym (lem₁ (pow₂ l)) = lshift¹ l #0

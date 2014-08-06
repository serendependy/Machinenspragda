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

module Machine where

Bit : Set
Bit = Bool

Bits : ℕ → Set
Bits n = Vec Bit n

Byte : Set
Byte = Bits 8

bits-0 : ∀ {n} → Bits n
bits-0 {n} = tabulate (λ _ → false)

Bit-toℕ : Bit → ℕ
Bit-toℕ true = 1
Bit-toℕ false = 0

bin-placevals : ∀ n → Vec ℕ n
bin-placevals n = reverse $ map (pow₂ ∘ Fin-toℕ) (allFin n)

Bits-toℕ : ∀ {n} → Bits n → ℕ
Bits-toℕ [] = 0
Bits-toℕ (b ∷ bits) = foldr₁ _+_ $ 
  zipWith _*_ (bin-placevals _)
              (map Bit-toℕ (b ∷ bits))

Bits-fromℕ : ℕ → Σ[ n ∈ ℕ ] Bits n
-- defined lower down with BitView

Byte-toℕ : Byte → ℕ
Byte-toℕ byte = Bits-toℕ byte

-- bit operatons for bytes
Op₁ : Set
Op₁ = Byte → Byte

Op₂ : Set
Op₂ = Byte → Byte → Byte

Op : ℕ → Set
Op zero = Bit
Op (suc n) = Bit → Op n

~_ : Op₁
~ b = map not b

_&_ : Op₂
b1 & b2 = zipWith _∧_ b1 b2

_∣_ : Op₂
b1 ∣ b2 = zipWith _∨_ b1 b2

_^_ : Op₂
b1 ^ b2 = zipWith _xor_ b2 b2

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

mux₂ : Op 3
mux₂ true  b₀ b₁ = b₁
mux₂ false b₀ b₁ = b₀

bit-fits : ℕ → Set
bit-fits n = {!!}

{-
  The workhorse here is foldMe, which takes the bits
at the same position of each byte, computes a bit sum and carry,
adds the bit sum to the sum-in-progress and passes along this and
the new carry.

  Overflow is discarded
-}

_+₈_ : Byte → Byte → Byte
b₁ +₈ b₂ = proj₁ (foldr (λ n → (Bits n) × Bit) foldMe ([] , false) (zip b₁ b₂))
  where
    foldMe : ∀ {n} →  Bit × Bit → (Bits n) × Bit → (Bits (suc n) × Bit)
    foldMe (bit₁ , bit₂) (bits , c) = 
      let (c' , sum) = bit₁ +₂ bit₂ carry c
      in (sum ∷ bits , c')

private
  module _ where
    b1 : Byte
    b1 = false ∷ true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ [ true ]

    b2 : Byte
    b2 = true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ true ∷ [ true ]

open import Relation.Binary.PropositionalEquality
  hiding ([_])


-- conversion functions

infixl 100 _#1
infixl 100 _#0

data BitView : ℕ → ℕ → Set where
  ₂#0 : BitView 0 1
  ₂#1 : BitView 1 1
  _#0 : ∀ {s l} → BitView s l → BitView (s * 2) (suc l)
  _#1 : ∀ {s l} → BitView s l → BitView (1 + s * 2) (suc l)

private
  mypf : BitView 65 8
  mypf = ₂#0 #1 #0 #0 #0 #0 #0 #1

suc₂ : ∀ {s l} → BitView s l →
       Σ[ over ∈ Bool ] BitView (suc s) (if over then suc l else l)
suc₂ ₂#0 = false , ₂#1
suc₂ ₂#1 = true  , ₂#1 #0
suc₂ (bv #0) = false , bv #1
suc₂ (bv #1) with suc₂ bv 
...  | true  , sbv = true  , sbv #0
...  | false , sbv = false , sbv #0

bitView : ∀ (n : ℕ) → Σ[ l ∈ ℕ ] BitView n l
bitView 0 = 1 , ₂#0
bitView (suc n) with bitView n
...     | l , bvn with suc₂ bvn 
...     | b , sbvn = (if b then suc l else l) , sbvn

Bits-fromBitView : ∀ {n l} → BitView n l → Bits l
Bits-fromBitView ₂#0 = [ false ]
Bits-fromBitView ₂#1 = [ true  ]
Bits-fromBitView (bv #0) = Bits-fromBitView bv ∷ʳ false
Bits-fromBitView (bv #1) = Bits-fromBitView bv ∷ʳ true

Bits-fromℕ n with bitView n
...      | l , bv = l , Bits-fromBitView bv

-- experimenting with ring solver
private
  lem₁ : (x : ℕ) → x * 2 ≡ x + 1 * x
  lem₁ = (solve 1 (λ x' → x' :* con 2 := x' :+ con 1 :* x') refl)

-- 1 followed by l zeros
lshift¹ : (l : ℕ) → BitView (pow₂ l) (suc l)
lshift¹ 0 = ₂#1
lshift¹ (suc l) rewrite sym $ lem₁ $ pow₂ l = lshift¹ l #0
--sym (lem₁ (pow₂ l)) = lshift¹ l #0

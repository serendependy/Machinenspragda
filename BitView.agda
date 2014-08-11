open import Data.Nat
open import Data.Product
open import Data.Bool

open import Relation.Binary.PropositionalEquality
open import Function

open import Data.Nat.Properties.Simple

open import Parity

module BitView where

infixl 100 _#1
infixl 100 _#0

data BitView : ℕ → ℕ → Set where
  ₂#0 : BitView 0 1
  ₂#1 : BitView 1 1
  _#0 : ∀ {s l} → BitView s l → BitView (s * 2) (suc l)
  _#1 : ∀ {s l} → BitView s l → BitView (1 + s * 2) (suc l)

private
  b0 : BitView 65 8
  b0 = ₂#0 #1 #0 #0 #0 #0 #0 #1

  b1 : BitView 85 8
  b1 = ₂#0 #1 #0 #1 #0 #1 #0 #1

  b2 : BitView 171 8
  b2 = ₂#1 #0 #1 #0 #1 #0 #1 #1

-- projections
BitView-len : ∀ {n l} → BitView n l → ℕ
BitView-len {l = len} bv = len

BitView-val : ∀ {n l} → BitView n l → ℕ
BitView-val {n = val} bv = val

from-BitView₁ : ∀ {n} → BitView n 1 → ℕ
from-BitView₁ ₂#0 = 0
from-BitView₁ ₂#1 = 1
from-BitView₁ (() #0)
from-BitView₁ (() #1)

-- appending MSB
#0-#ˡ_ : ∀ {n l} → BitView n l → BitView n (suc l)
#0-#ˡ ₂#0 = ₂#0 #0
#0-#ˡ ₂#1 = ₂#0 #1
#0-#ˡ bv #0 = (#0-#ˡ bv) #0
#0-#ˡ bv #1 = (#0-#ˡ bv) #1

-- can't wait for reflection tactics....
#1-#ˡ_ : ∀ {n l} → BitView n l → BitView (n + pow₂ l) (suc l)
#1-#ˡ ₂#0 = ₂#1 #0
#1-#ˡ ₂#1 = ₂#1 #1
#1-#ˡ bv #0 with #1-#ˡ bv
... | bv' = {!bv' #0!}
#1-#ˡ bv #1 with #1-#ˡ bv
... | bv' = {!bv' #1!}

-- _#ˡ_ : ∀ {n n' l} → (bv₁ : BitView n' 1) → BitView n l → 
--                     BitView (n + from-BitView₁ bv₁ * pow₂ l) (suc l)
-- ₂#0 #ˡ ₂#0 = ₂#0 #0
-- ₂#0 #ˡ ₂#1 = ₂#0 #1
-- ₂#0 #ˡ bv #0 with BitView-val bv
-- ...    | val rewrite +-comm (val * 2) 0 = {!!}
-- ₂#0 #ˡ bv #1 = {!!}
-- ₂#1 #ˡ ₂#0 = ₂#1 #0
-- ₂#1 #ˡ ₂#1 = ₂#1 #1
-- ₂#1 #ˡ bv #0 = {!!}
-- ₂#1 #ˡ bv #1 = {!!}
-- () #0 #ˡ bv
-- () #1 #ˡ bv

-- _#ˡ_ : ∀ {n' n l} → BitView n' 1 → BitView n l → Σ[ m ∈ ℕ ] BitView m (suc l)
-- b #ˡ ₂#0 = _ , b #0
-- b #ˡ ₂#1 = _ , b #1
-- b #ˡ bv #0 = _ , proj₂ (b #ˡ bv) #0
-- b #ˡ bv #1 = _ , proj₂ (b #ˡ bv) #1

-- adding one to a BitView
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

-- prove that bitView computes the smallest bit length

import Data.Nat.Properties
open Data.Nat.Properties.SemiringSolver
    using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)

private
  lem₁ : (x : ℕ) → x * 2 ≡ x + 1 * x
  lem₁ = (solve 1 (λ x' → x' :* con 2 := x' :+ con 1 :* x') refl)

-- 1 followed by l zeros
lshift¹ : (l : ℕ) → BitView (pow₂ l) (suc l)
lshift¹ 0 = ₂#1
lshift¹ (suc l) rewrite sym $ lem₁ $ pow₂ l = lshift¹ l #0

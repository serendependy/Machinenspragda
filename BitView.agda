open import Data.Nat
open import Data.Fin
  renaming (toℕ to Fin-toℕ ; compare to Fin-compare)
  hiding (_+_ ; _≤_)
open import Data.Product
open import Data.Bool

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

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

private
  lem₁-#1 : (s l : ℕ) → (s + pow₂ l) * 2 ≡ s * 2 + (pow₂ l + (pow₂ l + 0))
  lem₁-#1 s l =
    begin 
      (s + pow₂ l) * 2
    ≡⟨ distribʳ-*-+ 2 s (pow₂ l) ⟩
      s * 2 + pow₂ l * 2
    ≡⟨ cong (λ x → s * 2 + x) (*-comm (pow₂ l) 2) ⟩
      s * 2 + (pow₂ l + (pow₂ l + 0)) ∎

-- can't wait for reflection tactics....
#1-#ˡ_ : ∀ {n l} → BitView n l → BitView (n + pow₂ l) (suc l)
#1-#ˡ ₂#0 = ₂#1 #0
#1-#ˡ ₂#1 = ₂#1 #1
#1-#ˡ bv #0            with #1-#ˡ bv
#1-#ˡ (_#0 {s} {l} bv) | bv' rewrite sym $ lem₁-#1 s l = bv' #0
#1-#ˡ bv #1            with #1-#ˡ bv
#1-#ˡ (_#1 {s} {l} bv) | bv' rewrite sym $ lem₁-#1 s l = bv' #1

-- really appending MSB
_#ˡ'_ : ∀ {n n' l} → (bv₁ : BitView n' 1) → BitView n l → 
                    BitView (n + n' * pow₂ l) (suc l)
_#ˡ'_ {n = n} ₂#0 bv rewrite +-comm n        0 = #0-#ˡ bv
_#ˡ'_ {l = l} ₂#1 bv rewrite +-comm (pow₂ l) 0 = #1-#ˡ bv
() #0 #ˡ' bv
() #1 #ˡ' bv

-- appending MSB the easy way
_#ˡ_ : ∀ {n' n l} → BitView n' 1 → BitView n l → Σ[ m ∈ ℕ ] BitView m (suc l)
b #ˡ ₂#0 = _ , b #0
b #ˡ ₂#1 = _ , b #1
b #ˡ bv #0 = _ , proj₂ (b #ˡ bv) #0
b #ˡ bv #1 = _ , proj₂ (b #ˡ bv) #1


-- adding one to a BitView
suc₂ : ∀ {s l} → BitView s l →
       Σ[ over ∈ Bool ] BitView (suc s) (if over then suc l else l)
suc₂ ₂#0 = false , ₂#1
suc₂ ₂#1 = true  , ₂#1 #0
suc₂ (bv #0) = false , bv #1
suc₂ (bv #1) with suc₂ bv 
...  | true  , sbv = true  , sbv #0
...  | false , sbv = false , sbv #0

bitView : (n : ℕ) → Σ[ l ∈ ℕ ] BitView n l
bitView 0 = 1 , ₂#0
bitView (suc n) with bitView n
...     | l , bvn with suc₂ bvn 
...     | b , sbvn = (if b then suc l else l) , sbvn

private
  import Data.Nat.Properties
  open Data.Nat.Properties.SemiringSolver
    using (prove; solve; _:=_; con; var; _:+_; _:*_; :-_; _:-_)

  lem₁ : (x : ℕ) → x * 2 ≡ x + 1 * x
  lem₁ = (solve 1 (λ x' → x' :* con 2 := x' :+ con 1 :* x') refl)

-- 1 followed by l zeros
lshift¹ : (l : ℕ) → BitView (pow₂ l) (suc l)
lshift¹ 0 = ₂#1
lshift¹ (suc l) rewrite sym $ lem₁ $ pow₂ l = lshift¹ l #0

open import Util.Fin
open Properties
bitView-Fin : ∀ {n} → (i : Fin (pow₂ n)) → BitView (Fin-toℕ i) (1 ⊔ n)
bitView-Fin {zero} zero = ₂#0
bitView-Fin {zero} (suc ())
bitView-Fin {suc n} i with Fin-toℕ i | inspect Fin-toℕ i | pow₂≡sk n
...       | i' | i'-insp | k , 2ⁿ≡sk with compare i' (suc k)

--less
bitView-Fin {suc n} i | i' | _ | .(i' + l) , 2ⁿ≡sk | less .i' l
         with from-l+m≡nₗ i' l (sym 2ⁿ≡sk) | from-l+m≡nₗ-toℕ i' l (sym 2ⁿ≡sk)
...           | i″ | i″-eq
         with sym i″-eq | bitView-Fin {n} i″
-- pattern match on n for the return type
bitView-Fin {suc zero} i    | .(Fin-toℕ i″) | _ | .(Fin-toℕ i″ + l) , 2ⁿ≡sk
                            | less .(Fin-toℕ i″) l | i″ | i″-eq | refl | bv-i″
            = bv-i″
bitView-Fin {suc (suc n)} i | .(Fin-toℕ i″) | _ | .(Fin-toℕ i″ + l) , 2ⁿ≡sk
                            | less .(Fin-toℕ i″) l | i″ | i″-eq | refl | bv-i″
            = #0-#ˡ bv-i″

-- eq
bitView-Fin {suc n} i | .(suc k) | _ | k , 2ⁿ≡sk | equal .(suc k)
         rewrite sym 2ⁿ≡sk = lshift¹ n

-- greater
bitView-Fin {suc n} i | .(suc (suc (k + l))) | [ eq ] | k , 2ⁿ≡sk | greater .(suc k) l
            rewrite sym $ +-suc k l | +-right-identity (pow₂ n) = {!!}
  where
  module _ {n k : ℕ} (l : ℕ) (2ⁿ=k : pow₂ n ≡ k)
           (i : Fin (pow₂ n + pow₂ n)) (i'=k+l : Fin-toℕ i ≡ k + l) where
    #1-#ˡₖ : BitView l n → BitView (k + l) (suc n)
    #1-#ˡₖ bv rewrite +-comm k l | sym 2ⁿ=k = #1-#ˡ bv

    l≤k : l ≤ k
    l≤k with to-≤ i | i'=k+l
    ... | i'≤k+k | i'=k+l = extract-+≤ (pow₂ n) 2ⁿ+l≤2ⁿ+k
      where
        i'=2ⁿ+l = subst (λ x → Fin-toℕ i ≡ x + l) (sym 2ⁿ=k) i'=k+l

        i'≤2ⁿ+k : Fin-toℕ i ≤ pow₂ n + k
        i'≤2ⁿ+k = subst (λ x → Fin-toℕ i ≤ pow₂ n + x) 2ⁿ=k i'≤k+k

        2ⁿ+l≤2ⁿ+k : pow₂ n + l ≤ pow₂ n + k
        2ⁿ+l≤2ⁿ+k = subst (λ x → x ≤ pow₂ n + k) i'=2ⁿ+l i'≤2ⁿ+k
  


--          rewrite sym $ +-suc k l | 2ⁿ≡sk with +≡-to-≤ (suc k) (suc l) (Fin-toℕ i) (sym eq)
-- ...      | i'≤sk+sk with reduce≥ {suc k} i i'≤sk+sk | reduce≥-≡ {suc k} i i'≤sk+sk
-- ...      | i'-2ⁿ | i'-2ⁿ-eq = {!!}
--   where
--     i-2ⁿ : Fin (suc k + 0)
--     i-2ⁿ = reduce≥ {suc k} i (+≡-to-≤ (suc k) (suc l) (Fin-toℕ i) (sym eq))

-- reduce≥ {suc k} {suc k + 0}
-- prove that bitView computes the smallest bit length


-- some more fancy conversions
open import Data.Nat.Properties.Simple
--open import Util.Fin

-- BitView-toFin : ∀ {val #bits} → BitView val #bits → Fin (pow₂ #bits)
-- BitView-toFin ₂#0 = zero
-- BitView-toFin ₂#1 = suc zero
-- BitView-toFin (_#0 {l = l} bv) with BitView-toFin bv 
-- ...         | ret = 2 *ℕF ret
-- BitView-toFin (bv #1) = {!!}

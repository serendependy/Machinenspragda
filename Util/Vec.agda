open import Data.Nat
open import Data.Vec

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties.Simple
open import Function

module Util.Vec where

vec-resize : ∀ {n} {α} {A : Set α} → Vec A n → A → (m : ℕ) → Vec A m
vec-resize {n = n} xs a m with compare n m
vec-resize xs a .(suc (n + k)) | less n k rewrite sym $ +-suc n k = xs ++ (tabulate $ const a)
vec-resize xs a n | equal .n = xs
vec-resize xs a m | greater .m k rewrite sym $ +-suc m k = take m xs



module Data.Vec.Split where
open import Data.Nat
open import Data.Product
open import Data.Vec hiding (splitAt)

splitAt : ∀ {a} {A : Set a} → ∀ m {n} → Vec A (m + n) → Vec A m × Vec A n
splitAt zero vec = [] , vec
splitAt (suc m) (x ∷ vec) with splitAt m vec
... | fst , snd = x ∷ fst , snd

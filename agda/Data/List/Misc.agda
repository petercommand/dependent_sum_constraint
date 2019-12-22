module Data.List.Misc where
open import Data.List

open import Data.Nat

safeHead : ∀ {ℓ} {A : Set ℓ} → (l : List A) → length l > 0 → A
safeHead (x ∷ l) p = x

head' : ∀ {ℓ} {A : Set ℓ} → A → List A → A
head' a [] = a
head' a (x ∷ l) = x

tail' : ∀ {ℓ} {A : Set ℓ} → (l : List A) → List A
tail' [] = []
tail' (x ∷ l) = l

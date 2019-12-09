module Data.List.Misc where
open import Data.List

open import Data.Nat

safeHead : ∀ {ℓ} {A : Set ℓ} → (l : List A) → length l > 0 → A
safeHead (x ∷ l) p = x

tail' : ∀ {ℓ} {A : Set ℓ} → (l : List A) → List A
tail' [] = []
tail' (x ∷ l) = l

module Data.Vec.Repeat where
open import Data.Nat
open import Data.Vec

repeat : ∀ {ℓ} {A : Set ℓ} → A → ∀ n → Vec A n
repeat a zero = []
repeat a (suc n) = a ∷ repeat a n

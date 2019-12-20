{-# OPTIONS --prop #-}
module Data.Vec.AllProp where


open import Data.Vec

open import Level

data All {ℓ} {ℓ'} {A : Set ℓ} (P : A → Prop ℓ') : ∀ {n} → Vec A n → Prop (ℓ ⊔ ℓ') where
  [] : All P []
  _∷_ : ∀ {n x} {xs : Vec A n} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

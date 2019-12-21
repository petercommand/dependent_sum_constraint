module Data.Vec.Split where
open import Data.Nat
open import Data.Product
open import Data.Vec hiding (splitAt)

open import Relation.Binary.PropositionalEquality

splitAt : ∀ {a} {A : Set a} → ∀ m {n} → Vec A (m + n) → Vec A m × Vec A n
splitAt zero vec = [] , vec
splitAt (suc m) (x ∷ vec) with splitAt m vec
... | fst , snd = x ∷ fst , snd


splitAtCorrect : ∀ {a} {A : Set a} → ∀ m {n} → (vec : Vec A (m + n)) → let fst , snd = splitAt m vec in vec ≡ fst ++ snd
splitAtCorrect zero vec = refl
splitAtCorrect (suc m) (x ∷ vec) with splitAtCorrect m vec
... | eq with splitAt m vec
... | fst , snd = cong (_∷_ x) eq


vecSplit₁ : ∀ {a} {A : Set a} → ∀ {m n} → (v₁ v₂ : Vec A m) → {v₃ v₄ : Vec A n} → v₁ ++ v₃ ≡ v₂ ++ v₄ → v₁ ≡ v₂
vecSplit₁ [] [] eq = refl
vecSplit₁ (x ∷ v₁) (x₁ ∷ v₂) eq rewrite cong head eq = cong (_∷_ x₁) (vecSplit₁ v₁ v₂ (cong tail eq))

vecSplit₂ : ∀ {a} {A : Set a} → ∀ {m n} → (v₁ v₂ : Vec A m) → {v₃ v₄ : Vec A n} → v₁ ++ v₃ ≡ v₂ ++ v₄ → v₃ ≡ v₄
vecSplit₂ [] [] eq = eq
vecSplit₂ (x ∷ v₁) (x₁ ∷ v₂) eq = vecSplit₂ v₁ v₂ (cong tail eq)

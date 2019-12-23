module Data.List.Occ where

open import Data.Empty
open import Data.List
open import Data.Nat

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary



occAux : ∀ {ℓ} {A : Set ℓ} {a x : A} → Dec (a ≡ x) → ℕ → ℕ → ℕ
occAux (yes p) m n = m
occAux (no ¬p) m n = n

occAux₂ : ∀ {ℓ} {A : Set ℓ} (a x : A) (dec : Dec (a ≡ x)) m n → ¬ a ≡ x → occAux dec m n ≡ n
occAux₂ a x (yes p) m n neq = ⊥-elim (neq p)
occAux₂ a x (no ¬p) m n neq = refl

occ : ∀ {ℓ} {A : Set ℓ} → (Decidable {A = A} _≡_) → A → List A → ℕ
occ dec a [] = 0
occ dec a (x ∷ l) = occAux (dec a x) (suc (occ dec a l)) (occ dec a l)

occPrfIrr : ∀ {ℓ} {A : Set ℓ} → (dec dec' : Decidable {A = A} _≡_) → (v : A) (l : List A) → occ dec v l ≡ occ dec' v l
occPrfIrr dec dec' v [] = refl
occPrfIrr dec dec' v (x ∷ l) with dec v x | dec' v x
occPrfIrr dec dec' v (x ∷ l) | yes p | yes p₁ = cong suc (occPrfIrr dec dec' v l)
occPrfIrr dec dec' v (x ∷ l) | yes p | no ¬p = ⊥-elim (¬p p)
occPrfIrr dec dec' v (x ∷ l) | no ¬p | yes p = ⊥-elim (¬p p)
occPrfIrr dec dec' v (x ∷ l) | no ¬p | no ¬p₁ = occPrfIrr dec dec' v l

occLem : ∀ {ℓ} {A : Set ℓ} → (dec : Decidable {A = A} _≡_) → (x : A) (l l' : List A) → occ dec x (l ++ l') ≡ occ dec x l + occ dec x l'
occLem dec x [] l' = refl
occLem dec x (x₁ ∷ l) l' with dec x x₁
occLem dec x (x₁ ∷ l) l' | yes p = cong suc (occLem dec x l l')
occLem dec x (x₁ ∷ l) l' | no ¬p = occLem dec x l l'

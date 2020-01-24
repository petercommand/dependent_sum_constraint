module Language.Universe (f : Set) where

open import Data.Bool
open import Data.Empty
open import Data.Field
open import Data.Finite
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Data.Vec


data U : Set
⟦_⟧ : U → Set

data U where
  `One : U
  `Two : U
  `Base : U
  `Vec : (S : U) → ℕ → U
  `Σ `Π : (S : U) → (⟦ S ⟧ → U) → U



⟦ `One ⟧ = ⊤
⟦ `Two ⟧ = Bool
⟦ `Base ⟧ = f
⟦ `Vec ty x ⟧ = Vec ⟦ ty ⟧ x
⟦ `Σ fst snd ⟧ = Σ ⟦ fst ⟧ (λ f → ⟦ snd f ⟧)
⟦ `Π fst snd ⟧ = (x : ⟦ fst ⟧) → ⟦ snd x ⟧


U-ind : ∀ {ℓ} (C : (u : U) → ⟦ u ⟧ → Set ℓ)
  → (∀ (b : ⟦ `One ⟧) → C `One b)
  → (∀ (b : ⟦ `Two ⟧) → C `Two b)
  → (∀ (b : ⟦ `Base ⟧) → C `Base b)
  → (∀ ty x b → (∀ (elem : ⟦ ty ⟧) → C ty elem) → C (`Vec ty x) b)
  → (∀ fst snd (elem-fst : ⟦ fst ⟧) (elem-snd : ⟦ snd elem-fst ⟧) → C fst elem-fst → C (snd elem-fst) elem-snd → C (`Σ fst snd) (elem-fst , elem-snd))
  → (∀ fst (snd : ⟦ fst ⟧ → U) → (elem : (x : ⟦ fst ⟧) → ⟦ snd x ⟧) → (∀ (dom : ⟦ fst ⟧) → C fst dom) → (∀ (dom : ⟦ fst ⟧) → C (snd dom) (elem dom)) → C (`Π fst snd) elem)
  → ∀ u elem → C u elem
U-ind C o t b v s p `One elem = o elem
U-ind C o t b v s p `Two elem = t elem
U-ind C o t b v s p `Base elem = b elem
U-ind C o t b v s p (`Vec u x) elem = v u x elem (U-ind C o t b v s p u)
U-ind C o t b v s p (`Σ u x) (fst , snd) = s u x fst snd (U-ind C o t b v s p u fst) (U-ind C o t b v s p (x fst) snd)
U-ind C o t b v s p (`Π u x) elem = p u x elem (U-ind C o t b v s p u) (λ dom → U-ind C o t b v s p (x dom) (elem dom))

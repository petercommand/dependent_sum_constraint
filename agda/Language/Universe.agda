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
  `Zero : U
  `One : U
  `Two : U
  `Base : U
  `Vec : (S : U) → ℕ → U
  `Σ : (S : U) → (⟦ S ⟧ → U) → U


⟦ `Zero ⟧ = ⊥
⟦ `One ⟧ = ⊤
⟦ `Two ⟧ = Bool
⟦ `Base ⟧ = f
⟦ `Vec ty x ⟧ = Vec ⟦ ty ⟧ x
⟦ `Σ fst snd ⟧ = Σ ⟦ fst ⟧ (λ f → ⟦ snd f ⟧)

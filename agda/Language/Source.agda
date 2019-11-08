open import Data.Field
open import Data.Finite
open import Data.Nat
open import Data.Vec

open import Relation.Binary.PropositionalEquality
module Language.Source (f : Set) (finite : Finite f) where

open import Language.TySize f finite
open import Language.Universe f


data Source : U → Set where
  Ind : ∀ {u} {m} → m ≡ tySize u → Vec ℕ m → Source u
  Lit : ∀ {u} → ⟦ u ⟧ → Source u
  Add : Source `Base → Source `Base → Source `Base



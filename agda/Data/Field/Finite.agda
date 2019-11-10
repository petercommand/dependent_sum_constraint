open import Agda.Builtin.Nat

open import Data.Field
open import Data.Nat
open import Data.Nat.Mod

module Data.Field.Finite where


record FiniteField (n : ℕ) : Set where
  field
    elem : ℕ

open FiniteField

isField : ∀ n → Field (FiniteField n)
isField n = record { _+_ = λ x x₁ → record { elem = mod (elem x + elem x₁) n }
                   ; _*_ = λ x x₁ → record { elem = mod (elem x * elem x₁) n } 
                   ; -_ = λ x → record { elem = mod (n - (elem x)) n }
                   ; zero = record { elem = 0 }
                   ; one = record { elem = 1 } }


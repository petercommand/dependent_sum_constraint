module Data.Nat.Properties2 where

open import Agda.Builtin.Nat
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

a-zero : ∀ a → a - zero ≡ a
a-zero zero = refl
a-zero (suc a) = refl

a-b+b≡a : ∀ a b → a ≥ b → (a - b) + b ≡ a
a-b+b≡a a .0 z≤n rewrite a-zero a | +-comm a 0 = refl
a-b+b≡a (suc n) (suc m) (s≤s a≥b) rewrite +-comm (n - m) (suc m)
                                        | +-comm m (n - m) = cong suc (a-b+b≡a n m a≥b)

a-b+b≡a₂ : ∀ a b → a ≥ b → b + (a - b) ≡ a
a-b+b≡a₂ a b p = trans (+-comm b (a ∸ b)) (a-b+b≡a a b p)

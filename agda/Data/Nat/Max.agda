module Data.Nat.Max where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

max : ℕ → ℕ → ℕ
max zero zero = zero
max zero (suc b) = suc b
max (suc a) zero = suc a
max (suc a) (suc b) = suc (max a b)

max-a-0≡a : ∀ a → max a 0 ≡ a
max-a-0≡a zero = refl
max-a-0≡a (suc a) = refl

max-left : ∀ a b → max a b ≥ a
max-left zero zero = z≤n
max-left zero (suc b) = z≤n
max-left (suc a) zero = s≤s ≤-refl
max-left (suc a) (suc b) = s≤s (max-left a b)

max-right : ∀ a b → max a b ≥ b
max-right zero zero = z≤n
max-right zero (suc b) = ≤-refl
max-right (suc a) zero = z≤n
max-right (suc a) (suc b) = s≤s (max-right a b)

max-monotoneᵣ : ∀ a b c → b ≥ c → max a b ≥ c
max-monotoneᵣ a b .0 z≤n = z≤n
max-monotoneᵣ zero .(suc _) .(suc _) (s≤s le) = s≤s le
max-monotoneᵣ (suc a) .(suc _) .(suc _) (s≤s le) = s≤s (max-monotoneᵣ a _ _ le)

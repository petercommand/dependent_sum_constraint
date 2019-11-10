open import Agda.Builtin.Nat hiding (_<_)

open import Data.Nat
open import Data.Nat.DivMod

module Data.Nat.Mod where
-- thin wrapper around builtin mod-helper


-- computes n mod m
mod : ℕ → ℕ → ℕ
mod n m = mod-helper 0 (m - 1) n (m - 1)


mod< : ∀ n m → m > 0 → mod n m < m
mod< n (suc m) (s≤s p) = m%n<n n m

open import Agda.Builtin.Nat

open import Data.Nat

module Data.Nat.Mod where
-- thin wrapper around builtin mod-helper



-- computes n mod m
mod : ℕ → ℕ → ℕ
mod n m = mod-helper 0 (m - 1) n (m - 1)

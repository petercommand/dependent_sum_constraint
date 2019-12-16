module Data.Binary where

open import Agda.Builtin.Nat

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Mod

open import Data.String

data Binary : Set where
  Zero : Binary
  One : Binary
  2n_ : Binary → Binary
  2n+1_ : Binary → Binary

{-# TERMINATING #-}
toBin : ℕ → Binary
toBin zero = Zero
toBin (suc zero) = One
toBin r@(suc (suc n)) with mod r 2
toBin r@(suc (suc n)) | zero = 2n toBin (r / 2)
toBin r@(suc (suc n)) | suc w = 2n+1 (toBin (r / 2))


showBin : Binary → String
showBin Zero = "0"
showBin One = "1"
showBin (2n bin) = showBin bin ++ "0"
showBin (2n+1 bin) = showBin bin ++ "1"


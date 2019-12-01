module TypeClass.Ord where

open import Data.Nat

postulate
  Ord : Set → Set
  natOrd : Ord ℕ

{-# COMPILE GHC Ord = type OrdDict #-}
{-# COMPILE GHC natOrd = OrdDict #-}


module TypeClass.Ord where

open import Data.Nat

postulate
  Ord : Set → Set
  natOrd : Ord ℕ
{-# FOREIGN GHC data OrdDict ord = Ord ord => OrdDict #-}
{-# COMPILE GHC Ord = type OrdDict #-}
{-# COMPILE GHC natOrd = OrdDict #-}


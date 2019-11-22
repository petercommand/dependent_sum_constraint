module Data.MaybeC where

data MaybeC (A : Set) : Set where
  nothing : MaybeC A
  just    : A → MaybeC A


{-# COMPILE GHC MaybeC = data Maybe (Nothing | Just) #-}

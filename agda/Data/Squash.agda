{-# OPTIONS --prop #-}
module Data.Squash where

open import Level

data Squash {ℓ} (A : Set ℓ) : Prop ℓ where
  sq : A → Squash A

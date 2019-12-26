{-# OPTIONS --prop #-}
module Data.ProductPrime where

open import Level
record Σ′ {a b} (A : Set a) (B : A → Prop b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ′ public



record Σ′′ {a b} (A : Prop a) (B : A → Prop b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ′′ public


infixr 4 _,_

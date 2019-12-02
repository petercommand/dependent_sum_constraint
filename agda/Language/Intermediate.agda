module Language.Intermediate (f : Set) where

open import Data.List
open import Data.Map
open import Data.Nat
open import Data.Product

open import Data.String

open import Language.Common

data Intermediate : Set where
  IAdd : f → List (f × Var) → Intermediate
         -- sums to zero
  IMul : (a : f) → (b : Var) → (c : Var) → (d : f) → (e : Var) → Intermediate
         -- a * b * c = d * e
  Hint : (Map Var ℕ → Map Var ℕ) → Intermediate
  Log : String → Intermediate

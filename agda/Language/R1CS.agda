module Language.R1CS (f : Set) where

open import Data.List
open import Data.Map
open import Data.Nat
open import Data.Product

open import Data.String

open import Language.Common

data R1CS : Set where
  IAdd : f → List (f × Var) → R1CS
         -- sums to zero
  IMul : (a : f) → (b : Var) → (c : Var) → (d : f) → (e : Var) → R1CS
         -- a * b * c = d * e
  Hint : (Map Var ℕ → Map Var ℕ) → R1CS
  Log : String → R1CS

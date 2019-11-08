module Data.Finite where

open import Data.List
open import Data.List.Membership.Propositional

record Finite {a} (f : Set a) : Set a where
  field
    elems : List f
    a∈elems : (a : f) → a ∈ elems

module Data.Finite where

open import Data.List
open import Data.List.Membership.Propositional

open import Data.Nat

open import Relation.Binary.PropositionalEquality

record Finite {a} (f : Set a) : Set a where
  field
    elems : List f
    size : ℕ
    a∈elems : (a : f) → a ∈ elems
    size≡len-elems : size ≡ length elems

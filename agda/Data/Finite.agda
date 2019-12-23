module Data.Finite where

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Occ

open import Data.Nat


open import Relation.Binary
open import Relation.Binary.PropositionalEquality

record Finite {a} (f : Set a) : Set a where
  field
    elems : List f
    size : ℕ
    a∈elems : (a : f) → a ∈ elems
    occ-1 : (a : f) (dec : Decidable {A = f} _≡_) → occ dec a elems ≡ 1
    size≡len-elems : size ≡ length elems

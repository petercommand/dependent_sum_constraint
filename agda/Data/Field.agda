module Data.Field where

open import Relation.Binary.PropositionalEquality
import Algebra.FunctionProperties

record Field {a} (f : Set a) : Set a where
  field
    _+_ _*_ : f → f → f
    -_ : f → f
    1/_ : f → f
    zero : f
    one : f

record IsField {a} (f : Set a) (field' : Field f) : Set a where
    open Field field'
    open Algebra.FunctionProperties {A = f} _≡_
    field
      +-identityˡ : LeftIdentity zero _+_
      +-identityʳ : RightIdentity zero _+_
      +-comm : Commutative _+_
      *-comm : Commutative _*_
      *-identityˡ : LeftIdentity one _*_
      *-identityʳ : RightIdentity one _*_
      *-zeroˡ : LeftZero zero _*_
      *-zeroʳ : RightZero zero _*_
      +-assoc : Associative _+_
      *-assoc : Associative _*_
      +-invˡ : LeftInverse zero -_ _+_
      +-invʳ : RightInverse zero -_ _+_
      *-invˡ : LeftInverse one 1/_ _*_
      *-invʳ : RightInverse one 1/_ _*_
      *-distr-+ˡ : _*_ DistributesOverˡ _+_
      *-distr-+ʳ : _*_ DistributesOverʳ _+_
      -one*f≡-f : ∀ f → (- one) * f ≡ - f


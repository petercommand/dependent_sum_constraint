module Data.Field where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
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
      *-invˡ : ∀ x → ¬ x ≡ zero → (1/ x) * x ≡ one
      *-invʳ : ∀ x → ¬ x ≡ zero → x * (1/ x) ≡ one
      *-distr-+ˡ : _*_ DistributesOverˡ _+_
      *-distr-+ʳ : _*_ DistributesOverʳ _+_
      -one*f≡-f : ∀ f → (- one) * f ≡ - f
      -zero≡zero : - zero ≡ zero

    a-b≡zero→a≡b : ∀ {a} {b} → a + (- b) ≡ zero → a ≡ b
    a-b≡zero→a≡b {a} {b} p =
        begin
          a
        ≡⟨ sym (+-identityʳ a) ⟩
          a + zero
        ≡⟨ cong (_+_ a) (sym (+-invˡ b)) ⟩
          (a + ((- b) + b))
        ≡⟨ sym (+-assoc a (- b) b) ⟩
          ((a + (- b)) + b)
        ≡⟨ cong (λ x → x + b) p ⟩
           zero + b
        ≡⟨ +-identityˡ b ⟩
          b
        ∎
      where
        open ≡-Reasoning

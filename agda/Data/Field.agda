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
      +-assoc : Associative _+_
      *-assoc : Associative _*_
      +-invˡ : LeftInverse zero -_ _+_
      +-invʳ : RightInverse zero -_ _+_
      *-invˡ : ∀ x → ¬ x ≡ zero → (1/ x) * x ≡ one
      *-invʳ : ∀ x → ¬ x ≡ zero → x * (1/ x) ≡ one
      *-distr-+ˡ : _*_ DistributesOverˡ _+_
      *-distr-+ʳ : _*_ DistributesOverʳ _+_
    *-zeroˡ : LeftZero zero _*_
    *-zeroˡ f = lem'''
      where
        lem : ((zero + zero) * f) ≡ (zero * f)
        lem = cong (_* f) (+-identityˡ zero)
        lem' : (zero * f) + (zero * f) ≡ zero * f
        lem' rewrite sym (*-distr-+ʳ f zero zero) = lem
        lem'' : ((zero * f) + (zero * f)) + (- (zero * f)) ≡ (zero * f) + (- (zero * f))
        lem'' = cong (_+ (- (zero * f))) lem'

        lem''' : zero * f ≡ zero
        lem''' with lem''
        ... | prf rewrite +-assoc (zero * f) (zero * f) (- (zero * f))
                        | +-invʳ (zero * f)
                        | +-identityʳ (zero * f) = prf
    *-zeroʳ : RightZero zero _*_
    *-zeroʳ f =
        begin
          f * zero
        ≡⟨ *-comm f zero ⟩
          zero * f
        ≡⟨ *-zeroˡ f ⟩
          zero
        ∎
      where
        open ≡-Reasoning
    -one*f≡-f : ∀ f → (- one) * f ≡ - f
    -one*f≡-f f = lem''
      where
        open ≡-Reasoning
        lem : (one * f) + ((- one) * f) ≡ zero
        lem =
          begin
            (one * f) + ((- one) * f)
          ≡⟨ sym (*-distr-+ʳ _ _ _) ⟩
            (one + (- one)) * f
          ≡⟨ cong (_* f) (+-invʳ one) ⟩
            zero * f
          ≡⟨ *-zeroˡ f ⟩
            zero
          ∎
        lem' : ((one * f) + ((- one) * f)) + (- f) ≡ - f
        lem' rewrite lem = +-identityˡ (- f)

        lem'' : (- one) * f ≡ - f
        lem'' rewrite sym lem'
                    | +-assoc (one * f) ((- one) * f) (- f)
                    | +-comm ((- one) * f) (- f)
                    | sym (+-assoc (one * f) (- f) ((- one) * f))
                    | *-identityˡ f
                    | +-invʳ f
                    | +-identityˡ ((- one) * f) = refl
    -zero≡zero : - zero ≡ zero
    -zero≡zero =
        begin
          - zero
        ≡⟨ sym (-one*f≡-f zero) ⟩
          (- one) * zero
        ≡⟨ *-zeroʳ (- one) ⟩
          zero
        ∎
      where
        open ≡-Reasoning
    -≡zero→≡zero : ∀ {f} → - f ≡ zero → f ≡ zero
    -≡zero→≡zero {f} eq =
        begin
          f
        ≡⟨ sym (+-identityʳ f) ⟩
          f + zero
        ≡⟨ sym (cong (f +_) eq) ⟩
          f + (- f)
        ≡⟨ +-invʳ f ⟩
          zero
        ∎
      where
        open ≡-Reasoning
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

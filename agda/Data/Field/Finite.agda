open import Agda.Builtin.Nat hiding (_<_)

open import Data.Empty
open import Data.Field
open import Data.Finite
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Mod
open import Data.Nat.Properties renaming (_≟_ to _≟ℕ_)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable using (False)
module Data.Field.Finite where


record FiniteField (n : ℕ) : Set where
  field
    elem : ℕ
    .elem<n : elem < n

open FiniteField

fieldElem : ∀ {n} {≢ : False (n ≟ℕ 0) } → ℕ → FiniteField n
fieldElem {suc n} m = record { elem = mod m (suc n) ; elem<n = mod< m (suc n) (s≤s z≤n) }

isField : ∀ n {≢0 : False (n ≟ℕ 0)} → Field (FiniteField n)
isField (suc n) = record { _+_ = λ x x₁ → record { elem = mod (elem x + elem x₁) (suc n) ; elem<n = mod< (elem x + elem x₁) (suc n) (s≤s z≤n) }
                         ; _*_ = λ x x₁ → record { elem = mod (elem x * elem x₁) (suc n) ; elem<n = mod< (elem x * elem x₁) (suc n) (s≤s z≤n) } 
                         ; -_ = λ x → record { elem = mod ((suc n) - (elem x)) (suc n) ; elem<n = mod< ((suc n) - (elem x)) (suc n) (s≤s z≤n) }
                         ; zero = record { elem = mod 0 (suc n) ; elem<n = s≤s z≤n }
                         ; one = record { elem = mod 1 (suc n) ; elem<n = mod< 1 (suc n) (s≤s z≤n) } }

private
  enumFieldElem : (n : ℕ) → (m : ℕ) → .(n > m) → List (FiniteField n)
  enumFieldElem n zero p = [ record { elem = zero ; elem<n = p } ]
  enumFieldElem n (suc m) p = record { elem = suc m ; elem<n = p } ∷ enumFieldElem n m (≤⇒pred≤ p)


  enumFieldElemSizePrf : ∀ n m p → suc m ≡ length (enumFieldElem n m p)
  enumFieldElemSizePrf n zero p = refl
  enumFieldElemSizePrf n (suc m) p = cong suc (enumFieldElemSizePrf n m
                                                 (≤-trans (s≤s (≤-step (≤-reflexive refl))) p))

  
  enumComplete : ∀ n m → (p : m < n) → record { elem = m ; elem<n = p } ∈ enumFieldElem n m p
  enumComplete n zero p = here refl
  enumComplete n (suc m) p = here refl

  enumComplete' : ∀ n m m' a p p' → m ≤′ m' → a ∈ enumFieldElem n m p → a ∈ enumFieldElem n m' p'
  enumComplete' n m .m a p p' ≤′-refl ant = ant
  enumComplete' n m .(suc _) a p p' (≤′-step prf) ant = there (enumComplete' n m _ a p
                                                                (≤-trans (s≤s (≤-step ≤-refl)) p') prf ant)

  enumPrf : ∀ n (a : FiniteField (suc n)) p → a ∈ enumFieldElem (suc n) n p
  enumPrf n record { elem = elem ; elem<n = elem<n } p =
            enumComplete' (suc n) elem n (record { elem = elem ; elem<n = elem<n })
                           (recompute ((suc elem) ≤? (suc n)) elem<n) p
                           (≤⇒≤′ (≤-pred (recompute (suc elem ≤? suc n) elem<n)))
                           (enumComplete (suc n) elem (recompute (suc elem ≤? suc n) elem<n))


isFinite : ∀ n {≢ : False (n ≟ℕ 0)} → Finite (FiniteField n)
isFinite (suc n) = record { elems = enumFieldElem (suc n) n ≤-refl
                          ; size = suc n
                          ; a∈elems = λ a → enumPrf n a ≤-refl
                          ; size≡len-elems = enumFieldElemSizePrf (suc n) n ≤-refl }

_≟_ : ∀ {n} {≢ : False (n ≟ℕ 0)} → Decidable {A = FiniteField n} _≡_
record { elem = elem₁ ; elem<n = elem<n₁ } ≟ record { elem = elem ; elem<n = elem<n } with elem ≟ℕ elem₁
(record { elem = elem₁ ; elem<n = elem<n₁ } ≟ record { elem = .elem₁ ; elem<n = elem<n }) | yes refl = yes refl
(record { elem = elem₁ ; elem<n = elem<n₁ } ≟ record { elem = elem ; elem<n = elem<n }) | no ¬p = no (λ x → ⊥-elim (¬p (cong FiniteField.elem (sym x))))


open import Agda.Builtin.Nat hiding (_<_)

open import Data.Empty
open import Data.Field
open import Data.Finite
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Mod
open import Data.Nat.Coprimality hiding (sym)
open import Data.Nat.GCD
open import Data.Nat.Primality
open import Data.Nat.Properties renaming (_≟_ to _≟ℕ_)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable using (False)
module Data.Field.Finite where


record FiniteField (n : ℕ) : Set where
  field
    elem : ℕ
    .nIsPrime : Prime n
    .elem<n : elem < n

open FiniteField

fieldElem : ∀ {n} {≢ : False (n ≟ℕ 0) } → Prime n → (m : ℕ) → FiniteField n
fieldElem {suc n} p m = record { elem = mod m (suc n)
                               ; nIsPrime = p
                               ; elem<n = mod< m (suc n) (s≤s z≤n)
                               }

multInv : ∀ {n} {≢ : False (n ≟ℕ 0)} → FiniteField n → FiniteField n
multInv {suc n} record { elem = zero ; nIsPrime = nIsPrime ; elem<n = elem<n } =
    record { elem = zero ; nIsPrime = nIsPrime ; elem<n = elem<n }
multInv {suc n} record { elem = (suc elem₁) ; nIsPrime = nIsPrime ; elem<n = elem<n } =
    record { elem = mod (inv (suc elem₁) (suc n) (lem (suc elem₁) (suc n) (GCD.sym gcd≡1) LemmaResult)) (suc n)
           ; nIsPrime = nIsPrime
           ; elem<n = mod< (inv (suc elem₁) (suc n) (lem (suc elem₁) (suc n) (GCD.sym gcd≡1) LemmaResult)) (suc n) (s≤s z≤n) }
  where
    cop = prime⇒coprime _ (recompute (prime? _) nIsPrime) (suc elem₁) (s≤s z≤n) (recompute ((suc (suc elem₁)) ≤? _) elem<n)
    gcd≡1 = coprime-gcd cop
    open Bézout
    LemmaResult = lemma (suc elem₁) (suc n)

    lem : ∀ m n → GCD m n 1 → Lemma m n → Identity 1 m n
    lem m n gcd (result d g b) with GCD.unique gcd g
    ... | refl = b

    inv : ∀ m n → Identity 1 m n → ℕ
    inv m n (+- x y eq) = x
    inv m n (-+ x y eq) = n - x

isField : ∀ n {≢0 : False (n ≟ℕ 0)} → Prime n → Field (FiniteField n)
isField (suc n) p = record { _+_ = λ x x₁ → record { elem = mod (elem x + elem x₁) (suc n)
                                                   ; nIsPrime = p
                                                   ; elem<n = mod< (elem x + elem x₁) (suc n) (s≤s z≤n) }
                         ; _*_ = λ x x₁ → record { elem = mod (elem x * elem x₁) (suc n)
                                                 ; nIsPrime = p
                                                 ; elem<n = mod< (elem x * elem x₁) (suc n) (s≤s z≤n) } 
                         ; -_ = λ x → record { elem = mod ((suc n) - (elem x)) (suc n)
                                             ; nIsPrime = p
                                             ; elem<n = mod< ((suc n) - (elem x)) (suc n) (s≤s z≤n) }
                         ; zero = record { elem = mod 0 (suc n)
                                         ; nIsPrime = p
                                         ; elem<n = s≤s z≤n }
                         ; one = record { elem = mod 1 (suc n)
                                        ; nIsPrime = p
                                        ; elem<n = mod< 1 (suc n) (s≤s z≤n) }
                         ; 1/_ = multInv }

private
  enumFieldElem : (n : ℕ) → Prime n → (m : ℕ) → .(n > m) → List (FiniteField n)
  enumFieldElem n prf zero p = [ record { elem = zero ; nIsPrime = prf ; elem<n = p } ]
  enumFieldElem n prf (suc m) p = record { elem = suc m ; nIsPrime = prf ; elem<n = p } ∷ enumFieldElem n prf m (≤⇒pred≤ p)


  enumFieldElemSizePrf : ∀ n prf m p → suc m ≡ length (enumFieldElem n prf m p)
  enumFieldElemSizePrf n prf zero p = refl
  enumFieldElemSizePrf n prf (suc m) p = cong suc (enumFieldElemSizePrf n prf m
                                                    (≤-trans (s≤s (≤-step (≤-reflexive refl))) p))

  
  enumComplete : ∀ n prf m → (p : m < n) → record { elem = m ; nIsPrime = prf ; elem<n = p } ∈ enumFieldElem n prf m p
  enumComplete n prf zero p = here refl
  enumComplete n prf (suc m) p = here refl

  enumComplete' : ∀ n prf m m' a p p' → m ≤′ m' → a ∈ enumFieldElem n prf m p → a ∈ enumFieldElem n prf m' p'
  enumComplete' n prf m .m a p p' ≤′-refl ant = ant
  enumComplete' n prf m .(suc _) a p p' (≤′-step prf') ant = there (enumComplete' n prf m _ a p
                                                                (≤-trans (s≤s (≤-step ≤-refl)) p') prf' ant)

  enumPrf : ∀ n prf (a : FiniteField (suc n)) p → a ∈ enumFieldElem (suc n) prf n p
  enumPrf n prf record { elem = elem ; elem<n = elem<n } p =
            enumComplete' (suc n) prf elem n (record { elem = elem ; elem<n = elem<n })
                           (recompute ((suc elem) ≤? (suc n)) elem<n) p
                           (≤⇒≤′ (≤-pred (recompute (suc elem ≤? suc n) elem<n)))
                           (enumComplete (suc n) prf elem (recompute (suc elem ≤? suc n) elem<n))


isFinite : ∀ n {≢ : False (n ≟ℕ 0)} → Prime n → Finite (FiniteField n)
isFinite (suc n) prf = record { elems = enumFieldElem (suc n) prf n ≤-refl
                              ; size = suc n
                              ; a∈elems = λ a → enumPrf n prf a ≤-refl
                              ; size≡len-elems = enumFieldElemSizePrf (suc n) prf n ≤-refl }

_≟_ : ∀ {n} {≢ : False (n ≟ℕ 0)} → Decidable {A = FiniteField n} _≡_
record { elem = elem₁ ; elem<n = elem<n₁ } ≟ record { elem = elem ; elem<n = elem<n } with elem ≟ℕ elem₁
(record { elem = elem₁ ; elem<n = elem<n₁ } ≟ record { elem = .elem₁ ; elem<n = elem<n }) | yes refl = yes refl
(record { elem = elem₁ ; elem<n = elem<n₁ } ≟ record { elem = elem ; elem<n = elem<n }) | no ¬p = no (λ x → ⊥-elim (¬p (cong FiniteField.elem (sym x))))


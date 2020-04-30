open import Agda.Builtin.Nat hiding (_<_)

open import Data.Empty
open import Data.Field
open import Data.Finite
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Occ
open import Data.List.Relation.Unary.Any
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Mod
open import Data.Nat.Coprimality hiding (sym)
open import Data.Nat.GCD
open import Data.Nat.Primality
open import Data.Nat.Properties renaming (_≟_ to _≟ℕ_)

open import Math.Arithmoi

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable using (False)
module Data.Field.Prime where


record PrimeField (n : ℕ) : Set where
  field
    elem : ℕ
    .nIsPrime : Prime n
    .elem<n : elem < n

open PrimeField

fieldElem : ∀ {n} {≢ : False (n ≟ℕ 0) } → Prime n → (m : ℕ) → PrimeField n
fieldElem {suc n} p m = record { elem = mod m (suc n)
                               ; nIsPrime = p
                               ; elem<n = mod< m (suc n) (s≤s z≤n)
                               }

multInv : ∀ {n} {≢ : False (n ≟ℕ 0)} → PrimeField n → PrimeField n
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

fastInv : ∀ {n} {≢ : False (n ≟ℕ 0)} → PrimeField n → PrimeField n
fastInv {suc n} record { elem = zero ; nIsPrime = nIsPrime ; elem<n = elem<n } =
    record { elem = zero ; nIsPrime = nIsPrime ; elem<n = elem<n }
fastInv {suc n} record { elem = (suc elem₁) ; nIsPrime = nIsPrime ; elem<n = elem<n } =
    record { elem = mod (getInv (suc elem₁) (suc n)) (suc n)
           ; nIsPrime = nIsPrime
           ; elem<n = mod< (getInv (suc elem₁) (suc n)) (suc n) (s≤s z≤n) }

isField : ∀ n {≢0 : False (n ≟ℕ 0)} → Prime n → Field (PrimeField n)
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
                         ; 1/_ = fastInv }

private
  enumFieldElem : (n : ℕ) → Prime n → (m : ℕ) → .(n > m) → List (PrimeField n)
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

  enumUniq-occ≡0 : ∀ n dec prf m a p p' → m < a → occ dec (record{ elem = a ; nIsPrime = prf ; elem<n = p }) (enumFieldElem n prf m p') ≡ 0
  enumUniq-occ≡0 n dec prf zero (suc n₁) p p' (s≤s le) with (dec (record { elem = suc n₁ ; nIsPrime = prf ; elem<n = p })
       (record { elem = zero ; nIsPrime = prf ; elem<n = p' }))
  enumUniq-occ≡0 n dec prf zero (suc n₁) p p' (s≤s le) | no ¬p = refl
  enumUniq-occ≡0 n dec prf (suc m) (suc n₁) p p' (s≤s le) with (dec (record { elem = suc n₁ ; nIsPrime = prf ; elem<n = p })
       (record { elem = suc m ; nIsPrime = prf ; elem<n = p' }))
  enumUniq-occ≡0 n dec prf (suc m) (suc .m) p p' (s≤s le) | yes refl = ⊥-elim (m+n≮n 0 m le)
  enumUniq-occ≡0 n dec prf (suc m) (suc n₁) p p' (s≤s le) | no ¬p = enumUniq-occ≡0 n dec prf m (suc n₁) p (≤-trans (s≤s (≤-step ≤-refl)) p') (≤-trans le (≤-step ≤-refl))
  
  enumUniq-occ≡1 : ∀ n dec prf m a p p' → a ≤ m → occ dec (record{ elem = a ; nIsPrime = prf ; elem<n = p }) (enumFieldElem n prf m p') ≡ 1
  enumUniq-occ≡1 n dec prf zero .0 p p' z≤n with (dec (record { elem = zero ; nIsPrime = prf ; elem<n = p })
       (record { elem = zero ; nIsPrime = prf ; elem<n = p' }))
  enumUniq-occ≡1 n dec prf zero .zero p p' z≤n | yes p₁ = refl
  enumUniq-occ≡1 n dec prf zero .zero p p' z≤n | no ¬p = ⊥-elim (¬p refl)
  enumUniq-occ≡1 n dec prf (suc m) .0 p p' z≤n with (dec (record { elem = 0 ; nIsPrime = prf ; elem<n = p })
       (record { elem = suc m ; nIsPrime = prf ; elem<n = p' }))
  enumUniq-occ≡1 n dec prf (suc m) .zero p p' z≤n | no ¬p = enumUniq-occ≡1 n dec prf m 0 p (≤-trans (≤-step ≤-refl) p') z≤n
  enumUniq-occ≡1 n dec prf (suc m) (suc m₁) p p' (s≤s le) with (dec (record { elem = suc m₁ ; nIsPrime = prf ; elem<n = p })
       (record { elem = suc m ; nIsPrime = prf ; elem<n = p' }))
  enumUniq-occ≡1 n dec prf (suc .m₁) (suc m₁) p p' (s≤s le) | yes refl = cong suc (enumUniq-occ≡0 n dec prf m₁ (suc m₁) p' (≤-trans (≤-step ≤-refl) p) ≤-refl)
  enumUniq-occ≡1 n dec prf (suc m) (suc m₁) p p' (s≤s le) | no ¬p = enumUniq-occ≡1 n dec prf m (suc m₁) p (≤-trans (≤-step ≤-refl) p') (≤∧≢⇒< le λ { refl → ¬p refl })

  enumUniq : ∀ n dec prf a p → occ dec a (enumFieldElem (suc n) prf n p) ≡ 1
  enumUniq n dec prf record { elem = elem ; nIsPrime = nIsPrime ; elem<n = elem<n } p = enumUniq-occ≡1 (suc n) dec prf n elem (recompute (_ ≤? _) elem<n) ≤-refl (lem (recompute (_ ≤? _) elem<n))
    where
      lem : suc elem ≤ suc n → elem ≤ n
      lem (s≤s t) = t
  
  enumPrf : ∀ n prf (a : PrimeField (suc n)) p → a ∈ enumFieldElem (suc n) prf n p
  enumPrf n prf record { elem = elem ; elem<n = elem<n } p =
            enumComplete' (suc n) prf elem n (record { elem = elem ; elem<n = elem<n })
                           (recompute ((suc elem) ≤? (suc n)) elem<n) p
                           (≤⇒≤′ (≤-pred (recompute (suc elem ≤? suc n) elem<n)))
                           (enumComplete (suc n) prf elem (recompute (suc elem ≤? suc n) elem<n))


isFinite : ∀ n {≢ : False (n ≟ℕ 0)} → Prime n → Finite (PrimeField n)
isFinite (suc n) prf = record { elems = enumFieldElem (suc n) prf n ≤-refl
                              ; size = suc n
                              ; a∈elems = λ a → enumPrf n prf a ≤-refl
                              ; size≡len-elems = enumFieldElemSizePrf (suc n) prf n ≤-refl
                              ; occ-1 = λ a dec → enumUniq n dec prf a ≤-refl }

_≟_ : ∀ {n} {≢ : False (n ≟ℕ 0)} → Decidable {A = PrimeField n} _≡_
record { elem = elem₁ ; elem<n = elem<n₁ } ≟ record { elem = elem ; elem<n = elem<n } with elem ≟ℕ elem₁
(record { elem = elem₁ ; elem<n = elem<n₁ } ≟ record { elem = .elem₁ ; elem<n = elem<n }) | yes refl = yes refl
(record { elem = elem₁ ; elem<n = elem<n₁ } ≟ record { elem = elem ; elem<n = elem<n }) | no ¬p = no (λ x → ⊥-elim (¬p (cong PrimeField.elem (sym x))))


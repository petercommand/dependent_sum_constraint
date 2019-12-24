module Data.List.Occ where

open import Data.Empty
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Misc
open import Data.List.Relation.Unary.Any
open import Data.Nat

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary



occAux : ∀ {ℓ} {A : Set ℓ} {a x : A} → Dec (a ≡ x) → ℕ → ℕ → ℕ
occAux (yes p) m n = m
occAux (no ¬p) m n = n

occAux₂ : ∀ {ℓ} {A : Set ℓ} (a x : A) (dec : Dec (a ≡ x)) m n → ¬ a ≡ x → occAux dec m n ≡ n
occAux₂ a x (yes p) m n neq = ⊥-elim (neq p)
occAux₂ a x (no ¬p) m n neq = refl

occ : ∀ {ℓ} {A : Set ℓ} → (Decidable {A = A} _≡_) → A → List A → ℕ
occ dec a [] = 0
occ dec a (x ∷ l) = occAux (dec a x) (suc (occ dec a l)) (occ dec a l)

occPrfIrr : ∀ {ℓ} {A : Set ℓ} → (dec dec' : Decidable {A = A} _≡_) → (v : A) (l : List A) → occ dec v l ≡ occ dec' v l
occPrfIrr dec dec' v [] = refl
occPrfIrr dec dec' v (x ∷ l) with dec v x | dec' v x
occPrfIrr dec dec' v (x ∷ l) | yes p | yes p₁ = cong suc (occPrfIrr dec dec' v l)
occPrfIrr dec dec' v (x ∷ l) | yes p | no ¬p = ⊥-elim (¬p p)
occPrfIrr dec dec' v (x ∷ l) | no ¬p | yes p = ⊥-elim (¬p p)
occPrfIrr dec dec' v (x ∷ l) | no ¬p | no ¬p₁ = occPrfIrr dec dec' v l

occLem : ∀ {ℓ} {A : Set ℓ} → (dec : Decidable {A = A} _≡_) → (x : A) (l l' : List A) → occ dec x (l ++ l') ≡ occ dec x l + occ dec x l'
occLem dec x [] l' = refl
occLem dec x (x₁ ∷ l) l' with dec x x₁
occLem dec x (x₁ ∷ l) l' | yes p = cong suc (occLem dec x l l')
occLem dec x (x₁ ∷ l) l' | no ¬p = occLem dec x l l'

mem-occ : ∀ {ℓ} {A : Set ℓ} dec x (l : List A) → x ∈ l → occ dec x l ≥ 1
mem-occ dec x .(x ∷ _) (here refl) with dec x x
mem-occ dec x .(x ∷ _) (here refl) | yes p = s≤s z≤n
mem-occ dec x .(x ∷ _) (here refl) | no ¬p = ⊥-elim (¬p refl)
mem-occ dec x (x₁ ∷ xs) (there mem) with dec x x₁
mem-occ dec x (x₁ ∷ xs) (there mem) | yes p = s≤s z≤n
mem-occ dec x (x₁ ∷ xs) (there mem) | no ¬p = mem-occ dec x xs mem

¬mem-occ : ∀ {ℓ} {A : Set ℓ} dec x (l : List A) → ¬ x ∈ l → occ dec x l ≡ 0
¬mem-occ dec x [] ¬∈ = refl
¬mem-occ dec x (x₁ ∷ l) ¬∈ with dec x x₁
¬mem-occ dec x (x₁ ∷ l) ¬∈ | yes refl = ⊥-elim (¬∈ (here refl))
¬mem-occ dec x (x₁ ∷ l) ¬∈ | no ¬p = ¬mem-occ dec x l λ x₂ → ¬∈ (there x₂)

occ≡1→memUnique : ∀ {ℓ} {A : Set ℓ} → ∀ dec l l' → (uniq : ∀ v → ¬ v ∈ l' → occ dec v l ≡ 1) → ∀ (a : A) → (m₁ m₂ : a ∈ l) → ¬ a ∈ l' → m₁ ≡ m₂
occ≡1→memUnique dec .(a ∷ _) l' uniq a (here refl) (here refl) ¬∈ = refl
occ≡1→memUnique dec (a ∷ xs) l' uniq a (here refl) (there m₂) ¬∈ with uniq a ¬∈
... | occPrf with dec a a
occ≡1→memUnique dec (a ∷ xs) l' uniq a (here refl) (there m₂) ¬∈ | occPrf | yes p with s≤s (mem-occ dec a xs m₂)
... | occ≥2 rewrite occPrf with occ≥2
... | s≤s ()
occ≡1→memUnique dec (a ∷ xs) l' uniq a (here refl) (there m₂) ¬∈ | occPrf | no ¬p = ⊥-elim (¬p refl)
occ≡1→memUnique dec (a ∷ xs) l' uniq a (there m₁) (here refl) ¬∈ with uniq a ¬∈
... | occPrf with dec a a
occ≡1→memUnique dec (a ∷ xs) l' uniq a (there m₁) (here refl) ¬∈ | occPrf | yes p with s≤s (mem-occ dec a xs m₁)
... | occ≥2 rewrite occPrf with occ≥2
... | s≤s ()
occ≡1→memUnique dec (a ∷ xs) l' uniq a (there m₁) (here refl) ¬∈ | occPrf | no ¬p = ⊥-elim (¬p refl)
occ≡1→memUnique dec (x ∷ xs) l' uniq a (there m₁) (there m₂) ¬∈ with uniq a ¬∈
... | occPrf with dec a x
occ≡1→memUnique dec (x ∷ xs) l' uniq a (there m₁) (there m₂) ¬∈ | occPrf | yes p with s≤s (mem-occ dec a xs m₁)
... | occ≥2 rewrite occPrf with occ≥2
... | s≤s () 
occ≡1→memUnique dec (x ∷ xs) l' uniq a (there m₁) (there m₂) ¬∈ | occPrf | no ¬p = cong there (occ≡1→memUnique dec xs (x ∷ l') (λ v x₁ → trans (sym (occAux₂ v x (dec v x) _ _ λ x₂ → x₁ (here x₂))) (uniq v λ x₂ → x₁ (there x₂))) a m₁ m₂ λ x₁ → ¬∈ (lem x₁))
    where
      lem : ∀ (mem : a ∈ x ∷ l') → a ∈ l'
      lem (here refl) = ⊥-elim (¬p refl)
      lem (there mem) = mem

occ-tail : ∀ {ℓ} {A : Set ℓ} dec (x : A) (l : List A) → (∀ v → v ∈ (x ∷ l) → occ dec v (x ∷ l) ≡ 1) → (∀ v → v ∈ l → occ dec v l ≡ 1)
occ-tail dec x l p v mem with p v (there mem)
... | p₁ with dec v x
occ-tail dec x l p .x mem | p₁ | yes refl with mem-occ dec x l mem
... | oc rewrite cong pred p₁ with oc
... | ()
occ-tail dec x l p v mem | p₁ | no ¬p = p₁

dec-mem : ∀ {ℓ} {A : Set ℓ} (dec : Decidable {A = A} _≡_) → ∀ (x : A) (l : List A) → Dec (x ∈ l)
dec-mem dec x [] = no (λ ())
dec-mem dec x (x₁ ∷ l) with dec x x₁
dec-mem dec x (.x ∷ l) | yes refl = yes (here refl)
dec-mem dec x (x₁ ∷ l) | no ¬p with dec-mem dec x l
dec-mem dec x (x₁ ∷ l) | no ¬p | yes p = yes (there p)
dec-mem dec x (x₁ ∷ l) | no ¬p | no ¬p₁ = no (λ x₂ → lem x₂ ¬p ¬p₁)
  where
    lem : x ∈ (x₁ ∷ l) → ¬ x ≡ x₁ → ¬ x ∈ l → ⊥
    lem (here px) neg neg' = neg px
    lem (there mem) neg neg' = ¬p₁ mem

occ-tail0 : ∀ {ℓ} {A : Set ℓ} dec (x : A) (l : List A) → (∀ v → v ∈ (x ∷ l) → occ dec v (x ∷ l) ≡ 1) → occ dec x l ≡ 0
occ-tail0 dec x l p with p x (here refl)
... | p₁ with dec x x
occ-tail0 dec x l p | p₁ | yes p₂ with dec-mem dec x l
occ-tail0 dec x l p | p₁ | yes p₂ | yes p₃ with mem-occ dec x l p₃
... | oc rewrite cong pred p₁ with oc
... | ()
occ-tail0 dec x l p | p₁ | yes p₂ | no ¬p = ¬mem-occ dec x l ¬p
occ-tail0 dec x l p | p₁ | no ¬p = ⊥-elim (¬p refl)


occ-0-¬∈ : ∀ {ℓ} {A : Set ℓ} dec (x : A) (l : List A) → occ dec x l ≡ 0 → ¬ x ∈ l
occ-0-¬∈ dec x l oc mem with mem-occ dec x l mem
... | prf rewrite oc with prf
... | ()

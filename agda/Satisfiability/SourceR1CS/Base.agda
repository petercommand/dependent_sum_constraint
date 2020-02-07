{-# OPTIONS --prop #-}

open import Agda.Builtin.Nat

open import Data.Bool
open import Data.Empty
open import Data.Field
open import Data.Finite
open import Data.List hiding (lookup; head; splitAt)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any hiding (head)
open import Data.Nat
open import Data.Nat.Primality


open import Data.Product hiding (map)
open import Data.ProductPrime
open import Data.Vec hiding (_>>=_; splitAt) renaming (_++_ to _V++_)
open import Data.Vec.AllProp
open import Data.Vec.Split
open import Data.Squash
open import Data.String hiding (_≈_; _≟_; _++_)
open import Data.Sum
open import Data.Unit


open import Function

open import Language.Common

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

import Relation.Binary.HeterogeneousEquality
module HE = Relation.Binary.HeterogeneousEquality
open import Relation.Binary.HeterogeneousEquality.Core
open import Relation.Nullary
module Satisfiability.SourceR1CS.Base (f : Set) (_≟F_ : Decidable {A = f} _≡_) (field' : Field f) (isField : IsField f field')
     (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f)
        (ℕtoF-1≡1 : ℕtoF 1 ≡ Field.one field')
        (ℕtoF-0≡0 : ℕtoF 0 ≡ Field.zero field') (prime : ℕ) (isPrime : Prime prime) where


open import Language.TySize f finite
open import Language.Universe f
open import Language.R1CS f


open Field field' renaming ( _+_ to _+F_
                           ; _*_ to _*F_
                           ; -_ to -F_
                           ; 1/_ to 1F/_
                           ; zero to zerof
                           ; one to onef)
open IsField isField
open import Compile.SourceR1CS f field' finite showf fToℕ ℕtoF hiding (SI-Monad)
import Compile.SourceR1CS
open Compile.SourceR1CS.SI-Monad f field' finite showf fToℕ ℕtoF


output : ∀ {a} {b} {c} {d} {S : Set a} {W : Set b} {A : Set c} {P : W → Prop d} → Σ′ (S × W × A) (λ prod → P (proj₁ (proj₂ prod))) → A
output ((s , w , a) , _) = a

writerOutput : ∀ {a} {b} {c} {d} {S : Set a} {W : Set b} {A : Set c} {P : W → Prop d} → Σ′ (S × W × A) (λ prod → P (proj₁ (proj₂ prod))) → W
writerOutput ((s , w , a) , _) = w

varOut : ∀ {a} {b} {c} {d} {S : Set a} {W : Set b} {A : Set c} {P : W → Prop d} → Σ′ (S × W × A) (λ prod → P (proj₁ (proj₂ prod))) → S
varOut ((s , _ , _) , _) = s

writerInv : ∀ {a} {b} {c} {d} {S : Set a} {W : Set b} {A : Set c} {P : W → Prop d} → (p : Σ′ (S × W × A) (λ prod → P (proj₁ (proj₂ prod)))) → P (proj₁ (proj₂ (fst p)))
writerInv ((s , w , a) , inv) = inv

_≈_ : ℕ → ℕ → Prop
x ≈ y = Squash (ℕtoF x ≡ ℕtoF y)

≈-refl : ∀ {n} → n ≈ n
≈-refl = sq refl

≈-sym : ∀ {m n} → m ≈ n → n ≈ m
≈-sym (sq eq) = sq (sym eq)

≈-trans : ∀ {m n o} → m ≈ n → n ≈ o → m ≈ o
≈-trans (sq eq₁) (sq eq₂) = sq (trans eq₁ eq₂)

data ListLookup : Var → List (Var × ℕ) → ℕ → Prop where
  LookupHere : ∀ v l n n' → n ≈ n' → ListLookup v ((v , n) ∷ l) n'
  LookupThere : ∀ v l n t → ListLookup v l n → ¬ v ≡ proj₁ t → ListLookup v (t ∷ l) n

data BatchListLookup : {n : ℕ} → Vec Var n → List (Var × ℕ) → Vec ℕ n → Prop where
  BatchLookupNil : ∀ l → BatchListLookup [] l []
  BatchLookupCons : ∀ {len} v n (vec₁ : Vec Var len) vec₂ l
        → ListLookup v l n
        → BatchListLookup vec₁ l vec₂
        → BatchListLookup (v ∷ vec₁) l (n ∷ vec₂)

BatchListLookup-Head : ∀ {n} {vec : Vec Var (suc n)}
  → {l : List (Var × ℕ)}
  → {val : Vec ℕ (suc n)}
  → BatchListLookup vec l val
  → ListLookup (head vec) l (head val)
BatchListLookup-Head (BatchLookupCons v n vec₁ vec₂ l x look) = x

BatchListLookup-++ : ∀ {m n} (vec : Vec Var m) (val : Vec Var m) {vec' : Vec Var n} {val' : Vec ℕ n}
  → {l : List (Var × ℕ)}
  → BatchListLookup vec l val
  → BatchListLookup vec' l val'
  → BatchListLookup (vec V++ vec') l (val V++ val')
BatchListLookup-++ .[] .[] (BatchLookupNil l) look₂ = look₂
BatchListLookup-++ .(v ∷ vec₁) .(n ∷ vec₂) (BatchLookupCons v n vec₁ vec₂ l x look₁) look₂ = BatchLookupCons v n _ _ l x (BatchListLookup-++ vec₁ vec₂ look₁ look₂)


BatchListLookup-Split₁ :
  ∀ a b → (vec : Vec Var (a + b))
     → (l : List (Var × ℕ))
     → (val : Vec ℕ (a + b))
     → (vec₁ : Vec Var a) → (vec₂ : Vec Var b)
     → (val₁ : Vec ℕ a) → (val₂ : Vec ℕ b)
     → splitAt a vec ≡ (vec₁ , vec₂)
     → splitAt a val ≡ (val₁ , val₂)
     → BatchListLookup vec l val
     → BatchListLookup vec₁ l val₁
BatchListLookup-Split₁ zero b vec l val [] vec₂ [] val₂ eq₁ eq₂ look = BatchLookupNil l
BatchListLookup-Split₁ (suc a) b (x ∷ vec) l (x₁ ∷ val) (.x ∷ .(proj₁ (splitAt a vec))) .(proj₂ (splitAt a vec)) (.x₁ ∷ .(proj₁ (splitAt a val))) .(proj₂ (splitAt a val)) refl refl (BatchLookupCons .x .x₁ .vec .val .l x₂ look)
   with splitAt a vec | inspect (splitAt a) vec
... | fst , snd | [ eq₁ ] with splitAt a val | inspect (splitAt a) val
... | fstv , sndv | [ eq₂ ] = BatchLookupCons x x₁ fst fstv l x₂ (BatchListLookup-Split₁ a b vec l val fst snd fstv sndv eq₁ eq₂ look)

BatchListLookup-Split₂ :
  ∀ a b → (vec : Vec Var (a + b))
     → (l : List (Var × ℕ))
     → (val : Vec ℕ (a + b))
     → (vec₁ : Vec Var a) → (vec₂ : Vec Var b)
     → (val₁ : Vec ℕ a) → (val₂ : Vec ℕ b)
     → splitAt a vec ≡ (vec₁ , vec₂)
     → splitAt a val ≡ (val₁ , val₂)
     → BatchListLookup vec l val
     → BatchListLookup vec₂ l val₂
BatchListLookup-Split₂ .0 b vec l val [] .vec [] .val refl refl look = look
BatchListLookup-Split₂ (suc a) b (x₂ ∷ vec) l (x₃ ∷ val) (.x₂ ∷ .(proj₁ (splitAt a vec))) .(proj₂ (splitAt a vec)) (.x₃ ∷ .(proj₁ (splitAt a val))) .(proj₂ (splitAt a val)) refl refl (BatchLookupCons .x₂ .x₃ .vec .val .l x look) 
   with splitAt a vec | inspect (splitAt a) vec
... | fst , snd | [ eq₁ ] with splitAt a val | inspect (splitAt a) val
... | fstv , sndv | [ eq₂ ] = BatchListLookup-Split₂ a b vec l val fst snd fstv sndv eq₁ eq₂ look

subst′ : ∀ {ℓ} {ℓ'} → {A : Set ℓ} → (P : A → Prop ℓ') → ∀ {x} {y} → x ≡ y → P x → P y
subst′ _ refl px = px

BatchListLookupLenSubst : ∀ {len} {len₁} {l} → (vec val : Vec ℕ len) (prf : len ≡ len₁) → BatchListLookup vec l val
   → BatchListLookup (subst (Vec ℕ) prf vec) l (subst (Vec ℕ) prf val)
BatchListLookupLenSubst {len} {len₁} {l} vec val refl look = look

BatchListLookup-MaxTySplit₁ :
  ∀ u (uval : ⟦ u ⟧) (x : ⟦ u ⟧ → U) l
  → (vec : Vec Var (maxTySizeOver (enum u) x))
  → (vec₁ : Vec Var (tySize (x uval)))
  → (val : Vec Var (maxTySizeOver (enum u) x))
  → (val₁ : Vec Var (tySize (x uval)))
  → proj₁ (maxTySplit u uval x vec) ≡ vec₁
  → proj₁ (maxTySplit u uval x val) ≡ val₁
  → BatchListLookup vec l val
  → BatchListLookup vec₁ l val₁
BatchListLookup-MaxTySplit₁ u uval x l vec vec₁ val val₁ eq₁ eq₂ look =
  let
      sub₁ = BatchListLookupLenSubst vec val (maxTyVecSizeEq u uval x) look  
      hyp = BatchListLookup-Split₁ (tySize (x uval)) _ (subst (Vec ℕ) (maxTyVecSizeEq u uval x) vec) l (subst (Vec ℕ) (maxTyVecSizeEq u uval x) val)  (proj₁ (maxTySplit u uval x vec)) (proj₂ (maxTySplit u uval x vec)) (proj₁ (maxTySplit u uval x val)) (proj₂ (maxTySplit u uval x val)) refl refl sub₁
      hyp₁ = subst′ (λ t → BatchListLookup t l (proj₁ (maxTySplit u uval x val))) eq₁ hyp
      hyp₂ = subst′ (λ t → BatchListLookup vec₁ l t) eq₂ hyp₁
  in hyp₂

BatchListLookup-MaxTySplit₂ :
  ∀ u (uval : ⟦ u ⟧) (x : ⟦ u ⟧ → U) l
  → (vec : Vec Var (maxTySizeOver (enum u) x))
  → (vec₁ : Vec Var (maxTySizeOver (enum u) x - tySize (x uval)))
  → (val : Vec Var (maxTySizeOver (enum u) x))
  → (val₁ : Vec Var (maxTySizeOver (enum u) x - tySize (x uval)))
  → proj₂ (maxTySplit u uval x vec) ≡ vec₁
  → proj₂ (maxTySplit u uval x val) ≡ val₁
  → BatchListLookup vec l val
  → BatchListLookup vec₁ l val₁
BatchListLookup-MaxTySplit₂ u uval x l vec vec₁ val val₁ eq₁ eq₂ look = 
  let
    sub₁ = BatchListLookupLenSubst vec val (maxTyVecSizeEq u uval x) look  
    hyp = BatchListLookup-Split₂ (tySize (x uval)) _ (subst (Vec ℕ) (maxTyVecSizeEq u uval x) vec) l (subst (Vec ℕ) (maxTyVecSizeEq u uval x) val)  (proj₁ (maxTySplit u uval x vec)) (proj₂ (maxTySplit u uval x vec)) (proj₁ (maxTySplit u uval x val)) (proj₂ (maxTySplit u uval x val)) refl refl sub₁
    hyp₁ = subst′ (λ t → BatchListLookup t l (proj₂ (maxTySplit u uval x val))) eq₁ hyp
    hyp₂ = subst′ (λ t → BatchListLookup vec₁ l t) eq₂ hyp₁
  in hyp₂

BatchListLookupLenSubst' : ∀ n {m} {o} → (p : n + m ≡ o) → ∀ sol
   → (vec : Vec ℕ o)
   → (vec' : Vec ℕ n)
   → (vec'' : Vec ℕ m)
   → (val' : Vec ℕ n)
   → (val'' : Vec ℕ m)
   → vec ≅ vec' V++ vec''
   → BatchListLookup vec' sol val'
   → BatchListLookup vec'' sol val''
   → BatchListLookup vec sol (subst (Vec ℕ) p (val' V++ val''))
BatchListLookupLenSubst' n refl sol .(vec' V++ vec'') vec' vec'' val' val'' refl look₁ look₂ = BatchListLookup-++ vec' val' look₁ look₂
data ⊥′ : Prop where


⊥′→⊥ : ⊥′ → ⊥
⊥′→⊥ ()

⊥→⊥′ : ⊥ → ⊥′
⊥→⊥′ ()

⊥-elim′ : ∀ {w} {Whatever : Prop w} → ⊥ → Whatever
⊥-elim′ ()

-- ListLookup `respects` _≈_

ListLookup-Respects-≈ : ∀ v l n n' → n ≈ n' → ListLookup v l n → ListLookup v l n'
ListLookup-Respects-≈ v .((v , n₁) ∷ l) n n' (sq eq) (LookupHere .v l n₁ .n (sq x)) = LookupHere v l n₁ n' (sq (trans x eq))
ListLookup-Respects-≈ v .(t ∷ l) n n' eq (LookupThere .v l .n t look x) = LookupThere v l n' t (ListLookup-Respects-≈ v l n n' eq look) x

ListLookup-≈ : ∀ {v} {l} {n} {n'} → ListLookup v l n → ListLookup v l n' → n ≈ n'
ListLookup-≈ {v} .{(v , n₁) ∷ l} {n} {n'} (LookupHere .v l n₁ .n (sq x)) (LookupHere .v .l .n₁ .n' (sq x₁)) = sq (trans (sym x) x₁)
ListLookup-≈ {v} .{(v , n₁) ∷ l} {n} {n'} (LookupHere .v l n₁ .n x) (LookupThere .v .l .n' .(v , n₁) look₂ x₁) = ⊥-elim′ (x₁ refl)
ListLookup-≈ {v} .{(v , n₁) ∷ l} {n} {n'} (LookupThere .v l .n .(v , n₁) look₁ x) (LookupHere .v .l n₁ .n' x₁) = ⊥-elim′ (x refl)
ListLookup-≈ {v} .{(t ∷ l)} {n} {n'} (LookupThere .v l .n t look₁ x) (LookupThere .v .l .n' .t look₂ x₁) = ListLookup-≈ look₁ look₂

data LinearCombVal (solution : List (Var × ℕ)) : List (f × Var) → f → Prop where
  LinearCombValBase : LinearCombVal solution [] zerof
  LinearCombValCons : ∀ coeff var varVal {l} {acc}
      → ListLookup var solution varVal
      → LinearCombVal solution l acc
      → LinearCombVal solution ((coeff , var) ∷ l) ((coeff *F ℕtoF varVal) +F acc)

data R1CSSolution (solution : List (Var × ℕ)) : R1CS → Prop where
  addSol : ∀ {coeff} {linComb} {linCombVal}
                 → LinearCombVal solution linComb linCombVal
                 → linCombVal +F coeff ≡ zerof
                 → R1CSSolution solution (IAdd coeff linComb)
  multSol : ∀ a b bval c cval d e eval
                 → ListLookup b solution bval
                 → ListLookup c solution cval
                 → ListLookup e solution eval
                 → ((a *F (ℕtoF bval)) *F (ℕtoF cval)) ≡ (d *F (ℕtoF eval))
                 → R1CSSolution solution (IMul a b c d e)
  hintSol : ∀ f → R1CSSolution solution (Hint f) -- Hint does not have to be solved
  logSol : ∀ s → R1CSSolution solution (Log s)

BuilderProdSol : Builder × Builder → List (Var × ℕ) → Prop
BuilderProdSol (fst , snd) sol = ∀ x → x ∈ (fst (snd [])) → R1CSSolution sol x

data isBool : ℕ → Set where
  isZero : ∀ n → ℕtoF n ≡ zerof → isBool n
  isOne : ∀ n → ℕtoF n ≡ onef → isBool n

data isBoolStrict : ℕ → Set where
  isZeroS : ∀ {n} → n ≡ 0 → isBoolStrict n
  isOneS : ∀ {n} → n ≡ 1 → isBoolStrict n

isBoolStrict→isBool : ∀ {n} → isBoolStrict n → isBool n
isBoolStrict→isBool (isZeroS refl) = isZero 0 ℕtoF-0≡0
isBoolStrict→isBool (isOneS refl) = isOne 1 ℕtoF-1≡1

BuilderProdSolSubsetImp : ∀ b₁ b₂ b₃ b₄ (b₁₂ : Builder × Builder) (b₃₄ : Builder × Builder) sol
    → (b₁ , b₂) ≡ b₁₂ → (b₃ , b₄) ≡ b₃₄
    → (∀ x → x ∈ (b₁ (b₂ [])) → x ∈ (b₃ (b₄ [])))
    → BuilderProdSol (b₃ , b₄) sol → BuilderProdSol (b₁ , b₂) sol 
BuilderProdSolSubsetImp b₁ b₂ b₃ b₄ b₁₂ b₃₄ sol refl refl subs isSol x x∈b₁₂ = isSol x (subs x x∈b₁₂)

writerOutput->>=-Decomp : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'}
    → (p₁ : SI-Monad A)
    → (p₂ : A → SI-Monad B)
    → ∀ r init
    → let p₁′ = p₁ ((r , prime) , init)
          wo = writerOutput ((p₁ >>= p₂) ((r , prime) , init))
          wo₁ = writerOutput p₁′
          wo₂ = writerOutput (p₂ (output p₁′) ((r , prime) , varOut p₁′))
      in Squash (proj₁ wo (proj₂ wo []) ≡ (proj₁ wo₁ [] ++ proj₁ wo₂ []) ++ (proj₂ wo₁ [] ++ proj₂ wo₂ []))
writerOutput->>=-Decomp p₁ p₂ r init with writerInv ((p₁ >>= p₂) ((r , prime) , init))
... | sq inv₁ with writerInv (p₁ ((r , prime) , init))
... | sq inv₂ with let p₁′ = p₁ ((r , prime) , init)
                   in writerInv (p₂ (output p₁′) ((r , prime) , (varOut p₁′)))
... | sq inv₃ = sq (
            let p₁′ = p₁ ((r , prime) , init)
                wo = writerOutput ((p₁ >>= p₂) ((r , prime) , init))
                wo₁ = writerOutput p₁′
                wo₂ = writerOutput (p₂ (output p₁′) ((r , prime) , varOut p₁′))
            in begin
                  proj₁ wo (proj₂ wo [])
               ≡⟨ proj₁ (inv₁ (proj₂ wo [])) ⟩
                  proj₁ wo [] ++ proj₂ wo []
               ≡⟨ refl ⟩
                  proj₁ wo₁ (proj₁ wo₂ []) ++ (proj₂ wo₁ (proj₂ wo₂ []))
               ≡⟨ cong (λ x → x ++ (proj₂ wo₁ (proj₂ wo₂ []))) (proj₁ (inv₂ (proj₁ wo₂ []))) ⟩
                  (proj₁ wo₁ [] ++ proj₁ wo₂ []) ++ (proj₂ wo₁ (proj₂ wo₂ []))
               ≡⟨ cong (λ x → (proj₁ wo₁ [] ++ proj₁ wo₂ []) ++ x) (proj₂ (inv₂ (proj₂ wo₂ []))) ⟩
                  (proj₁ wo₁ [] ++ proj₁ wo₂ []) ++ (proj₂ wo₁ [] ++ proj₂ wo₂ [])
               ∎)
         where
           open ≡-Reasoning


BuilderProdSol->>=⁻₁ : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'}
    → (p₁ : SI-Monad A)
    → (p₂ : A → SI-Monad B)
    → ∀ r init sol
    → BuilderProdSol (writerOutput ((p₁ >>= p₂) ((r , prime) , init))) sol
    → BuilderProdSol (writerOutput (p₁ ((r , prime) , init))) sol
BuilderProdSol->>=⁻₁ p₁ p₂ r init sol isSol x x∈p₁ with writerInv ((p₁ >>= p₂) ((r , prime) , init))
... | sq inv₁ with writerInv (p₁ ((r , prime) , init))
... | sq inv₂ with let p₁′ = p₁ ((r , prime) , init)
                   in writerInv (p₂ (output p₁′) ((r , prime) , (varOut p₁′)))
... | sq inv₃ with writerOutput->>=-Decomp p₁ p₂ r init
... | sq lemEq = isSol x lem

  where
    lem : let wo = writerOutput ((p₁ >>= p₂) ((r , prime) , init))
          in x ∈ proj₁ wo (proj₂ wo [])
    lem rewrite lemEq
              | (let p₁′ = p₁ ((r , prime) , init)
                     wo₁ = writerOutput p₁′
                 in proj₁ (inv₂ (proj₂ wo₁ [])))
        with ∈-++⁻ (let p₁′ = p₁ ((r , prime) , init)
                        wo₁ = writerOutput p₁′
                    in proj₁ wo₁ []) x∈p₁
    ... | inj₁ x∈proj₁ = ∈-++⁺ˡ (∈-++⁺ˡ x∈proj₁)
    ... | inj₂ x∈proj₂ = ∈-++⁺ʳ (let
                                    p₁′ = p₁ ((r , prime) , init)
                                    p₂′ = p₂ (output p₁′) ((r , prime) , (varOut p₁′))
                                    wo₁ = writerOutput p₁′
                                    wo₂ = writerOutput p₂′
                                  in proj₁ wo₁ [] ++ proj₁ wo₂ []) (∈-++⁺ˡ x∈proj₂)
BuilderProdSol->>=⁻₂ : ∀ {ℓ} {ℓ'} {A : Set ℓ} {B : Set ℓ'}
    → (p₁ : SI-Monad A)
    → (p₂ : A → SI-Monad B)
    → ∀ r init sol
    → BuilderProdSol (writerOutput ((p₁ >>= p₂) ((r , prime) , init))) sol
    → BuilderProdSol (writerOutput (p₂ (output (p₁ ((r , prime) , init))) ((r , prime) , varOut (p₁ ((r , prime) , init))))) sol
BuilderProdSol->>=⁻₂ p₁ p₂ r init sol isSol x x∈p₂ with writerInv ((p₁ >>= p₂) ((r , prime) , init))
... | sq inv₁ with writerInv (p₁ ((r , prime) , init))
... | sq inv₂ with let p₁′ = p₁ ((r , prime) , init)
                   in writerInv (p₂ (output p₁′) ((r , prime) , (varOut p₁′)))
... | sq inv₃ with writerOutput->>=-Decomp p₁ p₂ r init
... | sq lemEq = isSol x lem

  where
    lem : let wo = writerOutput ((p₁ >>= p₂) ((r , prime) , init))
          in x ∈ proj₁ wo (proj₂ wo [])
    lem rewrite lemEq
              | (let p₁′ = p₁ ((r , prime) , init)
                     wo₂ = writerOutput (p₂ (output p₁′) ((r , prime) , varOut p₁′))
                 in proj₁ (inv₃ (proj₂ wo₂ [])))
         with ∈-++⁻ (let p₁′ = p₁ ((r , prime) , init)
                         wo₂ = writerOutput (p₂ (output p₁′) ((r , prime) , varOut p₁′))
                      in proj₁ wo₂ []) x∈p₂
    ... | inj₁ x∈proj₁ = let
                             p₁′ = p₁ ((r , prime) , init)
                             wo₁ = writerOutput p₁′ 
                          in ∈-++⁺ˡ (∈-++⁺ʳ (proj₁ wo₁ []) x∈proj₁)
    ... | inj₂ x∈proj₂ = let
                             p₁′ = p₁ ((r , prime) , init)
                             p₂′ = p₂ (output p₁′) ((r , prime) , varOut p₁′)
                             wo₁ = writerOutput p₁′
                             wo₂ = writerOutput p₂′
                          in ∈-++⁺ʳ (proj₁ wo₁ [] ++ proj₁ wo₂ []) (∈-++⁺ʳ (proj₂ wo₁ []) x∈proj₂) 

{-
x ∈ proj₁ wo (proj₂ wo [])
  ≡ { writer invariant }
x ∈ proj₁ wo [] ++ proj₂ wo []
  ≡ { def of wo }
x ∈ proj₁ (writerOutput ((p₁ >>= p₂) ((r , prime) , init))) [] ++ proj₂ wo []
  ≡ { def of >>= }
x ∈ proj₁ (writerOutput (let ((r' , init') , w , a) , inv = p₁ ((r , prime) , init)
                             ((r'' , init'') , w' b) , inv = p₂ a ((r , prime)' , init')
                          in ((r'' , init'') , mappend w w' , b))) [] ++ proj₂ wo []
  ≡ { def of writer output }
x ∈ proj₁ (let ((r' , init') , w , a) , inv = p₁ ((r , prime) , init)
                ((r'' , init'') , w' b) , inv = p₂ a ((r , prime)' , init')
            in mappend w w') [] ++ proj₂ wo []
  ≡ { eta expand }
x ∈ proj₁ (let ((r' , init') , w , a) , inv = p₁ ((r , prime) , init)
                ((r'' , init'') , w' b) , inv = p₂ a ((r , prime)' , init')
            in mappend (proj₁ w , proj₂ w) (proj₁ w' , proj₂ w')) [] ++ proj₂ wo []
  ≡ { def of mappend }
x ∈ proj₁ (let ((r' , init') , w , a) , inv = p₁ ((r , prime) , init)
                ((r'' , init'') , w' b) , inv = p₂ a ((r , prime)' , init')
            in (proj₁ w ∘′ proj₁ w', proj₂ w ∘′ proj₂ w')) [] ++ proj₂ wo []
  ≡ { def of proj₁ }
x ∈ (let ((r' , init') , w , a) , inv = p₁ ((r , prime) , init)
          ((r'' , init'') , w' b) , inv = p₂ a ((r , prime)' , init')
      in (proj₁ w ∘′ proj₁ w')) [] ++ proj₂ wo []
  ≡ { def of ∘′ }
x ∈ (let ((r' , init') , w , a) , inv = p₁ ((r , prime) , init)
          ((r'' , init'') , w' b) , inv = p₂ a ((r , prime)' , init')
      in (proj₁ w (proj₁ w' []))) ++ proj₂ wo []
  ≡ { ... } 
x ∈ let ((r' , init') , w , a) , inv = p₁ ((r , prime) , init)
          ((r'' , init'') , w' b) , inv = p₂ a ((r , prime)' , init')
     in (proj₁ w (proj₁ w' [])) ++ (proj₂ w (proj₂ w' []))
  ≡ { writer invariant }
x ∈ let ((r' , init') , w , a) , inv = p₁ ((r , prime) , init)
          ((r'' , init'') , w' b) , inv = p₂ a ((r , prime)' , init')
     in (proj₁ w [] ++ proj₁ w' []) ++ (proj₂ w (proj₂ w' []))
  ≡ { writer invariant }
x ∈ let ((r' , init') , w , a) , inv = p₁ ((r , prime) , init)
          ((r'' , init'') , w' b) , inv = p₂ a ((r , prime)' , init')
     in (proj₁ w [] ++ proj₁ w' []) ++ (proj₂ w [] ++ proj₂ w' [])
-}
linearCombMaxVar : List (f × Var) → ℕ
linearCombMaxVar [] = 1
linearCombMaxVar ((fst , snd) ∷ l) = snd ⊔ linearCombMaxVar l

R1CSMaxVar : R1CS → ℕ
R1CSMaxVar (IAdd x x₁) = linearCombMaxVar x₁
R1CSMaxVar (IMul a b c d e) = b ⊔ c ⊔ e
R1CSMaxVar (Hint x) = 1
R1CSMaxVar (Log x) = 1

R1CSsMaxVar : List R1CS → ℕ
R1CSsMaxVar [] = 1
R1CSsMaxVar (x ∷ l) = R1CSMaxVar x ⊔ R1CSsMaxVar l

builderMaxVar : (Builder × Builder) → ℕ
builderMaxVar (fst , snd) = R1CSsMaxVar (fst (snd []))



addSound : ∀ (r : WriterMode)
   → (ir : R1CS)
   → (sol : List (Var × ℕ))
   → ∀ (init : ℕ) → 
   let result = add ir ((r , prime) , init)
   in BuilderProdSol (writerOutput result) sol
   → R1CSSolution sol ir
addSound NormalMode ir sol init isSol' = isSol' ir (here refl)
addSound PostponedMode ir sol init isSol' = isSol' ir (here refl)



assertTrueSound : ∀ (r : WriterMode)
   → ∀ (v : Var) → (sol : List (Var × ℕ))
   → ∀ (init : ℕ) → {- (init > builderMaxVar builderProd) → -}
   let result = assertTrue v ((r , prime) , init)
   in
     BuilderProdSol (writerOutput result) sol
   → ListLookup v sol 1
assertTrueSound r v sol' init isSol' with addSound r (IAdd onef ((-F onef , v) ∷ []))  sol' init isSol'
assertTrueSound r v sol' init isSol' | addSol (LinearCombValCons .((Field.- field') (Field.one field')) .v varVal x LinearCombValBase) x₁
  rewrite +-identityʳ ((-F onef) *F ℕtoF varVal)
        | -one*f≡-f (ℕtoF varVal) = ListLookup-Respects-≈  _ _ _ _ (sq (trans lem (sym ℕtoF-1≡1))) x
      where
        lem : ℕtoF varVal ≡ onef
        lem with cong (_+F_ (ℕtoF varVal)) x₁
        ... | hyp rewrite sym (+-assoc (ℕtoF varVal) (-F (ℕtoF varVal)) onef)
                        | +-invʳ (ℕtoF varVal) | +-identityˡ onef | +-identityʳ (ℕtoF varVal) = sym hyp




data PiRepr (u : U) (x : ⟦ u ⟧ → U) (f : (v : ⟦ u ⟧) → ⟦ x v ⟧) : (eu : List ⟦ u ⟧) → Vec ℕ (tySumOver eu x) → Set

data ValRepr : ∀ u → ⟦ u ⟧ → Vec ℕ (tySize u) → Set where
  `OneValRepr : ∀ n → n ≈ 0 → ValRepr `One tt (n ∷ [])
  `TwoValFalseRepr : ∀ n → n ≈ 0 → ValRepr `Two false (n ∷ [])
  `TwoValTrueRepr : ∀ n → n ≈ 1 → ValRepr `Two true (n ∷ [])
  `BaseValRepr : ∀ {v : f} {v' : ℕ} → (fToℕ v) ≈ v' → ValRepr `Base v (v' ∷ [])
  `VecValBaseRepr : ∀ {u} → ValRepr (`Vec u 0) [] []
  `VecValConsRepr : ∀ {u} {n} {v₁} {vec₂} {val₁} {val₂} {val₃}
      → ValRepr u v₁ val₁
      → ValRepr (`Vec u n) vec₂ val₂
      → val₁ V++ val₂ ≡ val₃
      → ValRepr (`Vec u (suc n)) (v₁ ∷ vec₂) val₃
  `ΣValRepr : ∀ {u} {vu} (x : ⟦ u ⟧ → U) {vxu} {valu} {valxu} valxu+z {valu+valxu+z} {allZ : Vec ℕ (maxTySizeOver (enum u) x - tySize (x vu))}
      → ValRepr u vu valu
      → ValRepr (x vu) vxu valxu
      → All (_≈_ 0) allZ
      → valxu+z ≅ valxu V++ allZ
      → valu V++ valxu+z ≡ valu+valxu+z
      → ValRepr (`Σ u x) (vu , vxu) valu+valxu+z
  `ΠValRepr : ∀ {u} (x : ⟦ u ⟧ → U) {f : (v : ⟦ u ⟧) → ⟦ x v ⟧ } val → PiRepr u x f (enum u) val → ValRepr (`Π u x) f val

data PiRepr u x f where
  PiRepNil : PiRepr u x f [] []
  PiRepCons : ∀ {el} {vu} {valxu} {valel} {valxu+valel}
      → ValRepr (x vu) (f vu) valxu
      → PiRepr u x f el valel
      → valxu+valel ≡ valxu V++ valel
      → PiRepr u x f (vu ∷ el) valxu+valel


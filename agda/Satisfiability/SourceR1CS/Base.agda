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
open import Data.Unit hiding (setoid)


open import Function

open import Language.Common

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

import Relation.Binary.HeterogeneousEquality
module HE = Relation.Binary.HeterogeneousEquality
open import Relation.Binary.HeterogeneousEquality.Core
open import Relation.Nullary
module Satisfiability.SourceR1CS.Base (f : Set) (_≟F_ : Decidable {A = f} _≡_) (field' : Field f) (isField : IsField f field')
     (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (prime : ℕ) (isPrime : Prime prime) where


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
open import Compile.SourceR1CS f field' finite showf fToℕ


output : ∀ {a} {b} {c} {S : Set a} {W : Set b} {A : Set c} → (S × W × A) → A
output (s , w , a) = a

writerOutput : ∀ {a} {b} {c} {S : Set a} {W : Set b} {A : Set c} → (S × W × A) → W
writerOutput (s , w , a) = w

varOut : ∀ {a} {b} {c} {S : Set a} {W : Set b} {A : Set c} → (S × W × A) → S
varOut (s , _ , _) = s

data ListLookup : Var → List (Var × f) → f → Prop where
  LookupHere : ∀ v l n n' → n ≡ n' → ListLookup v ((v , n) ∷ l) n'
  LookupThere : ∀ v l n t → ListLookup v l n → ¬ v ≡ proj₁ t → ListLookup v (t ∷ l) n

data BatchListLookup : {n : ℕ} → Vec Var n → List (Var × f) → Vec f n → Prop where
  BatchLookupNil : ∀ l → BatchListLookup [] l []
  BatchLookupCons : ∀ {len} v n (vec₁ : Vec Var len) vec₂ l
        → ListLookup v l n
        → BatchListLookup vec₁ l vec₂
        → BatchListLookup (v ∷ vec₁) l (n ∷ vec₂)

BatchListLookup-Head : ∀ {n} {vec : Vec Var (suc n)}
  → {l : List (Var × f)}
  → {val : Vec f (suc n)}
  → BatchListLookup vec l val
  → ListLookup (head vec) l (head val)
BatchListLookup-Head (BatchLookupCons v n vec₁ vec₂ l x look) = x

BatchListLookup-++ : ∀ {m n} (vec : Vec Var m) (val : Vec f m) {vec' : Vec Var n} {val' : Vec f n}
  → {l : List (Var × f)}
  → BatchListLookup vec l val
  → BatchListLookup vec' l val'
  → BatchListLookup (vec V++ vec') l (val V++ val')
BatchListLookup-++ .[] .[] (BatchLookupNil l) look₂ = look₂
BatchListLookup-++ .(v ∷ vec₁) .(n ∷ vec₂) (BatchLookupCons v n vec₁ vec₂ l x look₁) look₂ = BatchLookupCons v n _ _ l x (BatchListLookup-++ vec₁ vec₂ look₁ look₂)


BatchListLookup-Split₁ :
  ∀ a b → (vec : Vec Var (a + b))
     → (l : List (Var × f))
     → (val : Vec f (a + b))
     → (vec₁ : Vec Var a) → (vec₂ : Vec Var b)
     → (val₁ : Vec f a) → (val₂ : Vec f b)
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
     → (l : List (Var × f))
     → (val : Vec f (a + b))
     → (vec₁ : Vec Var a) → (vec₂ : Vec Var b)
     → (val₁ : Vec f a) → (val₂ : Vec f b)
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

BatchListLookupLenSubst : ∀ {len} {len₁} {l} → (vec : Vec ℕ len) (val : Vec f len) (prf : len ≡ len₁) → BatchListLookup vec l val
   → BatchListLookup (subst (Vec ℕ) prf vec) l (subst (Vec f) prf val)
BatchListLookupLenSubst {len} {len₁} {l} vec val refl look = look

BatchListLookup-MaxTySplit₁ :
  ∀ u (uval : ⟦ u ⟧) (x : ⟦ u ⟧ → U) l
  → (vec : Vec Var (maxTySizeOver (enum u) x))
  → (vec₁ : Vec Var (tySize (x uval)))
  → (val : Vec f (maxTySizeOver (enum u) x))
  → (val₁ : Vec f (tySize (x uval)))
  → proj₁ (maxTySplit u uval x vec) ≡ vec₁
  → proj₁ (maxTySplit u uval x val) ≡ val₁
  → BatchListLookup vec l val
  → BatchListLookup vec₁ l val₁
BatchListLookup-MaxTySplit₁ u uval x l vec vec₁ val val₁ eq₁ eq₂ look =
  let
      sub₁ = BatchListLookupLenSubst vec val (maxTyVecSizeEq u uval x) look  
      hyp = BatchListLookup-Split₁ (tySize (x uval)) _ (subst (Vec ℕ) (maxTyVecSizeEq u uval x) vec) l (subst (Vec f) (maxTyVecSizeEq u uval x) val)  (proj₁ (maxTySplit u uval x vec)) (proj₂ (maxTySplit u uval x vec)) (proj₁ (maxTySplit u uval x val)) (proj₂ (maxTySplit u uval x val)) refl refl sub₁
      hyp₁ = subst′ (λ t → BatchListLookup t l (proj₁ (maxTySplit u uval x val))) eq₁ hyp
      hyp₂ = subst′ (λ t → BatchListLookup vec₁ l t) eq₂ hyp₁
  in hyp₂

BatchListLookup-MaxTySplit₂ :
  ∀ u (uval : ⟦ u ⟧) (x : ⟦ u ⟧ → U) l
  → (vec : Vec Var (maxTySizeOver (enum u) x))
  → (vec₁ : Vec Var (maxTySizeOver (enum u) x - tySize (x uval)))
  → (val : Vec f (maxTySizeOver (enum u) x))
  → (val₁ : Vec f (maxTySizeOver (enum u) x - tySize (x uval)))
  → proj₂ (maxTySplit u uval x vec) ≡ vec₁
  → proj₂ (maxTySplit u uval x val) ≡ val₁
  → BatchListLookup vec l val
  → BatchListLookup vec₁ l val₁
BatchListLookup-MaxTySplit₂ u uval x l vec vec₁ val val₁ eq₁ eq₂ look = 
  let
    sub₁ = BatchListLookupLenSubst vec val (maxTyVecSizeEq u uval x) look  
    hyp = BatchListLookup-Split₂ (tySize (x uval)) _ (subst (Vec ℕ) (maxTyVecSizeEq u uval x) vec) l (subst (Vec f) (maxTyVecSizeEq u uval x) val)  (proj₁ (maxTySplit u uval x vec)) (proj₂ (maxTySplit u uval x vec)) (proj₁ (maxTySplit u uval x val)) (proj₂ (maxTySplit u uval x val)) refl refl sub₁
    hyp₁ = subst′ (λ t → BatchListLookup t l (proj₂ (maxTySplit u uval x val))) eq₁ hyp
    hyp₂ = subst′ (λ t → BatchListLookup vec₁ l t) eq₂ hyp₁
  in hyp₂

BatchListLookupLenSubst' : ∀ n {m} {o} → (p : n + m ≡ o) → ∀ sol
   → (vec : Vec ℕ o)
   → (vec' : Vec ℕ n)
   → (vec'' : Vec ℕ m)
   → (val' : Vec f n)
   → (val'' : Vec f m)
   → vec ≅ vec' V++ vec''
   → BatchListLookup vec' sol val'
   → BatchListLookup vec'' sol val''
   → BatchListLookup vec sol (subst (Vec f) p (val' V++ val''))
BatchListLookupLenSubst' n refl sol .(vec' V++ vec'') vec' vec'' val' val'' refl look₁ look₂ = BatchListLookup-++ vec' val' look₁ look₂
data ⊥′ : Prop where


⊥′→⊥ : ⊥′ → ⊥
⊥′→⊥ ()

⊥→⊥′ : ⊥ → ⊥′
⊥→⊥′ ()

⊥-elim′ : ∀ {w} {Whatever : Prop w} → ⊥ → Whatever
⊥-elim′ ()

data LinearCombVal (solution : List (Var × f)) : List (f × Var) → f → Prop where
  LinearCombValBase : LinearCombVal solution [] zerof
  LinearCombValCons : ∀ coeff var varVal {l} {acc}
      → ListLookup var solution varVal
      → LinearCombVal solution l acc
      → LinearCombVal solution ((coeff , var) ∷ l) ((coeff *F varVal) +F acc)

data R1CSSolution (solution : List (Var × f)) : R1CS → Prop where
  addSol : ∀ {coeff} {linComb} {linCombVal}
                 → LinearCombVal solution linComb linCombVal
                 → linCombVal +F coeff ≡ zerof
                 → R1CSSolution solution (IAdd coeff linComb)
  multSol : ∀ a b bval c cval d e eval
                 → ListLookup b solution bval
                 → ListLookup c solution cval
                 → ListLookup e solution eval
                 → ((a *F bval) *F cval) ≡ (d *F eval)
                 → R1CSSolution solution (IMul a b c d e)
  hintSol : ∀ f → R1CSSolution solution (Hint f) -- Hint does not have to be solved
  logSol : ∀ s → R1CSSolution solution (Log s)

ConstraintsSol : List R1CS × List R1CS → List (Var × f) → Prop
ConstraintsSol (fst , snd) sol = ∀ x → x ∈ (fst ++ snd) → R1CSSolution sol x

data ProgSol {A : Set} (m : SI-Monad A) (mode : WriterMode) (prime : ℕ) (st : Var) (sol : List (Var × f)) : Prop where
  progSol : ConstraintsSol (writerOutput (runSI-Monad m ((mode , prime) , st))) sol → ProgSol m mode prime st sol


ConstraintsSol->>=⁻₁ : ∀ {A B : Set}
    → (p₁ : SI-Monad A)
    → (p₂ : A → SI-Monad B)
    → ∀ r init sol
    → ConstraintsSol (writerOutput (runSI-Monad (p₁ >>= p₂) ((r , prime) , init))) sol
    → ConstraintsSol (writerOutput (runSI-Monad p₁ ((r , prime) , init))) sol
ConstraintsSol->>=⁻₁ p₁ p₂ r init sol isSol x x∈p₁
    with ∈-++⁻ (proj₁ (writerOutput (runSI-Monad p₁ ((r , prime) , init)))) x∈p₁
... | inj₁ y
  = isSol x (∈-++⁺ˡ (∈-++⁺ˡ y))
... | inj₂ y
  = isSol x (∈-++⁺ʳ
                 (proj₁
                   (writerOutput (runSI-Monad (p₁ >>= p₂) ((r , prime) , init))))
                 (∈-++⁺ˡ y))

ProgSol₁ : ∀ {A B : Set}
    → {p₁ : SI-Monad A}
    → {p₂ : A → SI-Monad B}
    → ∀ {r} {init} {sol}
    → ProgSol (p₁ >>= p₂) r prime init sol
    → ProgSol p₁ r prime init sol
ProgSol₁ {_} {_} {p₁} {p₂} {r} {init} {sol} (progSol x) = progSol (ConstraintsSol->>=⁻₁ p₁ p₂ r init sol x)



ConstraintsSol->>=⁻₂ : ∀ {A B : Set}
    → (p₁ : SI-Monad A)
    → (p₂ : A → SI-Monad B)
    → ∀ r init sol
    → ConstraintsSol (writerOutput (runSI-Monad (p₁ >>= p₂) ((r , prime) , init))) sol
    → let newSt , _ , a = runSI-Monad p₁ ((r , prime) , init)
      in ConstraintsSol (writerOutput (runSI-Monad (p₂ a) ((r , prime) , newSt))) sol
ConstraintsSol->>=⁻₂ p₁ p₂ r init sol isSol x x∈p₂
    with let newSt , _ , a = runSI-Monad p₁ ((r , prime) , init)
         in ∈-++⁻ (proj₁ (writerOutput (runSI-Monad (p₂ a) ((r , prime) , newSt)))) x∈p₂
... | inj₁ y = isSol x (∈-++⁺ˡ (∈-++⁺ʳ
                                  (proj₁ (writerOutput (runSI-Monad p₁ ((r , prime) , init)))) y))
... | inj₂ y =
         let newSt  , (w₁₁ , w₁₂) , a = runSI-Monad p₁ ((r , prime) , init)
             newSt' , (w₂₁ , w₂₂) , b = runSI-Monad (p₂ a) ((r , prime) , newSt)
         in isSol x (∈-++⁺ʳ (w₁₁ ++ w₂₁) (∈-++⁺ʳ w₁₂ y))

ProgSol₂ : ∀ {A B : Set}
    → {p₁ : SI-Monad A}
    → {p₂ : A → SI-Monad B}
    → ∀ {r} {init} {sol}
    → ProgSol (p₁ >>= p₂) r prime init sol
    → let newSt , _ , a = runSI-Monad p₁ ((r , prime) , init)
      in ProgSol (p₂ a) r prime newSt sol
ProgSol₂ {_} {_} {p₁} {p₂} {r} {init} {sol} (progSol x) = progSol (ConstraintsSol->>=⁻₂ p₁ p₂ r init sol x)


addSound :
   {r : WriterMode}
   → {ir : R1CS}
   → {sol : List (Var × f)}
   → {init : ℕ}
   → ProgSol (add ir) r prime init sol
   → R1CSSolution sol ir
addSound {NormalMode} {ir} {sol} {init} (progSol isSol) = isSol ir (here refl)
addSound {PostponedMode} {ir} {sol} {init} (progSol isSol) = isSol ir (here refl)

assertTrueSound : ∀ (r : WriterMode)
   → ∀ (v : Var) → (sol : List (Var × f))
   → ∀ (init : ℕ)
   → ProgSol (assertTrue v) r prime init sol
   → ListLookup v sol onef
assertTrueSound r v sol init isSol
    with addSound isSol
... | addSol (LinearCombValCons .((Field.- field') (Field.one field')) .v varVal x LinearCombValBase) x₁
    rewrite +-identityʳ ((-F onef) *F varVal)
          | -one*f≡-f varVal
          | a-b≡zero→a≡b (trans (sym (+-comm (-F varVal) onef)) x₁)
          = x


data PiRepr (u : U) (x : ⟦ u ⟧ → U) (func : (v : ⟦ u ⟧) → ⟦ x v ⟧) : (eu : List ⟦ u ⟧) → Vec f (tySumOver eu x) → Set

data ValRepr : ∀ u → ⟦ u ⟧ → Vec f (tySize u) → Set where
  `OneValRepr : ValRepr `One tt (zerof ∷ [])
  `TwoValFalseRepr : ValRepr `Two false (zerof ∷ [])
  `TwoValTrueRepr : ValRepr `Two true (onef ∷ [])
  `BaseValRepr : ∀ {v : f} → ValRepr `Base v (v ∷ [])
  `VecValBaseRepr : ∀ {u} → ValRepr (`Vec u 0) [] []
  `VecValConsRepr : ∀ {u} {n} {v₁} {vec₂} {val₁} {val₂} {val₃}
      → ValRepr u v₁ val₁
      → ValRepr (`Vec u n) vec₂ val₂
      → val₁ V++ val₂ ≡ val₃
      → ValRepr (`Vec u (suc n)) (v₁ ∷ vec₂) val₃
  `ΣValRepr : ∀ {u} {⟦u⟧} (x : ⟦ u ⟧ → U) {⟦xu⟧} {val⟦u⟧} {val⟦xu⟧} val⟦xu⟧+z {val⟦u⟧+val⟦xu⟧+z} {allZ : Vec f (maxTySizeOver (enum u) x - tySize (x ⟦u⟧))}
      → ValRepr u ⟦u⟧ val⟦u⟧
      → ValRepr (x ⟦u⟧) ⟦xu⟧ val⟦xu⟧
      → All (λ x → Squash (x ≡ zerof)) allZ
      → val⟦xu⟧+z ≅ val⟦xu⟧ V++ allZ
      → val⟦u⟧ V++ val⟦xu⟧+z ≡ val⟦u⟧+val⟦xu⟧+z
      → ValRepr (`Σ u x) (⟦u⟧ , ⟦xu⟧) val⟦u⟧+val⟦xu⟧+z
  `ΠValRepr : ∀ {u} (x : ⟦ u ⟧ → U) {f : (v : ⟦ u ⟧) → ⟦ x v ⟧ } val → PiRepr u x f (enum u) val → ValRepr (`Π u x) f val

data PiRepr u x func where
  PiRepNil : PiRepr u x func [] []
  PiRepCons : ∀ {el} {⟦u⟧} {val⟦xu⟧} {vec} {val⟦xu⟧+vec}
      → ValRepr (x ⟦u⟧) (func ⟦u⟧) val⟦xu⟧
      → PiRepr u x func el vec
      → val⟦xu⟧+vec ≡ val⟦xu⟧ V++ vec
      → PiRepr u x func (⟦u⟧ ∷ el) val⟦xu⟧+vec



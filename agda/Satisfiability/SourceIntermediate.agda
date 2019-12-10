open import Data.Field
open import Data.Finite
open import Data.List hiding (lookup; head)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Primality


open import Data.Product hiding (map)
open import Data.Vec
open import Data.String hiding (_≈_)

open import Function

open import Language.Common

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
module Satisfiability.SourceIntermediate (f : Set) (field' : Field f) (isField : IsField f field')
     (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f) (ℕtoF-1≡1 : ℕtoF 1 ≡ Field.one field') (prime : ℕ) (isPrime : Prime prime) where

open import Language.Intermediate f

{-

asserts : List (∃ (λ u → Source u × Source u))

output : Source u


-}
open Field field' renaming ( _+_ to _+F_
                           ; _*_ to _*F_
                           ; -_ to -F_
                           ; 1/_ to 1F/_
                           ; zero to zerof
                           ; one to onef)
open IsField isField
open import Compile.SourceIntermediate f field' finite showf fToℕ ℕtoF
open SI-Monad


output : ∀ {a} {b} {c} {S : Set a} {W : Set b} {A : Set c} → (S × W × A) → A
output (s , w , a) = a

writerOutput : ∀ {a} {b} {c} {S : Set a} {W : Set b} {A : Set c} → (S × W × A) → W
writerOutput (s , w , a) = w

_≈_ : ℕ → ℕ → Set
x ≈ y = ℕtoF x ≡ ℕtoF y

≈-IsEquiv : IsEquivalence _≈_
≈-IsEquiv = record { refl = λ {x} → refl
                   ; sym = λ x → sym x
                   ; trans = λ {i} {j} {k} → trans }

data ListLookup : Var → List (Var × ℕ) → ℕ → Set where
  LookupHere : ∀ v l n n' → n ≈ n' → ListLookup v ((v , n) ∷ l) n'
  LookupThere : ∀ v l n t → ListLookup v l n → ¬ v ≡ proj₁ t → ListLookup v (t ∷ l) n

-- ListLookup `respects` _≈_

ListLookup-Respects-≈ : ∀ v l n n' → n ≈ n' → ListLookup v l n → ListLookup v l n'
ListLookup-Respects-≈ v .((v , n₁) ∷ l) n n' eq (LookupHere .v l n₁ .n x) = LookupHere v l n₁ n' (≈-trans x eq)
  where
    open IsEquivalence ≈-IsEquiv renaming (trans to ≈-trans)
ListLookup-Respects-≈ v .(t ∷ l) n n' eq (LookupThere .v l .n t look x) = LookupThere v l n' t (ListLookup-Respects-≈ v l n n' eq look) x

data LinearCombVal (solution : List (Var × ℕ)) : List (f × Var) → f → Set where
  LinearCombValBase : LinearCombVal solution [] zerof
  LinearCombValCons : ∀ coeff var varVal l acc
      → ListLookup var solution varVal
      → LinearCombVal solution l acc
      → LinearCombVal solution ((coeff , var) ∷ l) ((coeff *F ℕtoF varVal) +F acc)


data IntermediateSolution (solution : List (Var × ℕ)) : Intermediate → Set where
  addSol : ∀ coeff linComb linCombVal
                 → LinearCombVal solution linComb linCombVal
                 → linCombVal +F coeff ≡ zerof
                 → IntermediateSolution solution (IAdd coeff linComb)
  multSol : ∀ a b bval c cval d e eval
                 → ListLookup b solution bval
                 → ListLookup c solution cval
                 → ListLookup e solution eval
                 → ((a *F (ℕtoF bval)) *F (ℕtoF cval)) ≡ (d *F (ℕtoF eval))
                 → IntermediateSolution solution (IMul a b c d e)

BuilderProdSol : Builder × Builder → List (Var × ℕ) → Set
BuilderProdSol (fst , snd) sol = ∀ x → x ∈ (fst (snd [])) → IntermediateSolution sol x

linearCombMaxVar : List (f × Var) → ℕ
linearCombMaxVar [] = 1
linearCombMaxVar ((fst , snd) ∷ l) = snd ⊔ linearCombMaxVar l

intermediateMaxVar : Intermediate → ℕ
intermediateMaxVar (IAdd x x₁) = linearCombMaxVar x₁
intermediateMaxVar (IMul a b c d e) = b ⊔ c ⊔ e
intermediateMaxVar (Hint x) = 1
intermediateMaxVar (Log x) = 1

intermediatesMaxVar : List Intermediate → ℕ
intermediatesMaxVar [] = 1
intermediatesMaxVar (x ∷ l) = intermediateMaxVar x ⊔ intermediatesMaxVar l

builderMaxVar : (Builder × Builder) → ℕ
builderMaxVar (fst , snd) = intermediatesMaxVar (fst (snd []))

addSound : ∀ (r : WriterMode)
   → (builderProd : Builder × Builder)
   → (ir : Intermediate)
   → (solution' : List (Var × ℕ))
   → ∀ (init : ℕ) → 
   let result = add ir (prime , r , init)
   in BuilderProdSol (writerOutput result) solution'
   → IntermediateSolution solution' ir
addSound NormalMode buildProd ir solution' init isSol' = isSol' ir (here refl)
addSound PostponedMode buildProd ir solution' init isSol' = isSol' ir (here refl)


assertTrueSound : ∀ (r : WriterMode)
   → (builderProd : Builder × Builder)
   → ∀ (v : Var) → (solution' : List (Var × ℕ))
   → ∀ (init : ℕ) → {- (init > builderMaxVar builderProd) → -}
   let result = assertTrue v (prime , r , init)
   in
     BuilderProdSol (writerOutput result) solution'
   → ListLookup v solution' 1
assertTrueSound r builder v sol' init isSol' with addSound r builder (IAdd onef ((-F onef , v) ∷ []))  sol' init isSol'
assertTrueSound r builder v sol' init isSol' | addSol .(Field.one field') .(((Field.- field') (Field.one field') , v) ∷ []) .((field' Field.+ (field' Field.* (Field.- field') (Field.one field')) (ℕtoF varVal)) (Field.zero field')) (LinearCombValCons .((Field.- field') (Field.one field')) .v varVal .[] .(Field.zero field') x LinearCombValBase) x₁
  rewrite +-identityʳ ((-F onef) *F ℕtoF varVal)
        | -one*f≡-f (ℕtoF varVal) = ListLookup-Respects-≈  _ _ _ _ (trans lem (sym ℕtoF-1≡1)) x
      where
        lem : ℕtoF varVal ≡ onef
        lem with cong (_+F_ (ℕtoF varVal)) x₁
        ... | hyp rewrite sym (+-assoc (ℕtoF varVal) (-F (ℕtoF varVal)) onef)
                        | +-invʳ (ℕtoF varVal) | +-identityˡ onef | +-identityʳ (ℕtoF varVal) = sym hyp

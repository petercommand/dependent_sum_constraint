open import Data.Field
open import Data.Finite
open import Data.List hiding (lookup; head)
open import Data.List.Membership.Propositional
open import Data.Nat
open import Data.Nat.Primality


open import Data.Product hiding (map)
open import Data.Vec
open import Data.String

open import Function

open import Language.Common

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
module Satisfiability.SourceIntermediate (f : Set) (field' : Field f) (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f) (prime : ℕ) (isPrime : Prime prime) where

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

open import Compile.SourceIntermediate f field' finite showf fToℕ ℕtoF
open SI-Monad


output : ∀ {a} {b} {c} {S : Set a} {W : Set b} {A : Set c} → (S × W × A) → A
output (s , w , a) = a

writerOutput : ∀ {a} {b} {c} {S : Set a} {W : Set b} {A : Set c} → (S × W × A) → W
writerOutput (s , w , a) = w


data ListLookup : Var → List (Var × ℕ) → ℕ → Set where
  LookupHere : ∀ v l n → ListLookup v ((v , n) ∷ l) n
  LookupThere : ∀ v l n t → ListLookup v l n → ¬ v ≡ proj₁ t → ListLookup v (t ∷ l) n


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

isTrueCorrect : ∀ (r : WriterMode)
   → (builderProd : Builder × Builder)
   → (solution : List (Var × ℕ))
   → BuilderProdSol builderProd solution
   → ∀ (v : Var) → (solution' : List (Var × ℕ))
   → ∀ (init : ℕ) → (init > builderMaxVar builderProd) →
   let result = isTrue v (prime , r , init)
   in
     BuilderProdSol (writerOutput result) solution'
   → ListLookup v solution' 1
isTrueCorrect r builder sol isSol v sol' init init>max isSol' = {!!}

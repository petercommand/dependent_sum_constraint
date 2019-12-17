{-# OPTIONS --prop #-}

open import Data.Bool
open import Data.Empty
open import Data.Field
open import Data.Finite
open import Data.List hiding (lookup; head; splitAt)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Primality


open import Data.Product hiding (map)
open import Data.ProductPrime
open import Data.Vec hiding (_>>=_; _++_; splitAt)
open import Data.Vec.Split
open import Data.Squash
open import Data.String hiding (_≈_; _≟_; _++_)
open import Data.Sum
open import Data.Unit
open import Function

open import Language.Common

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
module Satisfiability.SourceIntermediate (f : Set) (_≟F_ : Decidable {A = f} _≡_) (field' : Field f) (isField : IsField f field')
     (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f)
        (ℕtoF-1≡1 : ℕtoF 1 ≡ Field.one field')
        (ℕtoF-0≡0 : ℕtoF 0 ≡ Field.zero field') (prime : ℕ) (isPrime : Prime prime)
        (onef≠zerof : ¬ Field.one field' ≡ Field.zero field') where

open import Language.Source f finite showf
open import Language.TySize f finite
open import Language.Universe f
open import Language.Intermediate f


open Field field' renaming ( _+_ to _+F_
                           ; _*_ to _*F_
                           ; -_ to -F_
                           ; 1/_ to 1F/_
                           ; zero to zerof
                           ; one to onef)
open IsField isField
open import Compile.SourceIntermediate f field' finite showf fToℕ ℕtoF hiding (SI-Monad)
import Compile.SourceIntermediate
open Compile.SourceIntermediate.SI-Monad f field' finite showf fToℕ ℕtoF


open import Satisfiability.SourceIntermediate.Base f _≟F_ field' isField finite showf fToℕ ℕtoF ℕtoF-1≡1 ℕtoF-0≡0 prime isPrime
open import Satisfiability.SourceIntermediate.LogicGates f _≟F_ field' isField finite showf fToℕ ℕtoF ℕtoF-1≡1 ℕtoF-0≡0 prime isPrime
open import Satisfiability.SourceIntermediate.SimpleComp f _≟F_ field' isField finite showf fToℕ ℕtoF ℕtoF-1≡1 ℕtoF-0≡0 prime isPrime onef≠zerof
{-
data UList (u : U) (x : ⟦ u ⟧ → U) : List ⟦ u ⟧ → Set where
  UNil : UList u x []
  UCons : ∀ val {l} → ⟦ x val ⟧ → UList u x l → UList u x (val ∷ l)
-}

tyCondFunc : ∀ u → (vec : Vec ℕ (tySize u)) → ℕ
enumSigmaCondFunc : ∀ u → (eu : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U)
  → (val₁ : Vec ℕ (tySize u))
  → (val₂ : Vec ℕ (maxTySizeOver (enum u) x))
  → ℕ

enumPiCondFunc : ∀ u → (eu : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U) → Vec ℕ (tySumOver eu x) → ℕ
enumPiCondFunc u [] x vec = 1
enumPiCondFunc u (x₁ ∷ eu) x vec with splitAt (tySize (x x₁)) vec
enumPiCondFunc u (x₁ ∷ eu) x vec | fst₁ , snd₁ = andFunc (tyCondFunc (x x₁) fst₁) (enumPiCondFunc u eu x snd₁)

tyCondFunc `One (x ∷ vec) with ℕtoF x ≟F zerof
tyCondFunc `One (x ∷ vec) | yes p = 1
tyCondFunc `One (x ∷ vec) | no ¬p = 0
tyCondFunc `Two (x ∷ vec) with ℕtoF x ≟F zerof
tyCondFunc `Two (x ∷ vec) | yes p = 1
tyCondFunc `Two (x ∷ vec) | no ¬p with ℕtoF x ≟F onef
tyCondFunc `Two (x ∷ vec) | no ¬p | yes p = 1
tyCondFunc `Two (x ∷ vec) | no ¬p | no ¬p₁ = 0
tyCondFunc `Base vec = 1
tyCondFunc (`Vec u zero) vec = 1
tyCondFunc (`Vec u (suc x)) vec with splitAt (tySize u) vec
... | fst , snd = andFunc (tyCondFunc u fst) (tyCondFunc (`Vec u x) snd)
tyCondFunc (`Σ u x) vec with splitAt (tySize u) vec
tyCondFunc (`Σ u x) vec | fst₁ , snd₁ = andFunc (tyCondFunc u fst₁) (enumSigmaCondFunc u (enum u) x fst₁ snd₁)
tyCondFunc (`Π u x) vec = enumPiCondFunc u (enum u) x vec

enumSigmaCondFunc u [] x val val₁ = 1
enumSigmaCondFunc u (x₁ ∷ eu) x v₁ v₂ with maxTySplit u x₁ x v₂
enumSigmaCondFunc u (x₁ ∷ eu) x v₁ v₂ | fst₁ , snd₁ =
  andFunc (impFunc (varEqLitFunc u v₁ x₁) (andFunc (tyCondFunc (x x₁) fst₁) (allEqzFunc snd₁)))
          (enumSigmaCondFunc u eu x v₁ v₂)

enumPiCondSound : ∀ r u → (eu : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U)
   → (vec : Vec Var (tySumOver eu x))
   → (val : Vec ℕ (tySumOver eu x))
   → (sol : List (Var × ℕ))
   → BatchListLookup vec sol val
   → ListLookup 0 sol 1
   → ∀ init →
   let result = enumPiCond eu x vec ((r , prime) , init)
   in BuilderProdSol (writerOutput result) sol
   → ListLookup (output result) sol (enumPiCondFunc u eu x val)

tyCondSound : ∀ r u
   → (vec : Vec Var (tySize u))
   → (val : Vec ℕ (tySize u))
   → (sol : List (Var × ℕ))
   → BatchListLookup vec sol val
   → ListLookup 0 sol 1
   → ∀ init →
   let result = tyCond u vec ((r , prime) , init)
   in BuilderProdSol (writerOutput result) sol
   → ListLookup (output result) sol (tyCondFunc u val)

enumSigmaCondSound : ∀ r u → (eu : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U)
   → (vec₁ : Vec Var (tySize u))
   → (vec₂ : Vec Var (maxTySizeOver (enum u) x))
   → (val₁ : Vec ℕ (tySize u))
   → (val₂ : Vec ℕ (maxTySizeOver (enum u) x))
   → (sol : List (Var × ℕ))
   → BatchListLookup vec₁ sol val₁
   → BatchListLookup vec₂ sol val₂
   → ListLookup 0 sol 1
   → ∀ init →
   let result = enumSigmaCond eu x vec₁ vec₂ ((r , prime) , init)
   in BuilderProdSol (writerOutput result) sol
     → ListLookup (output result) sol (enumSigmaCondFunc u eu x val₁ val₂)

tyCondSound r `One vec val sol look₁ tri init isSol =
  let sound = allEqzSound r vec val sol look₁ init isSol
  in ListLookup-Respects-≈ _ _ _ _ (lem val) sound
 where
   lem : ∀ val → allEqzFunc val ≈ tyCondFunc `One val
   lem (x ∷ val) with ℕtoF x ≟F zerof
   lem (x ∷ []) | yes p = sq refl
   lem (x ∷ val) | no ¬p = sq refl
tyCondSound r `Two vec val sol look₁ tri init isSol =
  let sound₁ = varEqLitSound r `Two vec val false sol look₁ tri init ?
  
  in {!!}
tyCondSound r `Base vec val sol look₁ tri init isSol = {!!}
tyCondSound r (`Vec u x) vec val sol look₁ tri init isSol = {!!}
tyCondSound r (`Σ u x) vec val sol look₁ tri init isSol = {!!}
tyCondSound r (`Π u x) vec val sol look₁ tri init isSol = {!!}


enumPiCondSound r u euu x vec val sol look₁ tri init isSol = {!!}

enumSigmaCondSound r u eu x vec₁ vec₂ val₁ val₂ sol look₁ look₂ tri init isSol = {!!}

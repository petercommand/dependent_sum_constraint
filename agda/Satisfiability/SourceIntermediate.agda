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

tyCondFunc `One vec = {!!}
tyCondFunc `Two vec = {!!}
tyCondFunc `Base vec = {!!}
tyCondFunc (`Vec u x) vec = {!!}
tyCondFunc (`Σ u x) vec = {!!}
tyCondFunc (`Π u x) vec = {!!}

enumSigmaCondFunc u [] x val val₁ = 1
enumSigmaCondFunc u (x₁ ∷ eu) x v₁ v₂ with maxTySplit u x₁ x v₂
enumSigmaCondFunc u (x₁ ∷ eu) x v₁ v₂ | fst₁ , snd₁ =
  andFunc (impFunc (varEqLitFunc u v₁ x₁) (andFunc (tyCondFunc (x x₁) fst₁) (allEqzFunc snd₁)))
          (enumSigmaCondFunc u eu x v₁ v₂)

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
     → ListLookup (output result) sol {!!}

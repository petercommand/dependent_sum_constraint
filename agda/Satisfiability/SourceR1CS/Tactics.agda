{-# OPTIONS --prop -vtest:20 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection 
open import Data.Bool
open import Data.Char
open import Data.Empty
open import Data.Field
open import Data.Finite
open import Data.List hiding (lookup; head; splitAt)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any hiding (head; map)
open import Data.Nat
open import Data.Nat.Primality
open import Data.Nat.Show

open import Data.Product hiding (map)
open import Data.ProductPrime
open import Data.Squash
open import Data.String hiding (_≈_; _≟_; _++_)
open import Data.Unit


open import Function

open import Language.Common

open import Reflection

open import Relation.Binary
open import Relation.Binary.PropositionalEquality


import Relation.Binary.HeterogeneousEquality
module HE = Relation.Binary.HeterogeneousEquality
open import Relation.Binary.HeterogeneousEquality.Core
open import Relation.Nullary
module Satisfiability.SourceR1CS.Tactics (f : Set) (_≟F_ : Decidable {A = f} _≡_) (field' : Field f) (isField : IsField f field')
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
import Compile.SourceR1CS f field' finite showf fToℕ as SI
open import Satisfiability.SourceR1CS.Base f _≟F_ field' isField finite showf fToℕ prime isPrime

open import Level

ProgSolTlₙImpl : ℕ → Term → Term
ProgSolTlₙImpl zero isSolTerm = isSolTerm
ProgSolTlₙImpl (suc n) isSolTerm = def (quote ProgSol₂) (vArg (ProgSolTlₙImpl n isSolTerm) ∷ [])

macro
  ProgSolTlₙ : Term → ℕ → Term → TC ⊤
  ProgSolTlₙ isSolTerm n t = do
    unify t (ProgSolTlₙImpl n isSolTerm)


{-
neqzFunc : f → f
neqzFunc n with n ≟F zerof
neqzFunc n | yes p = zerof
neqzFunc n | no ¬p = onef

neqzSound : (r : SI.SI-Monad-Module.WriterMode)
  → ∀ (v : Var) → (sol : List (Var × f))
  → ∀ (init : ℕ) → 
  let result = SI.runSI-Monad (SI.neqz v) ((r , prime) , init)
  in ProgSol (SI.neqz v) r prime init sol
  → Squash (∃ (λ val → Σ′′ (ListLookup v sol val) (λ _ → ListLookup (output result) sol (neqzFunc val))))
neqzSound r v sol init isSol
  with
  let isSol' = ProgSolTlₙ isSol 4
      imul₁IsSol = ProgSol₁ isSol'
  in addSound imul₁IsSol
... | t = {!!}
-}

open import Data.Finite
open import Data.List hiding ([_])
open import Data.Nat
open import Data.Product
open import Data.Vec hiding (_++_; _>>=_)

open import Language.Common

open import Relation.Binary.PropositionalEquality hiding ([_])

module Language.Source.Utils (f : Set) (finite : Finite f) where

open import Language.Source f finite
open import Language.TySize f finite
open import Language.Universe f

module S-Monad where
  import Control.StateWriter

  open Control.StateWriter Var (List (∃ (λ u → Source u × Source u)) × List ℕ) ([] , []) (λ a b → proj₁ a ++ proj₁ b , proj₂ a ++ proj₂ b) renaming (StateWriterMonad to S-Monad) public



  newVar : S-Monad Var
  newVar = do
    v ← get
    put (1 + v)
    return v


  newVars : ∀ n → S-Monad (Vec Var n)
  newVars zero = return []
  newVars (suc n) = do
    v ← newVar
    rest ← newVars n
    return (v ∷ rest)


open S-Monad hiding (newVar; newVars) public
open S-Monad using (newVar; newVars)

new : ∀ u → S-Monad (Source u)
new u = do
  vec ← newVars (tySize u)
  return (Ind refl vec)

newI : ∀ u → S-Monad (Source u)
newI u = do
  vec ← newVars (tySize u)
  tell ([] , toList vec)
  return (Ind refl vec)

open import Data.Fin hiding (_+_)
open import Data.Finite
open import Data.List hiding ([_]; splitAt)
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Data.Vec hiding (_++_; _>>=_; splitAt)
open import Data.Vec.Split

open import Function

open import Language.Common

open import Relation.Binary.PropositionalEquality hiding ([_])

module Language.Source.Utils (f : Set) (finite : Finite f) where

open import Language.Source f finite
open import Language.TySize f finite
open import Language.Universe f

module S-Monad where
  import Control.StateWriter

  import Function.Endomorphism.Propositional using (Endo)

  module Assert = Function.Endomorphism.Propositional (List (∃ (λ u → Source u × Source u)))
  --
  module Input = Function.Endomorphism.Propositional (List ℕ)
  open Control.StateWriter Var (Assert.Endo × Input.Endo) (id , id) (λ a b → proj₁ a ∘′ proj₁ b , proj₂ a ∘′ proj₂ b) renaming (StateWriterMonad to S-Monad) public



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

assertEq : ∀ {u} → Source u → Source u → S-Monad ⊤
assertEq {u} s₁ s₂ = tell ((λ x → ((u , s₁ , s₂) ∷ [])  ++ x) , id)

new : ∀ u → S-Monad (Source u)
new u = do
  vec ← newVars (tySize u)
  return (Ind refl vec)

newI : ∀ u → S-Monad (Source u)
newI u = do
  vec ← newVars (tySize u)
  tell (id , (λ x → toList vec ++ x))
  return (Ind refl vec)

getV : ∀ {u} {x} → Source (`Vec u x) → Fin x → Source u
getV {u} {suc x} (Ind refl x₁) f with splitAt (tySize u) x₁
getV {u} {suc x} (Ind refl x₁) 0F | fst , snd = Ind refl fst
getV {u} {suc x} (Ind refl x₁) (suc f) | fst , snd = getV (Ind refl snd) f
getV (Lit (x ∷ x₁)) 0F = Lit x
getV (Lit (x ∷ x₁)) (suc f) = getV (Lit x₁) f

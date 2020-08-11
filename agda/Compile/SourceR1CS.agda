{-# OPTIONS --prop #-}
open import Agda.Builtin.Nat renaming (zero to nzero) hiding (_+_; _*_)

open import Data.Bool
open import Data.Field
open import Data.Finite
open import Data.List hiding (splitAt; head; take; drop; intercalate; concat)
import Data.List.Properties
module LP = Data.List.Properties
import Data.Map
module M = Data.Map
open import Data.MaybeC
open import Data.Nat hiding (_⊔_) renaming (zero to nzero; _≟_ to _≟ℕ_; _+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Mod renaming (mod to modℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Nat.Properties
open import Data.Nat.Properties2
open import Data.Product hiding (map)
open import Data.ProductPrime
import Data.Sets
module S = Data.Sets
open import Data.Squash
open import Data.String renaming (_++_ to _S++_) hiding (show; fromList)
open import Data.String.Intercalate
open import Data.Sum hiding (map)
open import Data.Unit
open import Data.Vec hiding (_>>=_; _++_; [_]; splitAt; map; concat; fromList)
open import Data.Vec.Split

open import Function
import Function.Endomorphism.Propositional

open import Language.Common

open import Level renaming (zero to lzero; suc to lsuc)

open import Math.Arithmoi

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import TypeClass.Ord

module Compile.SourceR1CS (f : Set) (field' : Field f) (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f) where

open import Language.R1CS f
open import Language.R1CS.Show f showf
open import Language.Source f finite showf
open import Language.TySize f finite
open import Language.Universe f

open Field field' hiding (_+_)

import Compile.SourceR1CS.Base
open Compile.SourceR1CS.Base f field' finite showf fToℕ ℕtoF hiding (SI-Monad)
open Compile.SourceR1CS.Base f field' finite showf fToℕ ℕtoF using (SI-Monad) public

open import Compile.SourceR1CS.LogicGates f field' finite showf fToℕ ℕtoF public
open import Compile.SourceR1CS.SimpleComp f field' finite showf fToℕ ℕtoF public
open import Compile.SourceR1CS.Hints  f field' finite showf fToℕ ℕtoF public



litToInd : ∀ u → ⟦ u ⟧ → SI-Monad (Vec Var (tySize u))
litToInd u l = do
  vec ← newVarVec (tySize u)
  add (Hint (litEqVecHint u l vec))
  r ← varEqLit u vec l
  assertTrue r
  return vec


assertVarEqVar : ∀ n → Vec Var n → Vec Var n → SI-Monad ⊤
assertVarEqVar .0 [] [] = return tt
assertVarEqVar .(suc _) (x ∷ v₁) (x₁ ∷ v₂) = do
  add (IAdd zero ((one , x) ∷ (- one , x₁) ∷ []))
  assertVarEqVar _ v₁ v₂

sourceToR1CS : ∀ u → Source u → SI-Monad (Vec Var (tySize u))
sourceToR1CS u (Ind refl x) = withMode PostponedMode (indToIR u x)
sourceToR1CS u (Lit x) = litToInd u x
sourceToR1CS `Base (Add source source₁) = do
  r₁ ← sourceToR1CS `Base source
  r₂ ← sourceToR1CS `Base source₁
  v ← new
  add (IAdd zero ((one , head r₁) ∷ (one , head r₂) ∷ (- one , v) ∷ []))
  return (v ∷ [])
sourceToR1CS `Base (Mul source source₁) = do
  r₁ ← sourceToR1CS `Base source
  r₂ ← sourceToR1CS `Base source₁
  v ← new
  add (IMul one (head r₁) (head r₂) one v)
  return (v ∷ [])
module Comp where
  open import Language.Source.Utils f finite showf using (S-Monad)

  compAssert : (∃ (λ u → Source u × Source u)) → SI-Monad ⊤
  compAssert (u , s₁ , s₂) = do
    r₁ ← sourceToR1CS u s₁
    r₂ ← sourceToR1CS u s₂
    assertVarEqVar _ r₁ r₂

  compAsserts : List (∃ (λ u → Source u × Source u)) → SI-Monad ⊤
  compAsserts [] = return tt
  compAsserts (l ∷ ls) = do
    compAssert l
    compAsserts ls

  compAssertsHints : List (∃ (λ u → Source u × Source u) ⊎ (M.Map Var ℕ → M.Map Var ℕ)) → SI-Monad ⊤
  compAssertsHints [] = return tt
  compAssertsHints (inj₁ x ∷ ls) = do
    compAssert x
    compAssertsHints ls
  compAssertsHints (inj₂ y ∷ ls) = do
    add (Hint y)
    compAssertsHints ls

  compileSource : ∀ (n : ℕ) u → (S-Monad (Source u)) → Var × Builder × (Vec Var (tySize u) × List ℕ)
  compileSource n u source = 
    let v , (asserts , input) , output = source (tt , 1)
        ((v' , (bld₁ , bld₂) , outputVars) , inv) = (do
           compAssertsHints (asserts [])
           sourceToR1CS _ output) ((NormalMode , n) , v)
    in v' , bld₁ ∘′ bld₂ , outputVars , input []
  open import Data.Nat.Show



open Comp public



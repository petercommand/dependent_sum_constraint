open import Data.Field
open import Data.Finite
open import Data.List hiding (splitAt)
open import Data.Nat hiding (_⊔_) renaming (zero to nzero)
open import Data.Product
open import Data.Unit
open import Data.Vec hiding (_>>=_; _++_; [_]; splitAt)
open import Data.Vec.Split

open import Language.Common

open import Level renaming (zero to lzero)

open import Relation.Binary.PropositionalEquality hiding ([_])
module Compile.SourceIntermediate (f : Set) (field' : Field f) (finite : Finite f) where

open import Language.Intermediate f
open import Language.Source f finite
open import Language.TySize f finite
open import Language.Universe f

module SI-Monad where
  


    
  open import Control.StateWriter Var (List Intermediate) [] _++_ public

  SI-Monad : ∀ {a} → Set a → Set a
  SI-Monad = StateWriterMonad Var (List Intermediate)

  add : Intermediate → SI-Monad ⊤
  add w' = tell [ w' ]

  new : SI-Monad Var
  new = do
    s ← get
    put (1 + s)
    return s
open SI-Monad
open Field field'

isTrue : Var → SI-Monad ⊤
isTrue v = add (IAdd one ((- one , v) ∷ []))



trivial : SI-Monad Var
trivial = do
  v ← new
  isTrue v
  return v

neqz : Var → SI-Monad Var
neqz v = {!!}

lor : Var → Var → SI-Monad Var
lor n₁ n₂ = do
  v ← new
  v' ← new
  add (IMul one n₁ n₂ one v)
  add (IAdd zero ((one , n₁) ∷ (one , n₂) ∷ (- one , v) ∷ (- one , v') ∷ []))
  return v

enumSigmaCond : ∀ {u} → List ⟦ u ⟧ → (x : ⟦ u ⟧ → U) → Vec Var (tySize u) → Vec Var (maxTySizeOver (enum u) x) → SI-Monad Var
tyCond : ∀ u → Vec Var (tySize u) → SI-Monad Var
enumSigmaCond [] x v₁ v₂ = trivial
enumSigmaCond (x₁ ∷ enum₁) x v₁ v₂ = do
  {!!}
  rest ← enumSigmaCond enum₁ x v₁ v₂
  {!!}
tyCond u vec = {!!}

enumSigmaIR : ∀ {u} → List ⟦ u ⟧ → (x : ⟦ u ⟧ → U) → Vec Var (tySize u) → Vec Var (maxTySizeOver (enum u) x) → SI-Monad ⊤
enumSigmaIR enum x v₁ v₂ = {!!}

indToIR : ∀ u → Vec Var (tySize u) → SI-Monad ⊤
indToIR `Zero vec = return tt
indToIR `One (v ∷ []) = add (IAdd zero ((one , v) ∷ []))
indToIR `Two (v ∷ []) = add (IMul one v v one v)
indToIR `Base vec = return tt
indToIR (`Vec u nzero) vec = return tt
indToIR (`Vec u (suc x)) vec with splitAt (tySize u) vec
... | fst , snd = do
  indToIR u fst
  indToIR (`Vec u x) snd
  return tt
indToIR (`Σ u x) vec with splitAt (tySize u) vec
... | fst , snd = do
  indToIR u fst
  {!!}
sourceToIntermediate : ∀ u → Source u → SI-Monad ⊤
sourceToIntermediate u (Ind refl x) = indToIR u x
sourceToIntermediate u (Lit x) = {!!}
sourceToIntermediate `Base (Add source source₁) = {!!}

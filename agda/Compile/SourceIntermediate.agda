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
  
  StateWriterMonad : ∀ {a} {b} {c} → Set a → Set b → Set c → Set (a ⊔ b ⊔ c)
  StateWriterMonad s w a = s → (s × w × a)



  SI-Monad : ∀ {a} → Set a → Set a
  SI-Monad = StateWriterMonad Var (List Intermediate)

  module StateWriterMonad {a} {b} (S : Set a) (W : Set b) (mempty : W) (mappend : W → W → W) where
    _>>=_ : ∀ {c} {d} {A : Set c} {B : Set d}
                → StateWriterMonad S W A
                → (A → StateWriterMonad S W B)
                → StateWriterMonad S W B
    m >>= f = λ s → let s' , w , a = m s
                        s'' , w' , b = f a s'
                    in s'' , mappend w w' , b
  
    _>>_ : ∀ {c} {d} {A : Set c} {B : Set d}
                → StateWriterMonad S W A
                → StateWriterMonad S W B
                → StateWriterMonad S W B
    a >> b = a >>= λ _ → b
  
    return : ∀ {a} {A : Set a}
                → A → StateWriterMonad S W A
    return a = λ s → s , mempty , a

    get : StateWriterMonad S W S
    get = λ s → s , mempty , s

    put : S → StateWriterMonad S W ⊤
    put s = λ _ → s , mempty , tt

    tell : W → StateWriterMonad S W ⊤
    tell w = λ s → s , w , tt

    
  open StateWriterMonad Var (List Intermediate) [] _++_ public

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

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

module Compile.SourceR1CS.Base (f : Set) (field' : Field f) (finite : Finite f) (showf : f → String) where

open import Language.R1CS f
open import Language.R1CS.Show f showf
open import Language.Source f finite showf
open import Language.TySize f finite
open import Language.Universe f

module SI-Monad-Module where
  
  open Function.Endomorphism.Propositional (List R1CS) renaming (Endo to Builder) public


  data WriterMode : Set where
    NormalMode : WriterMode
    PostponedMode : WriterMode

  data SI-Monad : Set → Set₁ where
    return : {A : Set} → A → SI-Monad A
    _>>=_ : {A B : Set} → SI-Monad A → (A → SI-Monad B) → SI-Monad B
    addWithMode : R1CS → WriterMode → SI-Monad ⊤
    withMode : {A : Set} → WriterMode → SI-Monad A → SI-Monad A
    new : SI-Monad Var
    askPrime : SI-Monad ℕ
    askMode : SI-Monad WriterMode

  module PrimBuilder where
    import Control.RWS
    open Control.RWS (WriterMode × ℕ) (Builder × Builder) Var (id , id) (λ { (f₁ , f₂) (s₁ , s₂) → (f₁ ∘′ s₁ , f₂ ∘′ s₂) }) renaming (RWSMonad to SI-Monad-Prim) public

  runSI-MonadBuilder : {A : Set} → SI-Monad A → PrimBuilder.SI-Monad-Prim A
  runSI-MonadBuilder (SI-Monad.return x) = PrimBuilder.return x
  runSI-MonadBuilder (m SI-Monad.>>= f) = (runSI-MonadBuilder m) PrimBuilder.>>= (λ a → runSI-MonadBuilder (f a))
  runSI-MonadBuilder (addWithMode w NormalMode) = PrimBuilder.tell ((λ x → [ w ] ++ x) , id)
  runSI-MonadBuilder (addWithMode w PostponedMode) = PrimBuilder.tell (id , (λ x → [ w ] ++ x))
  runSI-MonadBuilder (withMode x s) =
    PrimBuilder.asks proj₂ PrimBuilder.>>= λ prime →
    PrimBuilder.local (x , prime) (runSI-MonadBuilder s)
  runSI-MonadBuilder new =
    PrimBuilder.get PrimBuilder.>>= λ n →
    PrimBuilder.put (1 +ℕ n) PrimBuilder.>>
    PrimBuilder.return n
  runSI-MonadBuilder askPrime = PrimBuilder.asks proj₂
  runSI-MonadBuilder askMode = PrimBuilder.asks proj₁

  runSI-MonadIsBuilder₁ : {A : Set} → (m : SI-Monad A)
      → (r : WriterMode × ℕ) → (st : Var)
      → let st' , (w₁ , w₂) , a = runSI-MonadBuilder m (r , st)
        in  (x : List R1CS)
      → w₁ x ≡ w₁ [] ++ x
  runSI-MonadIsBuilder₁ (return x₁) r st x = refl
  runSI-MonadIsBuilder₁ (m >>= f) r st x =
    let st' , (w₁₁ , w₁₂) , a = runSI-MonadBuilder m (r , st)
        st'' , (w₂₁ , w₂₂) , b = runSI-MonadBuilder (f a) (r , st')
        w₁₁w₂₁∙x≡mid = trans (runSI-MonadIsBuilder₁ m r st (w₂₁ x))
                             (cong (λ x → w₁₁ [] ++ x) (runSI-MonadIsBuilder₁ (f a) r st' x))
        mid≡w₁₁∘w₂₁∙[]++x = sym (trans (cong (λ t → t ++ x) (runSI-MonadIsBuilder₁ m r st (w₂₁ [])))
                                       (LP.++-assoc (w₁₁ []) (w₂₁ []) x))
    in trans w₁₁w₂₁∙x≡mid mid≡w₁₁∘w₂₁∙[]++x
  runSI-MonadIsBuilder₁ (addWithMode cs NormalMode) r st x = refl
  runSI-MonadIsBuilder₁ (addWithMode cs PostponedMode) r st x = refl
  runSI-MonadIsBuilder₁ (withMode mode m) (_ , prime) st x = runSI-MonadIsBuilder₁ m (mode , prime) st x
  runSI-MonadIsBuilder₁ new r st x = refl
  runSI-MonadIsBuilder₁ askPrime r st x = refl
  runSI-MonadIsBuilder₁ askMode r st x = refl

  runSI-MonadIsBuilder₂ : {A : Set} → (m : SI-Monad A)
      → (r : WriterMode × ℕ) → (st : Var)
      → let st' , (w₁ , w₂) , a = runSI-MonadBuilder m (r , st)
        in  (x : List R1CS)
      → w₂ x ≡ w₂ [] ++ x
  runSI-MonadIsBuilder₂ (return x₁) r st x = refl
  runSI-MonadIsBuilder₂ (m >>= f) r st x =
    let st' , (w₁₁ , w₁₂) , a = runSI-MonadBuilder m (r , st)
        st'' , (w₂₁ , w₂₂) , b = runSI-MonadBuilder (f a) (r , st')
        w₁₂w₂₂∙x≡mid = trans (runSI-MonadIsBuilder₂ m r st (w₂₂ x))
                             (cong (λ x → w₁₂ [] ++ x) (runSI-MonadIsBuilder₂ (f a) r st' x))
        mid≡w₁₂∘w₂₂∙[]++x = sym (trans (cong (λ t → t ++ x) (runSI-MonadIsBuilder₂ m r st (w₂₂ [])))
                                       (LP.++-assoc (w₁₂ []) (w₂₂ []) x))
    in trans w₁₂w₂₂∙x≡mid mid≡w₁₂∘w₂₂∙[]++x
  runSI-MonadIsBuilder₂ (addWithMode cs NormalMode) r st x = refl
  runSI-MonadIsBuilder₂ (addWithMode cs PostponedMode) r st x = refl
  runSI-MonadIsBuilder₂ (withMode mode m) (_ , prime) st x = runSI-MonadIsBuilder₂ m (mode , prime) st x
  runSI-MonadIsBuilder₂ new r st x = refl
  runSI-MonadIsBuilder₂ askPrime r st x = refl
  runSI-MonadIsBuilder₂ askMode r st x = refl


  module Prim where
    import Control.RWS
    open Control.RWS (WriterMode × ℕ) (List R1CS × List R1CS) Var ([] , []) (λ { (f₁ , f₂) (s₁ , s₂) → (f₁ ++ s₁ , f₂ ++ s₂) }) renaming (RWSMonad to SI-Monad-Prim) public


  runSI-Monad : {A : Set} → SI-Monad A → Prim.SI-Monad-Prim A
  runSI-Monad (SI-Monad.return x) = Prim.return x
  runSI-Monad (m SI-Monad.>>= f) = (runSI-Monad m) Prim.>>= (λ a → runSI-Monad (f a))
  runSI-Monad (addWithMode w NormalMode) = Prim.tell ([ w ] , [])
  runSI-Monad (addWithMode w PostponedMode) = Prim.tell ([] , [ w ])
  runSI-Monad (withMode x s) =
    Prim.asks proj₂ Prim.>>= λ prime →
    Prim.local (x , prime) (runSI-Monad s)
  runSI-Monad new =
    Prim.get Prim.>>= λ n →
    Prim.put (1 +ℕ n) Prim.>>
    Prim.return n
  runSI-Monad askPrime = Prim.asks proj₂
  runSI-Monad askMode = Prim.asks proj₁

{-
  BuilderCS≡₁ : {A : Set} → (r : WriterMode) (p : ℕ) (st : Var) (m : SI-Monad A) →
    let _ , (builderCS₁ , builderCS₂) , _ = runSI-MonadBuilder m ((r , p) , st)
        _ , (CS₁        , CS₂)        , _ = runSI-Monad m ((r , p) , st)
    in builderCS₁ [] ≡ CS₁
  BuilderCS≡₁ r p st (return x) = refl
  BuilderCS≡₁ r p st (m >>= x) = {!!}
  BuilderCS≡₁ r p st (addWithMode x x₁) = {!!}
  BuilderCS≡₁ r p st (withMode x m) = {!!}
  BuilderCS≡₁ r p st new = {!!}
  BuilderCS≡₁ r p st askPrime = {!!}
  BuilderCS≡₁ r p st askMode = {!!}
-}
  _>>_ : {A B : Set} → SI-Monad A → SI-Monad B → SI-Monad B
  a >> b = a >>= λ _ → b

  add : R1CS → SI-Monad ⊤
  add w = do
    mode ← askMode
    addWithMode w mode

  newVarVec : ∀ n → SI-Monad (Vec Var n)
  newVarVec nzero = return []
  newVarVec (suc n) = do
    v ← new
    vs ← newVarVec n
    return (v ∷ vs)

open SI-Monad-Module public


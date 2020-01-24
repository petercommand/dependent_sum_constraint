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

module Compile.SourceR1CS.Base (f : Set) (field' : Field f) (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f) where

open import Language.R1CS f
open import Language.R1CS.Show f showf
open import Language.Source f finite showf
open import Language.TySize f finite
open import Language.Universe f

module SI-Monad where
  
  open Function.Endomorphism.Propositional (List R1CS) renaming (Endo to Builder) public

  import Control.RWS-Invariant

  data WriterMode : Set where
    NormalMode : WriterMode
    PostponedMode : WriterMode
  {-
    The reader component is used to store the prime number used
    The state component records the "mode" that determines how the writer writes, and records the first unused var that's incremented every time a var is allocated
    The writer component forces delayed evaluation of some of the constraints during proof gen.
  -}
  WriterInvariant : Builder × Builder → Set
  WriterInvariant = λ builder → ∀ x → proj₁ builder x ≡ (proj₁ builder []) ++ x × proj₂ builder x ≡ (proj₂ builder []) ++ x

  SquashedWriterInvariant = λ b → Squash (WriterInvariant b)


  mempty-WriterInvariant : SquashedWriterInvariant (id , id)
  mempty-WriterInvariant = sq (λ x → refl , refl)

  mappend-WriterInvariant : ∀ {a} {b} → SquashedWriterInvariant a → SquashedWriterInvariant b
             → SquashedWriterInvariant (let f₁ , f₂ = a
                                            s₁ , s₂ = b
                                        in f₁ ∘′ s₁ , f₂ ∘′ s₂)
  mappend-WriterInvariant {f₁ , f₂} {s₁ , s₂} (sq ia) (sq ib) = sq lem
   where
     lem : ∀ x → (f₁ ∘′ s₁) x ≡ (f₁ ∘′ s₁) [] ++ x × (f₂ ∘′ s₂) x ≡ (f₂ ∘′ s₂) [] ++ x
     lem x with ia (s₁ x)
     ... | p₁ , p₂ rewrite p₁ | p₂ with ia (s₁ [])
     ... | p₃ , p₄ rewrite p₃ | p₄ with ib x
     ... | p₅ , p₆ rewrite p₅ | p₆ with ia (s₂ [] ++ x)
     ... | p₇ , p₈ rewrite p₇ | p₈ with ia (s₂ [])
     ... | p₉ , p₁₀ rewrite p₉ | p₁₀ = sym (LP.++-assoc (f₁ []) (s₁ []) x) , sym (LP.++-assoc (f₂ []) (s₂ []) x) 
     {-

f1 (s1 x)
= f1 [] ++ s1 x
= f1 [] ++ (s1 []) ++ x

     -}
  open Control.RWS-Invariant (WriterMode × ℕ) (Builder × Builder) Var SquashedWriterInvariant (id , id) mempty-WriterInvariant (λ { (f₁ , f₂) (s₁ , s₂) → (f₁ ∘′ s₁ , f₂ ∘′ s₂) }) mappend-WriterInvariant hiding (_>>=_; _>>_; return; RWSInvMonad; ask; asks)
  open Control.RWS-Invariant (WriterMode × ℕ) (Builder × Builder) Var SquashedWriterInvariant (id , id) mempty-WriterInvariant (λ { (f₁ , f₂) (s₁ , s₂) → (f₁ ∘′ s₁ , f₂ ∘′ s₂) }) mappend-WriterInvariant using (_>>=_; _>>_; return; ask; asks) renaming (RWSInvMonad to SI-Monad) public

  addWithMode : R1CS → WriterMode → SI-Monad ⊤
  addWithMode w NormalMode = tell ((λ x → [ w ] ++ x) , id) (sq (λ x → refl , refl))
  addWithMode w PostponedMode = tell (id , λ x → [ w ] ++ x) (sq (λ x → refl , refl))


  withMode : ∀ {ℓ} {A : Set ℓ} → WriterMode → SI-Monad A → SI-Monad A
  withMode m act = do
    prime ← asks proj₂
    local (m , prime) act
    

  add : R1CS → SI-Monad ⊤
  add w' = do
    m ← asks proj₁
    addWithMode w' m

  new : SI-Monad Var
  new = do
    v ← get
    put (1 +ℕ v)
    return v

  newVarVec : ∀ n → SI-Monad (Vec Var n)
  newVarVec nzero = return []
  newVarVec (suc n) = do
    v ← new
    vs ← newVarVec n
    return (v ∷ vs)
open SI-Monad public

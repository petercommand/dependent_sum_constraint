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

module Compile.SourceIntermediate.Hints (f : Set) (field' : Field f) (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f) where

open import Language.Intermediate f
open import Language.Intermediate.Show f showf
open import Language.Source f finite showf
open import Language.TySize f finite
open import Language.Universe f

open Field field' hiding (_+_)

import Compile.SourceIntermediate.Base
open import Compile.SourceIntermediate.Base f field' finite showf fToℕ ℕtoF 

open import Compile.SourceIntermediate.LogicGates f field' finite showf fToℕ ℕtoF


allZHint : ∀ {n} → Vec Var n → M.Map Var ℕ → M.Map Var ℕ
allZHint [] = id
allZHint (x ∷ v) = allZHint v ∘′ M.insert natOrd x 0


piLitEqVecHint : ∀ u → (eu : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U) → ⟦ `Π u x ⟧ → Vec Var (tySumOver eu x) → M.Map Var ℕ → M.Map Var ℕ
litEqVecHint : ∀ u → ⟦ u ⟧ → Vec Var (tySize u) → M.Map Var ℕ → M.Map Var ℕ

piLitEqVecHint u [] x f vec = id
piLitEqVecHint u (x₁ ∷ eu) x f vec with splitAt (tySize (x x₁)) vec
... | fst , rest = litEqVecHint (x x₁) (f x₁) fst ∘′ piLitEqVecHint u eu x f rest


litEqVecHint `One tt (v ∷ []) = M.insert natOrd v 0
litEqVecHint `Two false (v ∷ []) = M.insert natOrd v 0
litEqVecHint `Two true (v ∷ []) = M.insert natOrd v 1
litEqVecHint `Base l (v ∷ []) = M.insert natOrd v (fToℕ l)
litEqVecHint (`Vec u nzero) l v = id
litEqVecHint (`Vec u (suc x)) (x₁ ∷ l) v with splitAt (tySize u) v
litEqVecHint (`Vec u (suc x)) (x₁ ∷ l) v | fst , snd = litEqVecHint _ l snd ∘′ litEqVecHint _ x₁ fst
litEqVecHint (`Σ u x) l v with splitAt (tySize u) v
litEqVecHint (`Σ u x) (l₁ , l₂) v | v₁ , v₂ with maxTySplit u l₁ x v₂
... | v₂₁ , v₂₂ = allZHint v₂₂ ∘′ litEqVecHint (x l₁) l₂ v₂₁ ∘′ litEqVecHint u l₁ v₁
litEqVecHint (`Π u x) f vec = piLitEqVecHint u (enum u) x f vec

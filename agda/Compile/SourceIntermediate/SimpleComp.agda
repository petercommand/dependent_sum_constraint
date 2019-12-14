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

module Compile.SourceIntermediate.SimpleComp (f : Set) (field' : Field f) (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f) where

open import Language.Intermediate f
open import Language.Intermediate.Show f showf
open import Language.Source f finite showf
open import Language.TySize f finite
open import Language.Universe f

open Field field' hiding (_+_)

import Compile.SourceIntermediate.Base
open import Compile.SourceIntermediate.Base f field' finite showf fToℕ ℕtoF 

open import Compile.SourceIntermediate.LogicGates f field' finite showf fToℕ ℕtoF


varEqBaseLit : Var → f → SI-Monad Var
varEqBaseLit n l = do
  n-l ← new
  add (IAdd (- l) ((one , n) ∷ (- one , n-l) ∷ []))
  ¬r ← neqz n-l
  r ← lnot ¬r
  return r

anyNeqz : ∀ {n} → Vec Var n → SI-Monad Var
anyNeqz [] = do
  v ← new
  add (IAdd zero ((one , v) ∷ []))
  return v
anyNeqz (x ∷ vec) = do
 r ← neqz x
 rs ← anyNeqz vec
 lor r rs

allEqz : ∀ {n} → Vec Var n → SI-Monad Var
allEqz vec = do
  ¬r ← anyNeqz vec
  r ← lnot ¬r
  return r

piVarEqLit : ∀ u (x : ⟦ u ⟧ → U) (eu : List ⟦ u ⟧) → Vec Var (tySumOver eu x) → ⟦ `Π u x ⟧ → SI-Monad Var
varEqLit : ∀ u → Vec Var (tySize u) → ⟦ u ⟧ → SI-Monad Var

piVarEqLit u x [] vec f = trivial
piVarEqLit u x (x₁ ∷ eu) vec f with splitAt (tySize (x x₁)) vec
... | fst , snd = do
  r ← varEqLit (x x₁) fst (f x₁)
  s ← piVarEqLit u x eu snd f
  land r s

varEqLit `One vec lit = allEqz vec
varEqLit `Two vec false = allEqz vec
varEqLit `Two vec true = anyNeqz vec
varEqLit `Base (x ∷ []) lit = do
  v ← new
  add (IAdd lit ((- one , x) ∷ (- one , v) ∷ []))
  allEqz (v ∷ [])
varEqLit (`Vec u nzero) vec lit = trivial
varEqLit (`Vec u (suc x)) vec (l ∷ lit) with splitAt (tySize u) vec
... | fst , snd = do
  r ← varEqLit u fst l
  s ← varEqLit (`Vec u x) snd lit
  land r s
varEqLit (`Σ u x) vec (fstₗ , sndₗ) with splitAt (tySize u) vec
... | fst , snd with maxTySplit u fstₗ x snd
... | vecₜ₁ , vecₜ₂ = do
  r ← varEqLit u fst fstₗ
  s ← varEqLit (x fstₗ) vecₜ₁ sndₗ
  land r s


varEqLit (`Π u x) vec f = piVarEqLit u x (enum u) vec f

enumSigmaCond : ∀ {u} → List ⟦ u ⟧ → (x : ⟦ u ⟧ → U) → Vec Var (tySize u) → Vec Var (maxTySizeOver (enum u) x) → SI-Monad Var
enumPiCond : ∀ {u} → (eu : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U) → Vec Var (tySumOver eu x) → SI-Monad Var
tyCond : ∀ u → Vec Var (tySize u) → SI-Monad Var

enumSigmaCond [] x v₁ v₂ = trivial
enumSigmaCond {u} (elem₁ ∷ enum₁) x v₁ v₂ with maxTySplit u elem₁ x v₂
... | fst , snd = do
  eqElem₁ ← varEqLit u v₁ elem₁
  tyCons ← tyCond (x elem₁) fst
  restZ ← allEqz snd
  sat ← limp eqElem₁ tyCons
  rest ← enumSigmaCond enum₁ x v₁ v₂
  r' ← land sat rest
  land r' restZ

enumPiCond [] x vec = trivial
enumPiCond (x₁ ∷ eu) x vec with splitAt (tySize (x x₁)) vec
... | fst , rest = do
  r ← tyCond (x x₁) fst
  s ← enumPiCond eu x rest
  land r s
tyCond `Zero vec = trivial
tyCond `One vec = allEqz vec
tyCond `Two vec = do
  isZero ← varEqLit `Two vec false
  isOne ← varEqLit `Two vec true
  lor isZero isOne
tyCond `Base vec = trivial
tyCond (`Vec u nzero) vec = trivial
tyCond (`Vec u (suc x)) vec with splitAt (tySize u) vec
... | fst , snd = do
  r ← tyCond u fst
  s ← tyCond (`Vec u x) snd
  land r s
tyCond (`Σ u x) vec with splitAt (tySize u) vec
... | fst , snd = do
  r ← tyCond u fst
  s ← enumSigmaCond (enum u) x fst snd
  land r s
tyCond (`Π u x) vec = enumPiCond (enum u) x vec

indToIR : ∀ u → Vec Var (tySize u) → SI-Monad (Vec Var (tySize u))
indToIR `Zero vec = return []
indToIR `One vec@(v ∷ []) = do
  add (IAdd zero ((one , v) ∷ []))
  return vec
indToIR `Two vec@(v ∷ []) = do
  add (IMul one v v one v)
  return vec
indToIR `Base vec = return vec
indToIR (`Vec u nzero) vec = return vec
indToIR (`Vec u (suc x)) vec with splitAt (tySize u) vec
... | fst , snd = do
  indToIR u fst
  indToIR (`Vec u x) snd
  return vec
indToIR (`Σ u x) vec = do
  t ← tyCond (`Σ u x) vec
  assertTrue t
  return vec
indToIR (`Π u x) vec = do
  t ← tyCond (`Π u x) vec
  assertTrue t
  return vec

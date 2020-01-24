{-# OPTIONS --prop #-}
open import Agda.Builtin.Nat renaming (zero to nzero) hiding (_+_; _*_)

open import Data.Field
open import Data.Finite
open import Data.List hiding (splitAt; head; take; drop; intercalate; concat)
import Data.Map
module M = Data.Map
open import Data.MaybeC
open import Data.Nat hiding (_⊔_) renaming (zero to nzero; _≟_ to _≟ℕ_; _+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Mod renaming (mod to modℕ)
open import Data.Product hiding (map)
import Data.Sets
module S = Data.Sets
open import Data.String renaming (_++_ to _S++_) hiding (show; fromList)
open import Data.Unit

open import Language.Common

open import Level renaming (zero to lzero; suc to lsuc)

open import Math.Arithmoi

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import TypeClass.Ord

module Compile.SourceR1CS.LogicGates (f : Set) (field' : Field f) (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f) where

open import Compile.SourceR1CS.Base f field' finite showf fToℕ ℕtoF 


open import Language.R1CS f

open Field field' hiding (_+_)

assertTrue : Var → SI-Monad ⊤
assertTrue v = add (IAdd one ((- one , v) ∷ []))


trivial : SI-Monad Var
trivial = do
  return 0

neqzHint : ℕ → Var → Var → Var → M.Map Var ℕ → M.Map Var ℕ
neqzHint prime n v v' m with M.lookup natOrd n m
neqzHint prime n v v' m | nothing = m
neqzHint prime n v v' m | just nzero = M.insert natOrd v 0 (M.insert natOrd v' 0 m)
neqzHint prime n v v' m | just (suc x) = M.insert natOrd v (modℕ (getInv (suc x) prime) prime) (M.insert natOrd v' 1 m)

neqz : Var → SI-Monad Var
neqz n = do
  v ← new
  v' ← new
  prime ← asks proj₂
  add (Hint (neqzHint prime n v v'))
  add (IMul one v n one v')
  add (IMul one v' n one n)
  return v'


lor : Var → Var → SI-Monad Var
lor n₁ n₂ = do
  -- v = a + b - ab
  v ← new
  v' ← new
  add (IMul one n₁ n₂ one v)
  add (IAdd zero ((one , n₁) ∷ (one , n₂) ∷ (- one , v) ∷ (- one , v') ∷ []))
  return v'



land : Var → Var → SI-Monad Var
land n₁ n₂ = do
  v ← new
  add (IMul one n₁ n₂ one v)
  return v

lnot : Var → SI-Monad Var
lnot n₁ = do
  v ← new
  add (IAdd one ((- one , n₁) ∷ (- one , v) ∷ []))
  return v

limp : Var → Var → SI-Monad Var
limp n₁ n₂ = do
  notN₁ ← lnot n₁
  lor notN₁ n₂

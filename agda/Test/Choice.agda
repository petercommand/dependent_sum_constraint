{-# OPTIONS --prop #-}
module Test.Choice where
open import Data.Bool renaming (_≟_ to _≟B_)
open import Data.Field
open import Data.Field.Prime
open import Data.Fin hiding (_≟_; _+_)
open import Data.List hiding (splitAt)
open import Data.MaybeC 
import Data.Map
module M = Data.Map
open import Data.Map using (Map)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Primality
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product hiding (map)
open import Data.ProductPrime
open import Data.Unit hiding (_≟_)
open import Data.Vec hiding (_>>=_; map; splitAt) renaming (_++_ to _V++_)
open import Data.Vec.Split
open import Function

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import TypeClass.Ord

N = 21888242871839275222246405745257275088548364400416034343698204186575808495617

choice = 1
input1 = 99
input2 = 100
input3 = 384
input4 = 390

postulate
  nPrime : Prime N

FF = PrimeField N
FField = isField N nPrime
FFinite = isFinite N nPrime

open Field FField renaming ( _+_ to _+F_
                           ; _*_ to _*F_
                           ; -_ to -F_
                           ; 1/_ to 1F/_
                           ; zero to zerof
                           ; one to onef)


open import Language.Common


module Test where
  open import Language.Source FF FFinite (λ x → showℕ (PrimeField.elem x) )
  open import Language.Source.Utils FF FFinite (λ x → showℕ (PrimeField.elem x) )
  open import Language.TySize FF FFinite
  open import Language.Universe FF

  Σ-proj₁ : ∀ {u} {x : ⟦ u ⟧ → U} → Source (`Σ u x) → Source u
  Σ-proj₁ {u} (Ind refl x₁) with splitAt (tySize u) x₁
  ... | fst , snd = Ind refl fst
  Σ-proj₁ (Lit (fst , snd)) = Lit fst

  inputF : ⟦ `Two ⟧ → U
  inputF false = `Vec `Base 2
  inputF true = `Vec (`Vec `Base 2) 2
  
  resultF : ⟦ `Two ⟧ → U
  resultF false = `Base
  resultF true = `Vec `Base 2

  var : ℕ → Source `Base
  var n = Ind refl (n ∷ [])

  lnot : Var → S-Monad Var
  lnot n = do
    v ← S-Monad.newVar
    assertEq (Add (Lit onef) (Mul (Lit (-F onef)) (var n))) (var v)
    return v
  
  computeFalse : Vec Var (maxTySizeOver (enum `Two) inputF) →  S-Monad (Vec Var (maxTySizeOver (enum `Two) resultF))
  computeFalse vec with maxTySplit `Two false inputF vec
  ... | Σ₂₁ ∷ Σ₂₂ ∷ [] , blank = do
    r ← S-Monad.newVar
    filler ← S-Monad.newVar
    assertEq (Lit zerof) (var filler)
    assertEq (var r) (Add (var Σ₂₁) (var Σ₂₂))
    return (r ∷ filler ∷ [])

  computeTrue : Vec Var (maxTySizeOver (enum `Two) inputF) → S-Monad (Vec Var (maxTySizeOver (enum `Two) resultF))
  computeTrue vec with maxTySplit `Two true inputF vec
  ... | Σ₂₁ ∷ Σ₂₂ ∷ Σ₂₃ ∷ Σ₂₄ ∷ [] , [] = do
    r₁ ← S-Monad.newVar
    r₂ ← S-Monad.newVar
    assertEq (var r₁) (Add (var Σ₂₁) (var Σ₂₃))
    assertEq (var r₂) (Add (var Σ₂₂) (var Σ₂₄))
    return (r₁ ∷ r₂ ∷ [])

  assertEqWithCond : ∀ {n} → Var → Vec Var n → Vec Var n → S-Monad ⊤
  assertEqWithCond v [] [] = return tt
  assertEqWithCond v (x₁ ∷ vec₁) (x₂ ∷ vec₂) = do
    assertEq (Mul (var v) (var x₁)) (Mul (var v) (var x₂))
    assertEqWithCond v vec₁ vec₂

  computeHint : Vec Var (maxTySizeOver (enum `Two) resultF) → Map Var ℕ → Map Var ℕ
  computeHint (v₁ ∷ v₂ ∷ []) m with M.lookup natOrd 1 m
  ... | nothing = m -- choice not found
  ... | just 0 = M.insert natOrd 10 (input1 + input2) (M.insert natOrd 11 0 m)
  ... | just 1 = M.insert natOrd 10 (input1 + input3) (M.insert natOrd 11 (input2 + input4) m)
  ... | just _ = m -- invalid choice

  compute : Source (`Σ `Two inputF) → S-Monad (Source (`Σ `Two resultF))
  compute (Ind refl x₁) with splitAt (tySize `Two) x₁
  compute (Ind refl x₁) | fst ∷ [] , snd = do
    result ← S-Monad.newVars (maxTySizeOver (enum `Two) resultF) -- v₁₀ - v₁₁
    addHint (computeHint result)
    r₁ ← computeFalse snd
    r₂ ← computeTrue snd
    fst=0 ← lnot fst
    assertEqWithCond fst r₂ result
    assertEqWithCond fst=0 r₁ result
    return (Ind refl (fst ∷ result))
  compute (Lit (false , x₁ ∷ x₂ ∷ [])) = return (Lit (false , (x₁ +F x₂)))
  compute (Lit (true , ((x₁₁ ∷ x₁₂ ∷ []) ∷ (x₂₁ ∷ x₂₂ ∷ []) ∷ []))) = do
    return (Lit (true , ((x₁₁ +F x₂₁) ∷ (x₁₂ +F x₂₂) ∷ [])))

  test : S-Monad (Source (`Σ `Two resultF))
  test = do
    choice ← newI `Two -- v₁
    input ← newI (`Σ `Two inputF) -- v₂ - v₆
    result ← new (`Σ `Two resultF) -- v₇ - v₉
    assertEq (Σ-proj₁ result) choice
    assertEq (Σ-proj₁ input) choice
    r ← compute input
    assertEq result r
    return result
open Test

open import Compile.Generate FF FField FFinite (λ x → showℕ (PrimeField.elem x)) PrimeField.elem (fieldElem nPrime)

open import IO

main = let inputAss = (1 , choice) ∷ (2 , choice) ∷ (3 , input1) ∷ (4 , input2) ∷ (5 , input3) ∷ (6 , input4) ∷ []
       in run (genMain N test inputAss)

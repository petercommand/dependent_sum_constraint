{-# OPTIONS --prop #-}
module Test.MatrixMultSmall where

open import Data.Bool renaming (_≟_ to _≟B_)
open import Data.Field.Finite
open import Data.Fin hiding (_≟_)
open import Data.List hiding (foldl)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Primality
open import Data.Nat.Properties
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product hiding (map)
open import Data.Unit hiding (_≟_)
open import Data.Vec hiding (_>>=_; map; _++_)

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

N = 21888242871839275222246405745257275088548364400416034343698204186575808495617


postulate
  nPrime : Prime N


FF = FiniteField N
FField = isField N nPrime
FFinite = isFinite N nPrime

open import Language.Common


module Test where
  open import Language.Source FF FFinite (λ x → showℕ (FiniteField.elem x))
  open import Language.Source.Utils FF FFinite (λ x → showℕ (FiniteField.elem x))
  open import Language.TySize FF FFinite
  open import Language.Universe FF
  
  `Matrix : U → ℕ → ℕ → U
  `Matrix u m n = `Vec (`Vec u n) m
  
  f : ⟦ `Two ⟧ → U
  f t with t ≟B false
  f t | yes p = `Two
  f t | no ¬p = `One
  
  getMatrix : ∀ {u} {m} {n} → Source (`Matrix u m n) → Fin m → Fin n → Source u
  getMatrix s m n = getV (getV s m) n

  open import Function

  test : S-Monad (Source (`Matrix `Base 2 3))
  test = do
    m₁ ← newI (`Matrix `Base 2 4)
    m₂ ← newI (`Matrix `Base 4 3)
    m₃ ← new (`Matrix `Base 2 3)
    iterM 2 (λ m → do
       iterM 3 (λ n → do
          vec ← iterM 4 (λ o → do
            let fstElem = getMatrix m₁ m o
                sndElem = getMatrix m₂ o n
            return (Mul fstElem sndElem))
          let setElem = getMatrix m₃ m n
          let r = foldl (const (Source `Base)) Add (Lit (fieldElem nPrime 0)) vec
          assertEq r setElem))
    return m₃
open Test

open import Compile.Generate FF FField FFinite (λ x → showℕ (FiniteField.elem x)) FiniteField.elem (fieldElem nPrime)

open import IO

main = 
  let
      inputAss = (1 , 3) ∷ (2 , 5) ∷ (3 , 7) ∷ (4 , 9) ∷ (5 , 11) ∷ (6 , 13) ∷ (7 , 15) ∷ (8 , 17) ∷ (9 , 3) ∷ (10 , 5) ∷ (11 , 7) ∷ (12 , 9) ∷ (13 , 11) ∷ (14 , 13) ∷ (15 , 15) ∷ (16 , 17) ∷ (17 , 19) ∷ (18 , 21) ∷ (19 , 23) ∷ (20 , 25) ∷ []
  in run (genMain N test inputAss)

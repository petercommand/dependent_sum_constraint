{-# OPTIONS --prop #-}
module Test.DependentProdSimple where
open import Data.Bool renaming (_≟_ to _≟B_)
open import Data.Field.Prime
open import Data.Fin hiding (_≟_)
open import Data.List
open import Data.Nat hiding (_≟_)
open import Data.Nat.Primality
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product hiding (map)
open import Data.Unit hiding (_≟_)
open import Data.Vec hiding (_>>=_; map)

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

N = 21888242871839275222246405745257275088548364400416034343698204186575808495617

postulate
  nPrime : Prime N

FF = PrimeField N
FField = isField N nPrime
FFinite = isFinite N nPrime

open import Language.Common


module Test where
  open import Language.Source FF FFinite (λ x → showℕ (PrimeField.elem x) )
  open import Language.Source.Utils FF FFinite (λ x → showℕ (PrimeField.elem x) )
  open import Language.TySize FF FFinite
  open import Language.Universe FF

  f : ⟦ `Two ⟧ → U
  f t with t ≟B false
  f t | yes p = `Two
  f t | no ¬p = `Base

  func : ⟦ `Π `Two f ⟧
  func false = true
  func true = fieldElem nPrime 12345
  
  test : S-Monad (Source `Base)
  test = do
    m₁ ← new (`Π `Two f)
    assertEq m₁ (Lit func)
    app m₁ true
open Test

open import Compile.Generate FF FField FFinite (λ x → showℕ (PrimeField.elem x)) PrimeField.elem (fieldElem nPrime)

open import IO

main = run (genMain N test [])

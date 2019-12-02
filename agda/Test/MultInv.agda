module Test.MultInv where


open import Data.Bool renaming (_≟_ to _≟B_)
open import Data.Field
open import Data.Field.Finite
open import Data.Fin hiding (_≟_)
open import Data.List
open import Data.Nat hiding (_≟_)
open import Data.Nat.Primality
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


open Field FField
open import IO

main' = putStrLn (showℕ (FiniteField.elem (1/ fieldElem nPrime 1)))

main = run main'

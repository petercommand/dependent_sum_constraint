module Test.Simple where

open import Data.Bool renaming (_≟_ to _≟B_)
open import Data.Field.Finite
open import Data.Fin hiding (_≟_)
open import Data.List
open import Data.Nat hiding (_≟_)
open import Data.Product hiding (map)
open import Data.Unit hiding (_≟_)
open import Data.Vec hiding (_>>=_; map; _++_)

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

N = 21888242871839275222246405745257275088548364400416034343698204186575808495617

FF = FiniteField N
FField = isField N
FFinite = isFinite N

open import Language.Common


module Test where
  open import Language.Source FF FFinite
  open import Language.Source.Utils FF FFinite
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
  
  test : S-Monad (Source `Base)
  test = do
    m₁ ← newI `Base
    m₂ ← newI `Base
    return (Add m₁ m₂)
open Test

open import Codata.Musical.Colist using (Colist) renaming (fromList to coFromList)
open import Codata.Musical.Notation

open import Data.Nat.Show

open import Compile.SourceIntermediate FF FField FFinite (λ x → show (FiniteField.elem x))
open import Language.Intermediate FF

open import Function

IR : _
IR = compileSource _ test

open import Language.Intermediate.Show FF (λ x → show (FiniteField.elem x))
open import IO
open import Z3.Cmd
open import Level

open import Data.String renaming (_++_ to _S++_)

main' : IO (Lift Level.zero ⊤)
main' = 
  let n , result , (out , input) = IR
      z3Cmd = genWitnessSMT n ((1 , 10) ∷ (2 , 20) ∷ []) (result [])
  in
     ♯ writeFile "constraints" "" >>
     ♯ (♯ sequence′ (coFromList (map (appendFile "constraints" ∘′ (λ x → x S++ "\n") ∘′ showIntermediate) (result []))) >>
     ♯ (♯ writeFile "test.smt" "" >>
     ♯ sequence′ (coFromList (map (appendFile "test.smt" ∘′ (λ x → x S++ "\n") ∘′ showZ3) (z3Cmd ++ (CheckSat ∷ GetModel ∷ []))))))

main = run main'

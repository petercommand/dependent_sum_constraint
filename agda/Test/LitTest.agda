module Test.LitTest where

open import Data.Bool renaming (_≟_ to _≟B_)
open import Data.Field.Finite
open import Data.Fin hiding (_≟_)
open import Data.List
open import Data.Nat hiding (_≟_)
open import Data.Nat.Show renaming (show to showℕ)
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
  open import Language.Source FF FFinite (λ x → showℕ (FiniteField.elem x))
  open import Language.Source.Utils FF FFinite (λ x → showℕ (FiniteField.elem x))
  open import Language.TySize FF FFinite
  open import Language.Universe FF

  
  test : S-Monad (Source `Base)
  test = do
    m₁ ← new `Base
    assertEq m₁ (Add (Lit (fieldElem 2)) (Lit (fieldElem 23)))
    return m₁
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
      z3Cmd = genWitnessSMT n [] (result [])
  in
     ♯ writeFile "constraints" "" >>
     ♯ (♯ sequence′ (coFromList (map (appendFile "constraints" ∘′ (λ x → x S++ "\n") ∘′ showIntermediate) (result []))) >>
     ♯ (♯ writeFile "test.smt" "" >>
     ♯ sequence′ (coFromList (map (appendFile "test.smt" ∘′ (λ x → x S++ "\n") ∘′ showZ3) (z3Cmd ++ (CheckSat ∷ GetModel ∷ []))))))

main = run main'

open import Codata.Musical.Colist using (Colist) renaming (fromList to coFromList)
open import Codata.Musical.Notation

open import Data.Bool
open import Data.Field
open import Data.Finite
open import Data.List
open import Data.Nat
open import Data.Nat.Show 
open import Data.String hiding (show) renaming (_++_ to _S++_)
open import Data.Product hiding (map)
open import Data.Unit
open import Data.Vec hiding (_++_; map)

open import Function

open import IO

open import Level

module Compile.Generate (f : Set) (field' : Field f) (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ)  where

open import Compile.SourceIntermediate f field' finite showf fToℕ
open import Language.Common
open import Language.Intermediate.Show f showf
open import Language.Source f finite showf
open import Language.Source.Utils f finite showf hiding (_>>_)
open import Language.TySize f finite
open import Language.Universe f

open import Z3.Cmd

genMain : ∀ {u} → S-Monad (Source u) → List (Var × ℕ) → IO (Lift Level.zero ⊤)
genMain m i =
  let IR = compileSource _ m
      n , result , (out , input) = IR
      z3Cmd = genWitnessSMT n i (result [])
      magma = genMagmaSolve n i (result [])
  in

     ♯ writeFile "inputvars" "" >>
     ♯ (♯ sequence′ (coFromList (map (appendFile "inputvars" ∘′ (λ x → x S++ "\n") ∘′ show) input)) >>
     ♯ (♯ writeFile "outvars" "" >>
     ♯ (♯ sequence′ (coFromList (map (appendFile "outvars" ∘′ (λ x → x S++ "\n") ∘′ show) (Data.Vec.toList out))) >>
     ♯ (♯ writeFile "constraints" "" >>
     ♯ (♯ sequence′ (coFromList (map (appendFile "constraints" ∘′ (λ x → x S++ "\n") ∘′ showIntermediate) (result []))) >>
     ♯ (♯ writeFile "test.smt" "" >>
     ♯ (♯ writeFile "magma.input" "" >>
     ♯ (♯ sequence′ (coFromList (map (appendFile "magma.input" ∘′ (λ x → x S++ "\n")) magma)) >>
     ♯ sequence′ (coFromList (map (appendFile "test.smt" ∘′ (λ x → x S++ "\n") ∘′ showZ3) (z3Cmd ++ (CheckSat ∷ GetModel ∷ []))))))))))))


{-# OPTIONS --prop -vtest:20 #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection 
open import Data.Bool
open import Data.Char
open import Data.Empty
open import Data.Field
open import Data.Finite
open import Data.List hiding (lookup; head; splitAt)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any hiding (head; map)
open import Data.Nat
open import Data.Nat.Primality
open import Data.Nat.Show

open import Data.Product hiding (map)
open import Data.ProductPrime
open import Data.Squash
open import Data.String hiding (_≈_; _≟_; _++_)
open import Data.Unit


open import Function

open import Language.Common

open import Reflection


open import Relation.Binary
open import Relation.Binary.PropositionalEquality


import Relation.Binary.HeterogeneousEquality
module HE = Relation.Binary.HeterogeneousEquality
open import Relation.Binary.HeterogeneousEquality.Core
open import Relation.Nullary
module Satisfiability.SourceIntermediate.Tactics (f : Set) (_≟F_ : Decidable {A = f} _≡_) (field' : Field f) (isField : IsField f field')
     (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f)
        (ℕtoF-1≡1 : ℕtoF 1 ≡ Field.one field')
        (ℕtoF-0≡0 : ℕtoF 0 ≡ Field.zero field') (prime : ℕ) (isPrime : Prime prime) where


open import Language.TySize f finite
open import Language.Universe f
open import Language.Intermediate f


open Field field' renaming ( _+_ to _+F_
                           ; _*_ to _*F_
                           ; -_ to -F_
                           ; 1/_ to 1F/_
                           ; zero to zerof
                           ; one to onef)
open IsField isField
import Compile.SourceIntermediate f field' finite showf fToℕ ℕtoF as SI

open import Satisfiability.SourceIntermediate.Base f _≟F_ field' isField finite showf fToℕ ℕtoF ℕtoF-1≡1 ℕtoF-0≡0 prime isPrime


getTermsFromClauses : List Clause → List Term
getTermsFromClauses [] = []
getTermsFromClauses (clause ps t ∷ c) = t ∷ getTermsFromClauses c
getTermsFromClauses (absurd-clause ps ∷ c) = getTermsFromClauses c

getTerms : Definition → List Term
getTerms (function cs) = getTermsFromClauses cs
getTerms (data-type pars cs) = []
getTerms (record′ c fs) = []
getTerms (constructor′ d) = []
getTerms axiom = []
getTerms primitive′ = []


stringSplit : Char → List Char → List (List Char)
stringSplit c l = reverse (aux l [] [])
  where
    aux : List Char → List Char → List (List Char) → List (List Char)
    aux [] [] acc = acc
    aux [] (x ∷ buf) acc = reverse (x ∷ buf) ∷ acc
    aux (c' ∷ l) buf acc with Data.Char._≟_ c c'
    aux (c' ∷ l) buf acc | yes p = aux l [] ((reverse buf) ∷ acc)
    aux (c' ∷ l) buf acc | no ¬p = aux l (c' ∷ buf) acc

getLast : List (List Char) → List Char
getLast [] = []
getLast (l ∷ []) = l
getLast (l ∷ l₁ ∷ l₂) = getLast (l₁ ∷ l₂)

getFuncName : String → String
getFuncName s = fromList (getLast (stringSplit '.' (toList s)))

print : List ErrorPart → TC ⊤
print = debugPrint "test.debug" 10

head' : ∀ {ℓ} {A : Set ℓ} → List A → TC A
head' [] = typeError (strErr "empty head" ∷ [])
head' (x ∷ l) = return x

getDefName : Term → TC Name
getDefName (def n _) = return n
getDefName t = typeError (strErr "getDefName: not a definition" ∷ termErr t ∷ [])

getDefArgs : Term → TC (List (Arg Term))
getDefArgs (def n t) = return t
getDefArgs t = typeError (strErr "getDefArgs: not a definition" ∷ termErr t ∷ [])


_!!_ : ∀ {ℓ} {A : Set ℓ} → List A → ℕ → TC A
[] !! n = typeError (strErr "index out of range" ∷ [])
(x ∷ l) !! zero = return x
(x ∷ l) !! suc n = l !! n

getArg : ∀ {A : Set} → Arg A → A
getArg (arg i x) = x


printDef : Term → TC ⊤
printDef (def n args) = do
  print (strErr "printDef" ∷ [])
  print (nameErr n ∷ [])
  print (strErr "args" ∷ [])
  print (intersperse (strErr "&") (map (termErr ∘′ getArg) args))
printDef t = typeError (strErr "printDef" ∷ termErr t ∷ [])


{-# TERMINATING #-}
getActualDef : String → Term → TC Definition
getActualDef s (def funName _) with Data.String._≟_ s (getFuncName (showName funName))
getActualDef s (def funName _) | yes p with Data.String._≟_ s "_>>=_"
getActualDef s (def funName _) | yes p | yes p₁ = getDefinition funName
getActualDef s (def funName _) | yes p | no ¬p = do
  funDef ← getDefinition funName
--  print (strErr "---" ∷ strErr s ∷ [])
--  print (Data.List.map termErr (getTerms funDef))
  t ← head' (getTerms funDef)
--  print (strErr "-+-" ∷ [])
--  print (termErr t ∷ [])
--  print (strErr "-1-" ∷ [])
  n ← getDefName t
  aux funDef t n
 where
      aux : Definition → Term → Name → TC Definition
      aux acc t n with Data.String._≟_ s (getFuncName (showName n))
      aux acc t n | yes p = getActualDef s t
      aux acc t n | no ¬p = return acc

getActualDef s (def funName _) | no ¬p = do
--  print (strErr "result: " ∷ [])
  getDefinition funName
getActualDef _ t = typeError (strErr "getActualDef" ∷ termErr t ∷ [])

printVar : Term → TC ⊤
printVar (var x args) = print (strErr (Data.Nat.Show.show x) ∷ [] )
printVar t = typeError (strErr "printVar" ∷ termErr t ∷ [])


macro
  findSol : Term → Term → Term → TC ⊤
  findSol fdef@(def qualedFunName args) isSol goal = do
--    print (strErr "initial args" ∷ [])
    printDef fdef
    print (strErr "---" ∷ [])
    let funNameStr = getFuncName (showName qualedFunName)
    funDef ← getActualDef funNameStr fdef
    solTy ← inferType isSol
    let terms = getTerms funDef
--    print (intersperse (strErr "&") (Data.List.map termErr terms))
--    print (strErr "got terms" ∷ [])
    fstTerm ← terms !! 0
    args ← getDefArgs fstTerm
    test ← args !! 4
    testArgs ← getDefArgs (getArg test)
    writerMode ← testArgs !! 2
    writerModeArgs ← getDefArgs (getArg writerMode)
    r ← writerModeArgs !! 4
    m ← args !! 16
    m' ← getDefName (getArg m)
    f ← args !! 17
--    normalise (getArg m)
--    printDef fstTerm
-- no. 17, 18 args (i.e. at index 16 & 17)
--    (m , f) ← get>>=Args fstTerm
--    print (termErr m ∷ termErr f ∷ [])
    printDef (getArg m)
--    print (termErr (getArg f) ∷ [])
--    inferType (getArg m)
--    testTy ← inferType (getArg test)
--    print (termErr testTy ∷ [])
    let BaseModArgs = quoteTerm f ∷ quoteTerm field' ∷ quoteTerm finite ∷ quoteTerm showf ∷ quoteTerm fToℕ ∷ quoteTerm ℕtoF ∷ []
    unify goal (def (quote BuilderProdSol->>=⁻₁) (hArg unknown ∷ hArg unknown ∷ hArg unknown ∷ hArg unknown
        ∷ vArg (def m' (map vArg BaseModArgs)) ∷ vArg unknown ∷ vArg unknown ∷ vArg unknown ∷ vArg unknown ∷ vArg isSol ∷ []))
    return tt
    
  findSol _ _ _ = typeError (strErr "Invalid application of findSol" ∷ [])

neqzFunc : ℕ → ℕ
neqzFunc n with ℕtoF n ≟F zerof
neqzFunc n | yes p = 0
neqzFunc n | no ¬p = 1


neqzSound : ∀ (r : SI.SI-Monad.WriterMode)
  → ∀ (v : Var) → (val : ℕ) → (solution' : List (Var × ℕ))
  → ListLookup v solution' val
  → ∀ (init : ℕ) → 
  let result = SI.neqz v ((r , prime) , init)
  in BuilderProdSol (writerOutput result) solution'
  → ListLookup (output result) solution' (neqzFunc val)
neqzSound r v val solution' vIsVal init isSol
    with addSound r (IMul onef init v onef (suc init)) solution' (2 + init) (findSol SI.neqz isSol)
       | addSound r (IMul onef (suc init) v onef v) solution' (2 + init) {!quoteTerm r!}
neqzSound r v val solution' vIsVal init isSol
   | multSol .(Field.one field') .init bval .v cval .(Field.one field') .(suc init) eval x x₁ x₂ x₃
       | multSol .(Field.one field') .(suc init) bval₁ .v cval₁ .(Field.one field') .v eval₁ x₄ x₅ x₆ x₇
       rewrite *-identityˡ (ℕtoF bval₁)
             | *-identityˡ (ℕtoF eval₁)
             | *-identityˡ (ℕtoF bval)
             | *-identityˡ (ℕtoF eval)
    with ListLookup-≈ x₅ x₁ | ListLookup-≈ x₄ x₂ | ListLookup-≈ x₁ vIsVal | ListLookup-≈ x₆ vIsVal
... | (sq eq₁) | (sq eq₂) | (sq eq₃) | (sq eq₄) rewrite eq₁ | eq₂ | eq₃ | eq₄
    with ℕtoF val ≟F zerof
... | yes p rewrite p
                  | *-zeroʳ (ℕtoF bval) = ListLookup-Respects-≈ _ _ _ _ (sq (trans (sym x₃) (sym ℕtoF-0≡0))) x₂
... | no ¬p = ListLookup-Respects-≈ _ _ _ _ (sq (trans lem₁ (sym ℕtoF-1≡1))) x₂
  where
    open ≡-Reasoning
    lem₁ : ℕtoF eval ≡ onef
    lem₁ =
      begin
        ℕtoF eval
      ≡⟨ sym (*-identityʳ (ℕtoF eval)) ⟩
        ℕtoF eval *F onef
      ≡⟨ cong (_*F_ (ℕtoF eval)) (sym (*-invʳ (ℕtoF val) ¬p)) ⟩
        ℕtoF eval *F (ℕtoF val *F (1F/ ℕtoF val))
      ≡⟨ sym (*-assoc (ℕtoF eval) (ℕtoF val) (1F/ ℕtoF val)) ⟩
        (ℕtoF eval *F (ℕtoF val)) *F (1F/ ℕtoF val)
      ≡⟨ cong (λ x → _*F_ x (1F/ (ℕtoF val))) x₇ ⟩
        ℕtoF val *F (1F/ ℕtoF val)
      ≡⟨ *-invʳ (ℕtoF val) ¬p ⟩
        onef
      ∎


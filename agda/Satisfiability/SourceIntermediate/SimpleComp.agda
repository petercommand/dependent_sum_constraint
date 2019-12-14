{-# OPTIONS --prop #-}

open import Data.Bool
open import Data.Empty
open import Data.Field
open import Data.Finite
open import Data.List hiding (lookup; head; splitAt)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Primality


open import Data.Product hiding (map)
open import Data.ProductPrime
open import Data.Vec hiding (_>>=_; _++_; splitAt)
open import Data.Vec.Split
open import Data.Squash
open import Data.String hiding (_≈_; _≟_; _++_)
open import Data.Sum
open import Data.Unit
open import Function

open import Language.Common

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
module Satisfiability.SourceIntermediate.SimpleComp (f : Set) (_≟F_ : Decidable {A = f} _≡_) (field' : Field f) (isField : IsField f field')
     (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f)
        (ℕtoF-1≡1 : ℕtoF 1 ≡ Field.one field')
        (ℕtoF-0≡0 : ℕtoF 0 ≡ Field.zero field') (prime : ℕ) (isPrime : Prime prime)
        (onef≠zerof : ¬ Field.one field' ≡ Field.zero field') where

open import Language.Source f finite showf
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
open import Compile.SourceIntermediate f field' finite showf fToℕ ℕtoF hiding (SI-Monad)
import Compile.SourceIntermediate
open Compile.SourceIntermediate.SI-Monad f field' finite showf fToℕ ℕtoF


open import Satisfiability.SourceIntermediate.Base f _≟F_ field' isField finite showf fToℕ ℕtoF ℕtoF-1≡1 ℕtoF-0≡0 prime isPrime
open import Satisfiability.SourceIntermediate.LogicGates f _≟F_ field' isField finite showf fToℕ ℕtoF ℕtoF-1≡1 ℕtoF-0≡0 prime isPrime

varEqBaseLitFunc : ℕ → f → ℕ
varEqBaseLitFunc v l with ℕtoF v ≟F l
varEqBaseLitFunc v l | yes p = 1
varEqBaseLitFunc v l | no ¬p = 0

varEqBaseLitSound : ∀ (r : WriterMode)
  → (v : Var) → (val : ℕ) → (l : f)
  → (sol : List (Var × ℕ))
  → ListLookup v sol val
  → ∀ (init : ℕ) →
  let result = varEqBaseLit v l ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol (varEqBaseLitFunc val l)
varEqBaseLitSound r v val l sol look₁ init isSol
   with let
             n-l = output (new ((r , prime) , init))
             p₁₂ = new >>= λ n-l → add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ []))
             p₁₃ = new >>= λ n-l → add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ [])) >>= λ _ → neqz n-l
             ¬r = output (p₁₃ ((r , prime) , init))
             p₂₂ = add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ []))

             p₂₅ = λ n-l → add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ [])) >>= λ _ → neqz n-l >>= λ ¬r → lnot ¬r >>= λ r → return r
             p₃₃ = neqz n-l
             p₃₅ : ⊤ → SI-Monad Var
             p₃₅ = λ _ → let n-l = output (new ((r , prime) , init))
                         in neqz n-l >>= λ ¬r → lnot ¬r >>= λ r → return r
             p₄₅ = λ ¬r → lnot ¬r >>= λ r → return r
             p₂₅IsSol = BuilderProdSol->>=⁻₂ new p₂₅ r init sol isSol
             p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₅ r _ sol p₂₅IsSol
         in addSound r (IAdd (-F l) ((onef , v) ∷ (-F onef , init) ∷ [])) sol _ p₂₂IsSol
varEqBaseLitSound r v val l sol look₁ init isSol | addSol (LinearCombValCons .(Field.one field') .v varVal x (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₁ x₂ LinearCombValBase)) x₁
    with ListLookup-≈ x look₁
... | sq eq₁ rewrite eq₁
    with let
             n-l = output (new ((r , prime) , init))
             p₁₂ = new >>= λ n-l → add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ []))
             p₁₃ = new >>= λ n-l → add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ [])) >>= λ _ → neqz n-l
             ¬r = output (p₁₃ ((r , prime) , init))
             p₂₂ = add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ []))

             p₂₅ = λ n-l → add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ [])) >>= λ _ → neqz n-l >>= λ ¬r → lnot ¬r >>= λ r → return r
             p₃₃ = neqz n-l
             p₃₅ : ⊤ → SI-Monad Var
             p₃₅ = λ _ → let n-l = output (new ((r , prime) , init))
                         in neqz n-l >>= λ ¬r → lnot ¬r >>= λ r → return r
             p₄₅ = λ ¬r → lnot ¬r >>= λ r → return r
             p₂₅IsSol = BuilderProdSol->>=⁻₂ new p₂₅ r init sol isSol
             p₃₅IsSol = BuilderProdSol->>=⁻₂
                          p₂₂ p₃₅ r _ sol p₂₅IsSol
             p₃₃IsSol = BuilderProdSol->>=⁻₁
                          p₃₃ p₄₅ r _ sol p₃₅IsSol
         in neqzSound r init varVal₁ sol x₂ (varOut (p₁₂ ((r , prime) , init))) p₃₃IsSol
... | sound₂ with {- sound₂ : ListLookup ¬r sol (neqzFunc varVal₁ -}
         let p = new >>= λ n-l → add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ [])) >>= λ _ → (neqz n-l)
             n-l = output (new ((r , prime) , init))
             p₁₂ = new >>= λ n-l → add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ []))
             p₁₃ = new >>= λ n-l → add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ [])) >>= λ _ → neqz n-l
             p₁₄ = new >>= λ n-l → add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ [])) >>= λ _ → neqz n-l >>= λ ¬r → lnot ¬r
             ¬r = output (p₁₃ ((r , prime) , init))
             r' = output (p₁₄ ((r , prime) , init))
             p₂₂ = add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ []))

             p₂₅ = λ n-l → add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ [])) >>= λ _ → neqz n-l >>= λ ¬r → lnot ¬r >>= λ r → return r
             p₃₃ = neqz n-l
             p₃₅ : ⊤ → SI-Monad Var
             p₃₅ = λ _ → let n-l = output (new ((r , prime) , init))
                         in neqz n-l >>= λ ¬r → lnot ¬r >>= λ r → return r
             p₄₄ = lnot ¬r
             p₅₅ = λ r → return r
             p₄₅ = λ ¬r → lnot ¬r >>= λ r → return r
             p₂₅IsSol = BuilderProdSol->>=⁻₂ new p₂₅ r init sol isSol
             p₃₅IsSol = BuilderProdSol->>=⁻₂
                          p₂₂ p₃₅ r _ sol p₂₅IsSol
             p₄₅IsSol = BuilderProdSol->>=⁻₂
                          p₃₃ p₄₅ r _ sol p₃₅IsSol
             p₄₄IsSol = BuilderProdSol->>=⁻₁
                          p₄₄ p₅₅ r _ sol p₄₅IsSol
         in lnotSound r _ _ sol sound₂ (neqzFuncIsBool varVal₁) (varOut (p ((r , prime) , init))) p₄₄IsSol
... | sound₃ {- sound₃ : ListLookup `r` sol (notFunc (neqzFunc varVal₁)) -}
           rewrite *-identityˡ (ℕtoF val)
                   | -one*f≡-f (ℕtoF varVal₁)
                   | +-identityʳ (-F ℕtoF varVal₁) = ListLookup-Respects-≈ _ _ _ _ lem sound₃
        where
          lem : notFunc (neqzFunc varVal₁) ≈ varEqBaseLitFunc val l
          lem with ℕtoF varVal₁ ≟F zerof
          lem | yes p with ℕtoF 0 ≟F zerof
          lem | yes p | yes p₁ with ℕtoF val ≟F l
          lem | yes p | yes p₁ | yes p₂ = sq refl
          lem | yes p | yes p₁ | no ¬p rewrite p | -zero≡zero
                                             | +-identityʳ (ℕtoF val) = ⊥-elim′ (¬p (a-b≡zero→a≡b x₁))
          lem | yes p | no ¬p = ⊥-elim′ (¬p ℕtoF-0≡0)
          lem | no ¬p with ℕtoF 1 ≟F zerof
          lem | no ¬p | yes p = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) p))
          lem | no ¬p | no ¬p₁ with ℕtoF val ≟F l
          lem | no ¬p | no ¬p₁ | yes p rewrite p | +-comm l (-F ℕtoF varVal₁)
                                             | +-assoc (-F ℕtoF varVal₁) l (-F l)
                                             | +-invʳ l | +-identityʳ (-F ℕtoF varVal₁)
                                             = ⊥-elim′ (¬p (-≡zero→≡zero x₁))
          lem | no ¬p | no ¬p₁ | no ¬p₂ = sq refl
{-
init varVal₁[x₂]
v    varVal[x] val[look₁]

-}

anyNeqzFunc : ∀ {n} → Vec ℕ n → ℕ
anyNeqzFunc [] = 0
anyNeqzFunc (x ∷ vec) with ℕtoF x ≟F zerof
anyNeqzFunc (x ∷ vec) | yes p = anyNeqzFunc vec
anyNeqzFunc (x ∷ vec) | no ¬p = 1

anyNeqzFuncIsBool : ∀ {n} (vec : Vec ℕ n) → isBool (anyNeqzFunc vec)
anyNeqzFuncIsBool [] = isZero zero ℕtoF-0≡0
anyNeqzFuncIsBool (x ∷ vec) with ℕtoF x ≟F zerof
anyNeqzFuncIsBool (x ∷ vec) | yes p = anyNeqzFuncIsBool vec
anyNeqzFuncIsBool (x ∷ vec) | no ¬p = isOne 1 ℕtoF-1≡1

anyNeqzSound : ∀ (r : WriterMode)
  → ∀ {n}
  → (vec : Vec Var n) → (valVec : Vec ℕ n)
  → (sol : List (Var × ℕ))
  → BatchListLookup vec sol valVec
  → ∀ (init : ℕ) →
  let result = anyNeqz vec ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol (anyNeqzFunc valVec)
anyNeqzSound r .[] .[] sol (BatchLookupNil .sol) init isSol with addSound r (IAdd zerof ((onef , init) ∷ [])) sol (suc init) isSol
anyNeqzSound r .[] .[] sol (BatchLookupNil .sol) init isSol | addSol (LinearCombValCons .(Field.one field') .init varVal x LinearCombValBase) x₁
  rewrite *-identityˡ (ℕtoF varVal)
        | +-identityʳ (ℕtoF varVal)
        | +-identityˡ (ℕtoF varVal)
        | +-identityʳ (ℕtoF varVal) = ListLookup-Respects-≈ _ _ _ _ (sq (trans x₁ (sym ℕtoF-0≡0))) x
anyNeqzSound r .(v ∷ vec₁) .(n ∷ vec₂) sol (BatchLookupCons v n vec₁ vec₂ .sol x look₁) init isSol
   with let
            p₂₃ : Var → SI-Monad Var
            p₂₃ = λ r → anyNeqz vec₁ >>= λ rs → lor r rs
            p₁₁ = neqz v
        in neqzSound r v n sol x init (BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r init sol isSol)
... | sound₁
   with let
            input = ((r , prime) , init)
            p₁₁ = neqz v
            p₂₂ = anyNeqz vec₁
            p₂₃ : Var → SI-Monad Var
            p₂₃ = λ r → anyNeqz vec₁ >>= λ rs → lor r rs
            r' = output (p₁₁ input)
            p₃₃ = λ rs → lor r' rs
            p₁₁VarOut = varOut (p₁₁ input)
            p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r init sol isSol
            p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r _ sol p₂₃IsSol
        in anyNeqzSound r vec₁ vec₂ sol look₁ p₁₁VarOut p₂₂IsSol
... | sound₂
    with  let
            input = ((r , prime) , init)
            p₁₁ = neqz v
            p₁₂ = neqz v >>= λ r → anyNeqz vec₁
            p₂₂ = anyNeqz vec₁
            p₂₃ : Var → SI-Monad Var
            p₂₃ = λ r → anyNeqz vec₁ >>= λ rs → lor r rs
            r' = output (p₁₁ input)
            p₃₃ = λ rs → lor r' rs
            p₁₁VarOut = varOut (p₁₁ input)
            p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r init sol isSol
            p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r _ sol p₂₃IsSol
            p₃₃IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₃ r _ sol p₂₃IsSol
            p₁₂Output = output (p₁₂ input)
            
          in lorSound r r' p₁₂Output (neqzFunc n) (anyNeqzFunc vec₂) sol sound₁ sound₂ (neqzFuncIsBool n) (anyNeqzFuncIsBool vec₂) _ p₃₃IsSol
... | sound₃ = ListLookup-Respects-≈ _ _ _ _ lem sound₃
   where
     lem : lorFunc (neqzFunc n) (anyNeqzFunc vec₂) ≈ anyNeqzFunc (n ∷ vec₂)
     lem with ℕtoF n ≟F zerof
     lem | yes p with ℕtoF 0 ≟F zerof
     lem | yes p | yes p₁ with ℕtoF (anyNeqzFunc vec₂) ≟F zerof
     lem | yes p | yes p₁ | yes p₂ = sq (sym (trans p₂ (sym p₁)))
     lem | yes p | yes p₁ | no ¬p with anyNeqzFuncIsBool vec₂
     lem | yes p | yes p₁ | no ¬p | isZero .(anyNeqzFunc vec₂) x = ⊥-elim′ (¬p x)
     lem | yes p | yes p₁ | no ¬p | isOne .(anyNeqzFunc vec₂) x = sq (sym (trans x (sym ℕtoF-1≡1)))
     lem | yes p | no ¬p = ⊥-elim′ (¬p ℕtoF-0≡0)
     lem | no ¬p with ℕtoF 1 ≟F zerof
     lem | no ¬p | yes p = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) p))
     lem | no ¬p | no ¬p₁ = sq refl


allEqzFunc : ∀ {n} → Vec ℕ n → ℕ
allEqzFunc [] = 1
allEqzFunc (x ∷ vec) with ℕtoF x ≟F zerof
allEqzFunc (x ∷ vec) | yes p = allEqzFunc vec
allEqzFunc (x ∷ vec) | no ¬p = 0


allEqzFuncIsBool : ∀ {n} (vec : Vec ℕ n) → isBool (allEqzFunc vec)
allEqzFuncIsBool [] = isOne 1 ℕtoF-1≡1
allEqzFuncIsBool (x ∷ vec) with ℕtoF x ≟F zerof
allEqzFuncIsBool (x ∷ vec) | yes p = allEqzFuncIsBool vec
allEqzFuncIsBool (x ∷ vec) | no ¬p = isZero zero ℕtoF-0≡0



allEqzSoundLem : ∀ {n} (vec : Vec ℕ n) → notFunc (anyNeqzFunc vec) ≈ allEqzFunc vec
allEqzSoundLem [] with ℕtoF 0 ≟F zerof
allEqzSoundLem [] | yes p = sq refl
allEqzSoundLem [] | no ¬p = ⊥-elim′ (¬p ℕtoF-0≡0)
allEqzSoundLem (x ∷ vec) with ℕtoF x ≟F zerof
allEqzSoundLem (x ∷ vec) | yes p = allEqzSoundLem vec
allEqzSoundLem (x ∷ vec) | no ¬p with ℕtoF 1 ≟F zerof
allEqzSoundLem (x ∷ vec) | no ¬p | yes p = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) p))
allEqzSoundLem (x ∷ vec) | no ¬p | no ¬p₁ = sq refl

allEqzSound : ∀ (r : WriterMode)
  → ∀ {n}
  → (vec : Vec Var n) → (valVec : Vec ℕ n)
  → (sol : List (Var × ℕ))
  → BatchListLookup vec sol valVec
  → ∀ (init : ℕ) →
  let result = allEqz vec ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol (allEqzFunc valVec)
allEqzSound r vec val sol look init isSol =
  let
    input = ((r , prime) , init)
    p₁₁ = anyNeqz vec
    p₂₃ = λ ¬r → lnot ¬r >>= λ r → return r
    p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
    p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol
    sound₁ = anyNeqzSound r vec val sol look init p₁₁IsSol
    sound₂ = lnotSound r (output (p₁₁ input)) (anyNeqzFunc val) sol sound₁ (anyNeqzFuncIsBool val) _ p₂₃IsSol
  in ListLookup-Respects-≈ _ _ _ _ (allEqzSoundLem val) sound₂

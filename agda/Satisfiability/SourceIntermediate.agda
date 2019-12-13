{-# OPTIONS --prop #-}
open import Data.Empty
open import Data.Field
open import Data.Finite
open import Data.List hiding (lookup; head)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Primality


open import Data.Product hiding (map)
open import Data.ProductPrime
open import Data.Vec hiding (_>>=_; _++_)
open import Data.Squash
open import Data.String hiding (_≈_; _≟_; _++_)
open import Data.Sum
open import Data.Unit
open import Function

open import Language.Common

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
module Satisfiability.SourceIntermediate (f : Set) (_≟F_ : Decidable {A = f} _≡_) (field' : Field f) (isField : IsField f field')
     (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f)
        (ℕtoF-1≡1 : ℕtoF 1 ≡ Field.one field')
        (ℕtoF-0≡0 : ℕtoF 0 ≡ Field.zero field') (prime : ℕ) (isPrime : Prime prime)
        (onef≠zerof : ¬ Field.one field' ≡ Field.zero field') where

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
  → (solution' : List (Var × ℕ))
  → ListLookup v solution' val
  → ∀ (init : ℕ) →
  let result = varEqBaseLit v l ((r , prime) , init)
  in BuilderProdSol (writerOutput result) solution'
  → ListLookup (output result) solution' (varEqBaseLitFunc val l)
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
varEqBaseLitSound r v val l sol look₁ init isSol | addSol ._ .((onef , v) ∷ ((Field.- field') (Field.one field') , init) ∷ []) .((field' Field.+ (field' Field.* Field.one field') (ℕtoF varVal)) ((field' Field.+ (field' Field.* (Field.- field') (Field.one field')) (ℕtoF varVal₁)) (Field.zero field'))) (LinearCombValCons .(Field.one field') .v varVal .(((Field.- field') (Field.one field') , init) ∷ []) .((field' Field.+ (field' Field.* (Field.- field') (Field.one field')) (ℕtoF varVal₁)) (Field.zero field')) x (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₁ .[] .(Field.zero field') x₂ LinearCombValBase)) x₁
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

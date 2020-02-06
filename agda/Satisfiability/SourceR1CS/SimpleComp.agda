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
open import Data.Vec.AllProp
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
module Satisfiability.SourceR1CS.SimpleComp (f : Set) (_≟F_ : Decidable {A = f} _≡_) (field' : Field f) (isField : IsField f field')
     (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f)
        (ℕtoF-1≡1 : ℕtoF 1 ≡ Field.one field')
        (ℕtoF-0≡0 : ℕtoF 0 ≡ Field.zero field')
        (ℕtoF∘fToℕ≡ : ∀ x → ℕtoF (fToℕ x) ≡ x)
        (prime : ℕ) (isPrime : Prime prime)
        (onef≠zerof : ¬ Field.one field' ≡ Field.zero field') where

open import Language.Source f finite showf
open import Language.TySize f finite
open import Language.Universe f
open import Language.R1CS f


open Field field' renaming ( _+_ to _+F_
                           ; _*_ to _*F_
                           ; -_ to -F_
                           ; 1/_ to 1F/_
                           ; zero to zerof
                           ; one to onef)
open IsField isField
open import Compile.SourceR1CS f field' finite showf fToℕ ℕtoF hiding (SI-Monad)
import Compile.SourceR1CS
open Compile.SourceR1CS.SI-Monad f field' finite showf fToℕ ℕtoF


open import Satisfiability.SourceR1CS.Base f _≟F_ field' isField finite showf fToℕ ℕtoF ℕtoF-1≡1 ℕtoF-0≡0 prime isPrime
open import Satisfiability.SourceR1CS.LogicGates f _≟F_ field' isField finite showf fToℕ ℕtoF ℕtoF-1≡1 ℕtoF-0≡0 ℕtoF∘fToℕ≡ prime isPrime onef≠zerof

varEqBaseLitFunc : ℕ → f → ℕ
varEqBaseLitFunc v l with ℕtoF v ≟F l
varEqBaseLitFunc v l | yes p = 1
varEqBaseLitFunc v l | no ¬p = 0

varEqBaseLitIsBool : ∀ r (v : Var) (l : f)
   → ∀ sol init →
   let result = varEqBaseLit v l ((r , prime) , init)
   in BuilderProdSol (writerOutput result) sol
   → Squash (∃ (λ val → Σ′ (isBool val) (λ _ → ListLookup (output result) sol val)))
varEqBaseLitIsBool r v l sol init isSol
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
         in neqzIsBool r _ _ _ p₃₃IsSol
... | sq (¬rVal , ¬rValIsBool , ¬rValLook) =
         let
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
             p₄₅IsSol = BuilderProdSol->>=⁻₂
                          p₃₃ p₄₅ r _ sol p₃₅IsSol
         in sq (_ , lnotFuncIsBool ¬rVal , lnotSound r _ _ _ ¬rValLook ¬rValIsBool _ p₄₅IsSol)


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
          lem : lnotFunc (neqzFunc varVal₁) ≈ varEqBaseLitFunc val l
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

anyNeqzFuncIsBoolStrict : ∀ {n} (vec : Vec ℕ n) → isBoolStrict (anyNeqzFunc vec)
anyNeqzFuncIsBoolStrict [] = isZeroS refl
anyNeqzFuncIsBoolStrict (x ∷ vec) with ℕtoF x ≟F zerof
anyNeqzFuncIsBoolStrict (x ∷ vec) | yes p = anyNeqzFuncIsBoolStrict vec
anyNeqzFuncIsBoolStrict (x ∷ vec) | no ¬p = isOneS refl


anyNeqzIsBool : ∀ r {n} (vec : Vec Var n) sol init
  → let result = anyNeqz vec ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → Squash (∃ (λ val → Σ′ (isBool val) (λ _ → ListLookup (output result) sol val)))
anyNeqzIsBool r [] sol init isSol with addSound r (IAdd zerof ((onef , init) ∷ [])) sol _ isSol
anyNeqzIsBool r [] sol init isSol | addSol (LinearCombValCons .(Field.one field') .init varVal x LinearCombValBase) x₁
    rewrite *-identityˡ (ℕtoF varVal)
          | +-identityʳ (ℕtoF varVal)
          | +-identityʳ (ℕtoF varVal) = sq (varVal , ((isZero _ x₁) , x))
anyNeqzIsBool r (x ∷ vec) sol init isSol
    with let p₁₁ = neqz x
             p₂₃ = λ r → do
               rs ← anyNeqz vec
               lor r rs
             p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
         in neqzIsBool r x sol init p₁₁IsSol
... | sq (val₁ , isBool₁ , look₁)
    with let input = ((r , prime) , init)
             p₁₁ = neqz x
             p₂₂ = anyNeqz vec
             p₂₃ = λ r → do
               rs ← anyNeqz vec
               lor r rs
             r' = output (p₁₁ input)
             p₃₃ = λ rs → do
               lor r' rs
             p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol
             p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r _ sol p₂₃IsSol
         in anyNeqzIsBool r vec sol _ p₂₂IsSol
... | sq (val₂ , isBool₂ , look₂)
    with let input = ((r , prime) , init)
             p₁₁ = neqz x
             p₂₂ = anyNeqz vec
             p₂₃ = λ r → do
               rs ← anyNeqz vec
               lor r rs
             r' = output (p₁₁ input)
             p₃₃ = λ rs → do
               lor r' rs
             p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol
             p₃₃IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₃ r _ sol p₂₃IsSol
         in lorSound r _ _ _ _ _ look₁ look₂ isBool₁ isBool₂ _ p₃₃IsSol
... | sound₁ = sq ((lorFunc val₁ val₂) , ((orFuncIsBool val₁ val₂) , sound₁))

anyNeqzSound₀ : ∀ (r : WriterMode)
  → ∀ {n} → (vec : Vec Var n)
  → (sol : List (Var × ℕ))
  → ListLookup 0 sol 1
  → ∀ init →
  let result = anyNeqz vec ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol 0
  → Squash (∃ (λ val → (Σ′′ (BatchListLookup vec sol val) (λ _ → All (_≈_ 0) val))))
anyNeqzSound₀ r [] sol tri init isSol look = sq ([] , BatchLookupNil sol , [])
anyNeqzSound₀ r (x ∷ vec) sol tri init isSol look
    with let p₁₁ = neqz x
             p₂₃ = λ r → do
               rs ← anyNeqz vec
               lor r rs
             p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
         in neqzIsBool r x sol init p₁₁IsSol
... | sq (val₁ , isBool₁ , look₁)
    with let p₁₁ = neqz x
             p₂₂ = anyNeqz vec
             p₂₃ = λ r → do
               rs ← anyNeqz vec
               lor r rs
             r' = output (p₁₁ ((r , prime) , init))
             p₃₃ = λ rs → lor r' rs
             p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol
             p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r _ sol p₂₃IsSol
         in anyNeqzIsBool r vec sol _ p₂₂IsSol
... | sq (val₂ , isBool₂ , look₂)
    with let p₁₁ = neqz x
             p₂₂ = anyNeqz vec
             p₂₃ = λ r → do
               rs ← anyNeqz vec
               lor r rs
             r' = output (p₁₁ ((r , prime) , init))
             p₃₃ = λ rs → lor r' rs
             p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol
             p₃₃IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₃ r _ sol p₂₃IsSol
         in lorSound₀ r _ _ _ _ sol _ look₁ look₂ isBool₁ isBool₂ p₃₃IsSol look
... | sq (isZ₁ , isZ₂)
    with let p₁₁ = neqz x
             p₂₃ = λ r → do
               rs ← anyNeqz vec
               lor r rs
             p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
         in neqzSound₀ r x sol tri init p₁₁IsSol isZ₁
... | sq (val₁' , look₁' , eq₀)
    with let p₁₁ = neqz x
             p₂₂ = anyNeqz vec
             p₂₃ = λ r → do
               rs ← anyNeqz vec
               lor r rs
             r' = output (p₁₁ ((r , prime) , init))
             p₃₃ = λ rs → lor r' rs
             p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol
             p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r _ sol p₂₃IsSol
         in anyNeqzSound₀ r vec sol tri _ p₂₂IsSol isZ₂
... | sq (val₂' , look₂' , eq₁)
    =  sq ((val₁' ∷ val₂') , (BatchLookupCons _ _ _ _ _ look₁' look₂' , eq₀ ∷ eq₁))


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

allEqzIsBool : ∀ (r : WriterMode)
  → ∀ {n} → (vec : Vec Var n)
  → (sol : List (Var × ℕ))
  → ListLookup 0 sol 1
  → ∀ init →
  let result = allEqz vec ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → Squash (∃ (λ val → Σ′ (isBool val) (λ _ → ListLookup (output result) sol val)))
allEqzIsBool r vec sol tri init isSol
    with
  let
    p₁₁ = anyNeqz vec
    p₂₃ = λ ¬r → lnot ¬r >>= λ r → return r
    p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
    p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol
  in anyNeqzIsBool r vec sol init p₁₁IsSol
... | sq (¬rVal , ¬rValIsBool , ¬rValLook)
    with
  let
    p₁₁ = anyNeqz vec
    p₂₃ = λ ¬r → lnot ¬r >>= λ r → return r
    p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
    p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol
  in lnotSound r _ _ _ ¬rValLook ¬rValIsBool _ p₂₃IsSol
... | look = sq (_ , ((lnotFuncIsBool ¬rVal) , look))


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

allEqzFuncIsBoolStrict : ∀ {n} (vec : Vec ℕ n) → isBoolStrict (allEqzFunc vec)
allEqzFuncIsBoolStrict [] = isOneS refl
allEqzFuncIsBoolStrict (x ∷ vec) with ℕtoF x ≟F zerof
allEqzFuncIsBoolStrict (x ∷ vec) | yes p = allEqzFuncIsBoolStrict vec
allEqzFuncIsBoolStrict (x ∷ vec) | no ¬p = isZeroS refl


allEqzSoundLem : ∀ {n} (vec : Vec ℕ n) → lnotFunc (anyNeqzFunc vec) ≈ allEqzFunc vec
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




piVarEqLitFunc : ∀ {u} (x : ⟦ u ⟧ → U) → (eu : List ⟦ u ⟧)
  → (vec : Vec ℕ (tySumOver eu x))
  → ⟦ `Π u x ⟧ → ℕ
varEqLitFunc : ∀ u → Vec ℕ (tySize u) → ⟦ u ⟧ → ℕ
varEqLitFunc `One (x ∷ vec) lit with ℕtoF x ≟F zerof
varEqLitFunc `One (x ∷ vec) lit | yes p = 1
varEqLitFunc `One (x ∷ vec) lit | no ¬p = 0
varEqLitFunc `Two (x ∷ vec) false with ℕtoF x ≟F zerof
varEqLitFunc `Two (x ∷ vec) false | yes p = 1
varEqLitFunc `Two (x ∷ vec) false | no ¬p = 0
varEqLitFunc `Two (x ∷ vec) true  with ℕtoF x ≟F onef
varEqLitFunc `Two (x ∷ vec) true | yes p = 1
varEqLitFunc `Two (x ∷ vec) true | no ¬p = 0
varEqLitFunc `Base (x ∷ vec) lit with ℕtoF x ≟F lit
varEqLitFunc `Base (x ∷ vec) lit | yes p = 1
varEqLitFunc `Base (x ∷ vec) lit | no ¬p = 0
varEqLitFunc (`Vec u zero) vec lit = 1
varEqLitFunc (`Vec u (suc x)) vec (l ∷ lit) with splitAt (tySize u) vec
... | fst , snd = landFunc (varEqLitFunc u fst l) (varEqLitFunc (`Vec u x) snd lit)
varEqLitFunc (`Σ u x) vec (fstₗ , sndₗ) with splitAt (tySize u) vec
... | fst , snd with maxTySplit u fstₗ x snd
... | vecₜ₁ , vecₜ₂ = landFunc (landFunc (varEqLitFunc u fst fstₗ) (varEqLitFunc (x fstₗ) vecₜ₁ sndₗ)) (allEqzFunc vecₜ₂)
varEqLitFunc (`Π u x) vec lit = piVarEqLitFunc x (enum u) vec lit 

piVarEqLitFunc x [] vec pi = 1
piVarEqLitFunc x (x₁ ∷ eu) vec pi with splitAt (tySize (x x₁)) vec
... | fst , snd = landFunc (varEqLitFunc (x x₁) fst (pi x₁)) (piVarEqLitFunc x eu snd pi)


varEqLitFuncIsBoolStrict : ∀ u vec v → isBoolStrict (varEqLitFunc u vec v)
piVarEqLitFuncIsBoolStrict : ∀ {u} (x : ⟦ u ⟧ → U) eu vec pi → isBoolStrict (piVarEqLitFunc x eu vec pi)


varEqLitFuncIsBoolStrict `One (x ∷ vec) v with ℕtoF x ≟F zerof
varEqLitFuncIsBoolStrict `One (x ∷ vec) v | yes p = isOneS refl
varEqLitFuncIsBoolStrict `One (x ∷ vec) v | no ¬p = isZeroS refl
varEqLitFuncIsBoolStrict `Two (x ∷ vec) false with ℕtoF x ≟F zerof
varEqLitFuncIsBoolStrict `Two (x ∷ vec) false | yes p = isOneS refl
varEqLitFuncIsBoolStrict `Two (x ∷ vec) false | no ¬p = isZeroS refl
varEqLitFuncIsBoolStrict `Two (x ∷ vec) true with ℕtoF x ≟F onef
varEqLitFuncIsBoolStrict `Two (x ∷ vec) true | yes p = isOneS refl
varEqLitFuncIsBoolStrict `Two (x ∷ vec) true | no ¬p = isZeroS refl
varEqLitFuncIsBoolStrict `Base (x ∷ vec) v with ℕtoF x ≟F v
varEqLitFuncIsBoolStrict `Base (x ∷ vec) v | yes p = isOneS refl
varEqLitFuncIsBoolStrict `Base (x ∷ vec) v | no ¬p = isZeroS refl
varEqLitFuncIsBoolStrict (`Vec u zero) vec v = isOneS refl
varEqLitFuncIsBoolStrict (`Vec u (suc x)) vec (l ∷ lit) with splitAt (tySize u) vec
... | fst , snd = landFuncIsBoolStrict (varEqLitFunc u fst l) (varEqLitFunc (`Vec u x) snd lit)
varEqLitFuncIsBoolStrict (`Σ u x) vec (fstₗ , sndₗ) with splitAt (tySize u) vec
... | fst , snd with maxTySplit u fstₗ x snd
... | vecₜ₁ , vecₜ₂ = landFuncIsBoolStrict (landFunc (varEqLitFunc u fst fstₗ) (varEqLitFunc (x fstₗ) vecₜ₁ sndₗ)) (allEqzFunc vecₜ₂)
varEqLitFuncIsBoolStrict (`Π u x) vec v = piVarEqLitFuncIsBoolStrict x (enum u) vec v


piVarEqLitFuncIsBoolStrict x [] vec pi = isOneS refl
piVarEqLitFuncIsBoolStrict x (x₁ ∷ eu) vec pi with splitAt (tySize (x x₁)) vec
... | fst , snd = landFuncIsBoolStrict (varEqLitFunc (x x₁) fst (pi x₁)) (piVarEqLitFunc x eu snd pi)


varEqLitFuncIsBool : ∀ u vec v → isBool (varEqLitFunc u vec v)
piVarEqLitFuncIsBool : ∀ {u} (x : ⟦ u ⟧ → U) eu vec pi → isBool (piVarEqLitFunc x eu vec pi)



piVarEqLitFuncIsBool x [] vec pi = isOne 1 ℕtoF-1≡1
piVarEqLitFuncIsBool x (x₁ ∷ eu) vec pi with splitAt (tySize (x x₁)) vec
... | fst , snd = landFuncIsBool (varEqLitFunc (x x₁) fst (pi x₁)) (piVarEqLitFunc x eu snd pi)


varEqLitFuncIsBool `One (x ∷ vec) v with ℕtoF x ≟F zerof
varEqLitFuncIsBool `One (x ∷ vec) v | yes p = isOne 1 ℕtoF-1≡1
varEqLitFuncIsBool `One (x ∷ vec) v | no ¬p = isZero zero ℕtoF-0≡0
varEqLitFuncIsBool `Two (x ∷ vec) false with ℕtoF x ≟F zerof
varEqLitFuncIsBool `Two (x ∷ vec) false | yes p = isOne 1 ℕtoF-1≡1
varEqLitFuncIsBool `Two (x ∷ vec) false | no ¬p = isZero zero ℕtoF-0≡0
varEqLitFuncIsBool `Two (x ∷ vec) true with ℕtoF x ≟F onef
varEqLitFuncIsBool `Two (x ∷ vec) true | yes p = isOne 1 ℕtoF-1≡1
varEqLitFuncIsBool `Two (x ∷ vec) true | no ¬p = isZero zero ℕtoF-0≡0
varEqLitFuncIsBool `Base (x ∷ vec) v with ℕtoF x ≟F v
varEqLitFuncIsBool `Base (x ∷ vec) v | yes p = isOne 1 ℕtoF-1≡1
varEqLitFuncIsBool `Base (x ∷ vec) v | no ¬p = isZero zero ℕtoF-0≡0
varEqLitFuncIsBool (`Vec u zero) vec v = isOne 1 ℕtoF-1≡1
varEqLitFuncIsBool (`Vec u (suc x)) vec (l ∷ lit) with splitAt (tySize u) vec
... | fst , snd = landFuncIsBool (varEqLitFunc u fst l) (varEqLitFunc (`Vec u x) snd lit)
varEqLitFuncIsBool (`Σ u x) vec (fstₗ , sndₗ) with splitAt (tySize u) vec
... | fst , snd with maxTySplit u fstₗ x snd
... | vecₜ₁ , vecₜ₂ = landFuncIsBool (landFunc (varEqLitFunc u fst fstₗ) (varEqLitFunc (x fstₗ) vecₜ₁ sndₗ)) (allEqzFunc vecₜ₂)
varEqLitFuncIsBool (`Π u x) vec v = piVarEqLitFuncIsBool x (enum u) vec v


varEqLitSound : ∀ (r : WriterMode)
  → ∀ u → (vec : Vec Var (tySize u))
  → (val : Vec Var (tySize u))
  → (l : ⟦ u ⟧)
  → (sol : List (Var × ℕ))
  → BatchListLookup vec sol val
  → ListLookup 0 sol 1
  → ∀ (init : ℕ) →
  let result = varEqLit u vec l ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol (varEqLitFunc u val l)

piVarEqLitSound : ∀ (r : WriterMode)
  → ∀ u (x : ⟦ u ⟧ → U) (eu : List ⟦ u ⟧)
  → (vec : Vec Var (tySumOver eu x))
  → (val : Vec ℕ (tySumOver eu x))
  → (pi : ⟦ `Π u x ⟧)
  → (sol : List (Var × ℕ))
  → BatchListLookup vec sol val
  → ListLookup 0 sol 1
  → ∀ (init : ℕ) →
  let result = piVarEqLit u x eu vec pi ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol (piVarEqLitFunc x eu val pi)
varEqLitSound r `One vec val l sol look tri init isSol
  = let sound₁ = allEqzSound r vec val sol look init isSol
    in ListLookup-Respects-≈  _ _ _ _ (lem val l) sound₁
  where
    lem : ∀ val l → allEqzFunc val ≈ varEqLitFunc `One val l
    lem (x ∷ val) l with ℕtoF x ≟F zerof
    lem (x ∷ []) l | yes p = sq refl
    lem (x ∷ val) l | no ¬p = sq refl
varEqLitSound r `Two vec val false sol look tri init isSol
  = let sound₁ = allEqzSound r vec val sol look init isSol
    in ListLookup-Respects-≈ _ _ _ _ (lem val) sound₁
  where
    lem : ∀ val → allEqzFunc val ≈ varEqLitFunc `Two val false
    lem (x ∷ val) with ℕtoF x ≟F zerof
    lem (x ∷ []) | yes p = sq refl
    lem (x ∷ val) | no ¬p = sq refl
varEqLitSound r `Two (x ∷ vec) (val ∷ []) true sol (BatchLookupCons .x .val .vec .[] .sol x₁ look) tri init isSol
 =  let sound₁ = varEqBaseLitSound r x val onef sol x₁ init isSol
    in ListLookup-Respects-≈ _ _ _ _ lem sound₁
  where
    lem : varEqBaseLitFunc val onef ≈ varEqLitFunc `Two (val ∷ []) true
    lem with ℕtoF val ≟F onef
    lem | yes p = sq refl
    lem | no ¬p = sq refl
varEqLitSound r `Base (x ∷ []) (val ∷ []) l sol (BatchLookupCons .x .val .[] .[] .sol x₁ look) tri init isSol =
  let sound₁ = varEqBaseLitSound r x val l sol x₁ init isSol
  in ListLookup-Respects-≈ _ _ _ _ lem sound₁
 where
  lem : varEqBaseLitFunc val l ≈ varEqLitFunc `Base (val ∷ []) l
  lem with ℕtoF val ≟F l
  lem | yes p = sq refl
  lem | no ¬p = sq refl
varEqLitSound r (`Vec u zero) vec val l sol look tri init isSol = tri
varEqLitSound r (`Vec u (suc x)) vec val (l ∷ ls) sol look tri init isSol with splitAt (tySize u) vec | inspect (splitAt (tySize u)) vec
... | fst , snd   | [ prf ] with splitAt (tySize u) val | inspect (splitAt (tySize u)) val
... | fstv , sndv | [ prf₂ ] = let
                                   input = ((r , prime) , init)
                                   p₁₁ = varEqLit u fst l
                                   p₁₂ = varEqLit u fst l >>= λ r → varEqLit (`Vec u x) snd ls
                                   p₂₂ = varEqLit (`Vec u x) snd ls
                                   r' = output (p₁₁ input)
                                   p₃₃ = λ s → land r' s
                                   p₂₃ = λ r → varEqLit (`Vec u x) snd ls >>= λ s → land r s
                                   p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
                                   p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol
                                   p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r _ sol p₂₃IsSol
                                   p₃₃IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₃ r _ sol p₂₃IsSol
                                   sound₁ = varEqLitSound r u fst fstv l sol (BatchListLookup-Split₁ (tySize u) (tySize (`Vec u x)) vec sol val fst snd fstv sndv prf prf₂ look) tri init p₁₁IsSol
                                   sound₂ = varEqLitSound r (`Vec u x) snd sndv ls sol (BatchListLookup-Split₂ (tySize u) (tySize (`Vec u x)) vec sol val fst snd fstv sndv prf prf₂ look) tri (varOut (p₁₁ input)) p₂₂IsSol
                                   sound₃ = landSound r r' (output (p₁₂ input)) (varEqLitFunc u fstv l) (varEqLitFunc (`Vec u x) sndv ls) sol sound₁ sound₂ (varEqLitFuncIsBool u fstv l) (varEqLitFuncIsBool (`Vec u x) sndv ls) (varOut (p₁₂ input)) p₃₃IsSol
                               in sound₃
varEqLitSound r (`Σ u x) vec val (fstₗ , sndₗ) sol look tri init isSol with splitAt (tySize u) vec | inspect (splitAt (tySize u)) vec
... | fst , snd | [ prf ] with splitAt (tySize u) val | inspect (splitAt (tySize u)) val
... | fstv , sndv | [ prf₂ ] with maxTySplit u fstₗ x snd | inspect (maxTySplit u fstₗ x) snd
... | snd₁ , snd₂ | [ prf₃ ] with maxTySplit u fstₗ x sndv | inspect (maxTySplit u fstₗ x) sndv
... | sndv₁ , sndv₂ | [ prf₄ ] =
     let
       input = ((r , prime) , init)
       p₁₁ = varEqLit u fst fstₗ
       p₁₂ = varEqLit u fst fstₗ >>= λ r → varEqLit (x fstₗ) snd₁ sndₗ
       p₁₃ = do
         r ← varEqLit u fst fstₗ
         s ← varEqLit (x fstₗ) snd₁ sndₗ
         allEqz snd₂
       p₁₄ = do
         r ← varEqLit u fst fstₗ
         s ← varEqLit (x fstₗ) snd₁ sndₗ
         s' ← allEqz snd₂
         land r s
       p₂₂ = varEqLit (x fstₗ) snd₁ sndₗ
       p₂₅ = λ r → do
         s ← varEqLit (x fstₗ) snd₁ sndₗ
         s' ← allEqz snd₂
         and₁ ← land r s
         land and₁ s'
       r' = output (p₁₁ input)
       s = output (p₁₂ input)
       p₃₃ = allEqz snd₂
       p₃₅ = λ s → do
         s' ← allEqz snd₂
         and₁ ← land r' s
         land and₁ s'
       p₄₄ = land r' s
       p₄₅ = λ s' → do
         and₁ ← land r' s
         land and₁ s'
       s' = output (p₁₃ input)
       and₁ = output (p₁₄ input)
       p₅₅ = λ and₁ → land and₁ s'
       p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₅ r _ sol isSol
       p₂₅IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₅ r _ sol isSol
       p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₅ r _ sol p₂₅IsSol
       p₃₅IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₅ r _ sol p₂₅IsSol
       p₃₃IsSol = BuilderProdSol->>=⁻₁ p₃₃ p₄₅ r _ sol p₃₅IsSol
       p₄₅IsSol = BuilderProdSol->>=⁻₂ p₃₃ p₄₅ r _ sol p₃₅IsSol
       p₄₄IsSol = BuilderProdSol->>=⁻₁ p₄₄ p₅₅ r _ sol p₄₅IsSol
       p₅₅IsSol = BuilderProdSol->>=⁻₂ p₄₄ p₅₅ r _ sol p₄₅IsSol
       lookFst = BatchListLookup-Split₁ (tySize u) _ vec sol val fst snd fstv sndv prf prf₂ look
       lookSnd = BatchListLookup-Split₂ (tySize u) _ vec sol val fst snd fstv sndv prf prf₂ look
       lookSnd₁ = BatchListLookup-MaxTySplit₁ u fstₗ x sol snd snd₁ sndv sndv₁ (cong proj₁ prf₃) (cong proj₁ prf₄) lookSnd
       lookSnd₂ = BatchListLookup-MaxTySplit₂ u fstₗ x sol snd snd₂ sndv sndv₂ (cong proj₂ prf₃) (cong proj₂ prf₄) lookSnd
       sound₁ = varEqLitSound r u fst fstv fstₗ sol lookFst tri init p₁₁IsSol
       sound₂ = varEqLitSound r (x fstₗ) snd₁ sndv₁ sndₗ sol lookSnd₁ tri (varOut (p₁₁ input)) p₂₂IsSol
       sound₃ = allEqzSound r snd₂ sndv₂ sol lookSnd₂ _ p₃₃IsSol
       sound₄ = landSound r _ _ _ _ sol sound₁ sound₂ (varEqLitFuncIsBool u fstv fstₗ) (varEqLitFuncIsBool (x fstₗ) sndv₁ sndₗ) _ p₄₄IsSol
       sound₅ = landSound r _ _ _ _ sol sound₄ sound₃ (landFuncIsBool (varEqLitFunc u fstv fstₗ) (varEqLitFunc (x fstₗ) sndv₁ sndₗ)) (allEqzFuncIsBool sndv₂) _ p₅₅IsSol
    in sound₅

varEqLitSound r (`Π u x) vec val l sol look tri init isSol = piVarEqLitSound r u x (enum u) vec val l sol look tri init isSol

piVarEqLitSound r u x [] vec val pi sol look tri init isSol = tri
piVarEqLitSound r u x (x₁ ∷ eu) vec val pi sol look tri init isSol with splitAt (tySize (x x₁)) vec | inspect (splitAt (tySize (x x₁))) vec
... | fst , snd | [ prf₁ ] with splitAt (tySize (x x₁)) val | inspect (splitAt (tySize (x x₁))) val
... | fstv , sndv | [ prf₂ ] =
     let
       input = ((r , prime) , init)
       lookFst = BatchListLookup-Split₁ (tySize (x x₁)) _ vec sol val fst snd fstv sndv prf₁ prf₂ look
       lookSnd = BatchListLookup-Split₂ (tySize (x x₁)) _ vec sol val fst snd fstv sndv prf₁ prf₂ look
       p₁₁ = varEqLit (x x₁) fst (pi x₁)
       p₁₂ = varEqLit (x x₁) fst (pi x₁) >>= λ r → piVarEqLit u x eu snd pi
       p₂₂ = piVarEqLit u x eu snd pi
       r' = output (p₁₁ input)
       s = output (p₁₂ input)
       p₃₃ = λ s → land r' s 
       p₂₃ = λ r → piVarEqLit u x eu snd pi >>= λ s → land r s
       p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
       p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol
       p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r _ sol p₂₃IsSol
       p₃₃IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₃ r _ sol p₂₃IsSol
       sound₁ = varEqLitSound r (x x₁) fst fstv (pi x₁) sol lookFst tri init p₁₁IsSol
       sound₂ = piVarEqLitSound r u x eu snd sndv pi sol lookSnd tri (varOut (p₁₁ input)) p₂₂IsSol
       sound₃ = landSound r r' s (varEqLitFunc (x x₁) fstv (pi x₁)) (piVarEqLitFunc x eu sndv pi) sol sound₁ sound₂ (varEqLitFuncIsBool (x x₁) fstv (pi x₁)) (piVarEqLitFuncIsBool x eu sndv pi) (varOut (p₁₂ input)) p₃₃IsSol
     in sound₃

tyCondFunc : ∀ u → (vec : Vec ℕ (tySize u)) → ℕ
enumSigmaCondFunc : ∀ u → (eu : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U)
  → (val₁ : Vec ℕ (tySize u))
  → (val₂ : Vec ℕ (maxTySizeOver (enum u) x))
  → ℕ

enumPiCondFunc : ∀ u → (eu : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U) → Vec ℕ (tySumOver eu x) → ℕ
enumPiCondFunc u [] x vec = 1
enumPiCondFunc u (x₁ ∷ eu) x vec with splitAt (tySize (x x₁)) vec
enumPiCondFunc u (x₁ ∷ eu) x vec | fst₁ , snd₁ = landFunc (tyCondFunc (x x₁) fst₁) (enumPiCondFunc u eu x snd₁)

enumPiCondFuncIsBool : ∀ u eu x vec → isBool (enumPiCondFunc u eu x vec)
enumPiCondFuncIsBool u [] x vec = isOne 1 ℕtoF-1≡1
enumPiCondFuncIsBool u (x₁ ∷ eu) x vec with splitAt (tySize (x x₁)) vec
enumPiCondFuncIsBool u (x₁ ∷ eu) x vec | fst₁ , snd₁ = landFuncIsBool (tyCondFunc (x x₁) fst₁) (enumPiCondFunc u eu x snd₁)

enumPiCondFuncIsBoolStrict : ∀ u eu x vec → isBoolStrict (enumPiCondFunc u eu x vec)
enumPiCondFuncIsBoolStrict u [] x vec = isOneS refl
enumPiCondFuncIsBoolStrict u (x₁ ∷ eu) x vec with splitAt (tySize (x x₁)) vec
enumPiCondFuncIsBoolStrict u (x₁ ∷ eu) x vec | fst₁ , snd₁ = landFuncIsBoolStrict (tyCondFunc (x x₁) fst₁) (enumPiCondFunc u eu x snd₁)

tyCondFunc `One (x ∷ vec) with ℕtoF x ≟F zerof
tyCondFunc `One (x ∷ vec) | yes p = 1
tyCondFunc `One (x ∷ vec) | no ¬p = 0
tyCondFunc `Two (x ∷ vec) with ℕtoF x ≟F zerof
tyCondFunc `Two (x ∷ vec) | yes p = 1
tyCondFunc `Two (x ∷ vec) | no ¬p with ℕtoF x ≟F onef
tyCondFunc `Two (x ∷ vec) | no ¬p | yes p = 1
tyCondFunc `Two (x ∷ vec) | no ¬p | no ¬p₁ = 0
tyCondFunc `Base vec = 1
tyCondFunc (`Vec u zero) vec = 1
tyCondFunc (`Vec u (suc x)) vec with splitAt (tySize u) vec
... | fst , snd = landFunc (tyCondFunc u fst) (tyCondFunc (`Vec u x) snd)
tyCondFunc (`Σ u x) vec with splitAt (tySize u) vec
tyCondFunc (`Σ u x) vec | fst₁ , snd₁ = landFunc (tyCondFunc u fst₁) (enumSigmaCondFunc u (enum u) x fst₁ snd₁)
tyCondFunc (`Π u x) vec = enumPiCondFunc u (enum u) x vec

tyCondFuncIsBool : ∀ u vec → isBool (tyCondFunc u vec)
tyCondFuncIsBool `One (x ∷ vec) with ℕtoF x ≟F zerof
tyCondFuncIsBool `One (x ∷ vec) | yes p = isOne 1 ℕtoF-1≡1
tyCondFuncIsBool `One (x ∷ vec) | no ¬p = isZero zero ℕtoF-0≡0
tyCondFuncIsBool `Two (x ∷ vec) with ℕtoF x ≟F zerof
tyCondFuncIsBool `Two (x ∷ vec) | yes p = isOne 1 ℕtoF-1≡1
tyCondFuncIsBool `Two (x ∷ vec) | no ¬p with ℕtoF x ≟F onef
tyCondFuncIsBool `Two (x ∷ vec) | no ¬p | yes p = isOne 1 ℕtoF-1≡1
tyCondFuncIsBool `Two (x ∷ vec) | no ¬p | no ¬p₁ = isZero zero ℕtoF-0≡0
tyCondFuncIsBool `Base vec = isOne 1 ℕtoF-1≡1
tyCondFuncIsBool (`Vec u zero) vec = isOne 1 ℕtoF-1≡1
tyCondFuncIsBool (`Vec u (suc x)) vec with splitAt (tySize u) vec
... | fst , snd with ℕtoF (tyCondFunc u fst) ≟F zerof
tyCondFuncIsBool (`Vec u (suc x)) vec | fst , snd | yes p = isZero zero ℕtoF-0≡0
tyCondFuncIsBool (`Vec u (suc x)) vec | fst , snd | no ¬p with ℕtoF (tyCondFunc (`Vec u x) snd) ≟F zerof
tyCondFuncIsBool (`Vec u (suc x)) vec | fst , snd | no ¬p | yes p = isZero zero ℕtoF-0≡0
tyCondFuncIsBool (`Vec u (suc x)) vec | fst , snd | no ¬p | no ¬p₁ = isOne 1 ℕtoF-1≡1
tyCondFuncIsBool (`Σ u x) vec with splitAt (tySize u) vec
... | fst , snd with ℕtoF (tyCondFunc u fst) ≟F zerof
tyCondFuncIsBool (`Σ u x) vec | fst , snd | yes p = isZero zero ℕtoF-0≡0
tyCondFuncIsBool (`Σ u x) vec | fst , snd | no ¬p with ℕtoF (enumSigmaCondFunc u (enum u) x fst snd) ≟F zerof
tyCondFuncIsBool (`Σ u x) vec | fst , snd | no ¬p | yes p = isZero zero ℕtoF-0≡0
tyCondFuncIsBool (`Σ u x) vec | fst , snd | no ¬p | no ¬p₁ = isOne 1 ℕtoF-1≡1
tyCondFuncIsBool (`Π u x) vec = enumPiCondFuncIsBool u (enum u) x vec

tyCondFuncIsBoolStrict : ∀ u vec → isBoolStrict (tyCondFunc u vec)
tyCondFuncIsBoolStrict `One (x ∷ vec) with ℕtoF x ≟F zerof
tyCondFuncIsBoolStrict `One (x ∷ vec) | yes p = isOneS refl
tyCondFuncIsBoolStrict `One (x ∷ vec) | no ¬p = isZeroS refl
tyCondFuncIsBoolStrict `Two (x ∷ vec) with ℕtoF x ≟F zerof
tyCondFuncIsBoolStrict `Two (x ∷ vec) | yes p = isOneS refl
tyCondFuncIsBoolStrict `Two (x ∷ vec) | no ¬p with ℕtoF x ≟F onef
tyCondFuncIsBoolStrict `Two (x ∷ vec) | no ¬p | yes p = isOneS refl
tyCondFuncIsBoolStrict `Two (x ∷ vec) | no ¬p | no ¬p₁ = isZeroS refl
tyCondFuncIsBoolStrict `Base vec = isOneS refl
tyCondFuncIsBoolStrict (`Vec u zero) vec = isOneS refl
tyCondFuncIsBoolStrict (`Vec u (suc x)) vec with splitAt (tySize u) vec
... | fst , snd with ℕtoF (tyCondFunc u fst) ≟F zerof
tyCondFuncIsBoolStrict (`Vec u (suc x)) vec | fst , snd | yes p = isZeroS refl
tyCondFuncIsBoolStrict (`Vec u (suc x)) vec | fst , snd | no ¬p with ℕtoF (tyCondFunc (`Vec u x) snd) ≟F zerof
tyCondFuncIsBoolStrict (`Vec u (suc x)) vec | fst , snd | no ¬p | yes p = isZeroS refl
tyCondFuncIsBoolStrict (`Vec u (suc x)) vec | fst , snd | no ¬p | no ¬p₁ = isOneS refl
tyCondFuncIsBoolStrict (`Σ u x) vec with splitAt (tySize u) vec
... | fst , snd with ℕtoF (tyCondFunc u fst) ≟F zerof
tyCondFuncIsBoolStrict (`Σ u x) vec | fst , snd | yes p = isZeroS refl
tyCondFuncIsBoolStrict (`Σ u x) vec | fst , snd | no ¬p with ℕtoF (enumSigmaCondFunc u (enum u) x fst snd) ≟F zerof
tyCondFuncIsBoolStrict (`Σ u x) vec | fst , snd | no ¬p | yes p = isZeroS refl
tyCondFuncIsBoolStrict (`Σ u x) vec | fst , snd | no ¬p | no ¬p₁ = isOneS refl
tyCondFuncIsBoolStrict (`Π u x) vec = enumPiCondFuncIsBoolStrict u (enum u) x vec

enumSigmaCondFunc u [] x val val₁ = 1
enumSigmaCondFunc u (x₁ ∷ eu) x v₁ v₂ with maxTySplit u x₁ x v₂
enumSigmaCondFunc u (x₁ ∷ eu) x v₁ v₂ | fst₁ , snd₁ =
  landFunc (limpFunc (varEqLitFunc u v₁ x₁) (landFunc (tyCondFunc (x x₁) fst₁) (allEqzFunc snd₁)))
          (enumSigmaCondFunc u eu x v₁ v₂)

enumSigmaCondFuncIsBool : ∀ u eu x val₁ val₂ → isBool (enumSigmaCondFunc u eu x val₁ val₂)
enumSigmaCondFuncIsBool u [] x val₁ val₂ = isOne 1 ℕtoF-1≡1
enumSigmaCondFuncIsBool u (x₁ ∷ eu) x v₁ v₂ with maxTySplit u x₁ x v₂
... | fst₁ , snd₁ = landFuncIsBool (limpFunc (varEqLitFunc u v₁ x₁) (landFunc (tyCondFunc (x x₁) fst₁) (allEqzFunc snd₁))) (enumSigmaCondFunc u eu x v₁ v₂)

enumSigmaCondFuncIsBoolStrict : ∀ u eu x val₁ val₂ → isBoolStrict (enumSigmaCondFunc u eu x val₁ val₂)
enumSigmaCondFuncIsBoolStrict u [] x val₁ val₂ = isOneS refl
enumSigmaCondFuncIsBoolStrict u (x₁ ∷ eu) x v₁ v₂ with maxTySplit u x₁ x v₂
... | fst₁ , snd₁ = landFuncIsBoolStrict (limpFunc (varEqLitFunc u v₁ x₁) (landFunc (tyCondFunc (x x₁) fst₁) (allEqzFunc snd₁))) (enumSigmaCondFunc u eu x v₁ v₂)

enumPiCondSound : ∀ r u → (eu : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U)
   → (vec : Vec Var (tySumOver eu x))
   → (val : Vec ℕ (tySumOver eu x))
   → (sol : List (Var × ℕ))
   → BatchListLookup vec sol val
   → ListLookup 0 sol 1
   → ∀ init →
   let result = enumPiCond eu x vec ((r , prime) , init)
   in BuilderProdSol (writerOutput result) sol
   → ListLookup (output result) sol (enumPiCondFunc u eu x val)

tyCondSound : ∀ r u
   → (vec : Vec Var (tySize u))
   → (val : Vec ℕ (tySize u))
   → (sol : List (Var × ℕ))
   → BatchListLookup vec sol val
   → ListLookup 0 sol 1
   → ∀ init →
   let result = tyCond u vec ((r , prime) , init)
   in BuilderProdSol (writerOutput result) sol
   → ListLookup (output result) sol (tyCondFunc u val)

enumSigmaCondSound : ∀ r u → (eu : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U)
   → (vec₁ : Vec Var (tySize u))
   → (vec₂ : Vec Var (maxTySizeOver (enum u) x))
   → (val₁ : Vec ℕ (tySize u))
   → (val₂ : Vec ℕ (maxTySizeOver (enum u) x))
   → (sol : List (Var × ℕ))
   → BatchListLookup vec₁ sol val₁
   → BatchListLookup vec₂ sol val₂
   → ListLookup 0 sol 1
   → ∀ init →
   let result = enumSigmaCond eu x vec₁ vec₂ ((r , prime) , init)
   in BuilderProdSol (writerOutput result) sol
     → ListLookup (output result) sol (enumSigmaCondFunc u eu x val₁ val₂)

tyCondSound r `One vec val sol look₁ tri init isSol =
  let sound = allEqzSound r vec val sol look₁ init isSol
  in ListLookup-Respects-≈ _ _ _ _ (lem val) sound
 where
   lem : ∀ val → allEqzFunc val ≈ tyCondFunc `One val
   lem (x ∷ val) with ℕtoF x ≟F zerof
   lem (x ∷ []) | yes p = sq refl
   lem (x ∷ val) | no ¬p = sq refl
tyCondSound r `Two vec val sol look₁ tri init isSol =
  let
    input = ((r , prime) , init)
    p₁₁ = varEqLit `Two vec false
    p₁₂ = varEqLit `Two vec false >>= λ isZero -> varEqLit `Two vec true
    p₂₂ = varEqLit `Two vec true
    isZero = output (p₁₁ input)
    isOne = output (p₁₂ input)
    p₃₃ = λ isOne → lor isZero isOne
    p₂₃ = λ isZero → varEqLit `Two vec true >>= λ isOne → lor isZero isOne
    p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r init sol isSol
    p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r init sol isSol
    p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r _ sol p₂₃IsSol
    p₃₃IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₃ r _ sol p₂₃IsSol
    
    sound₁ = varEqLitSound r `Two vec val false sol look₁ tri init p₁₁IsSol
    sound₂ = varEqLitSound r `Two vec val true sol look₁ tri _ p₂₂IsSol
    sound₃ = lorSound r isZero isOne _ _ sol sound₁ sound₂ (varEqLitFuncIsBool `Two val false) (varEqLitFuncIsBool `Two val true) _ p₃₃IsSol
  in ListLookup-Respects-≈ _ _ _ _ (lem val) sound₃
 where
   lem : ∀ val → lorFunc (varEqLitFunc `Two val false) (varEqLitFunc `Two val true) ≈ tyCondFunc `Two val
   lem val with ℕtoF (varEqLitFunc `Two val false) ≟F zerof
   lem (x ∷ val) | yes p with ℕtoF x ≟F zerof
   lem (x ∷ val) | yes p | yes p₁ = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) p))
   lem (x ∷ val) | yes p | no ¬p with ℕtoF 1 ≟F zerof
   lem (x ∷ val) | yes p | no ¬p | yes p₁ = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) p₁))
   lem (x ∷ val) | yes p | no ¬p | no ¬p₁ with ℕtoF x ≟F onef
   lem (x ∷ val) | yes p | no ¬p | no ¬p₁ | yes p₁ with ℕtoF 1 ≟F zerof
   lem (x ∷ val) | yes p | no ¬p | no ¬p₁ | yes p₁ | yes p₂ = sq (sym (trans p₂ (sym p)))
   lem (x ∷ val) | yes p | no ¬p | no ¬p₁ | yes p₁ | no ¬p₂ = sq refl
   lem (x ∷ val) | yes p | no ¬p | no ¬p₁ | no ¬p₂ with ℕtoF 0 ≟F zerof
   lem (x ∷ val) | yes p | no ¬p | no ¬p₁ | no ¬p₂ | yes p₁ = sq refl
   lem (x ∷ val) | yes p | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ = ⊥-elim′ (¬p₃ p)
   lem (x ∷ val) | no ¬p with ℕtoF x ≟F zerof
   lem (x ∷ val) | no ¬p | yes p = sq refl
   lem (x ∷ val) | no ¬p | no ¬p₁ with ℕtoF x ≟F onef
   lem (x ∷ val) | no ¬p | no ¬p₁ | yes p = sq refl
   lem (x ∷ val) | no ¬p | no ¬p₁ | no ¬p₂ = ⊥-elim′ (¬p ℕtoF-0≡0)
tyCondSound r `Base vec val sol look₁ tri init isSol = tri
tyCondSound r (`Vec u zero) vec val sol look₁ tri init isSol = tri
tyCondSound r (`Vec u (suc x)) vec val sol look₁ tri init isSol with splitAt (tySize u) vec | inspect (splitAt (tySize u)) vec
... | fst , snd | [ prf₁ ] with splitAt (tySize u) val | inspect (splitAt (tySize u)) val
... | fstv , sndv | [ prf₂ ] =
  let p₁₁ = tyCond u fst
      p₂₂ = tyCond (`Vec u x) snd
      r' = output (p₁₁ ((r , prime) , init))
      p₃₃ = λ s → land r' s
      p₂₃ = λ r → tyCond (`Vec u x) snd >>= λ s → land r s
      p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
      p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol      
      p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r _ sol p₂₃IsSol     
      p₃₃IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₃ r _ sol p₂₃IsSol  
      lookFst = BatchListLookup-Split₁ (tySize u) _ vec sol val fst snd fstv sndv prf₁ prf₂ look₁
      lookSnd = BatchListLookup-Split₂ (tySize u) _ vec sol val fst snd fstv sndv prf₁ prf₂ look₁
      sound₁ = tyCondSound r u fst fstv sol lookFst tri init p₁₁IsSol
      sound₂ = tyCondSound r (`Vec u x) snd sndv sol lookSnd tri _ p₂₂IsSol
      sound₃ = landSound r _ _ _ _ sol sound₁ sound₂ (tyCondFuncIsBool u fstv) (tyCondFuncIsBool (`Vec u x) sndv) _ p₃₃IsSol
  in sound₃
tyCondSound r (`Σ u x) vec val sol look₁ tri init isSol with splitAt (tySize u) vec | inspect (splitAt (tySize u)) vec
... | fst , snd | [ prf₁ ] with splitAt (tySize u) val | inspect (splitAt (tySize u)) val
... | fstv , sndv | [ prf₂ ] =
  let p₁₁ = tyCond u fst
      p₂₂ = enumSigmaCond (enum u) x fst snd
      r' = output (p₁₁ ((r , prime) , init))
      p₃₃ = λ s → land r' s
      p₂₃ = λ r → enumSigmaCond (enum u) x fst snd >>= λ s → land r s
      p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
      p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol      
      p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r _ sol p₂₃IsSol     
      p₃₃IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₃ r _ sol p₂₃IsSol  
      lookFst = BatchListLookup-Split₁ (tySize u) _ vec sol val fst snd fstv sndv prf₁ prf₂ look₁
      lookSnd = BatchListLookup-Split₂ (tySize u) _ vec sol val fst snd fstv sndv prf₁ prf₂ look₁
      sound₁ = tyCondSound r u fst fstv sol lookFst tri _ p₁₁IsSol
      sound₂ = enumSigmaCondSound r u (enum u) x fst snd fstv sndv sol lookFst lookSnd tri _ p₂₂IsSol
      sound₃ = landSound r _ _ _ _ sol sound₁ sound₂ (tyCondFuncIsBool u fstv) (enumSigmaCondFuncIsBool u (enum u) x fstv sndv) _ p₃₃IsSol
  in sound₃
tyCondSound r (`Π u x) vec val sol look₁ tri init isSol = enumPiCondSound r u (enum u) x vec val sol look₁ tri init isSol


enumPiCondSound r u [] x vec val sol look₁ tri init isSol = tri
enumPiCondSound r u (x₁ ∷ eu) x vec val sol look₁ tri init isSol with splitAt (tySize (x x₁)) vec | inspect (splitAt (tySize (x x₁))) vec
... | fst , snd | [ prf₁ ] with splitAt (tySize (x x₁)) val | inspect (splitAt (tySize (x x₁))) val
... | fstv , sndv | [ prf₂ ] =
  let p₁₁ = tyCond (x x₁) fst
      p₂₂ = enumPiCond eu x snd
      r' = output (p₁₁ ((r , prime) , init))
      p₃₃ = λ s → land r' s
      p₂₃ = λ r → enumPiCond eu x snd >>= λ s → land r s
      p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
      p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol      
      p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r _ sol p₂₃IsSol     
      p₃₃IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₃ r _ sol p₂₃IsSol  
      lookFst = BatchListLookup-Split₁ (tySize (x x₁)) _ vec sol val fst snd fstv sndv prf₁ prf₂ look₁
      lookSnd = BatchListLookup-Split₂ (tySize (x x₁)) _ vec sol val fst snd fstv sndv prf₁ prf₂ look₁
      sound₁ = tyCondSound r (x x₁) fst fstv sol lookFst tri _ p₁₁IsSol
      sound₂ = enumPiCondSound r u eu x snd sndv sol lookSnd tri _ p₂₂IsSol
      sound₃ = landSound r _ _ _ _ _ sound₁ sound₂ (tyCondFuncIsBool (x x₁) fstv) (enumPiCondFuncIsBool u eu x sndv) _ p₃₃IsSol
  in sound₃


enumSigmaCondSound r u [] x vec₁ vec₂ val₁ val₂ sol look₁ look₂ tri init isSol = tri
enumSigmaCondSound r u (elem₁ ∷ enum₁) x v₁ v₂ val₁ val₂ sol look₁ look₂ tri init isSol with maxTySplit u elem₁ x v₂ | inspect (maxTySplit u elem₁ x) v₂
... | fst , snd | [ prf₁ ] with maxTySplit u elem₁ x val₂ | inspect (maxTySplit u elem₁ x) val₂
... | fstv , sndv | [ prf₂ ] =
  let input = ((r , prime) , init)
      p₁₁ = varEqLit u v₁ elem₁
      p₁₂ = do
        eqElem₁ ← varEqLit u v₁ elem₁
        tyCond (x elem₁) fst
      p₁₃ = do
        eqElem₁ ← varEqLit u v₁ elem₁
        tyCons ← tyCond (x elem₁) fst
        allEqz snd
      p₁₄ = do
        eqElem₁ ← varEqLit u v₁ elem₁
        tyCons ← tyCond (x elem₁) fst
        restZ ← allEqz snd
        land tyCons restZ
      p₁₅ = do
        eqElem₁ ← varEqLit u v₁ elem₁
        tyCons ← tyCond (x elem₁) fst
        restZ ← allEqz snd
        tyCons&restZ ← land tyCons restZ
        limp eqElem₁ tyCons&restZ

      eqElem₁ = output (p₁₁ input)
      p₂₂ = tyCond (x elem₁) fst
      tyCons = output (p₁₂ input)
      p₃₃ = allEqz snd
      restZ = output (p₁₃ input)
      p₄₄ = land tyCons restZ
      tyCons&restZ = output (p₁₄ input)
      p₅₅ = limp eqElem₁ tyCons&restZ
      sat = output (p₁₅ input)
      p₆₆ = enumSigmaCond enum₁ x v₁ v₂
      p₇₇ = λ rest → land sat rest
      p₆₇ = λ sat → do
        rest ← enumSigmaCond enum₁ x v₁ v₂
        land sat rest      
      p₅₇ = λ tyCons&restZ → do
        sat ← limp eqElem₁ tyCons&restZ
        rest ← enumSigmaCond enum₁ x v₁ v₂
        land sat rest

      p₄₇ = λ restZ → do
              tyCons&restZ ← land tyCons restZ
              sat ← limp eqElem₁ tyCons&restZ
              rest ← enumSigmaCond enum₁ x v₁ v₂
              land sat rest      
      p₃₇ = λ tyCons → do
              restZ ← allEqz snd
              tyCons&restZ ← land tyCons restZ
              sat ← limp eqElem₁ tyCons&restZ
              rest ← enumSigmaCond enum₁ x v₁ v₂
              land sat rest
      p₂₇ = λ eqElem₁ → do
              tyCons ← tyCond (x elem₁) fst
              restZ ← allEqz snd
              tyCons&restZ ← land tyCons restZ
              sat ← limp eqElem₁ tyCons&restZ
              rest ← enumSigmaCond enum₁ x v₁ v₂
              land sat rest
      p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₇ r _ sol isSol
      p₂₇IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₇ r _ sol isSol
      p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₇ r _ sol p₂₇IsSol
      p₃₇IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₇ r _ sol p₂₇IsSol
      p₃₃IsSol = BuilderProdSol->>=⁻₁ p₃₃ p₄₇ r _ sol p₃₇IsSol
      p₄₇IsSol = BuilderProdSol->>=⁻₂ p₃₃ p₄₇ r _ sol p₃₇IsSol
      p₄₄IsSol = BuilderProdSol->>=⁻₁ p₄₄ p₅₇ r _ sol p₄₇IsSol
      p₅₇IsSol = BuilderProdSol->>=⁻₂ p₄₄ p₅₇ r _ sol p₄₇IsSol
      p₅₅IsSol = BuilderProdSol->>=⁻₁ p₅₅ p₆₇ r _ sol p₅₇IsSol
      p₆₇IsSol = BuilderProdSol->>=⁻₂ p₅₅ p₆₇ r _ sol p₅₇IsSol
      p₆₆IsSol = BuilderProdSol->>=⁻₁ p₆₆ p₇₇ r _ sol p₆₇IsSol
      p₇₇IsSol = BuilderProdSol->>=⁻₂ p₆₆ p₇₇ r _ sol p₆₇IsSol
      lookFst = BatchListLookup-MaxTySplit₁ u elem₁ x sol v₂ fst val₂ fstv (cong proj₁ prf₁) (cong proj₁ prf₂) look₂
      lookSnd = BatchListLookup-MaxTySplit₂ u elem₁ x sol v₂ snd val₂ sndv (cong proj₂ prf₁) (cong proj₂ prf₂) look₂


      eqElem₁Sound = varEqLitSound r u v₁ val₁ elem₁ sol look₁ tri _ p₁₁IsSol
      tyConsSound = tyCondSound r (x elem₁) fst fstv sol lookFst tri _ p₂₂IsSol
      restZSound = allEqzSound r snd sndv sol lookSnd _ p₃₃IsSol
      tyCons&restZSound = landSound r _ _ _ _ sol tyConsSound restZSound (tyCondFuncIsBool (x elem₁) fstv) (allEqzFuncIsBool sndv) _ p₄₄IsSol
      satSound = limpSound r _ _ _ _ sol eqElem₁Sound tyCons&restZSound (varEqLitFuncIsBool u val₁ elem₁) (landFuncIsBool (tyCondFunc (x elem₁) fstv) (allEqzFunc sndv)) _ p₅₅IsSol
      restSound = enumSigmaCondSound r u enum₁ x v₁ v₂ val₁ val₂ sol look₁ look₂ tri _ p₆₆IsSol
      finalSound = landSound r _ _ _ _ sol satSound restSound (limpFuncIsBool (varEqLitFunc u val₁ elem₁) (landFunc (tyCondFunc (x elem₁) fstv) (allEqzFunc sndv))) (enumSigmaCondFuncIsBool u enum₁ x val₁ val₂) _ p₇₇IsSol
  in finalSound

varEqBaseLitSound₁ : ∀ (r : WriterMode)
  → (v : Var) (l : f)
  → (sol : List (Var × ℕ))
  → ListLookup 0 sol 1
  → ∀ init →
  let result = varEqBaseLit v l ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol 1
  → Squash (∃ (λ val → Σ′ (ℕtoF val ≡ l) (λ _ → ListLookup v sol val)))  
varEqBaseLitSound₁ r v l sol tri init isSol look
    with
    let
      input = ((r , prime) , init)
      p₁₂ = do
        n-l ← new
        add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ []))
      p₁₃ = do
        n-l ← new
        add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ []))
        neqz n-l
      n-l = init
      p₃₃ = neqz n-l
      p₃₅ = λ _ → do
        ¬r ← neqz n-l
        r ← lnot ¬r
        return r
      ¬r = output (p₁₃ input)
      p₄₅ = λ _ → do
        r ← lnot ¬r
        return r
      p₃₅IsSol = BuilderProdSol->>=⁻₂ p₁₂ p₃₅ r _ _ isSol
      p₃₃IsSol = BuilderProdSol->>=⁻₁ p₃₃ p₄₅ r _ _ p₃₅IsSol
    in neqzIsBool r _ _ _ p₃₃IsSol
... | sq (neqzOutVal , isBool₁ , look₁) with
    let
       input = ((r , prime) , init)
       p₁₂ = do
         n-l ← new
         add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ []))
       p₁₃ = do
         n-l ← new
         add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ []))
         neqz n-l
       n-l = init
       p₃₃ = neqz n-l
       p₃₅ = λ _ → do
         ¬r ← neqz n-l
         r ← lnot ¬r
         return r
       ¬r = output (p₁₃ input)
       p₄₄ = lnot ¬r
       p₄₅ = λ _ → do
         r ← lnot ¬r
         return r
       p₅₅ = λ r →
         return r
       p₃₅IsSol = BuilderProdSol->>=⁻₂ p₁₂ p₃₅ r _ _ isSol
       p₃₃IsSol = BuilderProdSol->>=⁻₁ p₃₃ p₄₅ r _ _ p₃₅IsSol
       p₄₅IsSol = BuilderProdSol->>=⁻₂ p₃₃ p₄₅ r _ _ p₃₅IsSol
       p₄₄IsSol = BuilderProdSol->>=⁻₁ p₄₄ p₅₅ r _ _ p₄₅IsSol
       notSound₁ = lnotSound₁ r _ _ _ _ look₁ isBool₁ p₄₄IsSol look
    in neqzSound₀ r init _ tri _ p₃₃IsSol notSound₁
... | sq (neqzInVal , look₂ , sq eq₀)
    with
    let
       p₁₂ = do
         n-l ← new
         add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ []))
       p₁₃ = do
         n-l ← new
         add (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ []))
         neqz n-l
       n-l = init
       p₃₅ = λ _ → do
         ¬r ← neqz n-l
         r ← lnot ¬r
         return r
       p₁₂IsSol = BuilderProdSol->>=⁻₁ p₁₂ p₃₅ r _ _ isSol

    in addSound r (IAdd (-F l) ((onef , v) ∷ (-F onef , n-l) ∷ [])) sol (suc init) p₁₂IsSol
varEqBaseLitSound₁ r v l sol tri init isSol look | sq (neqzOutVal , isBool₁ , look₁) | sq (neqzInVal , look₂ , sq eq₀) | addSol (LinearCombValCons .(Field.one field') .v varVal x (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₁ x₂ LinearCombValBase)) x₁ rewrite *-identityˡ (ℕtoF varVal)
                   | -one*f≡-f (ℕtoF varVal₁)
                   | +-identityʳ (-F (ℕtoF varVal₁))
                   with ListLookup-≈ x₂ look₂
... | sq p rewrite p | sym eq₀
                 = sq (varVal , ((trans (sym (subst (λ t → (ℕtoF varVal +F (-F t)) ≡ ℕtoF varVal) (sym ℕtoF-0≡0)
                                                (subst (λ t → (ℕtoF varVal +F t) ≡ ℕtoF varVal) (sym -zero≡zero)
                                                  (+-identityʳ (ℕtoF varVal))))) (a-b≡zero→a≡b x₁)) , x))
allEqzSound₁ : ∀ (r : WriterMode)
  → ∀ {n} → (vec : Vec Var n)
  → (sol : List (Var × ℕ))
  → ListLookup 0 sol 1
  → ∀ init →
  let result = allEqz vec ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol 1
  → Squash (∃ (λ val → (Σ′′ (BatchListLookup vec sol val) (λ _ → All (_≈_ 0) val))))
allEqzSound₁ r vec sol tri init isSol look
    with let p₁₁ = anyNeqz vec
             p₂₃ = λ ¬r → do
               r ← lnot ¬r
               return r
             p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
         in anyNeqzIsBool r vec sol init p₁₁IsSol
... | sq (val , isBool , look₁)
    = let p₁₁ = anyNeqz vec
          p₂₃ = λ ¬r → do
               r ← lnot ¬r
               return r
          p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
          p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol
      in anyNeqzSound₀ r vec sol tri init p₁₁IsSol (lnotSound₁ r _ _ sol _ look₁ isBool p₂₃IsSol look)

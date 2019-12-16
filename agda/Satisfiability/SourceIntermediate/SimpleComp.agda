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
varEqLitFunc `Two (x ∷ vec) true  with ℕtoF x ≟F zerof
varEqLitFunc `Two (x ∷ vec) true | yes p = 0
varEqLitFunc `Two (x ∷ vec) true | no ¬p = 1
varEqLitFunc `Base (x ∷ vec) lit with ℕtoF x ≟F lit
varEqLitFunc `Base (x ∷ vec) lit | yes p = 1
varEqLitFunc `Base (x ∷ vec) lit | no ¬p = 0
varEqLitFunc (`Vec u zero) vec lit = 1
varEqLitFunc (`Vec u (suc x)) vec (l ∷ lit) with splitAt (tySize u) vec
... | fst , snd = andFunc (varEqLitFunc u fst l) (varEqLitFunc (`Vec u x) snd lit)
varEqLitFunc (`Σ u x) vec (fstₗ , sndₗ) with splitAt (tySize u) vec
... | fst , snd with maxTySplit u fstₗ x snd
... | vecₜ₁ , vecₜ₂ = andFunc (varEqLitFunc u fst fstₗ) (varEqLitFunc (x fstₗ) vecₜ₁ sndₗ)
varEqLitFunc (`Π u x) vec lit = piVarEqLitFunc x (enum u) vec lit 

piVarEqLitFunc x [] vec pi = 1
piVarEqLitFunc x (x₁ ∷ eu) vec pi with splitAt (tySize (x x₁)) vec
... | fst , snd = andFunc (varEqLitFunc (x x₁) fst (pi x₁)) (piVarEqLitFunc x eu snd pi)

varEqLitFuncIsBool : ∀ u vec v → isBool (varEqLitFunc u vec v)
piVarEqLitFuncIsBool : ∀ {u} (x : ⟦ u ⟧ → U) eu vec pi → isBool (piVarEqLitFunc x eu vec pi)

varEqLitFuncIsBool `One (x ∷ vec) v with ℕtoF x ≟F zerof
varEqLitFuncIsBool `One (x ∷ vec) v | yes p = isOne 1 ℕtoF-1≡1
varEqLitFuncIsBool `One (x ∷ vec) v | no ¬p = isZero zero ℕtoF-0≡0
varEqLitFuncIsBool `Two (x ∷ vec) false with ℕtoF x ≟F zerof
varEqLitFuncIsBool `Two (x ∷ vec) false | yes p = isOne 1 ℕtoF-1≡1
varEqLitFuncIsBool `Two (x ∷ vec) false | no ¬p = isZero zero ℕtoF-0≡0
varEqLitFuncIsBool `Two (x ∷ vec) true with ℕtoF x ≟F zerof
varEqLitFuncIsBool `Two (x ∷ vec) true | yes p = isZero zero ℕtoF-0≡0
varEqLitFuncIsBool `Two (x ∷ vec) true | no ¬p = isOne 1 ℕtoF-1≡1
varEqLitFuncIsBool `Base (x ∷ vec) v with ℕtoF x ≟F v
varEqLitFuncIsBool `Base (x ∷ vec) v | yes p = isOne 1 ℕtoF-1≡1
varEqLitFuncIsBool `Base (x ∷ vec) v | no ¬p = isZero zero ℕtoF-0≡0
varEqLitFuncIsBool (`Vec u zero) vec v = isOne 1 ℕtoF-1≡1
varEqLitFuncIsBool (`Vec u (suc x)) vec (l ∷ lit) with splitAt (tySize u) vec
... | fst , snd = andFuncIsBool (varEqLitFunc u fst l) (varEqLitFunc (`Vec u x) snd lit)
varEqLitFuncIsBool (`Σ u x) vec (fstₗ , sndₗ) with splitAt (tySize u) vec
... | fst , snd with maxTySplit u fstₗ x snd
... | vecₜ₁ , vecₜ₂ = andFuncIsBool (varEqLitFunc u fst fstₗ) (varEqLitFunc (x fstₗ) vecₜ₁ sndₗ)
varEqLitFuncIsBool (`Π u x) vec v = piVarEqLitFuncIsBool x (enum u) vec v


piVarEqLitFuncIsBool x [] vec pi = isOne 1 ℕtoF-1≡1
piVarEqLitFuncIsBool x (x₁ ∷ eu) vec pi with splitAt (tySize (x x₁)) vec
... | fst , snd = andFuncIsBool (varEqLitFunc (x x₁) fst (pi x₁)) (piVarEqLitFunc x eu snd pi)

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
varEqLitSound r `Two vec val true sol look tri init isSol
  = let sound₁ = anyNeqzSound r vec val sol look init isSol
    in ListLookup-Respects-≈ _ _ _ _ (lem val) sound₁
  where
    lem : ∀ val → anyNeqzFunc val ≈ varEqLitFunc `Two val true
    lem (x ∷ val) with ℕtoF x ≟F zerof
    lem (x ∷ []) | yes p = sq refl
    lem (x ∷ val) | no ¬p = sq refl
varEqLitSound r `Base (x ∷ []) val l sol look tri init isSol
    with let
           p₁₁ = new
           p₂₂ = add (IAdd l ((-F onef , x) ∷ (-F onef , init) ∷ []))
           
           p₂₃ = λ v → add (IAdd l ((-F onef , x) ∷ (-F onef , init) ∷ [])) >>= λ _ → allEqz (v ∷ [])
           p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r init sol isSol
           p₃₃ = λ _ → allEqz (init ∷ [])
           p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r _ sol p₂₃IsSol
         in addSound r (IAdd l ((-F onef , x) ∷ (-F onef , init) ∷ [])) sol (suc init) p₂₂IsSol
varEqLitSound r `Base (x ∷ []) (val ∷ []) l sol look₁@(BatchLookupCons .x .val .[] .[] .sol x₄ look) tri init isSol | addSol (LinearCombValCons .((Field.- field') (Field.one field')) .x varVal x₁ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₁ x₃ LinearCombValBase)) x₂
  rewrite -one*f≡-f (ℕtoF varVal)
        | -one*f≡-f (ℕtoF varVal₁)
        | +-identityʳ (-F ℕtoF varVal₁)
        = let
           input = ((r , prime) , init)
           p₁₁ = new
           p₁₂ = new >>= λ v → add (IAdd l ((-F onef , x) ∷ (-F onef , init) ∷ []))
           p₂₂ = add (IAdd l ((-F onef , x) ∷ (-F onef , init) ∷ []))
           
           p₂₃ = λ v → add (IAdd l ((-F onef , x) ∷ (-F onef , v) ∷ [])) >>= λ _ → allEqz (v ∷ [])
           p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r init sol isSol
           p₃₃ = λ _ → allEqz (init ∷ [])
           p₃₃IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₃ r _ sol p₂₃IsSol
           sound₂ = allEqzSound r (init ∷ []) (varVal₁ ∷ []) sol (BatchLookupCons _ _ _ _ _ x₃ look) (varOut (p₁₂ input)) p₃₃IsSol
          in ListLookup-Respects-≈ _ _ _ _ lem sound₂
  where
    lem : allEqzFunc (varVal₁ ∷ []) ≈ varEqLitFunc `Base (val ∷ []) l
    lem with ℕtoF varVal₁ ≟F zerof
    lem | yes p with ℕtoF val ≟F l
    lem | yes p | yes p₁ = sq refl
    lem | yes p | no ¬p rewrite p
                                     | -zero≡zero
                                     | +-identityʳ (-F (ℕtoF varVal))
                                     | +-comm (-F (ℕtoF varVal)) l
                                     with ListLookup-≈ x₄ x₁
    ... | sq eq₁ = ⊥-elim′ (¬p (trans eq₁ (sym (a-b≡zero→a≡b x₂))))
    lem | no ¬p with ℕtoF val ≟F l
    lem | no ¬p | yes p with ListLookup-≈ x₁ x₄
    ... | sq eq₁        rewrite eq₁
                              | p
                              | +-comm (-F l) (-F (ℕtoF varVal₁))
                              | +-assoc (-F (ℕtoF varVal₁)) (-F l) l
                              | +-invˡ l
                              | +-identityʳ (-F (ℕtoF varVal₁)) = ⊥-elim′ (¬p (-≡zero→≡zero x₂))
    lem | no ¬p | no ¬p₁ = sq refl
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
       p₂₂ = varEqLit (x fstₗ) snd₁ sndₗ
       r' = output (p₁₁ input)
       p₃₃ = λ s → land r' s
       p₂₃ = λ r → varEqLit (x fstₗ) snd₁ sndₗ >>= λ s → land r s
       p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
       p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol
       p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r (varOut (p₁₁ input)) sol p₂₃IsSol
       p₃₃IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₃ r (varOut (p₁₁ input)) sol p₂₃IsSol
       lookFst = BatchListLookup-Split₁ (tySize u) _ vec sol val fst snd fstv sndv prf prf₂ look
       lookSnd = BatchListLookup-Split₂ (tySize u) _ vec sol val fst snd fstv sndv prf prf₂ look
       sound₁ = varEqLitSound r u fst fstv fstₗ sol lookFst tri init p₁₁IsSol
       sound₂ = varEqLitSound r (x fstₗ) snd₁ sndv₁ sndₗ sol (BatchListLookup-MaxTySplit₁ u fstₗ x sol snd snd₁ sndv sndv₁ (cong proj₁ prf₃) (cong proj₁ prf₄) lookSnd) tri (varOut (p₁₁ input)) p₂₂IsSol
       sound₃ = landSound r (output (p₁₁ input)) (output (p₁₂ input)) (varEqLitFunc u fstv fstₗ) (varEqLitFunc (x fstₗ) sndv₁ sndₗ) sol sound₁ sound₂ (varEqLitFuncIsBool u fstv fstₗ) (varEqLitFuncIsBool (x fstₗ) sndv₁ sndₗ) (varOut (p₁₂ input)) p₃₃IsSol
     in sound₃
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


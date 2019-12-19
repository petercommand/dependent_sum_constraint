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
module Satisfiability.SourceIntermediate (f : Set) (_≟F_ : Decidable {A = f} _≡_) (field' : Field f) (isField : IsField f field')
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
open import Satisfiability.SourceIntermediate.SimpleComp f _≟F_ field' isField finite showf fToℕ ℕtoF ℕtoF-1≡1 ℕtoF-0≡0 prime isPrime onef≠zerof
{-
data UList (u : U) (x : ⟦ u ⟧ → U) : List ⟦ u ⟧ → Set where
  UNil : UList u x []
  UCons : ∀ val {l} → ⟦ x val ⟧ → UList u x l → UList u x (val ∷ l)
-}

tyCondFunc : ∀ u → (vec : Vec ℕ (tySize u)) → ℕ
enumSigmaCondFunc : ∀ u → (eu : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U)
  → (val₁ : Vec ℕ (tySize u))
  → (val₂ : Vec ℕ (maxTySizeOver (enum u) x))
  → ℕ

enumPiCondFunc : ∀ u → (eu : List ⟦ u ⟧) → (x : ⟦ u ⟧ → U) → Vec ℕ (tySumOver eu x) → ℕ
enumPiCondFunc u [] x vec = 1
enumPiCondFunc u (x₁ ∷ eu) x vec with splitAt (tySize (x x₁)) vec
enumPiCondFunc u (x₁ ∷ eu) x vec | fst₁ , snd₁ = andFunc (tyCondFunc (x x₁) fst₁) (enumPiCondFunc u eu x snd₁)

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
... | fst , snd = andFunc (tyCondFunc u fst) (tyCondFunc (`Vec u x) snd)
tyCondFunc (`Σ u x) vec with splitAt (tySize u) vec
tyCondFunc (`Σ u x) vec | fst₁ , snd₁ = andFunc (tyCondFunc u fst₁) (enumSigmaCondFunc u (enum u) x fst₁ snd₁)
tyCondFunc (`Π u x) vec = enumPiCondFunc u (enum u) x vec

enumSigmaCondFunc u [] x val val₁ = 1
enumSigmaCondFunc u (x₁ ∷ eu) x v₁ v₂ with maxTySplit u x₁ x v₂
enumSigmaCondFunc u (x₁ ∷ eu) x v₁ v₂ | fst₁ , snd₁ =
  andFunc (impFunc (varEqLitFunc u v₁ x₁) (andFunc (tyCondFunc (x x₁) fst₁) (allEqzFunc snd₁)))
          (enumSigmaCondFunc u eu x v₁ v₂)

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
      sound₃ = landSound r _ _ _ _ sol sound₁ sound₂ {!!} {!!} _ p₃₃IsSol
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
      sound₃ = landSound r _ _ _ _ sol sound₁ sound₂ {!!} {!!} _ p₃₃IsSol
  in sound₃
tyCondSound r (`Π u x) vec val sol look₁ tri init isSol = enumPiCondSound r u (enum u) x vec val sol look₁ tri init isSol


enumPiCondSound r u [] x vec val sol look₁ tri init isSol = {!tri!}
enumPiCondSound r u (x₁ ∷ eu) x vec val sol look₁ tri init isSol = {!!}

enumSigmaCondSound r u eu x vec₁ vec₂ val₁ val₂ sol look₁ look₂ tri init isSol = {!!}

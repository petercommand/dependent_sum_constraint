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

varEqLitSound : ∀ (r : WriterMode)
  → ∀ u → (vec : Vec Var (tySize u))
  → (val : Vec Var (tySize u))
  → (l : ⟦ u ⟧)
  → (sol : List (Var × ℕ))
  → BatchListLookup vec sol val
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
  → ∀ (init : ℕ) →
  let result = piVarEqLit u x eu vec pi ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol (piVarEqLitFunc x eu val pi)
varEqLitSound r `One vec val l sol look init isSol
  = let sound₁ = allEqzSound r vec val sol look init isSol
    in ListLookup-Respects-≈  _ _ _ _ (lem val l) sound₁
  where
    lem : ∀ val l → allEqzFunc val ≈ varEqLitFunc `One val l
    lem (x ∷ val) l with ℕtoF x ≟F zerof
    lem (x ∷ []) l | yes p = sq refl
    lem (x ∷ val) l | no ¬p = sq refl
varEqLitSound r `Two vec val false sol look init isSol
  = let sound₁ = allEqzSound r vec val sol look init isSol
    in ListLookup-Respects-≈ _ _ _ _ (lem val) sound₁
  where
    lem : ∀ val → allEqzFunc val ≈ varEqLitFunc `Two val false
    lem (x ∷ val) with ℕtoF x ≟F zerof
    lem (x ∷ []) | yes p = sq refl
    lem (x ∷ val) | no ¬p = sq refl
varEqLitSound r `Two vec val true sol look init isSol
  = let sound₁ = anyNeqzSound r vec val sol look init isSol
    in ListLookup-Respects-≈ _ _ _ _ (lem val) sound₁
  where
    lem : ∀ val → anyNeqzFunc val ≈ varEqLitFunc `Two val true
    lem (x ∷ val) with ℕtoF x ≟F zerof
    lem (x ∷ []) | yes p = sq refl
    lem (x ∷ val) | no ¬p = sq refl
varEqLitSound r `Base (x ∷ []) val l sol look init isSol
    with let
           p₁₁ = new
           p₂₂ = add (IAdd l ((-F onef , x) ∷ (-F onef , init) ∷ []))
           
           p₂₃ = λ v → add (IAdd l ((-F onef , x) ∷ (-F onef , init) ∷ [])) >>= λ _ → allEqz (v ∷ [])
           p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r init sol isSol
           p₃₃ = λ _ → allEqz (init ∷ [])
           p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r _ sol p₂₃IsSol
         in addSound r (IAdd l ((-F onef , x) ∷ (-F onef , init) ∷ [])) sol (suc init) p₂₂IsSol
varEqLitSound r `Base (x ∷ []) (val ∷ []) l sol look₁@(BatchLookupCons .x .val .[] .[] .sol x₄ look) init isSol | addSol (LinearCombValCons .((Field.- field') (Field.one field')) .x varVal x₁ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₁ x₃ LinearCombValBase)) x₂
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
          in ListLookup-Respects-≈ _ _ _ _ {!lem!} sound₂
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

varEqLitSound r (`Vec u x) vec val l sol look init isSol = {!!}
varEqLitSound r (`Σ u x) vec val l sol look init isSol = {!!}
varEqLitSound r (`Π u x) vec val l sol look init isSol = {!!}

piVarEqLitSound r u x eu vec val pi sol look init isSol = {!!}


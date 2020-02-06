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
open import Data.Vec.AllProp
open import Data.Squash
open import Data.String hiding (_≈_; _≟_; _++_)
open import Data.Sum
open import Data.Unit
open import Function

open import Language.Common

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
module Satisfiability.SourceR1CS.LogicGates (f : Set) (_≟F_ : Decidable {A = f} _≡_) (field' : Field f) (isField : IsField f field')
     (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f)
        (ℕtoF-1≡1 : ℕtoF 1 ≡ Field.one field')
        (ℕtoF-0≡0 : ℕtoF 0 ≡ Field.zero field')
        (ℕtoF∘fToℕ≡ : ∀ x → ℕtoF (fToℕ x) ≡ x)
        (prime : ℕ) (isPrime : Prime prime)
        (onef≠zerof : ¬ Field.one field' ≡ Field.zero field') where

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

neqzFunc : ℕ → ℕ
neqzFunc n with ℕtoF n ≟F zerof
neqzFunc n | yes p = 0
neqzFunc n | no ¬p = 1

neqzFuncIsBoolStrict : ∀ n → isBoolStrict (neqzFunc n)
neqzFuncIsBoolStrict n with ℕtoF n ≟F zerof
... | yes p = isZeroS refl
... | no p = isOneS refl

neqzFuncIsBool : ∀ n → isBool (neqzFunc n)
neqzFuncIsBool n = isBoolStrict→isBool (neqzFuncIsBoolStrict n)

neqzSoundLem₁ : ∀ r v init →
  let b₁₂ = writerOutput
                  (add (IMul onef init v onef (suc init))
                    ((r , prime) , suc (suc init)))
      b₃₄ = writerOutput (neqz v ((r , prime) , init))
  in ∀ x → x ∈ proj₁ b₁₂ (proj₂ b₁₂ []) → x ∈ proj₁ b₃₄ (proj₂ b₃₄ [])
neqzSoundLem₁ NormalMode v init x (here px) = there (here px)
neqzSoundLem₁ PostponedMode v init x (here px) = there (here px)



neqzSoundLem₂ : ∀ r v init →
  let b₁₂ = writerOutput
                (add (IMul onef (suc init) v onef v) ((r , prime) , suc (suc init)))
      b₃₄ = writerOutput (neqz v ((r , prime) , init))
  in ∀ x → x ∈ proj₁ b₁₂ (proj₂ b₁₂ []) → x ∈ proj₁ b₃₄ (proj₂ b₃₄ [])
neqzSoundLem₂ NormalMode v init x (here px) = there (there (here px))
neqzSoundLem₂ PostponedMode v init x (here px) = there (there (here px))

{-
neqzOutputLook : ∀ (r : WriterMode)
  → ∀ (v : Var) → (sol : List (Var × ℕ))
  → ∀ init →
  let result = neqz v ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → Σ′ ℕ (λ val → ListLookup (output result) solution
-}


neqzSound : ∀ (r : WriterMode)
  → ∀ (v : Var) → (val : ℕ) → (sol : List (Var × ℕ))
  → ListLookup v sol val
  → ∀ (init : ℕ) → 
  let result = neqz v ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol (neqzFunc val)
neqzSound r v val sol vIsVal init isSol
    with addSound r (IMul onef init v onef (suc init)) sol (2 + init)
    (let b₁₂ = writerOutput
                  (add (IMul onef init v onef (suc init))
                    ((r , prime) , suc (suc init)))
         b₃₄ = writerOutput (neqz v ((r , prime) , init))
     in 
       BuilderProdSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄) (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (neqzSoundLem₁ r v init) isSol)
       | addSound r (IMul onef (suc init) v onef v) sol (2 + init)
           (let b₁₂ = writerOutput
                       (add (IMul onef (suc init) v onef v) ((r , prime) , suc (suc init)))
                b₃₄ = writerOutput (neqz v ((r , prime) , init))
            in BuilderProdSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄) (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (neqzSoundLem₂ r v init) isSol)
neqzSound r v val sol vIsVal init isSol
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



lorFunc : ℕ → ℕ → ℕ
lorFunc a b with ℕtoF a ≟F zerof
lorFunc a b | yes p with ℕtoF b ≟F zerof
lorFunc a b | yes p | yes p₁ = 0
lorFunc a b | yes p | no ¬p = 1
lorFunc a b | no ¬p = 1


orFuncIsBoolStrict : ∀ a b → isBoolStrict (lorFunc a b)
orFuncIsBoolStrict a b with ℕtoF a ≟F zerof
orFuncIsBoolStrict a b | yes p with ℕtoF b ≟F zerof
orFuncIsBoolStrict a b | yes p | yes p₁ = isZeroS refl
orFuncIsBoolStrict a b | yes p | no ¬p = isOneS refl
orFuncIsBoolStrict a b | no ¬p = isOneS refl

orFuncIsBool : ∀ a b → isBool (lorFunc a b)
orFuncIsBool a b = isBoolStrict→isBool (orFuncIsBoolStrict a b)

lorSoundLem₁ : ∀ init sol val val' varVal₃ → isBool val → isBool val' → (hyp : (ℕtoF val +F (ℕtoF val' +F ((-F (ℕtoF val *F ℕtoF val')) +F (-F ℕtoF varVal₃)))) ≡ zerof) → ListLookup (suc init) sol varVal₃ → ListLookup (suc init) sol (lorFunc val val')
lorSoundLem₁ init sol val val' varVal₃ valBool val'Bool hyp look₁ with ℕtoF val ≟F zerof
lorSoundLem₁ init sol val val' varVal₃ valBool val'Bool hyp look₁ | yes p with ℕtoF val' ≟F zerof
lorSoundLem₁ init sol val val' varVal₃ valBool val'Bool hyp look₁ | yes p | yes p₁ rewrite p | p₁
                                                                        | +-identityˡ (zerof +F ((-F (zerof *F zerof)) +F (-F ℕtoF varVal₃)))
                                                                        | *-zeroˡ zerof
                                                                        | -zero≡zero
                                                                        | +-identityˡ (-F ℕtoF varVal₃)
                                                                        | +-identityˡ (-F ℕtoF varVal₃) = ListLookup-Respects-≈ (suc init) sol varVal₃ zero lem look₁
     where
       lem : varVal₃ ≈ 0
       lem with cong (_+F_ (ℕtoF varVal₃)) hyp
       ... | t rewrite +-invʳ (ℕtoF varVal₃)
                     | +-identityʳ (ℕtoF varVal₃) = sq (trans (sym t) (sym ℕtoF-0≡0))
lorSoundLem₁ init sol val val' varVal₃ valBool val'Bool hyp look₁ | yes p | no ¬p rewrite p
                                                                       | *-zeroˡ (ℕtoF val')
                                                                       | -zero≡zero
                                                                       | +-identityˡ (-F ℕtoF varVal₃) with val'Bool
... | isZero .val' prf = ⊥-elim′ (¬p prf)
... | isOne .val' prf rewrite prf
                            | +-identityˡ (onef +F (-F ℕtoF varVal₃))
                            with cong (λ x → x +F (ℕtoF varVal₃)) hyp
... | hyp₁ = ListLookup-Respects-≈  (suc init) sol _ _ lem look₁
      where
        open ≡-Reasoning
        lem : varVal₃ ≈ 1
        lem = sq (
            begin
                ℕtoF varVal₃
            ≡⟨ sym (+-identityˡ (ℕtoF varVal₃)) ⟩
               zerof +F ℕtoF varVal₃
            ≡⟨ sym hyp₁ ⟩
               (onef +F (-F ℕtoF varVal₃)) +F ℕtoF varVal₃
            ≡⟨ +-assoc onef (-F (ℕtoF varVal₃)) (ℕtoF varVal₃) ⟩
               onef +F ((-F (ℕtoF varVal₃)) +F ℕtoF varVal₃)
            ≡⟨ cong (_+F_ onef) (+-invˡ (ℕtoF varVal₃)) ⟩
               onef +F zerof
            ≡⟨ +-identityʳ onef ⟩
               onef
            ≡⟨ sym ℕtoF-1≡1 ⟩
                ℕtoF 1
            ∎)
lorSoundLem₁ init sol val val' varVal₃ (isZero .val prf) val'Bool hyp look₁ | no ¬p = ⊥-elim′ (¬p prf)
lorSoundLem₁ init sol val val' varVal₃ (isOne .val prf) (isZero .val' prf') hyp look₁ | no ¬p rewrite prf | prf'
                                                                                                    | *-zeroʳ onef
                                                                                                    | -zero≡zero
                                                                                                    | +-identityˡ (-F ℕtoF varVal₃)
                                                                                                    | +-identityˡ (-F ℕtoF varVal₃) = ListLookup-Respects-≈ (suc init) sol _ _ (sq (trans (sym (a-b≡zero→a≡b hyp)) (sym ℕtoF-1≡1))) look₁
lorSoundLem₁ init sol val val' varVal₃ (isOne .val prf) (isOne .val' prf') hyp look₁ | no ¬p rewrite prf | prf'
                                                                                                   | *-identityˡ onef
                                                                                                   | sym (+-assoc onef (-F onef) (-F (ℕtoF varVal₃)))
                                                                                                   | +-invʳ onef
                                                                                                   | +-identityˡ (-F ℕtoF varVal₃) = ListLookup-Respects-≈ (suc init) sol _ _ (sq (trans (sym (a-b≡zero→a≡b hyp)) (sym ℕtoF-1≡1))) look₁

lorSoundLem₂ : ∀ r v v' init →
  let b₁₂ = writerOutput (add (IMul onef v v' onef init) ((r , prime) , suc (suc init)))
      b₃₄ = writerOutput (lor v v' ((r , prime) , init))
  in ∀ x → x ∈ proj₁ b₁₂ (proj₂ b₁₂ []) → x ∈ proj₁ b₃₄ (proj₂ b₃₄ [])
lorSoundLem₂ NormalMode v v' init x (here px) = here px
lorSoundLem₂ PostponedMode v v' init x (here px) = here px

lorSoundLem₃ : ∀ r v v' init →
  let b₁₂ = writerOutput (add (IAdd zerof
                                   ((onef , v) ∷ (onef , v') ∷ ((-F onef) , init) ∷ ((-F onef) , 1 + init) ∷ []))
                              ((r , prime) , suc (suc init)))
      b₃₄ = writerOutput (lor v v' ((r , prime) , init))
  in ∀ x → x ∈ proj₁ b₁₂ (proj₂ b₁₂ []) → x ∈ proj₁ b₃₄ (proj₂ b₃₄ [])
lorSoundLem₃ NormalMode v v' init x (here px) = there (here px)
lorSoundLem₃ PostponedMode v v' init x (here px) = there (here px)

lorSound : ∀ (r : WriterMode)
  → (v v' : Var) → (val val' : ℕ)
  → (sol : List (Var × ℕ))
  → ListLookup v sol val
  → ListLookup v' sol val'
  → isBool val → isBool val'
  → ∀ (init : ℕ) →
  let result = lor v v' ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol (lorFunc val val') 
lorSound r v v' val val' sol look₁ look₂ valBool val'Bool init isSol
    with addSound r (IMul onef v v' onef init) sol (2 + init)
           (let b₁₂ = writerOutput (add (IMul onef v v' onef init) ((r , prime) , suc (suc init)))
                b₃₄ = writerOutput (lor v v' ((r , prime) , init))
            in BuilderProdSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄)
                 (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (lorSoundLem₂ r v v' init) isSol)
       | addSound r (IAdd zerof ((onef , v) ∷ (onef , v') ∷ (-F onef , init) ∷ (-F onef , (1 + init)) ∷ [])) sol (2 + init)
           (let b₁₂ = writerOutput (add
                                      (IAdd zerof
                                       ((onef , v) ∷
                                        (onef , v') ∷ ((-F onef) , init) ∷ ((-F onef) , 1 + init) ∷ []))
                                      ((r , prime) , suc (suc init)))
                b₃₄ = writerOutput (lor v v' ((r , prime) , init))
            in BuilderProdSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄)
                 (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (lorSoundLem₃ r v v' init) isSol)
lorSound r v v' val val' sol look₁ look₂ valBool val'Bool init isSol | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅
  with ListLookup-≈ x₇ x₂ | ListLookup-≈ x₆ x₁ | ListLookup-≈ x₁ look₂ | ListLookup-≈ x₄ x | ListLookup-≈ x look₁
... | sq eq₁ | sq eq₂ | sq eq₃ | sq eq₄ | sq eq₅
  rewrite eq₁ | eq₂ | eq₃ | eq₄ | eq₅
        | *-identityˡ (ℕtoF val)
        | *-identityˡ (ℕtoF val')
        | *-identityˡ (ℕtoF eval)
        | -one*f≡-f (ℕtoF eval)
        | -one*f≡-f (ℕtoF varVal₃)
        | +-identityʳ (-F (ℕtoF varVal₃))
        | +-identityʳ (-F (ℕtoF eval))
        | sym x₃
        | +-identityʳ (ℕtoF val +F (ℕtoF val' +F ((-F (ℕtoF val *F ℕtoF val')) +F (-F ℕtoF varVal₃))))
        = lorSoundLem₁ init sol val val' varVal₃ valBool val'Bool x₅ x₈


lorSound₀ : ∀ (r : WriterMode)
  → (v v' : Var) (val val' : ℕ)
  → (sol : List (Var × ℕ))
  → ∀ init
  → ListLookup v sol val
  → ListLookup v' sol val'
  → isBool val
  → isBool val' →
  let result = lor v v' ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol 0
  → Squash (Σ′′ (ListLookup v sol 0) (λ _ → ListLookup v' sol 0))
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look with
       let
          p₁ = add (IMul onef v v' onef init)
          p₂ = add (IAdd zerof ((onef , v) ∷ (onef , v') ∷ (-F onef , init) ∷ (-F onef , (suc init)) ∷ []))
          p₁IsSol = BuilderProdSol->>=⁻₁ p₁ (λ _ → p₂) r (suc (suc init)) sol isSol
          p₂IsSol = BuilderProdSol->>=⁻₂ p₁ (λ _ → p₂) r (suc (suc init)) sol isSol
       in addSound r (IMul onef v v' onef init) sol (suc (suc init)) p₁IsSol
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ with
       let
          p₁ = add (IMul onef v v' onef init)
          p₂ = add (IAdd zerof ((onef , v) ∷ (onef , v') ∷ (-F onef , init) ∷ (-F onef , (suc init)) ∷ []))
          p₁IsSol = BuilderProdSol->>=⁻₁ p₁ (λ _ → p₂) r (suc (suc init)) sol isSol
          p₂IsSol = BuilderProdSol->>=⁻₂ p₁ (λ _ → p₂) r (suc (suc init)) sol isSol
       in addSound r (IAdd zerof ((onef , v) ∷ (onef , v') ∷ (-F onef , init) ∷ (-F onef , (suc init)) ∷ [])) sol _ p₂IsSol
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ with lorSound r v v' val val' sol look₁ look₂ isBool₁ isBool₂ init isSol
... | lorSound with ℕtoF val ≟F zerof
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | yes p with ℕtoF val' ≟F zerof
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | yes p | yes p₁ = sq ((ListLookup-Respects-≈ _ _ _ _ (sq (trans p (sym ℕtoF-0≡0))) look₁) , ListLookup-Respects-≈ _ _ _ _ (sq (trans p₁ (sym ℕtoF-0≡0))) look₂)
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | yes p | no ¬p with ListLookup-≈ lorSound look
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | yes p | no ¬p | sq x₉ = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) (trans x₉ ℕtoF-0≡0)))
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | no ¬p with ℕtoF val' ≟F zerof
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | no ¬p | yes p with ListLookup-≈ lorSound look
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | no ¬p | yes p | sq x₉ = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) (trans x₉ ℕtoF-0≡0)))
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | no ¬p | no ¬p₁ with ListLookup-≈ lorSound look
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | no ¬p | no ¬p₁ | sq x₉ = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) (trans x₉ ℕtoF-0≡0)))



landFunc : ℕ → ℕ → ℕ
landFunc a b with ℕtoF a ≟F zerof
landFunc a b | yes p = 0
landFunc a b | no ¬p with ℕtoF b ≟F zerof
landFunc a b | no ¬p | yes p = 0
landFunc a b | no ¬p | no ¬p₁ = 1



landFunc⁻₁ : ∀ {a} {b} → isBoolStrict a → landFunc a b ≡ 1 → a ≡ 1
landFunc⁻₁ (isZeroS refl) eq with ℕtoF 0 ≟F zerof
landFunc⁻₁ {b = b} (isZeroS refl) eq | no ¬p = ⊥-elim (¬p ℕtoF-0≡0)
landFunc⁻₁ (isOneS refl) eq = refl

landFunc⁻₂ : ∀ {a} {b} → isBoolStrict b → landFunc a b ≡ 1 → b ≡ 1
landFunc⁻₂ {a = a} (isZeroS refl) eq with ℕtoF a ≟F zerof
landFunc⁻₂ {a} (isZeroS refl) eq | no ¬p with ℕtoF 0 ≟F zerof
landFunc⁻₂ {a} (isZeroS refl) eq | no ¬p | no ¬p₁ = ⊥-elim (¬p₁ ℕtoF-0≡0)
landFunc⁻₂ (isOneS refl) eq = refl



landFuncIsBoolStrict : ∀ a b → isBoolStrict (landFunc a b)
landFuncIsBoolStrict a b with ℕtoF a ≟F zerof
landFuncIsBoolStrict a b | yes p = isZeroS refl
landFuncIsBoolStrict a b | no ¬p with ℕtoF b ≟F zerof
landFuncIsBoolStrict a b | no ¬p | yes p = isZeroS refl
landFuncIsBoolStrict a b | no ¬p | no ¬p₁ = isOneS refl

landFuncIsBool : ∀ a b → isBool (landFunc a b)
landFuncIsBool a b = isBoolStrict→isBool (landFuncIsBoolStrict a b)

landSoundLem : ∀ r v v' init →
  let b₁₂ = writerOutput (add (IMul onef v v' onef init) ((r , prime) , suc init))
      b₃₄ = writerOutput (land v v' ((r , prime) , init))
  in ∀ x → x ∈ proj₁ b₁₂ (proj₂ b₁₂ []) → x ∈ proj₁ b₃₄ (proj₂ b₃₄ [])
landSoundLem NormalMode v v' init x (here px) = here px
landSoundLem PostponedMode v v' init x (here px) = here px

landSound : ∀ (r : WriterMode)
  → (v v' : Var) → (val val' : ℕ)
  → (sol : List (Var × ℕ))
  → ListLookup v sol val
  → ListLookup v' sol val'
  → isBool val → isBool val'
  → ∀ (init : ℕ) →
  let result = land v v' ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol (landFunc val val') 
landSound r v v' val val' sol look₁ look₂ valBool val'Bool init isSol with addSound r (IMul onef v v' onef init) sol (suc init)
       (let b₁₂ = writerOutput (add (IMul onef v v' onef init) ((r , prime) , suc init))
            b₃₄ = writerOutput (land v v' ((r , prime) , init))
        in BuilderProdSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄) (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (landSoundLem r v v' init) isSol)
landSound r v v' val val' sol look₁ look₂ valBool val'Bool init isSol | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃
    with ListLookup-≈ x₁ look₂ | ListLookup-≈ x look₁
... | sq eq₁ | sq eq₂
  rewrite eq₁ | eq₂
        | *-identityˡ (ℕtoF val)
        | *-identityˡ (ℕtoF eval) = lem valBool val'Bool
    where



      lem : isBool val → isBool val' → ListLookup init sol (landFunc val val')
      lem valBool val'Bool with ℕtoF val ≟F zerof
      lem valBool val'Bool | yes p rewrite p | *-zeroˡ (ℕtoF val') = ListLookup-Respects-≈ _ _ _ _ (sq (trans (sym x₃) (sym ℕtoF-0≡0))) x₂
      lem valBool val'Bool | no ¬p with ℕtoF val' ≟F zerof
      lem valBool val'Bool | no ¬p | yes p rewrite p | *-zeroʳ (ℕtoF val) = ListLookup-Respects-≈ _ _ _ _ (sq (trans (sym x₃) (sym ℕtoF-0≡0))) x₂
      lem (isZero n x) (isZero n₁ x₁) | no ¬p | no ¬p₁ = ⊥-elim′ (¬p x)
      lem (isZero n x) (isOne n₁ x₁) | no ¬p | no ¬p₁ = ⊥-elim′ (¬p x)
      lem (isOne n x) (isZero n₁ x₁) | no ¬p | no ¬p₁ = ⊥-elim′ (¬p₁ x₁)
      lem (isOne n x) (isOne n₁ x₁) | no ¬p | no ¬p₁ rewrite x | x₁ | *-identityˡ onef = ListLookup-Respects-≈ _ _ _ _ (sq (trans (sym x₃) (sym ℕtoF-1≡1))) x₂
{-
v bval[x] val[look₁]
v' cval[x₁] val'[look₂]
init eval[x₂]
-}

notFunc : ℕ → ℕ
notFunc a with ℕtoF a ≟F zerof
notFunc a | yes p = 1
notFunc a | no ¬p = 0


notFuncIsBoolStrict : ∀ n → isBoolStrict (notFunc n)
notFuncIsBoolStrict n with ℕtoF n ≟F zerof
notFuncIsBoolStrict n | yes p = isOneS refl
notFuncIsBoolStrict n | no ¬p = isZeroS refl

notFuncIsBool : ∀ n → isBool (notFunc n)
notFuncIsBool n = isBoolStrict→isBool (notFuncIsBoolStrict n)

lnotSoundLem : ∀ r v init →
  let b₁₂ = writerOutput (add (IAdd onef (((-F onef) , v) ∷ ((-F onef) , init) ∷ [])) ((r , prime) , suc init))
      b₃₄ = writerOutput (lnot v ((r , prime) , init))
  in ∀ x → x ∈ proj₁ b₁₂ (proj₂ b₁₂ []) → x ∈ proj₁ b₃₄ (proj₂ b₃₄ [])
lnotSoundLem NormalMode v init x (here px) = here px
lnotSoundLem PostponedMode v init x (here px) = here px

lnotSound : ∀ (r : WriterMode)
  → (v : Var) → (val : ℕ)
  → (sol : List (Var × ℕ))
  → ListLookup v sol val
  → isBool val
  → ∀ (init : ℕ) →
  let result = lnot v ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol (notFunc val) 
lnotSound r v val sol look₁ valBool init isSol
  with addSound r (IAdd onef ((-F onef , v) ∷ (-F onef , init) ∷ [])) sol (suc init)
        (let b₁₂ = writerOutput (add (IAdd onef (((-F onef) , v) ∷ ((-F onef) , init) ∷ [])) ((r , prime) , suc init))
             b₃₄ = writerOutput (lnot v ((r , prime) , init))
         in BuilderProdSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄) (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (lnotSoundLem r v init) isSol)
lnotSound r v val sol look₁ valBool init isSol | addSol (LinearCombValCons .((Field.- field') (Field.one field')) .v varVal x (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₁ x₂ LinearCombValBase)) x₁ rewrite -one*f≡-f (ℕtoF varVal)
                                         | -one*f≡-f (ℕtoF varVal₁)
                                         | +-identityʳ (-F ℕtoF varVal₁)
    with ListLookup-≈ x look₁
... | sq eq₁
    rewrite eq₁ = lem valBool
          where
             lem : isBool val → ListLookup init sol (notFunc val)
             lem valBool with ℕtoF val ≟F zerof
             lem valBool | yes p rewrite p | -zero≡zero
                                       | +-identityˡ (-F (ℕtoF varVal₁))
                                       | +-comm (-F ℕtoF varVal₁) onef = ListLookup-Respects-≈ _ _ _ _ (sq (trans (sym (a-b≡zero→a≡b x₁)) (sym ℕtoF-1≡1))) x₂
             lem (isZero n x) | no ¬p = ⊥-elim′ (¬p x)
             lem (isOne n x) | no ¬p rewrite x | +-comm (-F onef) (-F (ℕtoF varVal₁))
                                           | +-assoc (-F ℕtoF varVal₁) (-F onef) onef
                                           | +-invˡ onef | +-identityʳ (-F (ℕtoF varVal₁))
                                           = ListLookup-Respects-≈ _ _ _ _ (sq (trans (-≡zero→≡zero x₁) (sym ℕtoF-0≡0))) x₂
{-
init varVal₁[x₂]
v varVal[x] val[look₁]

-}

limpFunc : ℕ → ℕ → ℕ
limpFunc a b = lorFunc (notFunc a) b

limpFuncImp : ∀ {a} {b} → a ≡ 1 → isBoolStrict b → limpFunc a b ≡ 1 → b ≡ 1
limpFuncImp refl (isZeroS refl) eq₂ with ℕtoF 1 ≟F zerof
limpFuncImp refl (isZeroS refl) eq₂ | yes p = ⊥-elim (onef≠zerof (trans (sym ℕtoF-1≡1) p))
limpFuncImp refl (isZeroS refl) eq₂ | no ¬p with ℕtoF 0 ≟F zerof
limpFuncImp refl (isZeroS refl) eq₂ | no ¬p | yes p with ℕtoF 0 ≟F zerof
limpFuncImp refl (isZeroS refl) eq₂ | no ¬p | yes p | no ¬p₁ = ⊥-elim (¬p₁ ℕtoF-0≡0)
limpFuncImp refl (isZeroS refl) eq₂ | no ¬p | no ¬p₁ = ⊥-elim (¬p₁ ℕtoF-0≡0)
limpFuncImp {b = b} refl (isOneS refl) eq₂ = refl

limpFuncIsBool : ∀ a b → isBool (limpFunc a b)
limpFuncIsBool a b = orFuncIsBool (notFunc a) b

limpFuncIsBoolStrict : ∀ a b → isBoolStrict (limpFunc a b)
limpFuncIsBoolStrict a b = orFuncIsBoolStrict (notFunc a) b

limpSoundLem₁ : ∀ r init sol v v' → BuilderProdSol (writerOutput (limp v v' ((r , prime) , init))) sol
                  → BuilderProdSol (writerOutput (lnot v ((r , prime) , init))) sol
limpSoundLem₁ r init sol v v' isSol = BuilderProdSol->>=⁻₁ (lnot v) (λ notV → lor notV v') r init sol isSol  


limpSound : ∀ (r : WriterMode)
  → (v v' : Var) → (val val' : ℕ)
  → (sol : List (Var × ℕ))
  → ListLookup v sol val
  → ListLookup v' sol val'
  → isBool val → isBool val'
  → ∀ (init : ℕ) →
  let result = limp v v' ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol (limpFunc val val') 
limpSound r v v' val val' sol look₁ look₂ valBool val'Bool init isSol
    with lnotSound r v val sol look₁ valBool init (limpSoundLem₁ r init sol v v' isSol)
... | sound₁ = lorSound r init v' (notFunc val) val' sol sound₁ look₂ (notFuncIsBool val) val'Bool
                 (varOut (lnot v ((r , prime) , init)))
                    (BuilderProdSol->>=⁻₂ (lnot v) (λ notV → lor notV v') r init sol isSol)


neqzIsBool : ∀ (r : WriterMode)
  → (v : Var)
  → (sol : List (Var × ℕ))
  → ∀ init →
  let result = neqz v ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → Squash (∃ (λ val → Σ′ (isBool val) (λ _ → ListLookup (output result) sol val)))
neqzIsBool r v sol init isSol
    with
      let p₄₄ = add (Hint (neqzHint prime v init (suc init)))
          p₅₅ = add (IMul onef init v onef (suc init))
          p₅₇ = λ _ → do
            add (IMul onef init v onef (suc init))
            add (IMul onef (suc init) v onef v)
            return (suc init)
          p₆₇ = λ _ → do
            add (IMul onef (suc init) v onef v)
            return (suc init)
          p₅₇IsSol = BuilderProdSol->>=⁻₂ p₄₄ p₅₇ r _ sol isSol
          p₅₅IsSol = BuilderProdSol->>=⁻₁ p₅₅ p₆₇ r _ sol p₅₇IsSol
      in addSound r (IMul onef init v onef (suc init)) sol _ p₅₅IsSol
neqzIsBool r v sol init isSol | multSol .(Field.one field') .init bval .v cval .(Field.one field') .(suc init) eval x x₁ x₂ x₃
    with
      let p₄₄ = add (Hint (neqzHint prime v init (suc init)))
          p₅₅ = add (IMul onef init v onef (suc init))
          p₅₇ = λ _ → do
            add (IMul onef init v onef (suc init))
            add (IMul onef (suc init) v onef v)
            return (suc init)
          p₆₇ = λ _ → do
            add (IMul onef (suc init) v onef v)
            return (suc init)
          p₅₇IsSol = BuilderProdSol->>=⁻₂ p₄₄ p₅₇ r _ sol isSol
          p₅₅IsSol = BuilderProdSol->>=⁻₁ p₅₅ p₆₇ r _ sol p₅₇IsSol
          p₆₇IsSol = BuilderProdSol->>=⁻₂ p₅₅ p₆₇ r _ sol p₅₇IsSol
      in addSound r (IMul onef (suc init) v onef v) sol _ p₆₇IsSol
neqzIsBool r v sol init isSol | multSol .(Field.one field') .init bval .v cval .(Field.one field') .(suc init) eval x x₁ x₂ x₃ | multSol .(Field.one field') .(suc init) bval₁ .v cval₁ .(Field.one field') .v eval₁ x₄ x₅ x₆ x₇
    with ListLookup-≈ x₄ x₂ | ListLookup-≈ x₅ x₆ | ListLookup-≈ x₆ x₁
... | sq t₁ | sq t₂ | sq t₃ rewrite t₁ | t₂ | t₃ | *-identityˡ (ℕtoF bval)
                                  | *-identityˡ (ℕtoF eval) | *-identityˡ (ℕtoF cval)
    with ℕtoF cval ≟F zerof
... | yes p rewrite p | *-zeroʳ (ℕtoF bval) = sq (eval , (isZero _ (sym x₃)) , x₂)
... | no ¬p with cong (λ t → t *F (1F/ ℕtoF cval)) x₇
... | eq rewrite *-assoc (ℕtoF eval) (ℕtoF cval) (1F/ ℕtoF cval)
               | *-invʳ _ ¬p
               | *-identityʳ (ℕtoF eval) = sq (eval , ((isOne _ eq) , x₂))

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


neqzSound₀ : ∀ (r : WriterMode)
  → (v : Var)
  → (sol : List (Var × ℕ))
  → ListLookup 0 sol 1
  → ∀ init →
  let result = neqz v ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol 0
  → Squash (∃ (λ val → (Σ′′ (ListLookup v sol val) (λ _ → 0 ≈ val))))
neqzSound₀ r v sol tri init isSol look
    with
      let p₄₄ = add (Hint (neqzHint prime v init (suc init)))
          p₅₅ = add (IMul onef init v onef (suc init))
          p₅₇ = λ _ → do
            add (IMul onef init v onef (suc init))
            add (IMul onef (suc init) v onef v)
            return (suc init)
          p₆₇ = λ _ → do
            add (IMul onef (suc init) v onef v)
            return (suc init)
          p₅₇IsSol = BuilderProdSol->>=⁻₂ p₄₄ p₅₇ r _ sol isSol
          p₅₅IsSol = BuilderProdSol->>=⁻₁ p₅₅ p₆₇ r _ sol p₅₇IsSol
      in addSound r (IMul onef init v onef (suc init)) sol _ p₅₅IsSol
neqzSound₀ r v sol tri init isSol look | multSol .(Field.one field') .init bval .v cval .(Field.one field') .(suc init) eval x x₁ x₂ x₃
    with
      let p₄₄ = add (Hint (neqzHint prime v init (suc init)))
          p₅₅ = add (IMul onef init v onef (suc init))
          p₅₇ = λ _ → do
            add (IMul onef init v onef (suc init))
            add (IMul onef (suc init) v onef v)
            return (suc init)
          p₆₇ = λ _ → do
            add (IMul onef (suc init) v onef v)
            return (suc init)
          p₅₇IsSol = BuilderProdSol->>=⁻₂ p₄₄ p₅₇ r _ sol isSol
          p₅₅IsSol = BuilderProdSol->>=⁻₁ p₅₅ p₆₇ r _ sol p₅₇IsSol
          p₆₇IsSol = BuilderProdSol->>=⁻₂ p₅₅ p₆₇ r _ sol p₅₇IsSol
      in addSound r (IMul onef (suc init) v onef v) sol _ p₆₇IsSol
neqzSound₀ r v sol tri init isSol look | multSol .(Field.one field') .init bval .v cval .(Field.one field') .(suc init) eval x x₁ x₂ x₃ | multSol .(Field.one field') .(suc init) bval₁ .v cval₁ .(Field.one field') .v eval₁ x₄ x₅ x₆ x₇
    with ListLookup-≈ x₄ x₂ | ListLookup-≈ x₅ x₆ | ListLookup-≈ x₆ x₁ | ListLookup-≈ x₂ look
... | sq t₁ | sq t₂ | sq t₃ | sq t₄ rewrite t₁ | t₂ | t₃ | *-identityˡ (ℕtoF bval)
                                          | *-identityˡ (ℕtoF eval) | *-identityˡ (ℕtoF cval)
                                          | t₄ = sq (cval , (x₁ , (sq (sym (trans (sym x₇) (subst (λ t → (t *F ℕtoF cval) ≡ t) (sym ℕtoF-0≡0) (*-zeroˡ (ℕtoF cval))))))))



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
lnotSound₁ : ∀ (r : WriterMode) v val sol init
  → ListLookup v sol val
  → isBool val →
  let result = lnot v ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol 1
  → ListLookup v sol 0
lnotSound₁ r v val sol init look isBool isSol look₁ with addSound r (IAdd onef ((-F onef , v) ∷ (-F onef , init) ∷ [])) sol (suc init) isSol
lnotSound₁ r v val sol init look isBool isSol look₁ | addSol (LinearCombValCons .((Field.- field') (Field.one field')) .v varVal x (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₁ x₂ LinearCombValBase)) x₁
  with ListLookup-≈ x look | ListLookup-≈ x₂ look₁
... | sq p₁ | sq p₂ rewrite p₁ | p₂ | -one*f≡-f (ℕtoF val)
                          | -one*f≡-f (ℕtoF 1)
                          | +-identityʳ (-F (ℕtoF 1))
                          | +-assoc (-F (ℕtoF val)) (-F (ℕtoF 1)) onef
                          = ListLookup-Respects-≈  _ _ _ _ (sq (trans (-≡zero→≡zero (subst (λ t → t ≡ zerof) (+-identityʳ (-F ℕtoF val)) (subst (λ t → ((-F ℕtoF val) +F t) ≡ zerof) (+-invˡ (ℕtoF 1)) (subst (λ t → ((-F (ℕtoF val)) +F ((-F (ℕtoF 1)) +F t)) ≡ zerof) (sym ℕtoF-1≡1) x₁)))) (sym ℕtoF-0≡0))) look



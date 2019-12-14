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
module Satisfiability.SourceIntermediate.LogicGates (f : Set) (_≟F_ : Decidable {A = f} _≡_) (field' : Field f) (isField : IsField f field')
     (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f)
        (ℕtoF-1≡1 : ℕtoF 1 ≡ Field.one field')
        (ℕtoF-0≡0 : ℕtoF 0 ≡ Field.zero field') (prime : ℕ) (isPrime : Prime prime) where

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

neqzFunc : ℕ → ℕ
neqzFunc n with ℕtoF n ≟F zerof
neqzFunc n | yes p = 0
neqzFunc n | no ¬p = 1

neqzFuncIsBool : ∀ n → isBool (neqzFunc n)
neqzFuncIsBool n with ℕtoF n ≟F zerof
... | yes p = isZero _ ℕtoF-0≡0
... | no p = isOne _ ℕtoF-1≡1

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


neqzSound : ∀ (r : WriterMode)
  → ∀ (v : Var) → (val : ℕ) → (solution' : List (Var × ℕ))
  → ListLookup v solution' val
  → ∀ (init : ℕ) → 
  let result = neqz v ((r , prime) , init)
  in BuilderProdSol (writerOutput result) solution'
  → ListLookup (output result) solution' (neqzFunc val)
neqzSound r v val solution' vIsVal init isSol
    with addSound r (IMul onef init v onef (suc init)) solution' (2 + init)
    (let b₁₂ = writerOutput
                  (add (IMul onef init v onef (suc init))
                    ((r , prime) , suc (suc init)))
         b₃₄ = writerOutput (neqz v ((r , prime) , init))
     in 
       BuilderProdSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄) (proj₂ b₃₄) b₁₂ b₃₄ solution' refl refl (neqzSoundLem₁ r v init) isSol)
       | addSound r (IMul onef (suc init) v onef v) solution' (2 + init)
           (let b₁₂ = writerOutput
                       (add (IMul onef (suc init) v onef v) ((r , prime) , suc (suc init)))
                b₃₄ = writerOutput (neqz v ((r , prime) , init))
            in BuilderProdSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄) (proj₂ b₃₄) b₁₂ b₃₄ solution' refl refl (neqzSoundLem₂ r v init) isSol)
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



lorFunc : ℕ → ℕ → ℕ
lorFunc a b with ℕtoF a ≟F zerof
lorFunc a b | yes p with ℕtoF b ≟F zerof
lorFunc a b | yes p | yes p₁ = 0
lorFunc a b | yes p | no ¬p = 1
lorFunc a b | no ¬p = 1

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
  → (solution' : List (Var × ℕ))
  → ListLookup v solution' val
  → ListLookup v' solution' val'
  → isBool val → isBool val'
  → ∀ (init : ℕ) →
  let result = lor v v' ((r , prime) , init)
  in BuilderProdSol (writerOutput result) solution'
  → ListLookup (output result) solution' (lorFunc val val') 
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


{-
init varVal₂[x₇] eval[x₂]
(suc init) varVal₃[x₈]
v' varVal₁[x₆] cval[x₁] val'[look₂]
v varVal[x₄] bval[x] val[look₁]
-}

andFunc : ℕ → ℕ → ℕ
andFunc a b with ℕtoF a ≟F zerof
andFunc a b | yes p = 0
andFunc a b | no ¬p with ℕtoF b ≟F zerof
andFunc a b | no ¬p | yes p = 0
andFunc a b | no ¬p | no ¬p₁ = 1

landSoundLem : ∀ r v v' init →
  let b₁₂ = writerOutput (add (IMul onef v v' onef init) ((r , prime) , suc init))
      b₃₄ = writerOutput (land v v' ((r , prime) , init))
  in ∀ x → x ∈ proj₁ b₁₂ (proj₂ b₁₂ []) → x ∈ proj₁ b₃₄ (proj₂ b₃₄ [])
landSoundLem NormalMode v v' init x (here px) = here px
landSoundLem PostponedMode v v' init x (here px) = here px

landSound : ∀ (r : WriterMode)
  → (v v' : Var) → (val val' : ℕ)
  → (solution' : List (Var × ℕ))
  → ListLookup v solution' val
  → ListLookup v' solution' val'
  → isBool val → isBool val'
  → ∀ (init : ℕ) →
  let result = land v v' ((r , prime) , init)
  in BuilderProdSol (writerOutput result) solution'
  → ListLookup (output result) solution' (andFunc val val') 
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



      lem : isBool val → isBool val' → ListLookup init sol (andFunc val val')
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

notFuncBool : ∀ n → isBool (notFunc n)
notFuncBool n with ℕtoF n ≟F zerof
notFuncBool n | yes p = isOne 1 ℕtoF-1≡1
notFuncBool n | no ¬p = isZero zero ℕtoF-0≡0

lnotSoundLem : ∀ r v init →
  let b₁₂ = writerOutput (add (IAdd onef (((-F onef) , v) ∷ ((-F onef) , init) ∷ [])) ((r , prime) , suc init))
      b₃₄ = writerOutput (lnot v ((r , prime) , init))
  in ∀ x → x ∈ proj₁ b₁₂ (proj₂ b₁₂ []) → x ∈ proj₁ b₃₄ (proj₂ b₃₄ [])
lnotSoundLem NormalMode v init x (here px) = here px
lnotSoundLem PostponedMode v init x (here px) = here px

lnotSound : ∀ (r : WriterMode)
  → (v : Var) → (val : ℕ)
  → (solution' : List (Var × ℕ))
  → ListLookup v solution' val
  → isBool val
  → ∀ (init : ℕ) →
  let result = lnot v ((r , prime) , init)
  in BuilderProdSol (writerOutput result) solution'
  → ListLookup (output result) solution' (notFunc val) 
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

impFunc : ℕ → ℕ → ℕ
impFunc a b = lorFunc (notFunc a) b

limpSoundLem₁ : ∀ r init sol v v' → BuilderProdSol (writerOutput (limp v v' ((r , prime) , init))) sol
                  → BuilderProdSol (writerOutput (lnot v ((r , prime) , init))) sol
limpSoundLem₁ r init sol v v' isSol = BuilderProdSol->>=⁻₁ (lnot v) (λ notV → lor notV v') r init sol isSol  


limpSound : ∀ (r : WriterMode)
  → (v v' : Var) → (val val' : ℕ)
  → (solution' : List (Var × ℕ))
  → ListLookup v solution' val
  → ListLookup v' solution' val'
  → isBool val → isBool val'
  → ∀ (init : ℕ) →
  let result = limp v v' ((r , prime) , init)
  in BuilderProdSol (writerOutput result) solution'
  → ListLookup (output result) solution' (impFunc val val') 
limpSound r v v' val val' sol look₁ look₂ valBool val'Bool init isSol
    with lnotSound r v val sol look₁ valBool init (limpSoundLem₁ r init sol v v' isSol)
... | sound₁ = lorSound r init v' (notFunc val) val' sol sound₁ look₂ (notFuncBool val) val'Bool
                 (varOut (lnot v ((r , prime) , init)))
                    (BuilderProdSol->>=⁻₂ (lnot v) (λ notV → lor notV v') r init sol isSol)

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
     (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ)
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
open import Compile.SourceR1CS f field' finite showf fToℕ hiding (SI-Monad)
import Compile.SourceR1CS
open Compile.SourceR1CS.SI-Monad f field' finite showf fToℕ


open import Satisfiability.SourceR1CS.Base f _≟F_ field' isField finite showf fToℕ prime isPrime
open import Satisfiability.SourceR1CS.Tactics f _≟F_ field' isField finite showf fToℕ prime isPrime

neqzFunc : f → f
neqzFunc n with n ≟F zerof
neqzFunc n | yes p = zerof
neqzFunc n | no ¬p = onef
{-
private
  open import Agda.Builtin.Reflection
  open import Reflection
  ProgSolTlₙImpl : ℕ → Term → Term
  ProgSolTlₙImpl zero isSolTerm = isSolTerm
  ProgSolTlₙImpl (suc n) isSolTerm = def (quote ProgSol₂) (vArg (ProgSolTlₙImpl n isSolTerm) ∷ [])
  
  macro
    ProgSolTlₙ : Term → ℕ → Term → TC ⊤
    ProgSolTlₙ isSolTerm n t = do
      unify t (ProgSolTlₙImpl n isSolTerm)
-}
test : (r : WriterMode)
  → (v : Var) → (sol : List (Var × f))
  → (init : ℕ)
  → ProgSol (neqz v) r prime init sol
  → ⊤
test r v sol init isSol
  with
  let isSol' = ProgSolTlₙ isSol 4
      imul₁IsSol = ProgSol₁ isSol'
  in addSound imul₁IsSol
... | t = {!!}
{-
neqzSound : ∀ (r : WriterMode)
  → ∀ (v : Var) → (val : ℕ) → (sol : List (Var × ℕ))
  → ListLookup v sol val
  → ∀ (init : ℕ) → 
  let result = neqz v ((r , prime) , init)
  in ConstraintsSol (writerOutput result) sol
  → ListLookup (output result) sol (neqzFunc val)
neqzSound r v val sol vIsVal init isSol
    with addSound r (IMul onef init v onef (suc init)) sol (2 + init)
    (let b₁₂ = writerOutput
                  (add (IMul onef init v onef (suc init))
                    ((r , prime) , suc (suc init)))
         b₃₄ = writerOutput (neqz v ((r , prime) , init))
     in 
       ConstraintsSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄) (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (neqzSoundLem₁ r v init) isSol)
       | addSound r (IMul onef (suc init) v onef v) sol (2 + init)
           (let b₁₂ = writerOutput
                       (add (IMul onef (suc init) v onef v) ((r , prime) , suc (suc init)))
                b₃₄ = writerOutput (neqz v ((r , prime) , init))
            in ConstraintsSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄) (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (neqzSoundLem₂ r v init) isSol)
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

-}
{-
neqzIsBool : ∀ (r : WriterMode)
  → (v : Var)
  → (sol : List (Var × ℕ))
  → ∀ init →
  let result = neqz v ((r , prime) , init)
  in ConstraintsSol (writerOutput result) sol
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
          p₅₇IsSol = ConstraintsSol->>=⁻₂ p₄₄ p₅₇ r _ sol isSol
          p₅₅IsSol = ConstraintsSol->>=⁻₁ p₅₅ p₆₇ r _ sol p₅₇IsSol
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
          p₅₇IsSol = ConstraintsSol->>=⁻₂ p₄₄ p₅₇ r _ sol isSol
          p₅₅IsSol = ConstraintsSol->>=⁻₁ p₅₅ p₆₇ r _ sol p₅₇IsSol
          p₆₇IsSol = ConstraintsSol->>=⁻₂ p₅₅ p₆₇ r _ sol p₅₇IsSol
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



neqzSound₀ : ∀ (r : WriterMode)
  → (v : Var)
  → (sol : List (Var × ℕ))
  → ListLookup 0 sol 1
  → ∀ init →
  let result = neqz v ((r , prime) , init)
  in ConstraintsSol (writerOutput result) sol
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
          p₅₇IsSol = ConstraintsSol->>=⁻₂ p₄₄ p₅₇ r _ sol isSol
          p₅₅IsSol = ConstraintsSol->>=⁻₁ p₅₅ p₆₇ r _ sol p₅₇IsSol
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
          p₅₇IsSol = ConstraintsSol->>=⁻₂ p₄₄ p₅₇ r _ sol isSol
          p₅₅IsSol = ConstraintsSol->>=⁻₁ p₅₅ p₆₇ r _ sol p₅₇IsSol
          p₆₇IsSol = ConstraintsSol->>=⁻₂ p₅₅ p₆₇ r _ sol p₅₇IsSol
      in addSound r (IMul onef (suc init) v onef v) sol _ p₆₇IsSol
neqzSound₀ r v sol tri init isSol look | multSol .(Field.one field') .init bval .v cval .(Field.one field') .(suc init) eval x x₁ x₂ x₃ | multSol .(Field.one field') .(suc init) bval₁ .v cval₁ .(Field.one field') .v eval₁ x₄ x₅ x₆ x₇
    with ListLookup-≈ x₄ x₂ | ListLookup-≈ x₅ x₆ | ListLookup-≈ x₆ x₁ | ListLookup-≈ x₂ look
... | sq t₁ | sq t₂ | sq t₃ | sq t₄ rewrite t₁ | t₂ | t₃ | *-identityˡ (ℕtoF bval)
                                          | *-identityˡ (ℕtoF eval) | *-identityˡ (ℕtoF cval)
                                          | t₄ = sq (cval , (x₁ , (sq (sym (trans (sym x₇) (subst (λ t → (t *F ℕtoF cval) ≡ t) (sym ℕtoF-0≡0) (*-zeroˡ (ℕtoF cval))))))))


lorFunc : ℕ → ℕ → ℕ
lorFunc a b with ℕtoF a ≟F zerof
lorFunc a b | yes p with ℕtoF b ≟F zerof
lorFunc a b | yes p | yes p₁ = 0
lorFunc a b | yes p | no ¬p = 1
lorFunc a b | no ¬p = 1


lorFuncIsBoolStrict : ∀ a b → isBoolStrict (lorFunc a b)
lorFuncIsBoolStrict a b with ℕtoF a ≟F zerof
lorFuncIsBoolStrict a b | yes p with ℕtoF b ≟F zerof
lorFuncIsBoolStrict a b | yes p | yes p₁ = isZeroS refl
lorFuncIsBoolStrict a b | yes p | no ¬p = isOneS refl
lorFuncIsBoolStrict a b | no ¬p = isOneS refl

lorFuncIsBool : ∀ a b → isBool (lorFunc a b)
lorFuncIsBool a b = isBoolStrict→isBool (lorFuncIsBoolStrict a b)

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
  in ConstraintsSol (writerOutput result) sol
  → ListLookup (output result) sol (lorFunc val val') 
lorSound r v v' val val' sol look₁ look₂ valBool val'Bool init isSol
    with addSound r (IMul onef v v' onef init) sol (2 + init)
           (let b₁₂ = writerOutput (add (IMul onef v v' onef init) ((r , prime) , suc (suc init)))
                b₃₄ = writerOutput (lor v v' ((r , prime) , init))
            in ConstraintsSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄)
                 (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (lorSoundLem₂ r v v' init) isSol)
       | addSound r (IAdd zerof ((onef , v) ∷ (onef , v') ∷ (-F onef , init) ∷ (-F onef , (1 + init)) ∷ [])) sol (2 + init)
           (let b₁₂ = writerOutput (add
                                      (IAdd zerof
                                       ((onef , v) ∷
                                        (onef , v') ∷ ((-F onef) , init) ∷ ((-F onef) , 1 + init) ∷ []))
                                      ((r , prime) , suc (suc init)))
                b₃₄ = writerOutput (lor v v' ((r , prime) , init))
            in ConstraintsSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄)
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
  in ConstraintsSol (writerOutput result) sol
  → ListLookup (output result) sol 0
  → Squash (Σ′′ (ListLookup v sol 0) (λ _ → ListLookup v' sol 0))
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look with
       let
          p₁ = add (IMul onef v v' onef init)
          p₂ = add (IAdd zerof ((onef , v) ∷ (onef , v') ∷ (-F onef , init) ∷ (-F onef , (suc init)) ∷ []))
          p₁IsSol = ConstraintsSol->>=⁻₁ p₁ (λ _ → p₂) r (suc (suc init)) sol isSol
          p₂IsSol = ConstraintsSol->>=⁻₂ p₁ (λ _ → p₂) r (suc (suc init)) sol isSol
       in addSound r (IMul onef v v' onef init) sol (suc (suc init)) p₁IsSol
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ with
       let
          p₁ = add (IMul onef v v' onef init)
          p₂ = add (IAdd zerof ((onef , v) ∷ (onef , v') ∷ (-F onef , init) ∷ (-F onef , (suc init)) ∷ []))
          p₁IsSol = ConstraintsSol->>=⁻₁ p₁ (λ _ → p₂) r (suc (suc init)) sol isSol
          p₂IsSol = ConstraintsSol->>=⁻₂ p₁ (λ _ → p₂) r (suc (suc init)) sol isSol
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

landIsBool : ∀ r v v' sol val val'
  → ListLookup v sol val
  → ListLookup v' sol val'
  → isBool val
  → isBool val'
  → ListLookup 0 sol 1
  → ∀ init →
  let result = land v v' ((r , prime) , init)
  in ConstraintsSol (writerOutput result) sol
  → Squash (∃ (λ val'' → Σ′ (isBool val'') (λ _ → ListLookup (output result) sol val'')))
landIsBool r v v' sol val val' look₁ look₂ isBool₁ isBool₂ tri init isSol with addSound r (IMul onef v v' onef init) sol _ isSol
landIsBool r v v' sol val val' look₁ look₂ isBool₁ isBool₂ tri init isSol | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃
    with ListLookup-≈ x look₁ | ListLookup-≈ x₁ look₂
... | sq t₁ | sq t₂ rewrite t₁ | t₂
                          | *-identityˡ (ℕtoF val)
                          | *-identityˡ (ℕtoF eval) = sq (eval , (lem isBool₁ isBool₂ , x₂))
    where
      lem : isBool val → isBool val' → isBool eval
      lem (isZero n x) b₂ rewrite x | *-zeroˡ (ℕtoF val') = isZero eval (sym x₃)
      lem (isOne val x) (isZero n x₁) rewrite x₁ | *-zeroʳ (ℕtoF val) = isZero eval (sym x₃)
      lem (isOne val x) (isOne n x₁) rewrite x | x₁ | *-identityˡ onef = isOne eval (sym x₃)


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
  in ConstraintsSol (writerOutput result) sol
  → ListLookup (output result) sol (landFunc val val') 
landSound r v v' val val' sol look₁ look₂ valBool val'Bool init isSol with addSound r (IMul onef v v' onef init) sol (suc init)
       (let b₁₂ = writerOutput (add (IMul onef v v' onef init) ((r , prime) , suc init))
            b₃₄ = writerOutput (land v v' ((r , prime) , init))
        in ConstraintsSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄) (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (landSoundLem r v v' init) isSol)
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


landSound₁ : ∀ (r : WriterMode)
  → (v v' : Var) (val val' : ℕ)
  → (sol : List (Var × ℕ))
  → ∀ init
  → ListLookup v sol val
  → ListLookup v' sol val'
  → isBool val
  → isBool val' →
  let result = land v v' ((r , prime) , init)
  in ConstraintsSol (writerOutput result) sol
  → ListLookup (output result) sol 1
  → Squash (Σ′′ (ListLookup v sol 1) (λ _ → ListLookup v' sol 1))
landSound₁ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look with addSound r (IMul onef v v' onef init) sol _ isSol
landSound₁ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ with landSound r v v' val val' sol look₁ look₂ isBool₁ isBool₂ init isSol
landSound₁ r v v' val val' sol init look₁ look₂ (isZero .val x₄) (isZero .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ with ℕtoF val ≟F zerof
landSound₁ r v v' val val' sol init look₁ look₂ (isZero .val x₄) (isZero .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | yes p with ListLookup-≈ sound₁ look
... | sq eq = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) (trans (sym eq) ℕtoF-0≡0)))
landSound₁ r v v' val val' sol init look₁ look₂ (isZero .val x₄) (isZero .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | no ¬p = ⊥-elim′ (¬p x₄)
landSound₁ r v v' val val' sol init look₁ look₂ (isZero .val x₄) (isOne .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ with ℕtoF val ≟F zerof
landSound₁ r v v' val val' sol init look₁ look₂ (isZero .val x₄) (isOne .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | yes p with ListLookup-≈ sound₁ look
... | sq eq = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) (trans (sym eq) ℕtoF-0≡0)))
landSound₁ r v v' val val' sol init look₁ look₂ (isZero .val x₄) (isOne .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | no ¬p = ⊥-elim′ (¬p x₄) 
landSound₁ r v v' val val' sol init look₁ look₂ (isOne .val x₄) (isZero .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ with ℕtoF val ≟F zerof
landSound₁ r v v' val val' sol init look₁ look₂ (isOne .val x₄) (isZero .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | yes p with ListLookup-≈ look sound₁
... | sq eq = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) (trans eq ℕtoF-0≡0)))
landSound₁ r v v' val val' sol init look₁ look₂ (isOne .val x₄) (isZero .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | no ¬p with ℕtoF val' ≟F zerof
landSound₁ r v v' val val' sol init look₁ look₂ (isOne .val x₄) (isZero .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | no ¬p | yes p with ListLookup-≈ sound₁ look
landSound₁ r v v' val val' sol init look₁ look₂ (isOne .val x₄) (isZero .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | no ¬p | yes p | sq x₆ = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) (trans (sym x₆) ℕtoF-0≡0)))
landSound₁ r v v' val val' sol init look₁ look₂ (isOne .val x₄) (isZero .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | no ¬p | no ¬p₁ = ⊥-elim′ (¬p₁ x₅)
landSound₁ r v v' val val' sol init look₁ look₂ (isOne .val x₄) (isOne .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ with ℕtoF val ≟F zerof
landSound₁ r v v' val val' sol init look₁ look₂ (isOne .val x₄) (isOne .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | yes p with ListLookup-≈ sound₁ look
landSound₁ r v v' val val' sol init look₁ look₂ (isOne .val x₄) (isOne .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | yes p | sq x₆ = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) (trans (sym x₆) ℕtoF-0≡0)))
landSound₁ r v v' val val' sol init look₁ look₂ (isOne .val x₄) (isOne .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | no ¬p with ℕtoF val' ≟F zerof
landSound₁ r v v' val val' sol init look₁ look₂ (isOne .val x₄) (isOne .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | no ¬p | yes p with ListLookup-≈ sound₁ look
landSound₁ r v v' val val' sol init look₁ look₂ (isOne .val x₄) (isOne .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | no ¬p | yes p | sq x₆ = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) (trans (sym x₆) ℕtoF-0≡0)))
landSound₁ r v v' val val' sol init look₁ look₂ (isOne .val x₄) (isOne .val' x₅) isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | sound₁ | no ¬p | no ¬p₁ = sq ((ListLookup-Respects-≈ _ _ _ _ (sq (trans x₄ (sym ℕtoF-1≡1))) look₁) , (ListLookup-Respects-≈ _ _ _ _ (sq (trans x₅ (sym ℕtoF-1≡1))) look₂))


lnotFunc : ℕ → ℕ
lnotFunc a with ℕtoF a ≟F zerof
lnotFunc a | yes p = 1
lnotFunc a | no ¬p = 0


lnotFuncIsBoolStrict : ∀ n → isBoolStrict (lnotFunc n)
lnotFuncIsBoolStrict n with ℕtoF n ≟F zerof
lnotFuncIsBoolStrict n | yes p = isOneS refl
lnotFuncIsBoolStrict n | no ¬p = isZeroS refl

lnotFuncIsBool : ∀ n → isBool (lnotFunc n)
lnotFuncIsBool n = isBoolStrict→isBool (lnotFuncIsBoolStrict n)

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
  in ConstraintsSol (writerOutput result) sol
  → ListLookup (output result) sol (lnotFunc val) 
lnotSound r v val sol look₁ valBool init isSol
  with addSound r (IAdd onef ((-F onef , v) ∷ (-F onef , init) ∷ [])) sol (suc init)
        (let b₁₂ = writerOutput (add (IAdd onef (((-F onef) , v) ∷ ((-F onef) , init) ∷ [])) ((r , prime) , suc init))
             b₃₄ = writerOutput (lnot v ((r , prime) , init))
         in ConstraintsSolSubsetImp (proj₁ b₁₂) (proj₂ b₁₂) (proj₁ b₃₄) (proj₂ b₃₄) b₁₂ b₃₄ sol refl refl (lnotSoundLem r v init) isSol)
lnotSound r v val sol look₁ valBool init isSol | addSol (LinearCombValCons .((Field.- field') (Field.one field')) .v varVal x (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₁ x₂ LinearCombValBase)) x₁ rewrite -one*f≡-f (ℕtoF varVal)
                                         | -one*f≡-f (ℕtoF varVal₁)
                                         | +-identityʳ (-F ℕtoF varVal₁)
    with ListLookup-≈ x look₁
... | sq eq₁
    rewrite eq₁ = lem valBool
          where
             lem : isBool val → ListLookup init sol (lnotFunc val)
             lem valBool with ℕtoF val ≟F zerof
             lem valBool | yes p rewrite p | -zero≡zero
                                       | +-identityˡ (-F (ℕtoF varVal₁))
                                       | +-comm (-F ℕtoF varVal₁) onef = ListLookup-Respects-≈ _ _ _ _ (sq (trans (sym (a-b≡zero→a≡b x₁)) (sym ℕtoF-1≡1))) x₂
             lem (isZero n x) | no ¬p = ⊥-elim′ (¬p x)
             lem (isOne n x) | no ¬p rewrite x | +-comm (-F onef) (-F (ℕtoF varVal₁))
                                           | +-assoc (-F ℕtoF varVal₁) (-F onef) onef
                                           | +-invˡ onef | +-identityʳ (-F (ℕtoF varVal₁))
                                           = ListLookup-Respects-≈ _ _ _ _ (sq (trans (-≡zero→≡zero x₁) (sym ℕtoF-0≡0))) x₂

lnotSound₁ : ∀ (r : WriterMode) v val sol init
  → ListLookup v sol val
  → isBool val →
  let result = lnot v ((r , prime) , init)
  in ConstraintsSol (writerOutput result) sol
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



limpFunc : ℕ → ℕ → ℕ
limpFunc a b = lorFunc (lnotFunc a) b

limpFuncImp : ∀ {a} {b} → a ≡ 1 → isBoolStrict b → limpFunc a b ≡ 1 → b ≡ 1
limpFuncImp refl (isZeroS refl) eq₂ with ℕtoF 1 ≟F zerof
limpFuncImp refl (isZeroS refl) eq₂ | yes p = ⊥-elim (onef≠zerof (trans (sym ℕtoF-1≡1) p))
limpFuncImp refl (isZeroS refl) eq₂ | no ¬p with ℕtoF 0 ≟F zerof
limpFuncImp refl (isZeroS refl) eq₂ | no ¬p | yes p with ℕtoF 0 ≟F zerof
limpFuncImp refl (isZeroS refl) eq₂ | no ¬p | yes p | no ¬p₁ = ⊥-elim (¬p₁ ℕtoF-0≡0)
limpFuncImp refl (isZeroS refl) eq₂ | no ¬p | no ¬p₁ = ⊥-elim (¬p₁ ℕtoF-0≡0)
limpFuncImp {b = b} refl (isOneS refl) eq₂ = refl

limpFuncIsBool : ∀ a b → isBool (limpFunc a b)
limpFuncIsBool a b = lorFuncIsBool (lnotFunc a) b

limpFuncIsBoolStrict : ∀ a b → isBoolStrict (limpFunc a b)
limpFuncIsBoolStrict a b = lorFuncIsBoolStrict (lnotFunc a) b

limpSoundLem₁ : ∀ r init sol v v' → ConstraintsSol (writerOutput (limp v v' ((r , prime) , init))) sol
                  → ConstraintsSol (writerOutput (lnot v ((r , prime) , init))) sol
limpSoundLem₁ r init sol v v' isSol = ConstraintsSol->>=⁻₁ (lnot v) (λ notV → lor notV v') r init sol isSol  


limpSound : ∀ (r : WriterMode)
  → (v v' : Var) → (val val' : ℕ)
  → (sol : List (Var × ℕ))
  → ListLookup v sol val
  → ListLookup v' sol val'
  → isBool val → isBool val'
  → ∀ (init : ℕ) →
  let result = limp v v' ((r , prime) , init)
  in ConstraintsSol (writerOutput result) sol
  → ListLookup (output result) sol (limpFunc val val') 
limpSound r v v' val val' sol look₁ look₂ valBool val'Bool init isSol
    with lnotSound r v val sol look₁ valBool init (limpSoundLem₁ r init sol v v' isSol)
... | sound₁ = lorSound r init v' (lnotFunc val) val' sol sound₁ look₂ (lnotFuncIsBool val) val'Bool
                 (varOut (lnot v ((r , prime) , init)))
                    (ConstraintsSol->>=⁻₂ (lnot v) (λ notV → lor notV v') r init sol isSol)





-}

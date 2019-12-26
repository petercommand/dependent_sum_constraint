{-# OPTIONS --prop #-}

open import Agda.Builtin.Nat

open import Data.Bool
open import Data.Empty
open import Data.Field
open import Data.Finite
open import Data.List hiding (lookup; head; splitAt)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Occ
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Primality
import Data.Nat.Properties
module ℕP = Data.Nat.Properties
open import Data.Nat.Properties2
open import Data.Product hiding (map)
open import Data.ProductPrime
open import Data.Vec hiding (_>>=_; splitAt) renaming (_++_ to _V++_)
open import Data.Vec.AllProp
open import Data.Vec.Repeat
open import Data.Vec.Split
open import Data.Squash
open import Data.String hiding (_≈_; _≟_; _++_)
open import Data.Sum
open import Data.Unit
open import Function

open import Language.Common

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.HeterogeneousEquality
module HE = Relation.Binary.HeterogeneousEquality
open import Relation.Binary.HeterogeneousEquality.Core
open Relation.Binary.HeterogeneousEquality using (_≅_)
open import Relation.Nullary
module Satisfiability.SourceIntermediate (f : Set) (_≟F_ : Decidable {A = f} _≡_) (field' : Field f) (isField : IsField f field')
     (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f)
        (ℕtoF-1≡1 : ℕtoF 1 ≡ Field.one field')
        (ℕtoF-0≡0 : ℕtoF 0 ≡ Field.zero field')
        (ℕtoF∘fToℕ≡ : ∀ x → ℕtoF (fToℕ x) ≡ x)
        (prime : ℕ) (isPrime : Prime prime)
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
open import Satisfiability.SourceIntermediate.LogicGates f _≟F_ field' isField finite showf fToℕ ℕtoF ℕtoF-1≡1 ℕtoF-0≡0 ℕtoF∘fToℕ≡ prime isPrime onef≠zerof
open import Satisfiability.SourceIntermediate.SimpleComp f _≟F_ field' isField finite showf fToℕ ℕtoF ℕtoF-1≡1 ℕtoF-0≡0 ℕtoF∘fToℕ≡ prime isPrime onef≠zerof



allEqz→All≈0 : ∀ {n} (vec : Vec ℕ n) → allEqzFunc vec ≡ 1 → All (_≈_ 0) vec
allEqz→All≈0 [] eq = []
allEqz→All≈0 (x ∷ vec) eq with ℕtoF x ≟F zerof
allEqz→All≈0 (x ∷ vec) eq | yes p = sq (sym (trans p (sym ℕtoF-0≡0))) ∷ allEqz→All≈0 vec eq

All≈0→allEqz : ∀ {n} (vec : Vec ℕ n) → All (_≈_ 0) vec → Squash (allEqzFunc vec ≡ 1)
All≈0→allEqz .[] [] = sq refl
All≈0→allEqz .(x ∷ _) (_∷_ {x = x} px all₁) with ℕtoF x ≟F zerof
All≈0→allEqz .(x ∷ _) (_∷_ {x = x} px all₁) | yes p = All≈0→allEqz _ all₁
All≈0→allEqz .(x ∷ _) (_∷_ {x = x} (sq px) all₁) | no ¬p = ⊥-elim′ (¬p (trans (sym px) ℕtoF-0≡0))



maxTySplitCorrect : ∀ u val x vec → vec HE.≅ proj₁ (maxTySplit u val x vec) V++ proj₂ (maxTySplit u val x vec)
maxTySplitCorrect u val x vec with splitAtCorrect (tySize (x val)) (subst (Vec ℕ)
        (sym
         (trans
          (ℕP.+-comm (tySize (x val))
           (maxTySizeOver (enum u) x ∸ tySize (x val)))
          (a-b+b≡a (maxTySizeOver (enum u) x)
           (tySize (x val)) (∈→≥ (enum u) x val (enumComplete u val)))))
        vec)
... | eq with splitAt (tySize (x val)) (subst (Vec ℕ)
        (sym
         (trans
          (ℕP.+-comm (tySize (x val))
           (maxTySizeOver (enum u) x ∸ tySize (x val)))
          (a-b+b≡a (maxTySizeOver (enum u) x)
           (tySize (x val)) (∈→≥ (enum u) x val (enumComplete u val)))))
        vec)
... | fst , snd = HE.trans
                    (HE.sym
                     (HE.≡-subst-removable (Vec ℕ)
                      (sym
                       (trans
                        (ℕP.+-comm (tySize (x val))
                         (maxTySizeOver (enum u) x ∸ tySize (x val)))
                        (a-b+b≡a (maxTySizeOver (enum u) x) (tySize (x val))
                         (∈→≥ (enum u) x val (enumComplete u val)))))
                      vec))
                    (HE.trans (≡-to-≅ eq) HE.refl)

ValIsRepr→varEqLit : ∀ u elem val val' → val ≡ val' → ValIsRepr u elem val' → Squash (varEqLitFunc u val elem ≡ 1)

PiPartialRepr→piVarEqLit : ∀ u x eu vec vec' f → vec ≡ vec' → PiPartialRepr u x f eu vec' → Squash (piVarEqLitFunc x eu vec f ≡ 1)
PiPartialRepr→piVarEqLit u x .[] .[] ._ f refl PiRepNil = sq refl
PiPartialRepr→piVarEqLit u x (x₁ ∷ eu) vec vec f refl (PiRepCons x₂ repr refl)
    with splitAtCorrect (tySize (x x₁)) vec
... | split₁
    with splitAt (tySize (x x₁)) vec
... | fst , snd with ValIsRepr→varEqLit (x x₁) (f x₁) fst _ (sym (vecSplit₁ _ fst split₁)) x₂
... | sq ind₁ with PiPartialRepr→piVarEqLit u x eu snd _ f (sym (vecSplit₂ _ _ split₁)) repr
... | sq ind₂ with ℕtoF (varEqLitFunc (x x₁) fst (f x₁)) ≟F zerof
PiPartialRepr→piVarEqLit u x (x₁ ∷ eu) ._ ._ f refl (PiRepCons x₂ repr refl) | split₁ | fst , snd | sq ind₁ | sq ind₂ | yes p = ⊥-elim′ (onef≠zerof (trans (sym (trans (cong ℕtoF ind₁) ℕtoF-1≡1)) p))
PiPartialRepr→piVarEqLit u x (x₁ ∷ eu) ._ ._ f refl (PiRepCons x₂ repr refl) | split₁ | fst , snd | sq ind₁ | sq ind₂ | no ¬p with  ℕtoF (piVarEqLitFunc x eu snd f) ≟F zerof
PiPartialRepr→piVarEqLit u x (x₁ ∷ eu) ._ ._ f refl (PiRepCons x₂ repr refl) | split₁ | fst , snd | sq ind₁ | sq ind₂ | no ¬p | yes p = ⊥-elim′ (onef≠zerof (trans (sym (trans (cong ℕtoF ind₂) ℕtoF-1≡1)) p))
PiPartialRepr→piVarEqLit u x (x₁ ∷ eu) ._ ._ f refl (PiRepCons x₂ repr refl) | split₁ | fst , snd | sq ind₁ | sq ind₂ | no ¬p | no ¬p₁ = sq refl

ValIsRepr→varEqLit .`One .tt .(n ∷ []) .(n ∷ []) refl (`OneValRepr n x) with ℕtoF n ≟F zerof
ValIsRepr→varEqLit .`One .tt .(n ∷ []) .(n ∷ []) refl (`OneValRepr n x) | yes p = sq refl
ValIsRepr→varEqLit .`One .tt .(n ∷ []) .(n ∷ []) refl (`OneValRepr n (sq eq)) | no ¬p = ⊥-elim′ (¬p (trans eq ℕtoF-0≡0))
ValIsRepr→varEqLit .`Two .false .(n ∷ []) .(n ∷ []) refl (`TwoValFalseRepr n x) with ℕtoF n ≟F zerof
ValIsRepr→varEqLit .`Two .false .(n ∷ []) .(n ∷ []) refl (`TwoValFalseRepr n x) | yes p = sq refl
ValIsRepr→varEqLit .`Two .false .(n ∷ []) .(n ∷ []) refl (`TwoValFalseRepr n (sq eq)) | no ¬p = ⊥-elim′ (¬p (trans eq ℕtoF-0≡0))
ValIsRepr→varEqLit .`Two .true .(n ∷ []) .(n ∷ []) refl (`TwoValTrueRepr n (sq eq)) with ℕtoF n ≟F onef
ValIsRepr→varEqLit .`Two .true .(n ∷ []) .(n ∷ []) refl (`TwoValTrueRepr n (sq eq)) | yes p = sq refl
ValIsRepr→varEqLit .`Two .true .(n ∷ []) .(n ∷ []) refl (`TwoValTrueRepr n (sq eq)) | no ¬p = ⊥-elim′ (¬p (trans eq ℕtoF-1≡1))
ValIsRepr→varEqLit .`Base elem .(v' ∷ []) .(v' ∷ []) refl (`BaseValRepr {v' = v'} x) with ℕtoF v' ≟F elem
ValIsRepr→varEqLit .`Base elem .(v' ∷ []) .(v' ∷ []) refl (`BaseValRepr {v' = v'} x) | yes p = sq refl
ValIsRepr→varEqLit .`Base elem .(v' ∷ []) .(v' ∷ []) refl (`BaseValRepr {v' = v'} (sq eq)) | no ¬p = ⊥-elim′ (¬p (trans (sym eq) (ℕtoF∘fToℕ≡ elem)))
ValIsRepr→varEqLit .(`Vec _ 0) .[] .[] .[] refl `VecValBaseRepr = sq refl
ValIsRepr→varEqLit (`Vec u (suc x)) (elem₁ ∷ elem) val ._ refl (`VecValConsRepr repr repr₁ refl)
     with splitAtCorrect (tySize u) val
... | eq
   with splitAt (tySize u) val
... | fst , snd with ValIsRepr→varEqLit u elem₁ fst _ (vecSplit₁ fst _ (sym eq)) repr
... | sq ind₁ with ValIsRepr→varEqLit (`Vec u x) elem snd _ (vecSplit₂ _ _ (sym eq)) repr₁
... | sq ind₂ with ℕtoF (varEqLitFunc u fst elem₁) ≟F zerof
ValIsRepr→varEqLit (`Vec u (suc x)) (elem₁ ∷ elem) ._ ._ refl (`VecValConsRepr repr repr₁ refl) | eq | fst , snd | sq ind₁ | sq ind₂ | yes p rewrite ind₁ = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) p))
ValIsRepr→varEqLit (`Vec u (suc x)) (elem₁ ∷ elem) ._ ._ refl (`VecValConsRepr repr repr₁ refl) | eq | fst , snd | sq ind₁ | sq ind₂ | no ¬p with ℕtoF (varEqLitFunc (`Vec u x) snd elem) ≟F zerof
ValIsRepr→varEqLit (`Vec u (suc x)) (elem₁ ∷ elem) ._ ._ refl (`VecValConsRepr repr repr₁ refl) | eq | fst , snd | sq ind₁ | sq ind₂ | no ¬p | yes p rewrite ind₂ = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) p))
ValIsRepr→varEqLit (`Vec u (suc x)) (elem₁ ∷ elem) ._ ._ refl (`VecValConsRepr repr repr₁ refl) | eq | fst , snd | sq ind₁ | sq ind₂ | no ¬p | no ¬p₁ = sq refl
ValIsRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) val .val refl (`ΣValRepr {_} {vu} x {vxu} {valu} {valxu} valxu+z {valu+valxu+z} repr repr₁ x₁ x₂ refl)
    with splitAtCorrect (tySize u) val
... | split₁₁
    with splitAt (tySize u) val
... | fst , snd
    with maxTySplitCorrect u fstₗ x snd
... | split₂
    with maxTySplit u fstₗ x snd
... | snd₁ , snd₂
    with ValIsRepr→varEqLit u fstₗ fst _ (vecSplit₁ _ _ (sym split₁₁)) repr
... | sq ind₁
    with vecSplit₂ valu fst split₁₁
... | split₁₂
    with ValIsRepr→varEqLit (x fstₗ) sndₗ snd₁ _ (vecSplit₁ _ _ (≅-to-≡ (HE.trans (HE.trans (HE.sym split₂) (≡-to-≅ (sym split₁₂))) x₂))) repr₁
... | sq ind₂ with ℕtoF (varEqLitFunc u fst fstₗ) ≟F zerof
ValIsRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | yes p = ⊥-elim′ (onef≠zerof (trans (trans (sym ℕtoF-1≡1) (sym (cong ℕtoF ind₁))) p))
ValIsRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p with  ℕtoF (varEqLitFunc (x fstₗ) snd₁ sndₗ) ≟F zerof
ValIsRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p | yes p = ⊥-elim′ (onef≠zerof (trans (sym (trans (cong ℕtoF ind₂) ℕtoF-1≡1)) p))
ValIsRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p | no ¬p₁ with ℕtoF 1 ≟F zerof
ValIsRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p | no ¬p₁ | yes p = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) p))
ValIsRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p | no ¬p₁ | no ¬p₂ with ℕtoF (allEqzFunc snd₂) ≟F zerof
ValIsRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p | no ¬p₁ | no ¬p₂ | yes p with All≈0→allEqz _ x₁
... | sq prf rewrite split₁₂
                   | vecSplit₂ valxu snd₁ (≅-to-≡ (HE.trans (HE.sym x₂) split₂))
                   | prf = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) p))
ValIsRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ = sq refl
ValIsRepr→varEqLit (`Π u x) elem val .val refl (`ΠValRepr x .val x₁) = PiPartialRepr→piVarEqLit u x (enum u) val val elem refl x₁ 

enumSigmaCondRestZ : ∀ u eu x fst snd val → val ∈ eu → ValIsRepr u val fst → enumSigmaCondFunc u eu x fst snd ≡ 1 → All (_≈_ 0) (proj₂ (maxTySplit u val x snd))
enumSigmaCondRestZ u .(_ ∷ _) x fst snd val (here refl) isRepr eq with ValIsRepr→varEqLit u val fst fst refl isRepr
... | sq varEqLit≡1 = allEqz→All≈0 (proj₂ (maxTySplit u val x snd)) (andFunc⁻₂ (allEqzFuncIsBoolStrict (proj₂ (maxTySplit u val x snd))) (impFuncImp varEqLit≡1 (andFuncIsBoolStrict (tyCondFunc (x val) (proj₁ (maxTySplit u val x snd)))
       (allEqzFunc (proj₂ (maxTySplit u val x snd)))) (andFunc⁻₁ (impFuncIsBoolStrict (varEqLitFunc u fst val)
       (andFunc (tyCondFunc (x val) (proj₁ (maxTySplit u val x snd)))
        (allEqzFunc (proj₂ (maxTySplit u val x snd)))) ) eq)))
enumSigmaCondRestZ u (_ ∷ eu) x fst snd val (there mem) isRepr eq = enumSigmaCondRestZ u eu x fst snd val mem isRepr (andFunc⁻₂ (enumSigmaCondFuncIsBoolStrict u eu x fst snd) eq)


tyCondFuncRepr : ∀ u → (vec : Vec ℕ (tySize u)) → tyCondFunc u vec ≡ 1 → Squash (∃ (λ elem → ValIsRepr u elem vec))

enumSigmaCondFuncRepr : ∀ u eu x elem val₁ val₂
  → ValIsRepr u elem val₁
  → elem ∈ eu
  → enumSigmaCondFunc u eu x val₁ val₂ ≡ 1
  → Squash (∃ (λ elem₁ → ValIsRepr (x elem) elem₁ (proj₁ (maxTySplit u elem x val₂))))
enumSigmaCondFuncRepr u [] x elem val₁ val₂ isRepr ()
enumSigmaCondFuncRepr u (elem ∷ eu) x elem val₁ val₂ isRepr (here refl) eq with ValIsRepr→varEqLit u elem val₁ val₁ refl isRepr
... | sq repr = tyCondFuncRepr (x elem) (proj₁ (maxTySplit u elem x val₂))
  (andFunc⁻₁ (tyCondFuncIsBoolStrict (x elem) (proj₁
        (splitAt (tySize (x elem))
         (subst (Vec ℕ)
          (sym
           (trans
            (ℕP.+-comm (tySize (x elem))
             (maxTySizeOver (enum u) x ∸ tySize (x elem)))
            (a-b+b≡a (maxTySizeOver (enum u) x) (tySize (x elem))
             (∈→≥ (enum u) x elem (enumComplete u elem)))))
          val₂)))) (impFuncImp repr (andFuncIsBoolStrict  (tyCondFunc (x elem) (proj₁ (maxTySplit u elem x val₂))) (allEqzFunc (proj₂ (maxTySplit u elem x val₂)))) (andFunc⁻₁ (impFuncIsBoolStrict (varEqLitFunc u val₁ elem) (andFunc (tyCondFunc (x elem) (proj₁ (maxTySplit u elem x val₂)))
        (allEqzFunc (proj₂ (maxTySplit u elem x val₂))))) eq)))
enumSigmaCondFuncRepr u (x₁ ∷ eu) x elem val₁ val₂ isRepr (there mem) eq = enumSigmaCondFuncRepr u eu x elem val₁ val₂ isRepr mem (andFunc⁻₂ (enumSigmaCondFuncIsBoolStrict u eu x val₁ val₂) eq)


postulate
  _≟U_ : ∀ {u} → Decidable {A = ⟦ u ⟧} _≡_
{-
_≟U_ : ∀ {u} → Decidable {A = ⟦ u ⟧} _≡_
_≟U_ {`One} tt tt = yes refl
_≟U_ {`Two} false false = yes refl
_≟U_ {`Two} false true = no (λ ())
_≟U_ {`Two} true false = no (λ ())
_≟U_ {`Two} true true = yes refl
_≟U_ {`Base} = _≟F_
_≟U_ {`Vec u zero} [] [] = yes refl
_≟U_ {`Vec u (suc x)} (a ∷ v₁) (b ∷ v₂) with a ≟U b
_≟U_ {`Vec u (suc x)} (a ∷ v₁) (b ∷ v₂) | yes p with v₁ ≟U v₂
_≟U_ {`Vec u (suc x)} (a ∷ v₁) (b ∷ v₂) | yes refl | yes refl = yes refl
_≟U_ {`Vec u (suc x)} (a ∷ v₁) (b ∷ v₂) | yes p | no ¬p = no (λ x₁ → ¬p (cong Data.Vec.tail x₁))
_≟U_ {`Vec u (suc x)} (a ∷ v₁) (b ∷ v₂) | no ¬p = no (λ x₁ → ¬p (cong Data.Vec.head x₁))
_≟U_ {`Σ u x} (a , b) (c , d) with a ≟U c
_≟U_ {`Σ u x} (a , b) (c , d) | yes refl with b ≟U d
_≟U_ {`Σ u x} (a , b) (a , d) | yes refl | yes refl = yes refl
_≟U_ {`Σ u x} (a , b) (a , d) | yes refl | no ¬p = no (λ { refl → ¬p refl })
_≟U_ {`Σ u x} (a , b) (c , d) | no ¬p = no (λ x₁ → ¬p (cong proj₁ x₁))
_≟U_ {`Π u x} p₁ p₂ = {!piToList u x (enum u) p₁ !}
-}

defaultElem : ∀ u → ⟦ u ⟧
defaultElem `One = tt
defaultElem `Two = false
defaultElem `Base = Field.zero field'
defaultElem (`Vec u zero) = []
defaultElem (`Vec u (suc x)) = (defaultElem u) ∷ (defaultElem (`Vec u x))
defaultElem (`Σ u x) = (defaultElem u) , (defaultElem (x (defaultElem u)))
defaultElem (`Π u x) = λ x₁ → defaultElem (x x₁)

trivialFunc : ∀ u (x : ⟦ u ⟧ → U) → (val : ⟦ u ⟧) → ⟦ x val ⟧
trivialFunc u x val = defaultElem (x val)

updateFunc : ∀ u (x : ⟦ u ⟧ → U) → (f : (val : ⟦ u ⟧) → ⟦ x val ⟧) → (val : ⟦ u ⟧) → (val' : ⟦ x val ⟧) → (dom : ⟦ u ⟧) → ⟦ x dom ⟧
updateFunc u x f val val' dom with dom ≟U val
updateFunc u x f val val' dom | yes refl = val'
updateFunc u x f val val' dom | no ¬p = f dom

updateFuncApp : ∀ u (x : ⟦ u ⟧ → U) → (f : (val : ⟦ u ⟧) → ⟦ x val ⟧) → (val : ⟦ u ⟧) → (val' : ⟦ x val ⟧) → updateFunc u x f val val' val ≡ val'
updateFuncApp u x f val val' with val ≟U val
updateFuncApp u x f val val' | yes refl = refl
updateFuncApp u x f val val' | no ¬p = ⊥-elim (¬p refl)

updateFuncApp' : ∀ u (x : ⟦ u ⟧ → U) → (f : (val : ⟦ u ⟧) → ⟦ x val ⟧) → (val₁ val₂ : ⟦ u ⟧) → (val' : ⟦ x val₁ ⟧) → ¬ val₁ ≡ val₂ → updateFunc u x f val₁ val' val₂ ≡ f val₂
updateFuncApp' u x f val₁ val₂ val' neq with val₂ ≟U val₁
updateFuncApp' u x f val₁ .val₁ val' neq | yes refl = ⊥-elim (neq refl)
updateFuncApp' u x f val₁ val₂ val' neq | no ¬p = refl

PiPartialRepr-¬∈ : ∀ u (x : ⟦ u ⟧ → U) eu vec → (f : (val : ⟦ u ⟧) → ⟦ x val ⟧) → (val : ⟦ u ⟧) → (val' : ⟦ x val ⟧) → ¬ val ∈ eu → PiPartialRepr u x f eu vec → PiPartialRepr u x (updateFunc u x f val val') eu vec
PiPartialRepr-¬∈ u x .[] .[] f val val' ¬∈ PiRepNil = PiRepNil
PiPartialRepr-¬∈ u x (x₃ ∷ eu) vec f val val' ¬∈ (PiRepCons {_} {_} {valxu} {valel} x₁ part x₂) =  PiRepCons (subst (λ t → ValIsRepr (x x₃) t valxu)
                                                                                                        (sym (updateFuncApp' u x f val x₃ val' (lem ¬∈))) x₁) (PiPartialRepr-¬∈ u x eu valel f val val' (λ x₄ → ¬∈ (there x₄)) part) x₂
    where
      lem : ¬ val ∈ x₃ ∷ eu → ¬ val ≡ x₃
      lem neg refl = neg (here refl)
piTyCondFuncPartialRepr : ∀ u (x : ⟦ u ⟧ → U) eu (prf : ∀ v → v ∈ eu → occ _≟U_ v eu ≡ 1) → (vec : Vec ℕ (tySumOver eu x)) → enumPiCondFunc u eu x vec ≡ 1 → Squash (∃ (λ f → PiPartialRepr u x f eu vec))
piTyCondFuncPartialRepr u x [] occ-prf [] eq = sq (trivialFunc u x , PiRepNil)
piTyCondFuncPartialRepr u x (x₁ ∷ eu) occ-prf vec eq with splitAtCorrect (tySize (x x₁)) vec
... | split with splitAt (tySize (x x₁)) vec
... | fst , snd with piTyCondFuncPartialRepr u x eu (occ-tail _ _ _ occ-prf) snd (andFunc⁻₂ (enumPiCondFuncIsBoolStrict u eu x snd) eq)
... | sq ind′ with ind′
... | acc , prf with tyCondFuncRepr (x x₁) fst (andFunc⁻₁ (tyCondFuncIsBoolStrict (x x₁) fst) eq)
... | sq elem′ with elem′
... | elem , prf' = sq ((updateFunc u x acc x₁ elem) , (PiRepCons {_} {_} {_} {_} {_} {fst} fApp (PiPartialRepr-¬∈ u x eu snd acc x₁ elem (occ-0-¬∈ _ _ _ (occ-tail0 _ _ _ occ-prf)) prf) split))
  where
    fApp : ValIsRepr (x x₁) (updateFunc u x acc x₁ elem x₁) fst
    fApp rewrite updateFuncApp u x acc x₁ elem = prf'
tyCondFuncRepr `One (x ∷ vec) eq with ℕtoF x ≟F zerof
tyCondFuncRepr `One (x ∷ []) eq | yes p = sq (tt , `OneValRepr x (sq (trans p (sym ℕtoF-0≡0))))
tyCondFuncRepr `Two (x ∷ []) eq with ℕtoF x ≟F zerof
tyCondFuncRepr `Two (x ∷ []) eq | yes p = sq (false , (`TwoValFalseRepr x (sq (trans p (sym ℕtoF-0≡0)))))
tyCondFuncRepr `Two (x ∷ []) eq | no ¬p with ℕtoF x ≟F onef
tyCondFuncRepr `Two (x ∷ []) eq | no ¬p | yes p = sq (true , `TwoValTrueRepr x (sq (trans p (sym ℕtoF-1≡1))))
tyCondFuncRepr `Base (x ∷ []) eq = sq ((ℕtoF x) , `BaseValRepr (sq (ℕtoF∘fToℕ≡ (ℕtoF x))))
tyCondFuncRepr (`Vec u zero) [] eq = sq ([] , `VecValBaseRepr)
tyCondFuncRepr (`Vec u (suc x)) vec eq with splitAt (tySize u) vec | inspect (splitAt (tySize u)) vec
... | fst , snd | [ refl ] with tyCondFuncRepr u fst (andFunc⁻₁ (tyCondFuncIsBoolStrict u (proj₁ (splitAt (tySize u) vec))) eq)
... | sq ind₁′ with ind₁′
... | elem₁ , ind₁ with tyCondFuncRepr (`Vec u x) snd (andFunc⁻₂ (tyCondFuncIsBoolStrict (`Vec u x) (proj₂ (splitAt (tySize u) vec))) eq)
... | sq ind₂′ with ind₂′
... | elem₂ , ind₂ = sq ((elem₁ ∷ elem₂) , (`VecValConsRepr ind₁ ind₂ (sym (splitAtCorrect (tySize u) vec))))
tyCondFuncRepr (`Σ u x) vec eq with splitAt (tySize u) vec | inspect (splitAt (tySize u)) vec
... | fst , snd | [ refl ] with ℕtoF (tyCondFunc u (proj₁ (splitAt (tySize u) vec))) ≟F zerof
tyCondFuncRepr (`Σ u x) vec eq | ._ , ._ | [ refl ] | no ¬p with ℕtoF (enumSigmaCondFunc u (enum u) x (proj₁ (splitAt (tySize u) vec))
                         (proj₂ (splitAt (tySize u) vec))) ≟F zerof
tyCondFuncRepr (`Σ u x) vec eq | ._ , ._ | [ refl ] | no ¬p | no ¬p₁ with tyCondFuncIsBoolStrict u (proj₁ (splitAt (tySize u) vec))
tyCondFuncRepr (`Σ u x) vec eq | ._ , ._ | [ refl ] | no ¬p | no ¬p₁ | isZeroS x₁ = ⊥-elim′ (¬p (trans (cong ℕtoF x₁) ℕtoF-0≡0))
tyCondFuncRepr (`Σ u x) vec eq | ._ , ._ | [ refl ] | no ¬p | no ¬p₁ | isOneS x₁ with enumSigmaCondFuncIsBoolStrict u (enum u) x (proj₁ (splitAt (tySize u) vec)) (proj₂ (splitAt (tySize u) vec))
tyCondFuncRepr (`Σ u x) vec eq | ._ , ._ | [ refl ] | no ¬p | no ¬p₁ | isOneS x₁ | isZeroS x₂ = ⊥-elim′ (¬p₁ (trans (cong ℕtoF x₂) ℕtoF-0≡0))
tyCondFuncRepr (`Σ u x) vec eq | fst , snd | [ refl ] | no ¬p | no ¬p₁ | isOneS x₁ | isOneS x₂ with tyCondFuncRepr u fst x₁
... | sq ind₁′ with ind₁′
... | elem₁ , ind₁ with enumSigmaCondFuncRepr u (enum u) x elem₁ fst snd ind₁ (enumComplete _ _) x₂
... | sq ind₂′ with ind₂′
... | elem₂ , ind₂  =  sq ((elem₁ , elem₂) , `ΣValRepr x snd ind₁ ind₂
                                    (enumSigmaCondRestZ u (enum u) x fst snd elem₁ (enumComplete u elem₁) ind₁ x₂)
                                    (maxTySplitCorrect u elem₁ x snd) (sym (splitAtCorrect (tySize u) vec)))
tyCondFuncRepr (`Π u x) vec eq with piTyCondFuncPartialRepr u x (enum u) (λ v x₁ → enumUnique u v _≟U_) vec eq
... | sq repr with repr
... | elem₁ , prf = sq (elem₁ , (`ΠValRepr x vec prf))


tyCondFunc≡1 : ∀ u val → tyCondFunc u val ≈ 1 → Squash (tyCondFunc u val ≡ 1)
tyCondFunc≡1 u val eq with tyCondFuncIsBoolStrict u val
tyCondFunc≡1 u val (sq x₁) | isZeroS x rewrite x = ⊥-elim′ (onef≠zerof (sym (trans (trans (sym ℕtoF-0≡0) x₁) ℕtoF-1≡1)))
tyCondFunc≡1 u val eq | isOneS x = sq x

varEqLitFunc≡1 : ∀ u val elem → varEqLitFunc u val elem ≈ 1 → Squash (varEqLitFunc u val elem ≡ 1)
varEqLitFunc≡1 u val elem eq with varEqLitFuncIsBoolStrict u val elem
varEqLitFunc≡1 u val elem (sq eq) | isZeroS x rewrite x = ⊥-elim′ (onef≠zerof (sym (trans (trans (sym ℕtoF-0≡0) eq) ℕtoF-1≡1)))
varEqLitFunc≡1 u val elem eq | isOneS x = sq x


indToIRSound : ∀ r u
  → (vec : Vec Var (tySize u))
  → (val : Vec ℕ (tySize u))
  → (sol : List (Var × ℕ))
  → BatchListLookup vec sol val
  → ListLookup 0 sol 1
  → ∀ init →
  let result = indToIR u vec ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → Squash (∃ (λ elem → ValIsRepr u elem val))
indToIRSound r u vec val sol look tri init isSol 
 with
  let input = ((r , prime) , init)
      p₁₁ = tyCond u vec
      t = output (p₁₁ input)
      p₂₂ = assertTrue t
      p₃₃ = λ _ → return vec
      p₂₃ = λ t → assertTrue t >>= λ _ → return vec
      p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₃ r _ sol isSol
      p₂₃IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₃ r _ sol isSol
      p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₃ r _ sol p₂₃IsSol
      sound₁ = tyCondSound r u vec val sol look tri _ p₁₁IsSol
      sound₂ = assertTrueSound r t sol _ p₂₂IsSol
      tyCond≈1 = ListLookup-≈ sound₁ sound₂
  in tyCondFunc≡1 u val tyCond≈1
... | sq tyCond≡1 = tyCondFuncRepr u val tyCond≡1

varEqLitFuncRepr : ∀ u val elem → varEqLitFunc u val elem ≡ 1 → Squash (ValIsRepr u elem val)
piVarEqLitFuncRepr : ∀ u (x : ⟦ u ⟧ → U) eu vec f → piVarEqLitFunc x eu vec f ≡ 1 → Squash (PiPartialRepr u x f eu vec)

piVarEqLitFuncRepr u x [] [] f eq = sq PiRepNil
piVarEqLitFuncRepr u x (x₁ ∷ eu) vec f eq with splitAtCorrect (tySize (x x₁)) vec
... | split with splitAt (tySize (x x₁)) vec
... | fst , snd with varEqLitFuncRepr (x x₁) fst (f x₁) (andFunc⁻₁ (varEqLitFuncIsBoolStrict (x x₁) fst (f x₁)) eq)
... | sq prf with piVarEqLitFuncRepr u x eu snd f (andFunc⁻₂ (piVarEqLitFuncIsBoolStrict x eu snd f) eq)
... | sq prf' = sq (PiRepCons prf prf' split)

varEqLitFuncRepr `One (v ∷ []) elem eq with ℕtoF v ≟F zerof
varEqLitFuncRepr `One (v ∷ []) tt eq | yes p = sq (`OneValRepr v (sq (trans p (sym ℕtoF-0≡0))))
varEqLitFuncRepr `Two (v ∷ []) false eq with ℕtoF v ≟F zerof
varEqLitFuncRepr `Two (v ∷ []) false eq | yes p = sq (`TwoValFalseRepr v (sq (trans p (sym ℕtoF-0≡0))))
varEqLitFuncRepr `Two (v ∷ []) true eq with ℕtoF v ≟F onef
varEqLitFuncRepr `Two (v ∷ []) true eq | yes p = sq (`TwoValTrueRepr v (sq (trans p (sym ℕtoF-1≡1))))
varEqLitFuncRepr `Base (v ∷ []) elem eq with ℕtoF v ≟F elem
varEqLitFuncRepr `Base (v ∷ []) elem eq | yes p = sq (`BaseValRepr (sq (trans (ℕtoF∘fToℕ≡ elem) (sym p))))
varEqLitFuncRepr (`Vec u zero) [] [] eq = sq `VecValBaseRepr
varEqLitFuncRepr (`Vec u (suc x)) val (e ∷ elem) eq with splitAtCorrect (tySize u) val
... | split with splitAt (tySize u) val
... | fst , snd with varEqLitFuncRepr u fst e (andFunc⁻₁ (varEqLitFuncIsBoolStrict u fst e) eq)
... | sq repr₁ with varEqLitFuncRepr (`Vec u x) snd elem (andFunc⁻₂ (varEqLitFuncIsBoolStrict (`Vec u x) snd elem) eq)
... | sq repr₂ = sq (`VecValConsRepr repr₁ repr₂ (sym split))
varEqLitFuncRepr (`Σ u x) val (fstₗ , sndₗ) eq
    with splitAtCorrect (tySize u) val
... | split₁
    with splitAt (tySize u) val
... | fst , snd
    with maxTySplitCorrect u fstₗ x snd
... | split₂
    with maxTySplit u fstₗ x snd
... | snd₁ , snd₂ with varEqLitFuncRepr u fst fstₗ (andFunc⁻₁ (varEqLitFuncIsBoolStrict u fst fstₗ) (andFunc⁻₁ (andFuncIsBoolStrict (varEqLitFunc u fst fstₗ)
       (varEqLitFunc (x fstₗ) snd₁ sndₗ)) eq))
... | sq repr₁ with varEqLitFuncRepr (x fstₗ) snd₁ sndₗ (andFunc⁻₂ (varEqLitFuncIsBoolStrict (x fstₗ) snd₁ sndₗ) (andFunc⁻₁ (andFuncIsBoolStrict (varEqLitFunc u fst fstₗ) (varEqLitFunc (x fstₗ) snd₁ sndₗ)) eq))
... | sq repr₂ = sq (`ΣValRepr {_} {_} x {sndₗ} {fst} {snd₁} snd {val} {snd₂} repr₁ repr₂ (allEqz→All≈0 _ (andFunc⁻₂ (allEqzFuncIsBoolStrict snd₂) eq)) split₂ (sym split₁))
varEqLitFuncRepr (`Π u x) val elem eq with piVarEqLitFuncRepr u x (enum u) val elem eq
... | sq prf = sq (`ΠValRepr x val prf)

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
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | yes p | yes p₁ = sq ((ListLookup-Respects-≈ _ _ _ _ (sq (trans p (sym ℕtoF-0≡0))) look₁) , {!!})
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | yes p | no ¬p with ListLookup-≈ lorSound look
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | yes p | no ¬p | sq x₉ = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) (trans x₉ ℕtoF-0≡0)))
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | no ¬p with ℕtoF val' ≟F zerof
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | no ¬p | yes p = {!ListLookup-≈ lorSound look!}
lorSound₀ r v v' val val' sol init look₁ look₂ isBool₁ isBool₂ isSol look | multSol .(Field.one field') .v bval .v' cval .(Field.one field') .init eval x x₁ x₂ x₃ | addSol (LinearCombValCons .(Field.one field') .v varVal x₄ (LinearCombValCons .(Field.one field') .v' varVal₁ x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .init varVal₂ x₇ (LinearCombValCons .((Field.- field') (Field.one field')) .(suc init) varVal₃ x₈ LinearCombValBase)))) x₅ | lorSound | no ¬p | no ¬p₁ = {!ListLookup-≈ lorSound look!}

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
anyNeqzIsBool r vec sol init isSol = {!!}
{-

Perhaps what you need is result lookup:
suppose that a variable v ∈ wo, this means that sol must contain a corresponding val for v, i.e. ListLookup v sol val
we know that v ∈ writerOutput of (neqz v) → ∴ ∃ val s.t. ListLookup v sol val

not only do we need neqzFuncIsBool, we need neqzIsBool..

-}
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
    with neqzIsBool r x sol init {!!}
... | sq (val₁ , isBool₁ , look₁)
    with anyNeqzIsBool r vec sol _ {!!}
... | sq (val₂ , isBool₂ , look₂)
    with lorSound₀ r _ _ _ _ sol _ look₁ look₂ isBool₁ isBool₂ {!!} look
... | sq (isZ₁ , isZ₂)
    with neqzSound₀ r x sol tri init {!!} isZ₁
... | sq (val₁' , look₁' , eq₀)
    with anyNeqzSound₀ r vec sol tri _ {!!} isZ₂
... | sq (val₂' , look₂' , eq₁)
    =  sq ((val₁' ∷ val₂') , (BatchLookupCons _ _ _ _ _ look₁' look₂' , eq₀ ∷ eq₁))

allEqzSound₁ : ∀ (r : WriterMode)
  → ∀ {n} → (vec : Vec Var n)
  → (sol : List (Var × ℕ))
  → ListLookup 0 sol 1
  → ∀ init →
  let result = allEqz vec ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol 1
  → ∃ (λ val → (Σ′′ (BatchListLookup vec sol val) (λ _ → All (_≈_ 0) val)))
allEqzSound₁ r vec sol tri init isSol look = {!!}

varEqLitSound' : ∀ (r : WriterMode)
  → ∀ u → (vec : Vec Var (tySize u))
  → (l : ⟦ u ⟧)
  → (sol : List (Var × ℕ))
  → ListLookup 0 sol 1
  → ∀ init →
  let result = varEqLit u vec l ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → ListLookup (output result) sol 1
  → ValIsRepr u l vec
varEqLitSound' r `One (v ∷ []) l sol tri init isSol look = {!!}
varEqLitSound' r `Two vec l sol tri init isSol look = {!!}
varEqLitSound' r `Base vec l sol tri init isSol look = {!!}
varEqLitSound' r (`Vec u x) vec l sol tri init isSol look = {!!}
varEqLitSound' r (`Σ u x) vec l sol tri init isSol look = {!!}
varEqLitSound' r (`Π u x) vec l sol tri init isSol look = {!!}

litToIndSound : ∀ r u
  → (elem : ⟦ u ⟧)
  → (sol : List (Var × ℕ))
  → ListLookup 0 sol 1
  → ∀ init →
  let result = litToInd u elem ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → Squash (∃ (λ val → Σ′ (ValIsRepr u elem val) (λ _ → BatchListLookup (output result) sol val)))
litToIndSound r u elem sol tri init isSol
  with
  let
    input = ((r , prime) , init)
    p₁₁ = newVarVec (tySize u)
    vec = output (p₁₁ input)
    p₁₃ = do
      vec ← newVarVec (tySize u)
      add (Hint (litEqVecHint u elem vec))
      varEqLit u vec elem
    r' = output (p₁₃ input)
    p₂₂ = add (Hint (litEqVecHint u elem vec))
    p₃₃ = varEqLit u vec elem
    p₂₅ = λ vec → do
      add (Hint (litEqVecHint u elem vec))
      r ← varEqLit u vec elem
      assertTrue r
      return vec
    p₃₅ = λ _ → do
      r ← varEqLit u vec elem
      assertTrue r
      return vec
    p₄₄ = assertTrue r'
    p₄₅ = λ r → do
      assertTrue r
      return vec
    p₅₅ = λ _ → return vec
    p₂₅IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₅ r _ sol isSol
    p₃₅IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₅ r _ sol p₂₅IsSol
    p₃₃IsSol = BuilderProdSol->>=⁻₁ p₃₃ p₄₅ r _ sol p₃₅IsSol
    p₄₅IsSol = BuilderProdSol->>=⁻₂ p₃₃ p₄₅ r _ sol p₃₅IsSol
    p₄₄IsSol = BuilderProdSol->>=⁻₁ p₄₄ p₅₅ r _ sol p₄₅IsSol
    sound₂ = assertTrueSound r r' sol _ p₄₄IsSol
    sound₁ = varEqLitSound r u vec {!!} elem sol {!!} tri _  p₃₃IsSol
    varEqLit≈1 = ListLookup-≈ sound₁ sound₂
  in varEqLitFunc≡1 u {!!} elem varEqLit≈1
... | sq varEqLit≡1 = {!!} -- varEqLitFuncRepr u val elem varEqLit≡1

{-
litToIndSound : ∀ r u
  → (elem : ⟦ u ⟧)
  → (sol : List (Var × ℕ))
  → (val : Vec ℕ (tySize u))
  → ListLookup 0 sol 1
  → ∀ init →
  let result = litToInd u elem ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → BatchListLookup (output result) sol val
  → Squash (ValIsRepr u elem val)
litToIndSound r u elem sol val tri init isSol look
  with
  let
    input = ((r , prime) , init)
    p₁₁ = newVarVec (tySize u)
    vec = output (p₁₁ input)
    p₁₃ = do
      vec ← newVarVec (tySize u)
      add (Hint (litEqVecHint u elem vec))
      varEqLit u vec elem
    r' = output (p₁₃ input)
    p₂₂ = add (Hint (litEqVecHint u elem vec))
    p₃₃ = varEqLit u vec elem
    p₂₅ = λ vec → do
      add (Hint (litEqVecHint u elem vec))
      r ← varEqLit u vec elem
      assertTrue r
      return vec
    p₃₅ = λ _ → do
      r ← varEqLit u vec elem
      assertTrue r
      return vec
    p₄₄ = assertTrue r'
    p₄₅ = λ r → do
      assertTrue r
      return vec
    p₅₅ = λ _ → return vec
    p₂₅IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₅ r _ sol isSol
    p₃₅IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₅ r _ sol p₂₅IsSol
    p₃₃IsSol = BuilderProdSol->>=⁻₁ p₃₃ p₄₅ r _ sol p₃₅IsSol
    p₄₅IsSol = BuilderProdSol->>=⁻₂ p₃₃ p₄₅ r _ sol p₃₅IsSol
    p₄₄IsSol = BuilderProdSol->>=⁻₁ p₄₄ p₅₅ r _ sol p₄₅IsSol
    sound₁ = varEqLitSound r u vec val elem sol look tri _  p₃₃IsSol
    sound₂ = assertTrueSound r r' sol _ p₄₄IsSol
    varEqLit≈1 = ListLookup-≈ sound₁ sound₂
  in varEqLitFunc≡1 u val elem varEqLit≈1
... | sq varEqLit≡1 = varEqLitFuncRepr u val elem varEqLit≡1

-}

data Vec-≈ : ∀ {n} → Vec ℕ n → Vec ℕ n → Prop where
  ≈-Nil : Vec-≈ [] []
  ≈-Cons : ∀ {n} x y {l : Vec ℕ n} {l'} → x ≈ y → Vec-≈ l l' → Vec-≈ (x ∷ l) (y ∷ l')

assertVarEqVarSound : ∀ r n
  → (v v' : Vec Var n)
  → (sol : List (Var × ℕ))
  → (val val' : Vec ℕ n)
  → BatchListLookup v sol val
  → BatchListLookup v' sol val'
  → ListLookup 0 sol 1
  → ∀ init →
  let result = assertVarEqVar n v v' ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → Vec-≈ val val'
assertVarEqVarSound r zero [] [] sol [] [] look look' tri init isSol = ≈-Nil
assertVarEqVarSound r (suc n) (x ∷ v) (x₁ ∷ v') sol (x₂ ∷ val) (x₃ ∷ val') (BatchLookupCons .x .x₂ .v .val .sol x₄ look) (BatchLookupCons .x₁ .x₃ .v' .val' .sol x₅ look') tri init isSol
  with let p₁₁ = add (IAdd zerof ((onef , x) ∷ (-F onef , x₁) ∷ []))
           p₂₂ = λ _ → assertVarEqVar _ v v'
           p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₂ r _ sol isSol
       in addSound r (IAdd zerof ((onef , x) ∷ (-F onef , x₁) ∷ [])) sol _ p₁₁IsSol
assertVarEqVarSound r (suc n) (x ∷ v) (x₁ ∷ v') sol (x₂ ∷ val) (x₃ ∷ val') (BatchLookupCons .x .x₂ .v .val .sol x₄ look) (BatchLookupCons .x₁ .x₃ .v' .val' .sol x₅ look') tri init isSol | addSol (LinearCombValCons .(Field.one field') .x varVal x₆ (LinearCombValCons .((Field.- field') (Field.one field')) .x₁ varVal₁ x₈ LinearCombValBase)) x₇ with ListLookup-≈ x₈ x₅ | ListLookup-≈ x₆ x₄
... | sq l₁ | sq l₂ rewrite l₁ | l₂
                          | *-identityˡ (ℕtoF x₂)
                          | -one*f≡-f (ℕtoF x₃)
                          | +-identityʳ (-F (ℕtoF x₃))
                          | +-identityʳ (ℕtoF x₂ +F (-F ℕtoF x₃))
                          =
       let p₁₁ = add (IAdd zerof ((onef , x) ∷ (-F onef , x₁) ∷ []))
           p₂₂ = λ _ → assertVarEqVar _ v v'
           p₂₂IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₂ r _ sol isSol
       in ≈-Cons x₂ x₃ (sq (a-b≡zero→a≡b x₇)) (assertVarEqVarSound r n v v' sol val val' look look' tri _ p₂₂IsSol)

data SourceStore (store : List (Var × ℕ)) : ∀ u → Source u → Set where
  IndStore : ∀ {u} {m} (vec : Vec Var m) (val : Vec ℕ m)
      → (p : m ≡ tySize u)
      → BatchListLookup vec store val
      → SourceStore store u (Ind p vec)
  LitStore : ∀ {u} (v : ⟦ u ⟧) → SourceStore store u (Lit v)
  AddStore : ∀ (s₁ s₂ : Source `Base) → SourceStore store `Base s₁ → SourceStore store `Base s₂ → SourceStore store `Base (Add s₁ s₂)
  MulStore : ∀ (s₁ s₂ : Source `Base) → SourceStore store `Base s₁ → SourceStore store `Base s₂ → SourceStore store `Base (Mul s₁ s₂)


data SourceStoreRepr (store : List (Var × ℕ)) : ∀ u → Source u → Set where
  IndStore′ : ∀ {u} {m} (vec : Vec Var m) (val : Vec ℕ m) elem
      → (p : m ≡ tySize u)
      → BatchListLookup vec store val
      → ValIsRepr u elem (subst (Vec ℕ) p val)
      → SourceStoreRepr store u (Ind p vec)
  LitStore′ : ∀ {u} (v : ⟦ u ⟧) → SourceStoreRepr store u (Lit v)
  AddStore′ : ∀ (s₁ s₂ : Source `Base) → SourceStoreRepr store `Base s₁ → SourceStoreRepr store `Base s₂ → SourceStoreRepr store `Base (Add s₁ s₂)
  MulStore′ : ∀ (s₁ s₂ : Source `Base) → SourceStoreRepr store `Base s₁ → SourceStoreRepr store `Base s₂ → SourceStoreRepr store `Base (Mul s₁ s₂)


sourceSem : ∀ u → (s : Source u) → (store : List (Var × ℕ)) → SourceStoreRepr store u s → ⟦ u ⟧
sourceSem `One s st ss = tt
sourceSem `Two .(Ind refl vec) st (IndStore′ vec val elem refl x x₁) = elem
sourceSem `Two .(Lit v) st (LitStore′ v) = v
sourceSem `Base .(Ind p vec) st (IndStore′ vec val elem p x x₁) = elem
sourceSem `Base .(Lit v) st (LitStore′ v) = v
sourceSem `Base .(Add s₁ s₂) st (AddStore′ s₁ s₂ ss ss₁) = sourceSem `Base s₁ st ss +F sourceSem `Base s₂ st ss₁
sourceSem `Base .(Mul s₁ s₂) st (MulStore′ s₁ s₂ ss ss₁) = sourceSem `Base s₁ st ss *F sourceSem `Base s₂ st ss₁
sourceSem (`Vec u x) .(Ind p vec) st (IndStore′ vec val elem p x₁ x₂) = elem
sourceSem (`Vec u x) .(Lit v) st (LitStore′ v) = v
sourceSem (`Σ u x) .(Ind p vec) st (IndStore′ vec val elem p x₁ x₂) = elem
sourceSem (`Σ u x) .(Lit v) st (LitStore′ v) = v
sourceSem (`Π u x) .(Ind p vec) st (IndStore′ vec val elem p x₁ x₂) = elem
sourceSem (`Π u x) .(Lit v) st (LitStore′ v) = v

indStore≡ : ∀ u {m} (elem : ⟦ u ⟧) (vec : Vec Var m) (store : List (Var × ℕ)) (val : Vec ℕ m) → (p : m ≡ tySize u)
  → (look : BatchListLookup vec store val)
  → (isRepr : ValIsRepr u elem (subst (Vec ℕ) p val))
  → sourceSem u (Ind p vec) store (IndStore′ vec val elem p look isRepr) ≡ elem
indStore≡ `One tt vec store val p look isRepr = refl
indStore≡ `Two elem vec store val refl look isRepr = refl
indStore≡ `Base elem vec store val refl look isRepr = refl
indStore≡ (`Vec u x) elem vec store val refl look isRepr = refl
indStore≡ (`Σ u x) elem vec store val refl look isRepr = refl
indStore≡ (`Π u x) elem vec store val refl look isRepr = refl

litStore≡ : ∀ u elem store → sourceSem u (Lit elem) store (LitStore′ elem) ≡ elem
litStore≡ `One tt store = refl
litStore≡ `Two elem store = refl
litStore≡ `Base elem store = refl
litStore≡ (`Vec u x) elem store = refl
litStore≡ (`Σ u x) elem store = refl
litStore≡ (`Π u x) elem store = refl



sourceToIntermediateSound : ∀ r u
  → (s : Source u)
  → (sol : List (Var × ℕ))
  → ListLookup 0 sol 1
  → SourceStore sol u s
  → ∀ init →
  let result = sourceToIntermediate u s ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → Squash (∃ (λ ⟦u⟧ → ∃ (λ val → ValIsRepr u ⟦u⟧ val × ∃ (λ ss → Σ′ (sourceSem u s sol ss ≡ ⟦u⟧) (λ _ → BatchListLookup (output result) sol val)))))
sourceToIntermediateSound r u .(Ind refl vec) sol tri (IndStore vec val refl x) init isSol with indToIRSound PostponedMode u vec val sol x tri init isSol
... | sq (fst , snd) = sq (fst , (val , (snd , (IndStore′ vec val fst refl x snd , (indStore≡ u fst vec sol val refl x snd , x)))))
sourceToIntermediateSound r u .(Lit v) sol tri (LitStore v) init isSol = {!litToIndSound r u v sol !}
sourceToIntermediateSound r .`Base .(Add s₁ s₂) sol tri (AddStore s₁ s₂ ss ss₁) init isSol = {!sourceToIntermediateSound r `Base s₁ sol tri ss init !}
sourceToIntermediateSound r .`Base .(Mul s₁ s₂) sol tri (MulStore s₁ s₂ ss ss₁) init isSol = {!!}


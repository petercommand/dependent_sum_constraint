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
open import Data.List.Relation.Unary.Any hiding (head)
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
module Satisfiability.SourceR1CS (f : Set) (_≟F_ : Decidable {A = f} _≡_) (field' : Field f) (isField : IsField f field')
     (finite : Finite f) (showf : f → String) (fToℕ : f → ℕ) (ℕtoF : ℕ → f)
        (ℕtoF-1≡1 : ℕtoF 1 ≡ Field.one field')
        (ℕtoF-0≡0 : ℕtoF 0 ≡ Field.zero field')
        (ℕtoF∘fToℕ≡ : ∀ x → ℕtoF (fToℕ x) ≡ x)
        (ℕtoF-+hom : ∀ x y → ℕtoF (x + y) ≡ (Field._+_ field') (ℕtoF x) (ℕtoF y))
        (ℕtoF-*hom : ∀ x y → ℕtoF (x * y) ≡ (Field._*_ field') (ℕtoF x) (ℕtoF y))
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
open import Satisfiability.SourceR1CS.SimpleComp f _≟F_ field' isField finite showf fToℕ ℕtoF ℕtoF-1≡1 ℕtoF-0≡0 ℕtoF∘fToℕ≡ prime isPrime onef≠zerof

¬anyNeqz→All≈0 : ∀ {n} (vec : Vec ℕ n) → anyNeqzFunc vec ≡ 0 → All (_≈_ 0) vec
¬anyNeqz→All≈0 [] any = []
¬anyNeqz→All≈0 (x ∷ vec) any with ℕtoF x ≟F zerof
¬anyNeqz→All≈0 (x ∷ vec) any | yes p = sq (sym (trans p (sym ℕtoF-0≡0))) ∷ ¬anyNeqz→All≈0 vec any

allEqz→All≈0 : ∀ {n} (vec : Vec ℕ n) → allEqzFunc vec ≡ 1 → All (_≈_ 0) vec
allEqz→All≈0 [] eq = []
allEqz→All≈0 (x ∷ vec) eq with ℕtoF x ≟F zerof
allEqz→All≈0 (x ∷ vec) eq | yes p = sq (sym (trans p (sym ℕtoF-0≡0))) ∷ allEqz→All≈0 vec eq

All≈0→allEqz : ∀ {n} (vec : Vec ℕ n) → All (_≈_ 0) vec → Squash (allEqzFunc vec ≡ 1)
All≈0→allEqz .[] [] = sq refl
All≈0→allEqz .(x ∷ _) (_∷_ {x = x} px all₁) with ℕtoF x ≟F zerof
All≈0→allEqz .(x ∷ _) (_∷_ {x = x} px all₁) | yes p = All≈0→allEqz _ all₁
All≈0→allEqz .(x ∷ _) (_∷_ {x = x} (sq px) all₁) | no ¬p = ⊥-elim′ (¬p (trans (sym px) ℕtoF-0≡0))




ValRepr→varEqLit : ∀ u elem val val' → val ≡ val' → ValRepr u elem val' → Squash (varEqLitFunc u val elem ≡ 1)

PiRepr→piVarEqLit : ∀ u x eu vec vec' f → vec ≡ vec' → PiRepr u x f eu vec' → Squash (piVarEqLitFunc x eu vec f ≡ 1)
PiRepr→piVarEqLit u x .[] .[] ._ f refl PiRepNil = sq refl
PiRepr→piVarEqLit u x (x₁ ∷ eu) vec vec f refl (PiRepCons x₂ repr refl)
    with splitAtCorrect (tySize (x x₁)) vec
... | split₁
    with splitAt (tySize (x x₁)) vec
... | fst , snd with ValRepr→varEqLit (x x₁) (f x₁) fst _ (sym (vecSplit₁ _ fst split₁)) x₂
... | sq ind₁ with PiRepr→piVarEqLit u x eu snd _ f (sym (vecSplit₂ _ _ split₁)) repr
... | sq ind₂ with ℕtoF (varEqLitFunc (x x₁) fst (f x₁)) ≟F zerof
PiRepr→piVarEqLit u x (x₁ ∷ eu) ._ ._ f refl (PiRepCons x₂ repr refl) | split₁ | fst , snd | sq ind₁ | sq ind₂ | yes p = ⊥-elim′ (onef≠zerof (trans (sym (trans (cong ℕtoF ind₁) ℕtoF-1≡1)) p))
PiRepr→piVarEqLit u x (x₁ ∷ eu) ._ ._ f refl (PiRepCons x₂ repr refl) | split₁ | fst , snd | sq ind₁ | sq ind₂ | no ¬p with  ℕtoF (piVarEqLitFunc x eu snd f) ≟F zerof
PiRepr→piVarEqLit u x (x₁ ∷ eu) ._ ._ f refl (PiRepCons x₂ repr refl) | split₁ | fst , snd | sq ind₁ | sq ind₂ | no ¬p | yes p = ⊥-elim′ (onef≠zerof (trans (sym (trans (cong ℕtoF ind₂) ℕtoF-1≡1)) p))
PiRepr→piVarEqLit u x (x₁ ∷ eu) ._ ._ f refl (PiRepCons x₂ repr refl) | split₁ | fst , snd | sq ind₁ | sq ind₂ | no ¬p | no ¬p₁ = sq refl

ValRepr→varEqLit .`One .tt .(n ∷ []) .(n ∷ []) refl (`OneValRepr n x) with ℕtoF n ≟F zerof
ValRepr→varEqLit .`One .tt .(n ∷ []) .(n ∷ []) refl (`OneValRepr n x) | yes p = sq refl
ValRepr→varEqLit .`One .tt .(n ∷ []) .(n ∷ []) refl (`OneValRepr n (sq eq)) | no ¬p = ⊥-elim′ (¬p (trans eq ℕtoF-0≡0))
ValRepr→varEqLit .`Two .false .(n ∷ []) .(n ∷ []) refl (`TwoValFalseRepr n x) with ℕtoF n ≟F zerof
ValRepr→varEqLit .`Two .false .(n ∷ []) .(n ∷ []) refl (`TwoValFalseRepr n x) | yes p = sq refl
ValRepr→varEqLit .`Two .false .(n ∷ []) .(n ∷ []) refl (`TwoValFalseRepr n (sq eq)) | no ¬p = ⊥-elim′ (¬p (trans eq ℕtoF-0≡0))
ValRepr→varEqLit .`Two .true .(n ∷ []) .(n ∷ []) refl (`TwoValTrueRepr n (sq eq)) with ℕtoF n ≟F onef
ValRepr→varEqLit .`Two .true .(n ∷ []) .(n ∷ []) refl (`TwoValTrueRepr n (sq eq)) | yes p = sq refl
ValRepr→varEqLit .`Two .true .(n ∷ []) .(n ∷ []) refl (`TwoValTrueRepr n (sq eq)) | no ¬p = ⊥-elim′ (¬p (trans eq ℕtoF-1≡1))
ValRepr→varEqLit .`Base elem .(v' ∷ []) .(v' ∷ []) refl (`BaseValRepr {v' = v'} x) with ℕtoF v' ≟F elem
ValRepr→varEqLit .`Base elem .(v' ∷ []) .(v' ∷ []) refl (`BaseValRepr {v' = v'} x) | yes p = sq refl
ValRepr→varEqLit .`Base elem .(v' ∷ []) .(v' ∷ []) refl (`BaseValRepr {v' = v'} (sq eq)) | no ¬p = ⊥-elim′ (¬p (trans (sym eq) (ℕtoF∘fToℕ≡ elem)))
ValRepr→varEqLit .(`Vec _ 0) .[] .[] .[] refl `VecValBaseRepr = sq refl
ValRepr→varEqLit (`Vec u (suc x)) (elem₁ ∷ elem) val ._ refl (`VecValConsRepr repr repr₁ refl)
     with splitAtCorrect (tySize u) val
... | eq
   with splitAt (tySize u) val
... | fst , snd with ValRepr→varEqLit u elem₁ fst _ (vecSplit₁ fst _ (sym eq)) repr
... | sq ind₁ with ValRepr→varEqLit (`Vec u x) elem snd _ (vecSplit₂ _ _ (sym eq)) repr₁
... | sq ind₂ with ℕtoF (varEqLitFunc u fst elem₁) ≟F zerof
ValRepr→varEqLit (`Vec u (suc x)) (elem₁ ∷ elem) ._ ._ refl (`VecValConsRepr repr repr₁ refl) | eq | fst , snd | sq ind₁ | sq ind₂ | yes p rewrite ind₁ = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) p))
ValRepr→varEqLit (`Vec u (suc x)) (elem₁ ∷ elem) ._ ._ refl (`VecValConsRepr repr repr₁ refl) | eq | fst , snd | sq ind₁ | sq ind₂ | no ¬p with ℕtoF (varEqLitFunc (`Vec u x) snd elem) ≟F zerof
ValRepr→varEqLit (`Vec u (suc x)) (elem₁ ∷ elem) ._ ._ refl (`VecValConsRepr repr repr₁ refl) | eq | fst , snd | sq ind₁ | sq ind₂ | no ¬p | yes p rewrite ind₂ = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) p))
ValRepr→varEqLit (`Vec u (suc x)) (elem₁ ∷ elem) ._ ._ refl (`VecValConsRepr repr repr₁ refl) | eq | fst , snd | sq ind₁ | sq ind₂ | no ¬p | no ¬p₁ = sq refl
ValRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) val .val refl (`ΣValRepr {_} {vu} x {vxu} {valu} {valxu} valxu+z {valu+valxu+z} repr repr₁ x₁ x₂ refl)
    with splitAtCorrect (tySize u) val
... | split₁₁
    with splitAt (tySize u) val
... | fst , snd
    with maxTySplitCorrect u fstₗ x snd
... | split₂
    with maxTySplit u fstₗ x snd
... | snd₁ , snd₂
    with ValRepr→varEqLit u fstₗ fst _ (vecSplit₁ _ _ (sym split₁₁)) repr
... | sq ind₁
    with vecSplit₂ valu fst split₁₁
... | split₁₂
    with ValRepr→varEqLit (x fstₗ) sndₗ snd₁ _ (vecSplit₁ _ _ (≅-to-≡ (HE.trans (HE.trans (HE.sym split₂) (≡-to-≅ (sym split₁₂))) x₂))) repr₁
... | sq ind₂ with ℕtoF (varEqLitFunc u fst fstₗ) ≟F zerof
ValRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | yes p = ⊥-elim′ (onef≠zerof (trans (trans (sym ℕtoF-1≡1) (sym (cong ℕtoF ind₁))) p))
ValRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p with  ℕtoF (varEqLitFunc (x fstₗ) snd₁ sndₗ) ≟F zerof
ValRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p | yes p = ⊥-elim′ (onef≠zerof (trans (sym (trans (cong ℕtoF ind₂) ℕtoF-1≡1)) p))
ValRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p | no ¬p₁ with ℕtoF 1 ≟F zerof
ValRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p | no ¬p₁ | yes p = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) p))
ValRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p | no ¬p₁ | no ¬p₂ with ℕtoF (allEqzFunc snd₂) ≟F zerof
ValRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p | no ¬p₁ | no ¬p₂ | yes p with All≈0→allEqz _ x₁
... | sq prf rewrite split₁₂
                   | vecSplit₂ valxu snd₁ (≅-to-≡ (HE.trans (HE.sym x₂) split₂))
                   | prf = ⊥-elim′ (onef≠zerof (trans (sym ℕtoF-1≡1) p))
ValRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ = sq refl
ValRepr→varEqLit (`Π u x) elem val .val refl (`ΠValRepr x .val x₁) = PiRepr→piVarEqLit u x (enum u) val val elem refl x₁ 

enumSigmaCondRestZ : ∀ u eu x fst snd val → val ∈ eu → ValRepr u val fst → enumSigmaCondFunc u eu x fst snd ≡ 1 → All (_≈_ 0) (proj₂ (maxTySplit u val x snd))
enumSigmaCondRestZ u .(_ ∷ _) x fst snd val (here refl) isRepr eq with ValRepr→varEqLit u val fst fst refl isRepr
... | sq varEqLit≡1 = allEqz→All≈0 (proj₂ (maxTySplit u val x snd)) (landFunc⁻₂ (allEqzFuncIsBoolStrict (proj₂ (maxTySplit u val x snd))) (limpFuncImp varEqLit≡1 (landFuncIsBoolStrict (tyCondFunc (x val) (proj₁ (maxTySplit u val x snd)))
       (allEqzFunc (proj₂ (maxTySplit u val x snd)))) (landFunc⁻₁ (limpFuncIsBoolStrict (varEqLitFunc u fst val)
       (landFunc (tyCondFunc (x val) (proj₁ (maxTySplit u val x snd)))
        (allEqzFunc (proj₂ (maxTySplit u val x snd)))) ) eq)))
enumSigmaCondRestZ u (_ ∷ eu) x fst snd val (there mem) isRepr eq = enumSigmaCondRestZ u eu x fst snd val mem isRepr (landFunc⁻₂ (enumSigmaCondFuncIsBoolStrict u eu x fst snd) eq)


tyCondFuncRepr : ∀ u → (vec : Vec ℕ (tySize u)) → tyCondFunc u vec ≡ 1 → Squash (∃ (λ elem → ValRepr u elem vec))

enumSigmaCondFuncRepr : ∀ u eu x elem val₁ val₂
  → ValRepr u elem val₁
  → elem ∈ eu
  → enumSigmaCondFunc u eu x val₁ val₂ ≡ 1
  → Squash (∃ (λ elem₁ → ValRepr (x elem) elem₁ (proj₁ (maxTySplit u elem x val₂))))
enumSigmaCondFuncRepr u [] x elem val₁ val₂ isRepr ()
enumSigmaCondFuncRepr u (elem ∷ eu) x elem val₁ val₂ isRepr (here refl) eq with ValRepr→varEqLit u elem val₁ val₁ refl isRepr
... | sq repr = tyCondFuncRepr (x elem) (proj₁ (maxTySplit u elem x val₂))
  (landFunc⁻₁ (tyCondFuncIsBoolStrict (x elem) (proj₁
        (splitAt (tySize (x elem))
         (subst (Vec ℕ)
          (sym
           (trans
            (ℕP.+-comm (tySize (x elem))
             (maxTySizeOver (enum u) x ∸ tySize (x elem)))
            (a-b+b≡a (maxTySizeOver (enum u) x) (tySize (x elem))
             (∈→≥ (enum u) x elem (enumComplete u elem)))))
          val₂)))) (limpFuncImp repr (landFuncIsBoolStrict  (tyCondFunc (x elem) (proj₁ (maxTySplit u elem x val₂))) (allEqzFunc (proj₂ (maxTySplit u elem x val₂)))) (landFunc⁻₁ (limpFuncIsBoolStrict (varEqLitFunc u val₁ elem) (landFunc (tyCondFunc (x elem) (proj₁ (maxTySplit u elem x val₂)))
        (allEqzFunc (proj₂ (maxTySplit u elem x val₂))))) eq)))
enumSigmaCondFuncRepr u (x₁ ∷ eu) x elem val₁ val₂ isRepr (there mem) eq = enumSigmaCondFuncRepr u eu x elem val₁ val₂ isRepr mem (landFunc⁻₂ (enumSigmaCondFuncIsBoolStrict u eu x val₁ val₂) eq)


postulate
  _≟U_ : ∀ {u} → Decidable {A = ⟦ u ⟧} _≡_

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

PiRepr-¬∈ : ∀ u (x : ⟦ u ⟧ → U) eu vec → (f : (val : ⟦ u ⟧) → ⟦ x val ⟧) → (val : ⟦ u ⟧) → (val' : ⟦ x val ⟧) → ¬ val ∈ eu → PiRepr u x f eu vec → PiRepr u x (updateFunc u x f val val') eu vec
PiRepr-¬∈ u x .[] .[] f val val' ¬∈ PiRepNil = PiRepNil
PiRepr-¬∈ u x (x₃ ∷ eu) vec f val val' ¬∈ (PiRepCons {_} {_} {valxu} {valel} x₁ part x₂) =  PiRepCons (subst (λ t → ValRepr (x x₃) t valxu)
                                                                                                        (sym (updateFuncApp' u x f val x₃ val' (lem ¬∈))) x₁) (PiRepr-¬∈ u x eu valel f val val' (λ x₄ → ¬∈ (there x₄)) part) x₂
    where
      lem : ¬ val ∈ x₃ ∷ eu → ¬ val ≡ x₃
      lem neg refl = neg (here refl)
piTyCondFuncPartialRepr : ∀ u (x : ⟦ u ⟧ → U) eu (prf : ∀ v → v ∈ eu → occ _≟U_ v eu ≡ 1) → (vec : Vec ℕ (tySumOver eu x)) → enumPiCondFunc u eu x vec ≡ 1 → Squash (∃ (λ f → PiRepr u x f eu vec))
piTyCondFuncPartialRepr u x [] occ-prf [] eq = sq (trivialFunc u x , PiRepNil)
piTyCondFuncPartialRepr u x (x₁ ∷ eu) occ-prf vec eq with splitAtCorrect (tySize (x x₁)) vec
... | split with splitAt (tySize (x x₁)) vec
... | fst , snd with piTyCondFuncPartialRepr u x eu (occ-tail _ _ _ occ-prf) snd (landFunc⁻₂ (enumPiCondFuncIsBoolStrict u eu x snd) eq)
... | sq ind′ with ind′
... | acc , prf with tyCondFuncRepr (x x₁) fst (landFunc⁻₁ (tyCondFuncIsBoolStrict (x x₁) fst) eq)
... | sq elem′ with elem′
... | elem , prf' = sq ((updateFunc u x acc x₁ elem) , (PiRepCons {_} {_} {_} {_} {_} {fst} fApp (PiRepr-¬∈ u x eu snd acc x₁ elem (occ-0-¬∈ _ _ _ (occ-tail0 _ _ _ occ-prf)) prf) split))
  where
    fApp : ValRepr (x x₁) (updateFunc u x acc x₁ elem x₁) fst
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
... | fst , snd | [ refl ] with tyCondFuncRepr u fst (landFunc⁻₁ (tyCondFuncIsBoolStrict u (proj₁ (splitAt (tySize u) vec))) eq)
... | sq ind₁′ with ind₁′
... | elem₁ , ind₁ with tyCondFuncRepr (`Vec u x) snd (landFunc⁻₂ (tyCondFuncIsBoolStrict (`Vec u x) (proj₂ (splitAt (tySize u) vec))) eq)
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
  → Squash (∃ (λ elem → ValRepr u elem val))
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

varEqLitFuncRepr : ∀ u val elem → varEqLitFunc u val elem ≡ 1 → Squash (ValRepr u elem val)
piVarEqLitFuncRepr : ∀ u (x : ⟦ u ⟧ → U) eu vec f → piVarEqLitFunc x eu vec f ≡ 1 → Squash (PiRepr u x f eu vec)

piVarEqLitFuncRepr u x [] [] f eq = sq PiRepNil
piVarEqLitFuncRepr u x (x₁ ∷ eu) vec f eq with splitAtCorrect (tySize (x x₁)) vec
... | split with splitAt (tySize (x x₁)) vec
... | fst , snd with varEqLitFuncRepr (x x₁) fst (f x₁) (landFunc⁻₁ (varEqLitFuncIsBoolStrict (x x₁) fst (f x₁)) eq)
... | sq prf with piVarEqLitFuncRepr u x eu snd f (landFunc⁻₂ (piVarEqLitFuncIsBoolStrict x eu snd f) eq)
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
... | fst , snd with varEqLitFuncRepr u fst e (landFunc⁻₁ (varEqLitFuncIsBoolStrict u fst e) eq)
... | sq repr₁ with varEqLitFuncRepr (`Vec u x) snd elem (landFunc⁻₂ (varEqLitFuncIsBoolStrict (`Vec u x) snd elem) eq)
... | sq repr₂ = sq (`VecValConsRepr repr₁ repr₂ (sym split))
varEqLitFuncRepr (`Σ u x) val (fstₗ , sndₗ) eq
    with splitAtCorrect (tySize u) val
... | split₁
    with splitAt (tySize u) val
... | fst , snd
    with maxTySplitCorrect u fstₗ x snd
... | split₂
    with maxTySplit u fstₗ x snd
... | snd₁ , snd₂ with varEqLitFuncRepr u fst fstₗ (landFunc⁻₁ (varEqLitFuncIsBoolStrict u fst fstₗ) (landFunc⁻₁ (landFuncIsBoolStrict (varEqLitFunc u fst fstₗ)
       (varEqLitFunc (x fstₗ) snd₁ sndₗ)) eq))
... | sq repr₁ with varEqLitFuncRepr (x fstₗ) snd₁ sndₗ (landFunc⁻₂ (varEqLitFuncIsBoolStrict (x fstₗ) snd₁ sndₗ) (landFunc⁻₁ (landFuncIsBoolStrict (varEqLitFunc u fst fstₗ) (varEqLitFunc (x fstₗ) snd₁ sndₗ)) eq))
... | sq repr₂ = sq (`ΣValRepr {_} {_} x {sndₗ} {fst} {snd₁} snd {val} {snd₂} repr₁ repr₂ (allEqz→All≈0 _ (landFunc⁻₂ (allEqzFuncIsBoolStrict snd₂) eq)) split₂ (sym split₁))
varEqLitFuncRepr (`Π u x) val elem eq with piVarEqLitFuncRepr u x (enum u) val elem eq
... | sq prf = sq (`ΠValRepr x val prf)



{-

Perhaps what you need is result lookup:
suppose that a variable v ∈ wo, this means that sol must contain a corresponding val for v, i.e. ListLookup v sol val
we know that v ∈ writerOutput of (neqz v) → ∴ ∃ val s.t. ListLookup v sol val

not only do we need neqzFuncIsBool, we need neqzIsBool..

-}




litToIndSound : ∀ r u
  → (elem : ⟦ u ⟧)
  → (sol : List (Var × ℕ))
  → ListLookup 0 sol 1
  → ∀ init →
  let result = litToInd u elem ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → Squash (∃ (λ val → Σ′ (ValRepr u elem val) (λ _ → BatchListLookup (output result) sol val)))
litToIndSound r u elem sol tri init isSol =
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
    sound₁ = varEqLitSound₁ r u vec elem sol tri _  p₃₃IsSol sound₂
  in sound₁



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
      → ValRepr u elem (subst (Vec ℕ) p val)
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
  → (isRepr : ValRepr u elem (subst (Vec ℕ) p val))
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



sourceToR1CSSound : ∀ r u
  → (s : Source u)
  → (sol : List (Var × ℕ))
  → ListLookup 0 sol 1
  → SourceStore sol u s
  → ∀ init →
  let result = sourceToR1CS u s ((r , prime) , init)
  in BuilderProdSol (writerOutput result) sol
  → Squash (∃ (λ ⟦u⟧ → ∃ (λ val → ValRepr u ⟦u⟧ val × ∃ (λ ss → Σ′ (sourceSem u s sol ss ≡ ⟦u⟧) (λ _ → BatchListLookup (output result) sol val)))))
sourceToR1CSSound r u .(Ind refl vec) sol tri (IndStore vec val refl x) init isSol with indToIRSound PostponedMode u vec val sol x tri init isSol
... | sq (fst , snd) = sq (fst , (val , (snd , (IndStore′ vec val fst refl x snd , (indStore≡ u fst vec sol val refl x snd , x)))))
sourceToR1CSSound r u .(Lit v) sol tri (LitStore v) init isSol with litToIndSound r u v sol tri init isSol
sourceToR1CSSound r u .(Lit v) sol tri (LitStore v) init isSol | sq (val , isRepr , look) = sq (v , (val , isRepr , ((LitStore′ v) , ((litStore≡ u v sol) , look))))
sourceToR1CSSound r .`Base .(Add s₁ s₂) sol tri (AddStore s₁ s₂ ss ss₁) init isSol
   with
   let input = ((r , prime) , init)
       p₁₁ = sourceToR1CS `Base s₁
       r₁ = output (p₁₁ input)
       p₂₅ = λ _ → do
         r₂ ← sourceToR1CS `Base s₂
         v ← new
         add (IAdd zerof ((onef , head r₁) ∷ (onef , head r₂) ∷ (-F onef , v) ∷ []))
         return (ann (Vec Var 1) (v ∷ []))
       p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₅ r _ sol isSol
   in sourceToR1CSSound r `Base s₁ sol tri ss init p₁₁IsSol
... | sq (l₁ , val₁ ∷ [] , isRepr₁ , ss′₁ , eq₁ , look₁)
   with
   let input = ((r , prime) , init)
       p₁₁ = sourceToR1CS `Base s₁
       p₁₂ = do
         r₁ ← sourceToR1CS `Base s₁
         sourceToR1CS `Base s₂
       p₁₃ = do
         r₁ ← sourceToR1CS `Base s₁
         r₂ ← sourceToR1CS `Base s₂
         new
       p₂₂ = sourceToR1CS `Base s₂
       r₁ = output (p₁₁ input)
       r₂ = output (p₁₂ input)
       v = output (p₁₃ input)
       p₂₅ = λ _ → do
         r₂ ← sourceToR1CS `Base s₂
         v ← new
         add (IAdd zerof ((onef , head r₁) ∷ (onef , head r₂) ∷ (-F onef , v) ∷ []))
         return (ann (Vec Var 1) (v ∷ []))
       p₃₃ = new
       p₃₅ = λ r₂ → do
         v ← new
         add (IAdd zerof ((onef , head r₁) ∷ (onef , head r₂) ∷ (-F onef , v) ∷ []))
         return (ann (Vec Var 1) (v ∷ []))
       p₄₄ = add (IAdd zerof ((onef , head r₁) ∷ (onef , head r₂) ∷ (-F onef , v) ∷ []))

       p₂₅IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₅ r _ sol isSol
       p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₅ r _ sol p₂₅IsSol
   in sourceToR1CSSound r `Base s₂ sol tri ss₁ (varOut (p₁₁ input)) p₂₂IsSol
sourceToR1CSSound r .`Base .(Add s₁ s₂) sol tri (AddStore s₁ s₂ ss ss₁) init isSol | sq (l₁ , val₁ ∷ [] , `BaseValRepr (sq x) , ss′₁ , eq₁ , look₁) | sq (l₂ , val₂ ∷ [] , `BaseValRepr (sq x₁) , ss′₂ , eq₂ , look₂)
   with
   let input = ((r , prime) , init)
       p₁₁ = sourceToR1CS `Base s₁
       p₁₂ = do
         r₁ ← sourceToR1CS `Base s₁
         sourceToR1CS `Base s₂
       p₁₃ = do
         r₁ ← sourceToR1CS `Base s₁
         r₂ ← sourceToR1CS `Base s₂
         new
       p₂₂ = sourceToR1CS `Base s₂
       r₁ = output (p₁₁ input)
       r₂ = output (p₁₂ input)
       v = output (p₁₃ input)
       p₂₅ = λ _ → do
         r₂ ← sourceToR1CS `Base s₂
         v ← new
         add (IAdd zerof ((onef , head r₁) ∷ (onef , head r₂) ∷ (-F onef , v) ∷ []))
         return (ann (Vec Var 1) (v ∷ []))
       p₃₃ = new
       p₃₅ = λ r₂ → do
         v ← new
         add (IAdd zerof ((onef , head r₁) ∷ (onef , head r₂) ∷ (-F onef , v) ∷ []))
         return (ann (Vec Var 1) (v ∷ []))
       p₄₄ = add (IAdd zerof ((onef , head r₁) ∷ (onef , head r₂) ∷ (-F onef , v) ∷ []))
       p₄₅ = λ _ → do
         add (IAdd zerof ((onef , head r₁) ∷ (onef , head r₂) ∷ (-F onef , v) ∷ []))
         return (ann (Vec Var 1) (v ∷ []))
       p₅₅ = λ _ → return (ann (Vec Var 1) (v ∷ []))
       p₂₅IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₅ r _ sol isSol
       p₃₅IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₅ r _ sol p₂₅IsSol
       p₄₅IsSol = BuilderProdSol->>=⁻₂ p₃₃ p₄₅ r _ sol p₃₅IsSol
       p₄₄IsSol = BuilderProdSol->>=⁻₁ p₄₄ p₅₅ r _ sol p₄₅IsSol
    in addSound r (IAdd zerof ((onef , head r₁) ∷ (onef , head r₂) ∷ (-F onef , v) ∷ [])) sol _ p₄₄IsSol
sourceToR1CSSound r .`Base .(Add s₁ s₂) sol tri (AddStore s₁ s₂ ss ss₁) init isSol | sq (l₁ , val₁ ∷ [] , `BaseValRepr (sq x) , ss′₁ , eq₁ , look₁) | sq (l₂ , val₂ ∷ [] , `BaseValRepr (sq x₁) , ss′₂ , eq₂ , look₂) | addSol (LinearCombValCons ._ ._ varVal x₂ (LinearCombValCons ._ ._ varVal₁ x₄ (LinearCombValCons ._ ._ varVal₂ x₅ LinearCombValBase))) x₃
    with ListLookup-≈ x₄ (BatchListLookup-Head look₂) | ListLookup-≈ x₂ (BatchListLookup-Head look₁)
... | sq p₁ | sq p₂ rewrite p₁ | p₂
                          | *-identityˡ (ℕtoF val₁)
                          | *-identityˡ (ℕtoF val₂)
                          | -one*f≡-f (ℕtoF varVal₂)
                          | +-identityʳ (-F (ℕtoF varVal₂))
                          | sym (+-assoc (ℕtoF val₁) (ℕtoF val₂) (-F (ℕtoF varVal₂)))
                          | +-identityʳ ((ℕtoF val₁ +F ℕtoF val₂) +F (-F ℕtoF varVal₂)) 
                          = sq ((l₁ +F l₂) , ((val₁ + val₂) ∷ [] , `BaseValRepr (sq (trans (ℕtoF∘fToℕ≡ (l₁ +F l₂)) lem')) , (AddStore′ s₁ s₂ ss′₁ ss′₂ , (lem , BatchLookupCons _ _ _ _ _ (ListLookup-Respects-≈ _ _ _ _ (sq (trans (sym (a-b≡zero→a≡b x₃)) (sym (ℕtoF-+hom val₁ val₂)))) x₅) (BatchLookupNil sol)))))
  where
    lem : (sourceSem `Base s₁ sol ss′₁ +F sourceSem `Base s₂ sol ss′₂) ≡ (l₁ +F l₂)
    lem rewrite eq₁ | eq₂ = refl
    lem' : (l₁ +F l₂) ≡ ℕtoF (val₁ + val₂)
    lem' rewrite ℕtoF-+hom val₁ val₂
               | sym x | sym x₁
               | ℕtoF∘fToℕ≡ l₁
               | ℕtoF∘fToℕ≡ l₂ = refl
sourceToR1CSSound r .`Base .(Mul s₁ s₂) sol tri (MulStore s₁ s₂ ss ss₁) init isSol with
   let input = ((r , prime) , init)
       p₁₁ = sourceToR1CS `Base s₁
       p₁₂ = do
         r₁ ← sourceToR1CS `Base s₁
         sourceToR1CS `Base s₂
       p₁₃ = do
         r₁ ← sourceToR1CS `Base s₁
         r₂ ← sourceToR1CS `Base s₂
         new
       p₂₂ = sourceToR1CS `Base s₂
       r₁ = output (p₁₁ input)
       r₂ = output (p₁₂ input)
       v = output (p₁₃ input)
       p₂₅ = λ _ → do
         r₂ ← sourceToR1CS `Base s₂
         v ← new
         add (IMul onef (head r₁) (head r₂) onef v)
         return (ann (Vec Var 1) (v ∷ []))
       p₃₃ = new
       p₃₅ = λ r₂ → do
         v ← new
         add (IMul onef (head r₁) (head r₂) onef v)
         return (ann (Vec Var 1) (v ∷ []))
       p₄₄ = add (IMul onef (head r₁) (head r₂) onef v)
       p₄₅ = λ _ → do
         add (IMul onef (head r₁) (head r₂) onef v)
         return (ann (Vec Var 1) (v ∷ []))
       p₅₅ = λ _ → return (ann (Vec Var 1) (v ∷ []))
       p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₅ r _ sol isSol
       p₂₅IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₅ r _ sol isSol
       p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₅ r _ sol p₂₅IsSol
       p₃₅IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₅ r _ sol p₂₅IsSol
       p₄₅IsSol = BuilderProdSol->>=⁻₂ p₃₃ p₄₅ r _ sol p₃₅IsSol
       p₄₄IsSol = BuilderProdSol->>=⁻₁ p₄₄ p₅₅ r _ sol p₄₅IsSol
    in sourceToR1CSSound r `Base s₁ sol tri ss _ p₁₁IsSol
... | sq (⟦s₁⟧ , ⟦s₁⟧Val , isRepr₁ , eq₁ , look₁) with
   let input = ((r , prime) , init)
       p₁₁ = sourceToR1CS `Base s₁
       p₁₂ = do
         r₁ ← sourceToR1CS `Base s₁
         sourceToR1CS `Base s₂
       p₁₃ = do
         r₁ ← sourceToR1CS `Base s₁
         r₂ ← sourceToR1CS `Base s₂
         new
       p₂₂ = sourceToR1CS `Base s₂
       r₁ = output (p₁₁ input)
       r₂ = output (p₁₂ input)
       v = output (p₁₃ input)
       p₂₅ = λ _ → do
         r₂ ← sourceToR1CS `Base s₂
         v ← new
         add (IMul onef (head r₁) (head r₂) onef v)
         return (ann (Vec Var 1) (v ∷ []))
       p₃₃ = new
       p₃₅ = λ r₂ → do
         v ← new
         add (IMul onef (head r₁) (head r₂) onef v)
         return (ann (Vec Var 1) (v ∷ []))
       p₄₄ = add (IMul onef (head r₁) (head r₂) onef v)
       p₄₅ = λ _ → do
         add (IMul onef (head r₁) (head r₂) onef v)
         return (ann (Vec Var 1) (v ∷ []))
       p₅₅ = λ _ → return (ann (Vec Var 1) (v ∷ []))
       p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₅ r _ sol isSol
       p₂₅IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₅ r _ sol isSol
       p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₅ r _ sol p₂₅IsSol
       p₃₅IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₅ r _ sol p₂₅IsSol
       p₄₅IsSol = BuilderProdSol->>=⁻₂ p₃₃ p₄₅ r _ sol p₃₅IsSol
       p₄₄IsSol = BuilderProdSol->>=⁻₁ p₄₄ p₅₅ r _ sol p₄₅IsSol
    in sourceToR1CSSound r `Base s₂ sol tri ss₁ _ p₂₂IsSol
... | sq (⟦s₂⟧ , ⟦s₂⟧Val , isRepr₂ , eq₂ , look₂) with
   let input = ((r , prime) , init)
       p₁₁ = sourceToR1CS `Base s₁
       p₁₂ = do
         r₁ ← sourceToR1CS `Base s₁
         sourceToR1CS `Base s₂
       p₁₃ = do
         r₁ ← sourceToR1CS `Base s₁
         r₂ ← sourceToR1CS `Base s₂
         new
       p₂₂ = sourceToR1CS `Base s₂
       r₁ = output (p₁₁ input)
       r₂ = output (p₁₂ input)
       v = output (p₁₃ input)
       p₂₅ = λ _ → do
         r₂ ← sourceToR1CS `Base s₂
         v ← new
         add (IMul onef (head r₁) (head r₂) onef v)
         return (ann (Vec Var 1) (v ∷ []))
       p₃₃ = new
       p₃₅ = λ r₂ → do
         v ← new
         add (IMul onef (head r₁) (head r₂) onef v)
         return (ann (Vec Var 1) (v ∷ []))
       p₄₄ = add (IMul onef (head r₁) (head r₂) onef v)
       p₄₅ = λ _ → do
         add (IMul onef (head r₁) (head r₂) onef v)
         return (ann (Vec Var 1) (v ∷ []))
       p₅₅ = λ _ → return (ann (Vec Var 1) (v ∷ []))
       p₁₁IsSol = BuilderProdSol->>=⁻₁ p₁₁ p₂₅ r _ sol isSol
       p₂₅IsSol = BuilderProdSol->>=⁻₂ p₁₁ p₂₅ r _ sol isSol
       p₂₂IsSol = BuilderProdSol->>=⁻₁ p₂₂ p₃₅ r _ sol p₂₅IsSol
       p₃₅IsSol = BuilderProdSol->>=⁻₂ p₂₂ p₃₅ r _ sol p₂₅IsSol
       p₄₅IsSol = BuilderProdSol->>=⁻₂ p₃₃ p₄₅ r _ sol p₃₅IsSol
       p₄₄IsSol = BuilderProdSol->>=⁻₁ p₄₄ p₅₅ r _ sol p₄₅IsSol
    in addSound r (IMul onef (head r₁) (head r₂) onef v) sol _ p₄₄IsSol
sourceToR1CSSound r .`Base .(Mul s₁ s₂) sol tri (MulStore s₁ s₂ ss ss₁) init isSol | sq (⟦s₁⟧ , ⟦s₁⟧Val ∷ [] , `BaseValRepr (sq x₄) , eq₁ , sem₁ , look₁) | sq (⟦s₂⟧ , ⟦s₂⟧Val ∷ [] , `BaseValRepr (sq x₅) , eq₂ , sem₂ , look₂) | multSol .(Field.one field') ._ bval ._ cval .(Field.one field') ._ eval x x₁ x₂ x₃ rewrite *-identityˡ (ℕtoF bval)
                                    | *-identityˡ (ℕtoF eval)
                                    = sq ((⟦s₁⟧ *F ⟦s₂⟧) , (⟦s₁⟧Val * ⟦s₂⟧Val ∷ [] , (`BaseValRepr (sq (trans lem (sym (ℕtoF-*hom ⟦s₁⟧Val ⟦s₂⟧Val))))) , (MulStore′ s₁ s₂ eq₁ eq₂) , (semEq , BatchLookupCons _ _ _ _ _ (ListLookup-Respects-≈ _ _ _ _ lem' x₂) (BatchLookupNil sol))))
  where
    lem : ℕtoF (fToℕ (⟦s₁⟧ *F ⟦s₂⟧)) ≡ (ℕtoF ⟦s₁⟧Val *F ℕtoF ⟦s₂⟧Val)
    lem rewrite sym x₄ | sym x₅ | ℕtoF∘fToℕ≡ (⟦s₁⟧ *F ⟦s₂⟧)
                                | ℕtoF∘fToℕ≡ ⟦s₁⟧
                                | ℕtoF∘fToℕ≡ ⟦s₂⟧ = refl

    lem' : eval ≈ (⟦s₁⟧Val * ⟦s₂⟧Val)
    lem' rewrite sym x₃ with ListLookup-≈ x (BatchListLookup-Head look₁)
    ... | sq p₁ rewrite p₁ with ListLookup-≈ x₁ (BatchListLookup-Head look₂)
    ... | sq p₂ rewrite p₂ = sq (sym (ℕtoF-*hom ⟦s₁⟧Val ⟦s₂⟧Val))

    semEq : (sourceSem `Base s₁ sol eq₁ *F sourceSem `Base s₂ sol eq₂) ≡
      (⟦s₁⟧ *F ⟦s₂⟧)
    semEq rewrite sem₁ | sem₂ = refl

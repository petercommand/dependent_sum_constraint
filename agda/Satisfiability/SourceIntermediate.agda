{-# OPTIONS --prop #-}

open import Agda.Builtin.Nat

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
open import Data.Nat.Properties renaming (+-comm to +ℕ-comm)
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

data PiPartialRepr (u : U) (x : ⟦ u ⟧ → U) (f : (v : ⟦ u ⟧) → ⟦ x v ⟧) : (eu : List ⟦ u ⟧) → Vec ℕ (tySumOver eu x) → Set


data ValIsRepr : ∀ u → ⟦ u ⟧ → Vec ℕ (tySize u) → Set where
  `OneValRepr : ∀ n → n ≈ 0 → ValIsRepr `One tt (n ∷ [])
  `TwoValFalseRepr : ∀ n → n ≈ 0 → ValIsRepr `Two false (n ∷ [])
  `TwoValTrueRepr : ∀ n → n ≈ 1 → ValIsRepr `Two true (n ∷ [])
  `BaseValRepr : ∀ {v : f} {v' : ℕ} → (fToℕ v) ≈ v' → ValIsRepr `Base v (v' ∷ [])
  `VecValBaseRepr : ∀ {u} → ValIsRepr (`Vec u 0) [] []
  `VecValConsRepr : ∀ {u} {n} {v₁} {vec₂} {val₁} {val₂} {val₃}
      → ValIsRepr u v₁ val₁
      → ValIsRepr (`Vec u n) vec₂ val₂
      → val₁ V++ val₂ ≡ val₃
      → ValIsRepr (`Vec u (suc n)) (v₁ ∷ vec₂) val₃
  `ΣValRepr : ∀ {u} {vu} (x : ⟦ u ⟧ → U) {vxu} {valu} {valxu} valxu+z {valu+valxu+z} {allZ}
      → ValIsRepr u vu valu
      → ValIsRepr (x vu) vxu valxu
      → All (_≈_ 0) (ann (Vec ℕ (maxTySizeOver (enum u) x - tySize (x vu))) allZ)
      → valxu+z ≅ valxu V++ allZ
      → valu V++ valxu+z ≡ valu+valxu+z
      → ValIsRepr (`Σ u x) (vu , vxu) valu+valxu+z
  `ΠValRepr : ∀ {u} (x : ⟦ u ⟧ → U) {f : (v : ⟦ u ⟧) → ⟦ x v ⟧ } val → PiPartialRepr u x f (enum u) val → ValIsRepr (`Π u x) f val

data PiPartialRepr u x f where
  PiRepNil : PiPartialRepr u x f [] []
  PiRepCons : ∀ {el} {vu} {valxu} {valel}
      → ValIsRepr (x vu) (f vu) valxu
      → PiPartialRepr u x f el valel
      → PiPartialRepr u x f (vu ∷ el) (valxu V++ valel)

enumSigmaCondRestZ : ∀ u eu x fst snd val → val ∈ eu → enumSigmaCondFunc u eu x fst snd ≡ 1 → All (_≈_ 0) (proj₂ (maxTySplit u val x snd))
enumSigmaCondRestZ = {!!}

maxTySplitCorrect : ∀ u val x vec → vec HE.≅ proj₁ (maxTySplit u val x vec) V++ proj₂ (maxTySplit u val x vec)
maxTySplitCorrect u val x vec with splitAtCorrect (tySize (x val)) (subst (Vec ℕ)
        (sym
         (trans
          (+ℕ-comm (tySize (x val))
           (maxTySizeOver (enum u) x ∸ tySize (x val)))
          (a-b+b≡a (maxTySizeOver (enum u) x)
           (tySize (x val)) (∈→≥ (enum u) x val (enumComplete u val)))))
        vec)
... | eq with splitAt (tySize (x val)) (subst (Vec ℕ)
        (sym
         (trans
          (+ℕ-comm (tySize (x val))
           (maxTySizeOver (enum u) x ∸ tySize (x val)))
          (a-b+b≡a (maxTySizeOver (enum u) x)
           (tySize (x val)) (∈→≥ (enum u) x val (enumComplete u val)))))
        vec)
... | fst , snd = HE.trans
                    (HE.sym
                     (HE.≡-subst-removable (Vec ℕ)
                      (sym
                       (trans
                        (+ℕ-comm (tySize (x val))
                         (maxTySizeOver (enum u) x ∸ tySize (x val)))
                        (a-b+b≡a (maxTySizeOver (enum u) x) (tySize (x val))
                         (∈→≥ (enum u) x val (enumComplete u val)))))
                      vec))
                    (HE.trans (≡-to-≅ eq) HE.refl)

ValIsRepr→varEqLit : ∀ u elem val val' → val ≡ val' → ValIsRepr u elem val' → Squash (varEqLitFunc u val elem ≡ 1)

PiPartialRepr→piVarEqLit : ∀ u x eu vec vec' f → vec ≡ vec' → PiPartialRepr u x f eu vec' → Squash (piVarEqLitFunc x eu vec f ≡ 1)
PiPartialRepr→piVarEqLit u x .[] .[] ._ f refl PiRepNil = sq refl
PiPartialRepr→piVarEqLit u x (x₁ ∷ eu) vec vec f refl (PiRepCons x₂ repr)
    with splitAtCorrect (tySize (x x₁)) vec
... | split₁
    with splitAt (tySize (x x₁)) vec
... | fst , snd with ValIsRepr→varEqLit (x x₁) (f x₁) fst _ (sym (vecSplit₁ _ fst split₁)) x₂
... | sq ind₁ with PiPartialRepr→piVarEqLit u x eu snd _ f (sym (vecSplit₂ _ _ split₁)) repr
... | sq ind₂ with ℕtoF (varEqLitFunc (x x₁) fst (f x₁)) ≟F zerof
PiPartialRepr→piVarEqLit u x (x₁ ∷ eu) ._ ._ f refl (PiRepCons x₂ repr) | split₁ | fst , snd | sq ind₁ | sq ind₂ | yes p = ⊥-elim′ (onef≠zerof (trans (sym (trans (cong ℕtoF ind₁) ℕtoF-1≡1)) p))
PiPartialRepr→piVarEqLit u x (x₁ ∷ eu) ._ ._ f refl (PiRepCons x₂ repr) | split₁ | fst , snd | sq ind₁ | sq ind₂ | no ¬p with  ℕtoF (piVarEqLitFunc x eu snd f) ≟F zerof
PiPartialRepr→piVarEqLit u x (x₁ ∷ eu) ._ ._ f refl (PiRepCons x₂ repr) | split₁ | fst , snd | sq ind₁ | sq ind₂ | no ¬p | yes p = ⊥-elim′ (onef≠zerof (trans (sym (trans (cong ℕtoF ind₂) ℕtoF-1≡1)) p))
PiPartialRepr→piVarEqLit u x (x₁ ∷ eu) ._ ._ f refl (PiRepCons x₂ repr) | split₁ | fst , snd | sq ind₁ | sq ind₂ | no ¬p | no ¬p₁ = sq refl

ValIsRepr→varEqLit .`One .tt .(n ∷ []) .(n ∷ []) refl (`OneValRepr n x) = {!!}
ValIsRepr→varEqLit .`Two .false .(n ∷ []) .(n ∷ []) refl (`TwoValFalseRepr n x) = {!!}
ValIsRepr→varEqLit .`Two .true .(n ∷ []) .(n ∷ []) refl (`TwoValTrueRepr n x) = {!!}
ValIsRepr→varEqLit .`Base elem .(_ ∷ []) .(_ ∷ []) refl (`BaseValRepr x) = {!!}
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
ValIsRepr→varEqLit (`Σ u x) (fstₗ , sndₗ) .(valu V++ valxu+z) .(valu V++ valxu+z) refl (`ΣValRepr {.u} {fstₗ} x {sndₗ} {valu} {valxu} valxu+z {.(valu V++ valxu+z)} repr repr₁ x₁ x₂ refl) | split₁₁ | fst , snd | split₂ | snd₁ , snd₂ | sq ind₁ | split₁₂ | sq ind₂ | no ¬p | no ¬p₁ = sq refl
ValIsRepr→varEqLit (`Π u x) elem val .val refl (`ΠValRepr x .val x₁) = PiPartialRepr→piVarEqLit u x (enum u) val val elem refl x₁ 

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
            (+ℕ-comm (tySize (x elem))
             (maxTySizeOver (enum u) x ∸ tySize (x elem)))
            (a-b+b≡a (maxTySizeOver (enum u) x) (tySize (x elem))
             (∈→≥ (enum u) x elem (enumComplete u elem)))))
          val₂)))) (impFuncImp repr (andFuncIsBoolStrict  (tyCondFunc (x elem) (proj₁ (maxTySplit u elem x val₂))) (allEqzFunc (proj₂ (maxTySplit u elem x val₂)))) (andFunc⁻₁ (impFuncIsBoolStrict (varEqLitFunc u val₁ elem) (andFunc (tyCondFunc (x elem) (proj₁ (maxTySplit u elem x val₂)))
        (allEqzFunc (proj₂ (maxTySplit u elem x val₂))))) eq)))
enumSigmaCondFuncRepr u (x₁ ∷ eu) x elem val₁ val₂ isRepr (there mem) eq = enumSigmaCondFuncRepr u eu x elem val₁ val₂ isRepr mem (andFunc⁻₂ (enumSigmaCondFuncIsBoolStrict u eu x val₁ val₂) eq)


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
                                    (enumSigmaCondRestZ u (enum u) x fst snd elem₁ (enumComplete u elem₁) x₂)
                                    (maxTySplitCorrect u elem₁ x snd) (sym (splitAtCorrect (tySize u) vec)))
tyCondFuncRepr (`Π u x) vec eq = {!!}
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
indToIRSound r `One .(v ∷ []) (n ∷ []) sol (BatchLookupCons v .n .[] .[] .sol x (BatchLookupNil .sol)) tri init isSol = {!!}
indToIRSound r `Two vec val sol look tri init isSol = {!!}
indToIRSound r `Base .(v ∷ []) (x ∷ []) sol (BatchLookupCons v .x .[] .[] .sol x₁ (BatchLookupNil .sol)) tri init isSol = sq ((ℕtoF x) , (`BaseValRepr (sq (ℕtoF∘fToℕ≡ (ℕtoF x)))))
indToIRSound r (`Vec u zero) [] [] sol look tri init isSol = sq ([] , `VecValBaseRepr)
indToIRSound r (`Vec u (suc x)) vec val sol look tri init isSol with splitAt (tySize u) vec | inspect (splitAt (tySize u)) vec
... | fst , snd | [ prf₁ ] with splitAt (tySize u) val | inspect (splitAt (tySize u)) val
... | fstv , sndv | [ refl ] with indToIRSound r u fst fstv sol {!!} tri init {!!}
... | sq (srep₁ , srep₁Prf)  with indToIRSound r (`Vec u x) snd sndv sol {!!} tri _ {!!}
... | sq (srep₂ , srep₂Prf) = sq ((srep₁ ∷ srep₂) , (`VecValConsRepr srep₁Prf srep₂Prf (sym (splitAtCorrect (tySize u) val))))
indToIRSound r (`Σ u x) vec val sol look tri init isSol = {!tyCondSound r (`Σ u x) vec val sol look tri init ?!}
indToIRSound r (`Π u x) vec val sol look tri init isSol = {!!}

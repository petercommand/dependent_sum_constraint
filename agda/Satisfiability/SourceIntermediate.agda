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
        (fToℕ∘ℕtoF≈ : ∀ x → ℕtoF (fToℕ (ℕtoF x)) ≡ ℕtoF x)
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
open import Satisfiability.SourceIntermediate.LogicGates f _≟F_ field' isField finite showf fToℕ ℕtoF ℕtoF-1≡1 ℕtoF-0≡0 prime isPrime
open import Satisfiability.SourceIntermediate.SimpleComp f _≟F_ field' isField finite showf fToℕ ℕtoF ℕtoF-1≡1 ℕtoF-0≡0 prime isPrime onef≠zerof

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

tyCondFuncRepr : ∀ u → (vec : Vec ℕ (tySize u)) → tyCondFunc u vec ≡ 1 → ∃ (λ elem → ValIsRepr u elem vec)

enumSigmaCondFuncRepr : ∀ u eu x elem val₁ val₂
  → ValIsRepr u elem val₁
  → elem ∈ eu
  → enumSigmaCondFunc u eu x val₁ val₂ ≡ 1
  → ∃ (λ elem₁ → ValIsRepr (x elem) elem₁ (proj₁ (maxTySplit u elem x val₂)))
enumSigmaCondFuncRepr u .(elem ∷ _) x elem val₁ val₂ isRepr (here refl) eq = {!andFunc⁻₁ eq!}
enumSigmaCondFuncRepr u (m ∷ ._) x elem val₁ val₂ isRepr (there mem) eq with maxTySplit u m x val₂
... | fst , snd with (impFunc (varEqLitFunc u val₁ m) (andFunc (tyCondFunc (x m) fst) (allEqzFunc snd)))
... | t with ℕtoF t ≟F zerof
enumSigmaCondFuncRepr u (m ∷ xs) x elem val₁ val₂ isRepr (there mem) eq | fst , snd | t | no ¬p with ℕtoF (enumSigmaCondFunc u xs x val₁ val₂) ≟F zerof
enumSigmaCondFuncRepr u (m ∷ xs) x elem val₁ val₂ isRepr (there mem) eq | fst , snd | t | no ¬p | no ¬p₁ with enumSigmaCondFuncIsBoolStrict u xs x val₁ val₂
enumSigmaCondFuncRepr u (m ∷ _) x elem val₁ val₂ isRepr (there mem) eq | fst , snd | t | no ¬p | no ¬p₁ | isZeroS x₁ = ⊥-elim (¬p₁ (trans (cong ℕtoF x₁) ℕtoF-0≡0))
enumSigmaCondFuncRepr u (m ∷ _) x elem val₁ val₂ isRepr (there mem) eq | fst , snd | t | no ¬p | no ¬p₁ | isOneS x₁ = enumSigmaCondFuncRepr u _ x elem val₁ val₂ isRepr mem x₁



tyCondFuncRepr `One (x ∷ vec) eq with ℕtoF x ≟F zerof
tyCondFuncRepr `One (x ∷ []) eq | yes p = tt , `OneValRepr x (sq (trans p (sym ℕtoF-0≡0)))
tyCondFuncRepr `Two (x ∷ []) eq with ℕtoF x ≟F zerof
tyCondFuncRepr `Two (x ∷ []) eq | yes p = false , (`TwoValFalseRepr x (sq (trans p (sym ℕtoF-0≡0))))
tyCondFuncRepr `Two (x ∷ []) eq | no ¬p with ℕtoF x ≟F onef
tyCondFuncRepr `Two (x ∷ []) eq | no ¬p | yes p = true , `TwoValTrueRepr x (sq (trans p (sym ℕtoF-1≡1)))
tyCondFuncRepr `Base (x ∷ []) eq = (ℕtoF x) , `BaseValRepr (sq (fToℕ∘ℕtoF≈ x))
tyCondFuncRepr (`Vec u zero) [] eq = [] , `VecValBaseRepr
tyCondFuncRepr (`Vec u (suc x)) vec eq with splitAt (tySize u) vec | inspect (splitAt (tySize u)) vec
... | fst , snd | [ refl ] with tyCondFuncRepr u fst {!!}
... | elem₁ , ind₁ with tyCondFuncRepr (`Vec u x) snd {!!}
... | elem₂ , ind₂ = (elem₁ ∷ elem₂) , (`VecValConsRepr ind₁ ind₂ (sym (splitAtCorrect (tySize u) vec)))
tyCondFuncRepr (`Σ u x) vec eq with splitAt (tySize u) vec | inspect (splitAt (tySize u)) vec
... | fst , snd | [ refl ] with ℕtoF (tyCondFunc u (proj₁ (splitAt (tySize u) vec))) ≟F zerof
tyCondFuncRepr (`Σ u x) vec eq | ._ , ._ | [ refl ] | no ¬p with ℕtoF (enumSigmaCondFunc u (enum u) x (proj₁ (splitAt (tySize u) vec))
                         (proj₂ (splitAt (tySize u) vec))) ≟F zerof
tyCondFuncRepr (`Σ u x) vec eq | ._ , ._ | [ refl ] | no ¬p | no ¬p₁ with tyCondFuncIsBoolStrict u (proj₁ (splitAt (tySize u) vec))
tyCondFuncRepr (`Σ u x) vec eq | ._ , ._ | [ refl ] | no ¬p | no ¬p₁ | isZeroS x₁ = ⊥-elim (¬p (trans (cong ℕtoF x₁) ℕtoF-0≡0))
tyCondFuncRepr (`Σ u x) vec eq | ._ , ._ | [ refl ] | no ¬p | no ¬p₁ | isOneS x₁ with enumSigmaCondFuncIsBoolStrict u (enum u) x (proj₁ (splitAt (tySize u) vec)) (proj₂ (splitAt (tySize u) vec))
tyCondFuncRepr (`Σ u x) vec eq | ._ , ._ | [ refl ] | no ¬p | no ¬p₁ | isOneS x₁ | isZeroS x₂ = ⊥-elim (¬p₁ (trans (cong ℕtoF x₂) ℕtoF-0≡0))
tyCondFuncRepr (`Σ u x) vec eq | fst , snd | [ refl ] | no ¬p | no ¬p₁ | isOneS x₁ | isOneS x₂ with tyCondFuncRepr u fst x₁
... | elem₁ , ind₁ with tyCondFuncRepr (x elem₁) (proj₁ (maxTySplit u elem₁ x snd)) {!!}
... | elem₂ , ind₂  =   (elem₁ , elem₂) , `ΣValRepr x snd ind₁ ind₂
                                    (enumSigmaCondRestZ u (enum u) x fst snd elem₁ (enumComplete u elem₁) {!!})
                                    (maxTySplitCorrect u elem₁ x snd) (sym (splitAtCorrect (tySize u) vec))

{-
 with tyCondFuncRepr u fst {!!}
... | elem₁ , ind₁ with tyCondFuncRepr (x elem₁) (proj₁ (maxTySplit u elem₁ x snd)) {!!}
... | elem₂ , ind₂ 
       (elem₁ , elem₂) , `ΣValRepr x snd ind₁ ind₂
                                    (enumSigmaCondRestZ u (enum u) x fst snd elem₁ (enumComplete u elem₁) p)
                                    (maxTySplitCorrect u elem₁ x snd) (sym (splitAtCorrect (tySize u) vec))
... | isZeroS p = ⊥-elim (¬p₁ (trans (cong ℕtoF p) ℕtoF-0≡0))
-}
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
indToIRSound r `Base .(v ∷ []) (x ∷ []) sol (BatchLookupCons v .x .[] .[] .sol x₁ (BatchLookupNil .sol)) tri init isSol = sq ((ℕtoF x) , (`BaseValRepr (sq (fToℕ∘ℕtoF≈ x))))
indToIRSound r (`Vec u zero) [] [] sol look tri init isSol = sq ([] , `VecValBaseRepr)
indToIRSound r (`Vec u (suc x)) vec val sol look tri init isSol with splitAt (tySize u) vec | inspect (splitAt (tySize u)) vec
... | fst , snd | [ prf₁ ] with splitAt (tySize u) val | inspect (splitAt (tySize u)) val
... | fstv , sndv | [ refl ] with indToIRSound r u fst fstv sol {!!} tri init {!!}
... | sq (srep₁ , srep₁Prf)  with indToIRSound r (`Vec u x) snd sndv sol {!!} tri _ {!!}
... | sq (srep₂ , srep₂Prf) = sq ((srep₁ ∷ srep₂) , (`VecValConsRepr srep₁Prf srep₂Prf (sym (splitAtCorrect (tySize u) val))))
indToIRSound r (`Σ u x) vec val sol look tri init isSol = {!tyCondSound r (`Σ u x) vec val sol look tri init ?!}
indToIRSound r (`Π u x) vec val sol look tri init isSol = {!!}

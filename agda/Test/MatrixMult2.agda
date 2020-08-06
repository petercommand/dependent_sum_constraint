{-# OPTIONS --prop #-}
module Test.MatrixMult2 where
open import Agda.Builtin.Nat

open import Data.Bool renaming (_≟_ to _≟B_)
open import Data.Field
open import Data.Field.Prime
open import Data.Fin hiding (_≟_; _+_; _-_; pred)
open import Data.Fin.Properties hiding (≤-trans; ≤-refl)
open import Data.List hiding (splitAt; map; lookup; foldl; concat; replicate; reverse)
open import Data.MaybeC 
import Data.Map
module M = Data.Map
open import Data.Map using (Map)
open import Data.Nat renaming (_≟_ to _ℕ≟_)
open import Data.Nat.DivMod
open import Data.Nat.Max
open import Data.Nat.Primality
open import Data.Nat.Properties
open import Data.Nat.Properties2
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product hiding (map)
open import Data.ProductPrime
open import Data.Unit hiding (_≟_)
open import Data.Vec hiding (_>>=_; splitAt) renaming (_++_ to _V++_)
open import Data.Vec.Split
open import Function

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)

open import TypeClass.Ord

N = 21888242871839275222246405745257275088548364400416034343698204186575808495617

choice = 1
input1 = 99
input2 = 100
input3 = 384
input4 = 390

postulate
  nPrime : Prime N

FF = PrimeField N
FField = isField N nPrime
FFinite = isFinite N nPrime

open Field FField renaming ( _+_ to _+F_
                           ; _*_ to _*F_
                           ; -_ to -F_
                           ; 1/_ to 1F/_
                           ; zero to zerof
                           ; one to onef)


open import Language.Common


module Test where
  open import Language.Source FF FFinite (λ x → showℕ (PrimeField.elem x) )
  open import Language.Source.Utils FF FFinite (λ x → showℕ (PrimeField.elem x) )
  open import Language.TySize FF FFinite
  open import Language.Universe FF

  _**_ : ℕ → ℕ → ℕ
  m ** zero = 1
  m ** suc n = (m ** n) * m

  data Bits : ℕ → Set where
    zero one : Bits 1
    0+ : ∀ {n} → Bits n → Bits (suc n)
    1+ : ∀ {n} → Bits n → Bits (suc n)

  data BitsR : ℕ → Set where
    zero one : BitsR 1
    2n : ∀ {n} → BitsR n → BitsR (suc n)
    2n+1 : ∀ {n} → BitsR n → BitsR (suc n)

  bitsToℕAux : ∀ {n} → Bits n → ℕ → ℕ
  bitsToℕAux zero acc = acc * 2
  bitsToℕAux one acc = acc * 2 + 1
  bitsToℕAux (0+ b) acc = bitsToℕAux b (acc * 2)
  bitsToℕAux (1+ b) acc = bitsToℕAux b (acc * 2 + 1)

  bitsToℕ : ∀ {n} → Bits n → ℕ
  bitsToℕ b = bitsToℕAux b 0

  /Fin2 : ∀ {n} → Fin (2 ** (suc n)) → Fin (2 ** n)
  /Fin2 {n} f = fromℕ≤ {toℕ f / 2} (*-cancelʳ-< (toℕ f / 2) (2 ** n) (≤-trans (s≤s (m/n*n≤m (toℕ f) 2)) (toℕ<n f)))

  %Fin2 : ∀ {n} → Fin (suc n) → Bool
  %Fin2 f with toℕ f % 2 
  %Fin2 f | 0F = false
  %Fin2 f | suc a = true

  **-suc : ∀ n → ∃ (λ m → 2 ** n ≡ suc m)
  **-suc 0F = 0F , refl
  **-suc (suc n) with **-suc n
  ... | m , prf rewrite prf = suc (m * 2F) , refl
  
  Fin2→BitsR : ∀ n → Fin (2 ** (suc n)) → BitsR (suc n)
  Fin2→BitsR 0F 0F = zero
  Fin2→BitsR 0F 1F = one
  Fin2→BitsR (suc n) f with **-suc (suc (suc n))
  Fin2→BitsR (suc n) f | m , prf with %Fin2 (subst Fin prf f)
  Fin2→BitsR (suc n) f | _       | false = 2n (Fin2→BitsR n (/Fin2 {suc n} f))
  Fin2→BitsR (suc n) f | _       | true = 2n+1 (Fin2→BitsR n (/Fin2 {suc n} f))

  BitsR→BitsAux : ∀ {m n} → BitsR m → Bits n → Bits (m + n)
  BitsR→BitsAux zero acc = 0+ acc
  BitsR→BitsAux one acc = 1+ acc
  BitsR→BitsAux {suc m} {n} (2n b) acc rewrite sym (+-suc m n) = BitsR→BitsAux b (0+ acc)
  BitsR→BitsAux {suc m} {n} (2n+1 b) acc rewrite sym (+-suc m n) = BitsR→BitsAux b (1+ acc)

  BitsR→Bits : ∀ {m} → BitsR m → Bits m
  BitsR→Bits zero = zero
  BitsR→Bits one = one
  BitsR→Bits {suc m} (2n b) rewrite +-comm 1 m = BitsR→BitsAux b zero
  BitsR→Bits {suc m} (2n+1 b) rewrite +-comm 1 m = BitsR→BitsAux b one

  Fin2→Bits : ∀ n → Fin (2 ** (suc n)) → Bits (suc n)
  Fin2→Bits n f = BitsR→Bits (Fin2→BitsR n f)

  Σₙ'F : (ℕ → U) → ℕ → ℕ → ⟦ `Two ⟧ → U
  Σₙ' : (ℕ → U) → ℕ → ℕ → U
  
  Σₙ'F ty m acc false = Σₙ' ty m (acc * 2)
  Σₙ'F ty m acc true = Σₙ' ty m (acc * 2 + 1)

  Σₙ' ty 0 acc = ty acc
  Σₙ' ty (suc m) acc = `Σ `Two (Σₙ'F ty m acc)

  Σₙ : (ℕ → U) → ℕ → U
  Σₙ ty m = Σₙ' ty m 0

  ΣₙIndSizeAux : (ty : ℕ → U) (n acc : ℕ) → Vec ℕ (tySize (Σₙ' ty n acc)) → Vec ℕ n
  ΣₙIndSizeAux ty 0F acc vec = []
  ΣₙIndSizeAux ty (suc n) acc vec with splitAt (tySize `Two) vec
  ... | fst ∷ [] , snd with maxTySplit `Two false (Σₙ'F ty n acc) snd
  ... | snd₁ , snd₂ = fst ∷ ΣₙIndSizeAux ty n (acc * 2) snd₁

  ΣₙIndSize : (ty : ℕ → U) (n : ℕ) → Vec ℕ (tySize (Σₙ ty n)) → Vec ℕ n
  ΣₙIndSize ty n vec = ΣₙIndSizeAux ty n 0 vec

  ΣₙIndBodyAux : (ty : ℕ → U) (n acc : ℕ) → (b : Bits n) → Vec ℕ (tySize (Σₙ' ty n acc)) → Vec ℕ (tySize (ty (bitsToℕAux b acc)))
  ΣₙIndBodyAux ty 1F acc zero vec with splitAt (tySize `Two) vec
  ... | _ , snd with maxTySplit `Two false (Σₙ'F ty 0 acc) snd
  ... | snd₁ , snd₂ = snd₁
  ΣₙIndBodyAux ty 1F acc one vec with splitAt (tySize `Two) vec
  ... | _ , snd with maxTySplit `Two true (Σₙ'F ty 0 acc) snd
  ... | snd₁ , snd₂ = snd₁
  ΣₙIndBodyAux ty (suc (suc n)) acc (0+ b) vec with splitAt (tySize `Two) vec
  ... | _ , snd with maxTySplit `Two false (Σₙ'F ty (suc n) acc) snd
  ... | snd₁ , snd₂ = ΣₙIndBodyAux ty (suc n) (acc * 2) b snd₁
  ΣₙIndBodyAux ty (suc (suc n)) acc (1+ b) vec with splitAt (tySize `Two) vec
  ... | _ , snd with maxTySplit `Two true (Σₙ'F ty (suc n) acc) snd
  ... | snd₁ , snd₂ = ΣₙIndBodyAux ty (suc n) (acc * 2 + 1) b snd₁

  ΣₙIndBody : (ty : ℕ → U) (n : ℕ) → (b : Bits n) → Vec ℕ (tySize (Σₙ ty n)) → Vec ℕ (tySize (ty (bitsToℕ b)))
  ΣₙIndBody ty n b vec = ΣₙIndBodyAux ty n 0 b vec

  ΣₙSize≥Aux : (ty : ℕ → U) (n acc : ℕ) → (b : Bits n) → tySize (Σₙ' ty n acc) ≥ n + (tySize (ty (bitsToℕAux b acc)))
  ΣₙSize≥Aux ty (suc .0) acc zero = s≤s (max-left (tySize (ty (acc * 2))) (max (tySize (ty (acc * 2 + 1))) 0))
  ΣₙSize≥Aux ty (suc .0) acc one = s≤s (max-monotoneᵣ
                                          (tySize (ty (acc * 2)))
                                          (max (tySize (ty (acc * 2 + 1))) 0)
                                          (tySize (ty (acc * 2 + 1)))
                                          (max-left (tySize (ty (acc * 2 + 1))) 0))
  ΣₙSize≥Aux ty (suc n) acc (0+ b) = s≤s (≤-trans (ΣₙSize≥Aux ty n (acc * 2) b)
                                                  (max-left (tySize (Σₙ' ty n (acc * 2)))
                                                            (max (tySize (Σₙ' ty n (acc * 2 + 1))) 0)))
  ΣₙSize≥Aux ty (suc n) acc (1+ b) = s≤s (≤-trans (ΣₙSize≥Aux ty n (acc * 2 + 1) b)
                                              (max-monotoneᵣ (tySize (Σₙ' ty n (acc * 2)))
                                                 (max (tySize (Σₙ' ty n (acc * 2 + 1))) 0)
                                                 (tySize (Σₙ' ty n (acc * 2 + 1)))
                                                 (max-left (tySize (Σₙ' ty n (acc * 2 + 1))) 0)))

  ΣₙSize≥ : (ty : ℕ → U) (n : ℕ) → (b : Bits n) → tySize (Σₙ ty n) ≥ n + (tySize (ty (bitsToℕ b)))
  ΣₙSize≥ ty n b = ΣₙSize≥Aux ty n 0 b

  ΣₙIndRest : (ty : ℕ → U) (n : ℕ) → (b : Bits n)
      → Vec ℕ (tySize (Σₙ ty n))
      → Vec ℕ (tySize (Σₙ ty n) - (n + (tySize (ty (bitsToℕ b)))))
  ΣₙIndRest ty n b vec with splitAt (n + (tySize (ty (bitsToℕ b)))) (subst (Vec ℕ) (sym (a-b+b≡a₂ (tySize (Σₙ ty n)) (n + (tySize (ty (bitsToℕ b)))) (ΣₙSize≥ ty n b))) vec)
  ... | fst , snd = snd

  ΣₙLitSizeAux : (ty : ℕ → U) (n acc : ℕ) → ⟦ Σₙ' ty n acc ⟧ → Vec ⟦ `Base ⟧ n
  ΣₙLitSizeAux ty 0 acc lit = []
  ΣₙLitSizeAux ty (suc n) acc (false , snd₁) = fieldElem nPrime 0 ∷ ΣₙLitSizeAux ty n (acc * 2) snd₁
  ΣₙLitSizeAux ty (suc n) acc (true , snd₁) = fieldElem nPrime 1 ∷ ΣₙLitSizeAux ty n (acc * 2 + 1) snd₁

  ΣₙLitSize : (ty : ℕ → U) (n : ℕ) → ⟦ Σₙ ty n ⟧ → Vec ⟦ `Base ⟧ n
  ΣₙLitSize ty n lit = ΣₙLitSizeAux ty n 0 lit

  ΣₙSize : (ty : ℕ → U) (n : ℕ) → Source (Σₙ ty n) → Vec (Source `Two) n
  ΣₙSize ty n s = ΣₙSizeAux n 0 s
    where
      ΣₙSizeAux : (n acc : ℕ) → Source (Σₙ' ty n acc) → Vec (Source `Two) n
      ΣₙSizeAux 0F acc s = []
      ΣₙSizeAux (suc n) acc (Ind refl x₁) with splitAt (tySize `Two) x₁
      ... | fst , snd   with maxTySplit `Two false (Σₙ'F ty n acc) snd
      ... | snd₁ , snd₂ = Ind refl fst ∷ ΣₙSizeAux n (acc * 2) (Ind refl snd₁)
      ΣₙSizeAux (suc n) acc (Lit (false , snd₁)) = Lit false ∷ ΣₙSizeAux n (acc * 2) (Lit snd₁)
      ΣₙSizeAux (suc n) acc (Lit (true , snd₁)) = Lit true ∷ ΣₙSizeAux n (acc * 2 + 1) (Lit snd₁)

  `Matrix : U → ℕ → ℕ → U
  `Matrix ty m n = Σₙ (λ m → Σₙ (λ n → `Vec (`Vec ty n) m) n) m

  matrixIndSizeAux : (m n acc : ℕ) → Vec ℕ (tySize (Σₙ' (λ m → Σₙ (λ n → `Vec (`Vec `Base n) m) n) m acc)) → Vec ℕ (m + n)
  matrixIndSizeAux 0F n acc vec = ΣₙIndSize (λ n → `Vec (`Vec `Base n) acc) n vec
  matrixIndSizeAux (suc m) n acc vec with splitAt (tySize `Two) vec
  ... | fst ∷ [] , snd   with maxTySplit `Two false (Σₙ'F (λ m → Σₙ (λ n → `Vec (`Vec `Base n) m) n) m acc) snd
  ... | snd₁ , snd₂ = fst ∷ matrixIndSizeAux m n (acc * 2) snd₁

  matrixIndSize : (m n : ℕ) → Vec ℕ (tySize (`Matrix `Base m n)) → Vec ℕ (m + n)
  matrixIndSize m n vec = matrixIndSizeAux m n 0 vec

  matrixLitSizeAux : (m n acc : ℕ) → ⟦ Σₙ' (λ m → Σₙ (λ n → `Vec (`Vec `Base n) m) n) m acc ⟧ → Vec ⟦ `Base ⟧ (m + n)
  matrixLitSizeAux 0 n acc lit = ΣₙLitSize (λ n → `Vec (`Vec `Base n) acc) n lit
  matrixLitSizeAux (suc m) n acc (false , snd₁) = fieldElem nPrime 0 ∷ matrixLitSizeAux m n (acc * 2) snd₁
  matrixLitSizeAux (suc m) n acc (true , snd₁) = fieldElem nPrime 1 ∷ matrixLitSizeAux m n (acc * 2 + 1) snd₁

  matrixLitSize : (m n : ℕ) → ⟦ `Matrix `Base m n ⟧ → Vec ⟦ `Base ⟧ (m + n)
  matrixLitSize m n lit = matrixLitSizeAux m n 0 lit

  matrixSize : (m n : ℕ) → {_ : True (m ℕ≟ suc (pred m))} → Source (`Matrix `Base m n) → Source (`Vec `Base (m + n))
  matrixSize (suc m) n (Ind refl x) = Ind (cong suc (sym (*-identityʳ (m + n)))) (matrixIndSize (suc m) n x)
  matrixSize (suc m) n (Lit x) = Lit (matrixLitSize (suc m) n x)



  matrixIndBody : (m n : ℕ) → (bm : Bits m) → (bn : Bits n) → Vec ℕ (tySize (`Matrix `Base m n)) → Vec ℕ (tySize (`Vec (`Vec `Base (bitsToℕ bn)) (bitsToℕ bm)))
  matrixIndBody m n bm bn vec =
      ΣₙIndBody (λ n → `Vec (`Vec `Base n) (bitsToℕ bm)) n bn
         (ΣₙIndBody (λ m → Σₙ (λ n → `Vec (`Vec `Base n) m) n) m bm vec)

  matrixIndRest : (m n : ℕ) → (bm : Bits m) → (bn : Bits n)
     → Vec ℕ (tySize (`Matrix `Base m n))
     → Vec ℕ (tySize (Σₙ (λ n₁ → `Vec (`Vec `Base n₁) (bitsToℕ bm)) n) ∸
                (n + tySize (`Vec (`Vec `Base (bitsToℕ bn)) (bitsToℕ bm))) +
             (tySize (Σₙ (λ m₁ → Σₙ (λ n₁ → `Vec (`Vec `Base n₁) m₁) n) m) ∸
                (m + tySize (Σₙ (λ n₁ → `Vec (`Vec `Base n₁) (bitsToℕ bm)) n))))
  matrixIndRest m n bm bn vec = let rest₁ = ΣₙIndRest (λ m → Σₙ (λ n → `Vec (`Vec `Base n) m) n) m bm vec
                                    body₁ = ΣₙIndBody (λ m → Σₙ (λ n → `Vec (`Vec `Base n) m) n) m bm vec
                                    rest₂ = ΣₙIndRest (λ n₁ → `Vec (`Vec `Base n₁) (bitsToℕ bm)) n bn body₁
                                in rest₂ V++ rest₁ 
  
  splitSourceVec : ∀ m {n u} → Source (`Vec u (m + n)) → Source (`Vec u m) × Source (`Vec u n)
  splitSourceVec m {n} {u} (Ind refl x) rewrite *-distribʳ-+ (tySize u) m n
      with splitAt (m * tySize u) x
  ... | fst , snd = Ind refl fst , Ind refl snd
  splitSourceVec m (Lit x) with splitAt m x
  ... | fst , snd = Lit fst , Lit snd

  conΣₙ' : (u : ℕ → U) {n : ℕ} (sz : Bits n) (acc : ℕ) → ⟦ u (bitsToℕAux sz acc) ⟧ → ⟦ Σₙ' u n acc ⟧
  conΣₙ' u zero acc lit = false , lit
  conΣₙ' u one acc lit = true , lit
  conΣₙ' u (0+ sz) acc lit = false , conΣₙ' u sz (acc * 2) lit
  conΣₙ' u (1+ sz) acc lit = true , conΣₙ' u sz (acc * 2 + 1) lit

  conΣℕ : (n : ℕ) (sz : Fin (2 ** n)) → ℕ
  conΣℕ 0 sz = 0
  conΣℕ (suc n) sz = bitsToℕ (Fin2→Bits n sz)

  conΣₙ : (u : ℕ → U) (n : ℕ) (sz : Fin (2 ** n)) → ⟦ u (conΣℕ n sz) ⟧ → ⟦ Σₙ u n ⟧
  conΣₙ u 0 sz lit = lit
  conΣₙ u (suc n) sz lit = conΣₙ' u (Fin2→Bits n sz) 0 lit

  conMatrix : (u : U) (m n : ℕ)
    → (sz₁ : Fin (2 ** m)) → (sz₂ : Fin (2 ** n))
    → ⟦ `Vec (`Vec u (conΣℕ n sz₂)) (conΣℕ m sz₁) ⟧ → ⟦ `Matrix u m n ⟧
  conMatrix u m n sz₁ sz₂ lit = conΣₙ (λ m → Σₙ (λ n → `Vec (`Vec u n) m) n) m sz₁
                                  (conΣₙ (λ n → `Vec (`Vec u n) (conΣℕ m sz₁)) n sz₂ lit)

  matrix₁ : ⟦ `Matrix `Base 5 5 ⟧
  matrix₁ = conMatrix `Base 5 5 (# 3) (# 4)
               (map (map (fieldElem nPrime))
                 ((1 ∷  2 ∷  3 ∷  4 ∷ []) ∷
                  (5 ∷  6 ∷  7 ∷  8 ∷ []) ∷
                  (9 ∷ 10 ∷ 11 ∷ 12 ∷ []) ∷ []))

  Σ-proj₁ : ∀ {u} {x : ⟦ u ⟧ → U} → Source (`Σ u x) → Source u
  Σ-proj₁ {u} (Ind refl x₁) with splitAt (tySize u) x₁
  ... | fst , snd = Ind refl fst
  Σ-proj₁ (Lit (fst , snd)) = Lit fst

  var : ℕ → Source `Base
  var n = Ind refl (n ∷ [])

  land : Var → Var → S-Monad Var
  land n₁ n₂ = do
    r ← S-Monad.newVar
    assertEq (Mul (var n₁) (var n₂)) (var r)
    return r

  lor : Var → Var → S-Monad Var
  lor n₁ n₂ = do
    r ← S-Monad.newVar
    assertEq (Add (Add (var n₁) (var n₂)) (Mul (Lit (-F onef)) (Mul (var n₁) (var n₂)))) (var r)
    return r
  lnot : Var → S-Monad Var
  lnot n = do
    v ← S-Monad.newVar
    assertEq (Add (Lit onef) (Mul (Lit (-F onef)) (var n))) (var v)
    return v
  limp : Var → Var → S-Monad Var
  limp n₁ n₂ = do
    notℕ₁ ← lnot n₁
    lor notℕ₁ n₂
  
  assertEqWithCond : ∀ {n} → Var → Vec Var n → Vec Var n → S-Monad ⊤
  assertEqWithCond v [] [] = return tt
  assertEqWithCond v (x₁ ∷ vec₁) (x₂ ∷ vec₂) = do
    assertEq (Mul (var v) (var x₁)) (Mul (var v) (var x₂))
    assertEqWithCond v vec₁ vec₂

  szEqIndBit : Var → Bits 1 → S-Monad Var
  szEqIndBit v zero = lnot v
  szEqIndBit v one = return v

  szEqLitBit : FF → Bits 1 → S-Monad Var
  szEqLitBit record { elem = 0F ; nIsPrime = nIsPrime ; elem<n = elem<n } zero = return 0
  szEqLitBit record { elem = (suc elem) ; nIsPrime = nIsPrime ; elem<n = elem<n } zero = do
    v ← S-Monad.newVar
    assertEq (Ind refl (v ∷ [])) (Lit zerof)
    return v
  szEqLitBit record { elem = 0F ; nIsPrime = nIsPrime ; elem<n = elem<n } one = do
    v ← S-Monad.newVar
    assertEq (Ind refl (v ∷ [])) (Lit zerof)
    return v
  szEqLitBit record { elem = (suc elem) ; nIsPrime = nIsPrime ; elem<n = elem<n } one = return 0

  -- szEq treats the vector as a vector of bools (which is justified by the Σ type constriants)
  szEq : ∀ {m} → Source (`Vec `Base m) → Bits m → S-Monad Var
  szEq {1F} (Ind refl (x ∷ [])) b = szEqIndBit x b
  szEq {1F} (Lit (l ∷ [])) b = szEqLitBit l b
  szEq {suc (suc m)} (Ind refl (x ∷ x₁)) (0+ b) = do
    r₁ ← szEqIndBit x zero
    r₂ ← szEq (Ind refl x₁) b
    land r₁ r₂
  szEq {suc (suc m)} (Ind refl (x ∷ x₁)) (1+ b) = do
    r₁ ← szEqIndBit x one
    r₂ ← szEq (Ind refl x₁) b
    land r₁ r₂
  szEq {suc (suc m)} (Lit (x ∷ x₁)) (0+ b) = do
    r₁ ← szEqLitBit x zero
    r₂ ← szEq (Lit x₁) b
    land r₁ r₂
  szEq {suc (suc m)} (Lit (x ∷ x₁)) (1+ b) = do
    r₁ ← szEqLitBit x one
    r₂ ← szEq (Lit x₁) b
    land r₁ r₂

  concat⁻¹ : ∀ m n → Vec Var (m * n) → Vec (Vec Var n) m
  concat⁻¹ 0F n v = []
  concat⁻¹ (suc m) n v with splitAt n v
  ... | fst , snd = fst ∷ concat⁻¹ m n snd

  getMatrix : ∀ {m} {n} → Vec Var (m * n) → Fin m → Fin n → Var
  getMatrix {m} {n} s fm fn = lookup (lookup (concat⁻¹ m n s) fm) fn
  
  matrixMultAux : ∀ m n o
      → {_ : True (m ℕ≟ suc (pred m))} → {_ : True (n ℕ≟ suc (pred n))} → {_ : True (o ℕ≟ suc (pred o))}
      → Var -- condition for correct sizes
      → (sz₁ : Fin (2 ** m)) (sz₂ : Fin (2 ** n)) (sz₃ : Fin (2 ** o))
      → Vec Var (tySize (`Matrix `Base m n)) → Vec Var (tySize (`Matrix `Base n o)) → Vec Var (tySize (`Matrix `Base m o))
      → S-Monad ⊤
  matrixMultAux m@(suc m') n@(suc n') o@(suc o') cond sz₁ sz₂ sz₃ x y z = do
    let
      x' = matrixIndBody m n (Fin2→Bits m' sz₁) (Fin2→Bits n' sz₂) x
      y' = matrixIndBody n o (Fin2→Bits n' sz₂) (Fin2→Bits o' sz₃) y
      z' = matrixIndBody m o (Fin2→Bits m' sz₁) (Fin2→Bits o' sz₃) z
    iterM (bitsToℕ (Fin2→Bits m' sz₁)) (λ a → do
      iterM (bitsToℕ (Fin2→Bits o' sz₃)) (λ b → do
        multResult <- iterM (bitsToℕ (Fin2→Bits n' sz₂)) (λ c → do
          let fstElem = getMatrix x' a (subst Fin (sym (*-identityʳ (bitsToℕ (Fin2→Bits n' sz₂)))) c)
              sndElem = getMatrix y' c (subst Fin (sym (*-identityʳ (bitsToℕ (Fin2→Bits o' sz₃)))) b)
          return (Mul (Ind refl (fstElem ∷ [])) (Ind refl (sndElem ∷ []))))
        let addMultResult = foldl (const (Source `Base)) Add (Lit (fieldElem nPrime 0)) multResult
            setElem = getMatrix z' a (subst Fin (sym (*-identityʳ (bitsToℕ (Fin2→Bits o' sz₃)))) b)
        assertEq (Mul (Ind refl (setElem ∷ [])) (var cond)) (Mul addMultResult (var cond))))
    return tt


  getVecFromMap : ∀ m → Vec Var m → M.Map Var ℕ → MaybeC (Vec ℕ m)
  getVecFromMap  0 []  map = just []
  getVecFromMap (suc m) (x ∷ vec) map
    = case getVecFromMap m vec map of
        λ { nothing → nothing
          ; (just ns) → case M.lookup natOrd x map of
                            λ { nothing → nothing
                              ; (just n) → just (n ∷ ns)
                              }
          }

  Mret : {A : Set} → A → MaybeC A
  Mret a = just a
  _M>>=_ : {A B : Set} → MaybeC A → (A → MaybeC B) → MaybeC B
  nothing M>>= f = nothing
  just x M>>= f = f x

  setVecMap : ∀ m → Vec Var m → Vec ℕ m → M.Map Var ℕ → M.Map Var ℕ
  setVecMap .0 [] [] map = map
  setVecMap .(suc _) (var ∷ vars) (val ∷ vals) map = M.insert natOrd var val (setVecMap _ vars vals map)


  getSizeFromMap : ∀ m → {_ : True (m ℕ≟ suc (pred m))} → Vec Var m → M.Map Var ℕ → MaybeC (Bits m)
  getSizeFromMap (suc .0) (x ∷ []) map = case M.lookup natOrd x map of
                                           λ { nothing → nothing
                                             ; (just zero) → just zero
                                             ; (just _) → just one
                                             }
  getSizeFromMap (suc (suc m)) (x ∷ y ∷ vec) map
    = case getSizeFromMap (suc m) {subst {_} {_} {_} True {yes refl} (sym (≟-diag refl)) tt} (y ∷ vec) map of
        λ { nothing → nothing
          ; (just bits) → case M.lookup natOrd x map of
                            λ { nothing → nothing
                              ; (just 0) → just (0+ bits)
                              ; (just _) → just (1+ bits)
                              }
          }


  setBitsMap : ∀ m → Vec Var m → Bits m → M.Map Var ℕ → M.Map Var ℕ
  setBitsMap .1 (x ∷ vec) zero map = M.insert natOrd x 0 map
  setBitsMap .1 (x ∷ vec) one map = M.insert natOrd x 1 map
  setBitsMap .(suc _) (x ∷ vec) (0+ b) map = M.insert natOrd x 0 (setBitsMap _ vec b map)
  setBitsMap .(suc _) (x ∷ vec) (1+ b) map = M.insert natOrd x 1 (setBitsMap _ vec b map)
  
  iter : ∀ {ℓ} {A : Set ℓ} (n : ℕ) → (Fin n → A) → Vec A n
  iter 0 act = []
  iter (suc n) act = 
    let r = act (#_ n {suc n} {fromWitness ≤-refl})
        rs = iter n (λ m → act (castF (inject+ 1 m)))
    in r ∷ rs
   where
    castF : Fin (n + 1) → Fin (1 + n)
    castF f rewrite +-comm 1 n = f
  
  matrixMultDirect : ∀ m n o → Vec (Vec ℕ n) m → Vec (Vec ℕ o) n → Vec (Vec ℕ o) m
  matrixMultDirect m n o v₁ v₂ =
    reverse
      (iter m (λ m' →
        reverse 
          (iter o (λ o' →
            let list = iter n (λ n' → lookup (lookup v₁ m') n' * lookup (lookup v₂ n') o')
            in foldl (const ℕ) _+_ 0 list))))
  matrixMultHint : ∀ m n o
      → {_ : True (m ℕ≟ suc (pred m))} → {_ : True (n ℕ≟ suc (pred n))} → {_ : True (o ℕ≟ suc (pred o))}
      → Vec Var (tySize (`Matrix `Base m n)) → Vec Var (tySize (`Matrix `Base n o)) → Vec Var (tySize (`Matrix `Base m o))
      → M.Map Var ℕ → M.Map Var ℕ
  matrixMultHint m@(suc m') n@(suc n') o@(suc o') {p₁} {p₂} {p₃} x y r map
      with splitAt m (matrixIndSize m n x)
                          | splitAt n (matrixIndSize n o y)
                                              | splitAt m (matrixIndSize m o r)
  ... | varRow₁ , varCol₁ | varRow₂ , varCol₂ | varRow₃ , varCol₃
      with
          getSizeFromMap m {p₁} varRow₁ map M>>= λ bm →
          getSizeFromMap n {p₂} varCol₁ map M>>= λ bn →
          getSizeFromMap o {p₃} varCol₂ map M>>= λ bo →
          getVecFromMap _ (matrixIndBody m n bm bn x) map M>>= λ xVals →
          let mat₁ = concat⁻¹ (bitsToℕ bm) (bitsToℕ bn) (subst (λ x → Vec ℕ (bitsToℕAux bm 0 * x)) (*-identityʳ (bitsToℕ bn)) xVals)
          in getVecFromMap _ (matrixIndBody n o bn bo y) map M>>= λ yVals →
          let mat₂ = concat⁻¹ (bitsToℕ bn) (bitsToℕ bo) (subst (λ x → Vec ℕ (bitsToℕAux bn 0 * x)) (*-identityʳ (bitsToℕ bo)) yVals)
              calcResult = concat (matrixMultDirect _ _ _ mat₁ mat₂)
              insertSizesMap = setBitsMap m varRow₃ bm (setBitsMap o varCol₃ bo map)
              insertBodyMap = setVecMap _ (matrixIndBody m o bm bo r) (subst (λ x → Vec ℕ (bitsToℕ bm * x)) (sym (*-identityʳ (bitsToℕ bo))) calcResult) insertSizesMap
              insertRestMap = setVecMap _ (matrixIndRest m o bm bo r) (replicate 0) insertBodyMap
          in Mret insertRestMap
  ... | just newMap = newMap
  ... | nothing = map

  matrixMult : ∀ m n o
      → {_ : True (m ℕ≟ suc (pred m))} → {_ : True (n ℕ≟ suc (pred n))} → {_ : True (o ℕ≟ suc (pred o))}
      → Source (`Matrix `Base m n) → Source (`Matrix `Base n o) → Source (`Matrix `Base m o) → S-Monad ⊤
  matrixMult m@(suc m') n@(suc n') o@(suc o') {p₁} {p₂} {p₃} x y r = do
    x' ← S-Monad.newVars (tySize (`Matrix `Base m n))
    y' ← S-Monad.newVars (tySize (`Matrix `Base n o))
    assertEq x (Ind refl x')
    assertEq y (Ind refl y')
    z' ← S-Monad.newVars (tySize (`Matrix `Base m o))
    addHint (matrixMultHint m n o {p₁} {p₂} {p₃} x' y' z')
    assertEq r (Ind refl z')
    let row₁ , col₁ = splitSourceVec m (matrixSize m n {p₁} x)
        row₂ , col₂ = splitSourceVec n (matrixSize n o {p₂} y)
    assertEq col₁ row₂
    iterM (2 ** m) (λ sz₁ → do
      iterM (2 ** n) (λ sz₂ → do
        iterM (2 ** o) (λ sz₃ → do
          row₁≟sz₁ ← szEq row₁ (Fin2→Bits m' sz₁)
          row₂≟sz₂ ← szEq row₂ (Fin2→Bits n' sz₂)
          col₂≟sz₃ ← szEq col₂ (Fin2→Bits o' sz₃)
          szCond ← S-Monad.newVar
          -- ∧ and together these sizes and use it as the condition to enforce the matrix constraints with assertEqWithCond
          assertEq (Ind refl (szCond ∷ [])) (Mul (Mul (var row₁≟sz₁) (var row₂≟sz₂)) (var col₂≟sz₃))
          matrixMultAux m n o {p₁} {p₂} {p₃} szCond sz₁ sz₂ sz₃ x' y' z')))
    assertEq r (Ind refl z')
    return tt
  test : S-Monad (Source (`Matrix `Base 2 2))
  test = do
    m ← newI (`Matrix `Base 2 2)
    n ← newI (`Matrix `Base 2 2)
    r ← newI (`Matrix `Base 2 2)
    matrixMult 2 2 2 m n r
    return r
open Test

open import Compile.Generate FF FField FFinite (λ x → showℕ (PrimeField.elem x)) PrimeField.elem (fieldElem nPrime)

open import IO

main = let inputAss = (1 , 1) ∷ (2 , 0) ∷ (3 , 1) ∷ (4 , 0) ∷ (5 , 13) ∷ (6 , 15) ∷ (7 , 17) ∷ (8 , 19) ∷ (9 , 0) ∷ (10 , 0) ∷ (11 , 0) ∷ (12 , 0) ∷ (13 , 0) ∷ (14 , 1) ∷ (15 , 0) ∷ (16 , 1) ∷ (17 , 1) ∷ (18 , 39) ∷ (19 , 41) ∷ (20 , 43) ∷ (21 , 45) ∷ (22 , 47) ∷ (23 , 49) ∷ (24 , 0) ∷ (25 , 0) ∷ (26 , 0) ∷ []
       in run (genMain N test inputAss)

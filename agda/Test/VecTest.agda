{-# OPTIONS --prop #-}
module Test.VecTest where
open import Data.Bool renaming (_≟_ to _≟B_)
open import Data.Field
open import Data.Field.Prime
open import Data.Fin hiding (_≟_; _+_)
open import Data.Fin.Properties hiding (≤-trans)
open import Data.List hiding (splitAt; map)
open import Data.MaybeC 
import Data.Map
module M = Data.Map
open import Data.Map using (Map)
open import Data.Nat hiding (_≟_)
open import Data.Nat.DivMod
open import Data.Nat.Primality
open import Data.Nat.Properties
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product hiding (map)
open import Data.ProductPrime
open import Data.Unit hiding (_≟_)
open import Data.Vec hiding (_>>=_; splitAt) renaming (_++_ to _V++_)
open import Data.Vec.Split
open import Function

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

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


  Σₙ' : U → ℕ → ℕ → U
  Σₙ' ty 0 acc = `Vec ty acc
  Σₙ' ty (suc m) acc = `Σ `Two f
    where
      f : ⟦ `Two ⟧ → U
      f false = Σₙ' ty m (acc * 2)
      f true = Σₙ' ty m (acc * 2 + 1)
  Σₙ : U → ℕ → U
  Σₙ ty m = Σₙ' ty m 0

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

  conΣₙ' : (u : U) {n : ℕ} (sz : Bits n) (acc : ℕ) → Vec ⟦ u ⟧ (bitsToℕAux sz acc) → ⟦ Σₙ' u n acc ⟧
  conΣₙ' u zero acc vec = false , vec
  conΣₙ' u one acc vec = true , vec
  conΣₙ' u (0+ sz) acc vec = false , conΣₙ' u sz (acc * 2) vec
  conΣₙ' u (1+ sz) acc vec = true , conΣₙ' u sz (acc * 2 + 1) vec

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

  conΣℕ : (u : U) (n : ℕ) (sz : Fin (2 ** n)) → ℕ
  conΣℕ u 0 sz = 0
  conΣℕ u (suc n) sz = bitsToℕ (Fin2→Bits n sz)

  conΣₙ : (u : U) (n : ℕ) (sz : Fin (2 ** n)) → Vec ⟦ u ⟧ (conΣℕ u n sz) → ⟦ Σₙ u n ⟧
  conΣₙ u 0 sz vec = []
  conΣₙ u (suc n) sz vec = conΣₙ' u (Fin2→Bits n sz) 0 vec

  Σ-proj₁ : ∀ {u} {x : ⟦ u ⟧ → U} → Source (`Σ u x) → Source u
  Σ-proj₁ {u} (Ind refl x₁) with splitAt (tySize u) x₁
  ... | fst , snd = Ind refl fst
  Σ-proj₁ (Lit (fst , snd)) = Lit fst

  var : ℕ → Source `Base
  var n = Ind refl (n ∷ [])

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

  test : S-Monad (Source (Σₙ `Base 5))
  test = do
    choice ← newI (Σₙ `Base 5)
    -- assertEq choice (Lit (false , (false , (false , (true , true , fieldElem nPrime 134 ∷ fieldElem nPrime 678 ∷ fieldElem nPrime 789 ∷ [])))))
    assertEq choice (Lit (conΣₙ `Base 5 (# 3) (map (fieldElem nPrime) (134 ∷ 678 ∷ 789 ∷ []))))
    return choice
open Test

open import Compile.Generate FF FField FFinite (λ x → showℕ (PrimeField.elem x)) PrimeField.elem (fieldElem nPrime)

open import IO

main = let inputAss = []
       in run (genMain N test inputAss)

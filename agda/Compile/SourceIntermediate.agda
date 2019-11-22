open import Agda.Builtin.Nat renaming (zero to nzero)

open import Data.Bool
open import Data.Field
open import Data.Finite
open import Data.List hiding (splitAt; head; take; drop)
open import Data.Nat hiding (_⊔_) renaming (zero to nzero)
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit
open import Data.Vec hiding (_>>=_; _++_; [_]; splitAt)
open import Data.Vec.Split

open import Function
import Function.Endomorphism.Propositional

open import Language.Common

open import Level renaming (zero to lzero; suc to lsuc)

open import Relation.Binary.PropositionalEquality hiding ([_])
module Compile.SourceIntermediate (f : Set) (field' : Field f) (finite : Finite f) where

open import Language.Intermediate f
open import Language.Source f finite
open import Language.TySize f finite
open import Language.Universe f

module SI-Monad where
  
  open Function.Endomorphism.Propositional (List Intermediate) renaming (Endo to Builder) public

  import Control.StateWriter
  open Control.StateWriter Var Builder id _∘′_ hiding (_>>=_; _>>_; return; StateWriterMonad)
  open Control.StateWriter Var Builder id _∘′_ using (_>>=_; _>>_; return) renaming (StateWriterMonad to SI-Monad) public
  
  add : Intermediate → SI-Monad ⊤
  add w' = tell (λ x → [ w' ] ++ x)

  new : SI-Monad Var
  new = do
    s ← get
    put (1 + s)
    return s

  newVarVec : ∀ n → SI-Monad (Vec Var n)
  newVarVec nzero = return []
  newVarVec (suc n) = do
    v ← new
    vs ← newVarVec n
    return (v ∷ vs)
open SI-Monad hiding (SI-Monad)
open SI-Monad using (SI-Monad) public
open Field field' hiding (_+_)

isTrue : Var → SI-Monad ⊤
isTrue v = add (IAdd one ((- one , v) ∷ []))



trivial : SI-Monad Var
trivial = do
  return 0

neqz : Var → SI-Monad Var
neqz n = do
  v ← new
  v' ← new
  add (IMul one v n one v')
  add (IMul one v' n one n)
  return v'


lor : Var → Var → SI-Monad Var
lor n₁ n₂ = do
  -- v = a + b - ab
  v ← new
  v' ← new
  add (IMul one n₁ n₂ one v)
  add (IAdd zero ((one , n₁) ∷ (one , n₂) ∷ (- one , v) ∷ (- one , v') ∷ []))
  return v

land : Var → Var → SI-Monad Var
land n₁ n₂ = do
  v ← new
  add (IMul one n₁ n₂ one v)
  return v

lnot : Var → SI-Monad Var
lnot n₁ = do
  v ← new
  add (IAdd one ((- one , n₁) ∷ (- one , v) ∷ []))
  return v

limp : Var → Var → SI-Monad Var
limp n₁ n₂ = do
  notN₁ ← lnot n₁
  lor notN₁ n₂

varEqBaseLit : Var → f → SI-Monad Var
varEqBaseLit n l = do
  n-l ← new
  add (IAdd (- l) ((one , n) ∷ (- one , n-l) ∷ []))
  ¬r ← neqz n-l
  r ← lnot ¬r
  return r

anyNeqz : ∀ {n} → Vec Var n → SI-Monad Var
anyNeqz [] = trivial
anyNeqz (x ∷ vec) = do
 r ← neqz x
 rs ← anyNeqz vec
 lor r rs

allEqz : ∀ {n} → Vec Var n → SI-Monad Var
allEqz vec = do
  ¬r ← anyNeqz vec
  lnot ¬r

module Private where
  a-zero : ∀ a → a - nzero ≡ a
  a-zero nzero = refl
  a-zero (suc a) = refl
  
  a-b+b≡a : ∀ a b → a ≥ b → (a - b) + b ≡ a
  a-b+b≡a a .0 z≤n rewrite a-zero a | +-comm a 0 = refl
  a-b+b≡a (suc n) (suc m) (s≤s a≥b) rewrite +-comm (n - m) (suc m)
                                          | +-comm m (n - m) = cong suc (a-b+b≡a n m a≥b)

open Private



varEqLit : ∀ u → Vec Var (tySize u) → ⟦ u ⟧ → SI-Monad Var
varEqLit `One vec lit = allEqz vec
varEqLit `Two vec false = allEqz vec
varEqLit `Two vec true = anyNeqz vec
varEqLit `Base vec lit = trivial
varEqLit (`Vec u nzero) vec lit = trivial
varEqLit (`Vec u (suc x)) vec (l ∷ lit) with splitAt (tySize u) vec
... | fst , snd = do
  r ← varEqLit u fst l
  s ← varEqLit (`Vec u x) snd lit
  land r s
varEqLit (`Σ u x) vec (fstₗ , sndₗ) with splitAt (tySize u) vec
... | fst , snd = do
  r ← varEqLit u fst fstₗ
  s ← varEqLit (x fstₗ) (take (tySize (x fstₗ)) vecₜ) sndₗ
  land r s
 where
   vecₜ : Vec Var (tySize (x fstₗ) + ((maxTySizeOver (enum u) x) - tySize (x fstₗ)))
   vecₜ rewrite +-comm (tySize (x fstₗ)) (maxTySizeOver (enum u) x - tySize (x fstₗ))
             | a-b+b≡a (maxTySizeOver (enum u) x) (tySize (x fstₗ)) (maxTySizeLem u fstₗ x) = snd


enumSigmaCond : ∀ {u} → List ⟦ u ⟧ → (x : ⟦ u ⟧ → U) → Vec Var (tySize u) → Vec Var (maxTySizeOver (enum u) x) → SI-Monad Var
tyCond : ∀ u → Vec Var (tySize u) → SI-Monad Var
enumSigmaCond [] x v₁ v₂ = trivial
enumSigmaCond {u} (elem₁ ∷ enum₁) x v₁ v₂ = do
  eqElem₁ ← varEqLit u v₁ elem₁
  tyCons ← tyCond (x elem₁) (take (tySize (x elem₁)) vecₜ)
  restZ ← allEqz (drop (tySize (x elem₁)) vecₜ)
  sat ← limp eqElem₁ tyCons
  rest ← enumSigmaCond enum₁ x v₁ v₂
  r' ← land sat rest
  land r' restZ
 where
   vecₜ : Vec Var (tySize (x elem₁) + (maxTySizeOver (enum u) x - tySize (x elem₁)))
   vecₜ rewrite +-comm (tySize (x elem₁)) (maxTySizeOver (enum u) x - tySize (x elem₁))
              | a-b+b≡a (maxTySizeOver (enum u) x) (tySize (x elem₁)) (maxTySizeLem u elem₁ x) = v₂

tyCond `Zero vec = trivial
tyCond `One vec = allEqz vec
tyCond `Two vec = do
  isZero ← varEqLit `Two vec false
  isOne ← varEqLit `Two vec true
  lor isZero isOne
tyCond `Base vec = trivial
tyCond (`Vec u nzero) vec = trivial
tyCond (`Vec u (suc x)) vec with splitAt (tySize u) vec
... | fst , snd = do
  r ← tyCond u fst
  s ← tyCond (`Vec u x) snd
  land r s
tyCond (`Σ u x) vec with splitAt (tySize u) vec
... | fst , snd = do
  r ← tyCond u fst
  s ← enumSigmaCond (enum u) x fst snd
  land r s

indToIR : ∀ u → Vec Var (tySize u) → SI-Monad (Vec Var (tySize u))
indToIR `Zero vec = return []
indToIR `One vec@(v ∷ []) = do
  add (IAdd zero ((one , v) ∷ []))
  return vec
indToIR `Two vec@(v ∷ []) = do
  add (IMul one v v one v)
  return vec
indToIR `Base vec = return vec
indToIR (`Vec u nzero) vec = return vec
indToIR (`Vec u (suc x)) vec with splitAt (tySize u) vec
... | fst , snd = do
  indToIR u fst
  indToIR (`Vec u x) snd
  return vec
indToIR (`Σ u x) vec = do
  t ← tyCond (`Σ u x) vec
  isTrue t
  return vec

litToInd : ∀ u → ⟦ u ⟧ → SI-Monad (Vec Var (tySize u))
litToInd u l = do
  vec ← newVarVec (tySize u)
  r ← varEqLit u vec l
  isTrue r
  return vec


assertVarEqVar : ∀ n → Vec Var n → Vec Var n → SI-Monad ⊤
assertVarEqVar .0 [] [] = return tt
assertVarEqVar .(suc _) (x ∷ v₁) (x₁ ∷ v₂) = do
  add (IAdd zero ((one , x) ∷ (- one , x₁) ∷ []))
  assertVarEqVar _ v₁ v₂

sourceToIntermediate : ∀ u → Source u → SI-Monad (Vec Var (tySize u))
sourceToIntermediate u (Ind refl x) = indToIR u x
sourceToIntermediate u (Lit x) = litToInd u x
sourceToIntermediate `Base (Add source source₁) = do
  r₁ ← sourceToIntermediate `Base source
  r₂ ← sourceToIntermediate `Base source₁
  v ← new
  add (IAdd zero ((one , head r₁) ∷ (one , head r₂) ∷ (- one , v) ∷ []))
  return (v ∷ [])

module Comp where
  open import Language.Source.Utils f finite using (S-Monad)

  compAssert : List (∃ (λ u → Source u × Source u)) → SI-Monad ⊤
  compAssert [] = return tt
  compAssert ((u' , s₁ , s₂) ∷ l) = do
    r₁ ← sourceToIntermediate u' s₁
    r₂ ← sourceToIntermediate u' s₂
    assertVarEqVar _ r₁ r₂
    compAssert l


  compileSource : ∀ u → (S-Monad (Source u)) → Var × Builder × (Vec Var (tySize u) × List ℕ)
  compileSource u source = 
    let v , (asserts , input) , output = source 1
    in  (do
      compAssert (asserts [])
      r ← sourceToIntermediate _ output
      return (r , input [])) v


open Comp public

open import Agda.Builtin.Nat renaming (zero to nzero) hiding (_+_; _*_)

open import Data.Bool
open import Data.Field
open import Data.Finite
open import Data.List hiding (splitAt; head; take; drop; intercalate; concat)

import Data.Map
module M = Data.Map
open import Data.MaybeC
open import Data.Nat hiding (_⊔_) renaming (zero to nzero; _≟_ to _≟ℕ_; _+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Mod renaming (mod to modℕ)
open import Data.Nat.Show 
open import Data.Product hiding (map)

import Data.Sets
module S = Data.Sets

open import Data.String renaming (_++_ to _S++_) hiding (show; fromList)
open import Data.String.Intercalate
open import Data.Sum hiding (map)
open import Data.Unit


open import Language.Common

open import Level renaming (zero to lzero; suc to lsuc)

open import Math.Arithmoi

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import TypeClass.Ord

module Compile.Solve (f : Set) (field' : Field f) (finite : Finite f) (showf : f → String) (fToℕ  : f → ℕ) (ℕtoF : ℕ → f) where

open Field field'

open import Language.Intermediate f
open import Language.Intermediate.Show f showf
open import Language.Source f finite showf
open import Language.TySize f finite
open import Language.Universe f


numUnknownsList : M.Map Var ℕ → S.Sets Var → List Var → ℕ → ℕ
numUnknownsList map set [] n = n
numUnknownsList map set (x ∷ l) n with S.member natOrd x set
numUnknownsList map set (x ∷ l) n | false with M.lookup natOrd x map
numUnknownsList map set (x ∷ l) n | false | nothing = numUnknownsList map (S.insert natOrd x set) l (suc n)
numUnknownsList map set (x ∷ l) n | false | just x₁ = numUnknownsList map set l n
numUnknownsList map set (x ∷ l) n | true = numUnknownsList map set l n

numUnknownsAux : M.Map Var ℕ → S.Sets Var → Intermediate → ℕ
numUnknownsAux m vars (IAdd x x₁) = numUnknownsList m vars (map proj₂ x₁) 0
numUnknownsAux m vars (IMul a b c d e) = numUnknownsList m vars (b ∷ c ∷ e ∷ []) 0
numUnknownsAux m vars (Hint x) = 0
numUnknownsAux m vars (Log x) = 0

numUnknowns : M.Map Var ℕ → Intermediate → ℕ
numUnknowns map ir = numUnknownsAux map S.empty ir

Error = String


Coeff = ℕ
open Field field' renaming (zero to zerof; one to onef; _+_ to _+f_; -_ to -f_; _*_ to _*f_; 1/_ to 1f/_)

evalLinCombKnown : M.Map Var ℕ → List (f × Var) → f
evalLinCombKnown map [] = zerof
evalLinCombKnown map ((coeff , v) ∷ l) with M.lookup natOrd v map
evalLinCombKnown map ((coeff , v) ∷ l) | nothing = zero -- shouldn't happen
evalLinCombKnown map ((coeff , v) ∷ l) | just x = (coeff *f (ℕtoF x)) +f evalLinCombKnown map l

evalVarsKnown : M.Map Var ℕ → List Var → f
evalVarsKnown map [] = onef
evalVarsKnown map (x ∷ l) with M.lookup natOrd x map
evalVarsKnown map (x ∷ l) | nothing = zerof -- shouldn't happen
evalVarsKnown map (x ∷ l) | just x₁ = (ℕtoF x₁) * evalVarsKnown map l

solveNoUnknown : M.Map Var ℕ → Intermediate → Bool
solveNoUnknown map (IAdd x x₁) with fToℕ ((evalLinCombKnown map x₁) +f x) ≟ℕ 0
solveNoUnknown map (IAdd x x₁) | yes p = true
solveNoUnknown map (IAdd x x₁) | no ¬p = false
solveNoUnknown map (IMul a b c d e) with fToℕ (a * evalVarsKnown map (b ∷ c ∷ [])) ≟ℕ fToℕ (d * evalVarsKnown map (e ∷ []))
solveNoUnknown map (IMul a b c d e) | yes p = true
solveNoUnknown map (IMul a b c d e) | no ¬p = false
solveNoUnknown map (Hint x) = true
solveNoUnknown map (Log x) = true


-- outputs the constants and the coefficients of the variables
collectCoeff : M.Map Var ℕ → List (f × Var) → ℕ → ℕ × M.Map Var Coeff
collectCoeff m [] const = const , M.empty
collectCoeff m ((coeff , v) ∷ l) const with collectCoeff m l const
... | const' , coeffMap with M.lookup natOrd v m -- is the value of v known?
collectCoeff m ((coeff , v) ∷ l) const | const' , coeffMap | nothing with M.lookup natOrd v coeffMap
collectCoeff m ((coeff , v) ∷ l) const | const' , coeffMap | nothing | nothing = const' , M.insert natOrd v (fToℕ coeff) coeffMap
collectCoeff m ((coeff , v) ∷ l) const | const' , coeffMap | nothing | just x = const' , M.insert natOrd v (fToℕ (coeff +f ℕtoF x)) coeffMap
collectCoeff m ((coeff , v) ∷ l) const | const' , coeffMap | just x = fToℕ ((ℕtoF x *f coeff) +f ℕtoF const') , coeffMap



directSolveAux : M.Map Var ℕ → List Intermediate → (Error × M.Map Var ℕ) ⊎ (M.Map Var ℕ)
directSolveAux map [] = inj₂ map
directSolveAux map (IAdd x x₁ ∷ irs) with collectCoeff map x₁ (fToℕ x)
directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap with M.size coeffMap
directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize with mSize ≟ℕ 0
directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | yes p with const ≟ℕ 0
directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | yes p | yes p₁ = directSolveAux map irs
directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | yes p | no ¬p = inj₁ (("Unsatisfiable constraint: " S++ showIntermediate (IAdd x x₁)) , map)
directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | no ¬p with mSize ≟ℕ 1
directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | no ¬p | yes p with M.toList coeffMap
directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | no ¬p | yes p | [] = inj₁ ("Internal error: the impossible happened @ SourceIntermediate.agda:directSolveAux" , map)
directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | no ¬p | yes p | (v , coeff) ∷ t = directSolveAux (M.insert natOrd v (fToℕ ((-f (ℕtoF const)) *f (1f/ (ℕtoF coeff)))) map) irs
directSolveAux map (IAdd x x₁ ∷ irs) | const , coeffMap | mSize | no ¬p | no ¬p₁ = inj₁ (("Cannot solve constraint " S++ showIntermediate (IAdd x x₁) S++ " without hint") , map)
directSolveAux map (IMul a b c d e ∷ irs) with numUnknowns map (IMul a b c d e)
directSolveAux map (IMul a b c d e ∷ irs) | unknowns with unknowns ≟ℕ 0
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | yes p with solveNoUnknown map (IMul a b c d e)
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | yes p | false = inj₁ (("Unsatisfiable constraint " S++ showIntermediate (IMul a b c d e)) , map)
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | yes p | true = directSolveAux map irs
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p with unknowns ≟ℕ 1
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p with M.lookup natOrd b map
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing with M.lookup natOrd c map
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | nothing = inj₁ (("Cannot solve constraint " S++ showIntermediate (IMul a b c d e)) , map)
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x with M.lookup natOrd e map
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | nothing with fToℕ (a *f (ℕtoF x)) ≟ℕ fToℕ d
   -- a * ⟦ b ⟧ * ⟦ c ⟧ = a * ⟦ b ⟧ * x = (a * x) * ⟦ b ⟧ = d * ⟦ e ⟧, and
   -- since b & e are unknowns, b = e
   -- and if a * x = d, it's a tautology
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | nothing | yes p₁ = directSolveAux map irs
   -- if a * x /= d, then ⟦ b ⟧ = ⟦ e ⟧ = 0
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | nothing | no ¬p₁ = directSolveAux (M.insert natOrd b 0 map) irs
   -- solve b
   -- a * ⟦ b ⟧ * ⟦ c ⟧ = d * ⟦ e ⟧
   -- => a * ⟦ b ⟧ * x = d * x₁
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | just x₁ with (fToℕ (a *f ℕtoF x)) ≟ℕ 0
 -- check whether or not d * x₁ ≡ 0 holds
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | just x₁ | yes p₁ with fToℕ (d *f (ℕtoF x₁)) ≟ℕ 0
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | just x₁ | yes p₁ | yes p₂ = directSolveAux map irs
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | just x₁ | yes p₁ | no ¬p₁ = inj₁ (("Unsatisfiable constraint " S++ showIntermediate (IMul a b c d e)) , map)
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | nothing | just x | just x₁ | no ¬p₁ = directSolveAux (M.insert natOrd b (fToℕ ((d *f (ℕtoF x₁)) *f (1f/ (a *f (ℕtoF x))))) map) irs
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x with M.lookup natOrd c map
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing with M.lookup natOrd e map
   -- a * ⟦ b ⟧ * ⟦ c ⟧ = d * ⟦ e ⟧
   -- a * x * ⟦ c ⟧ = d * ⟦ e ⟧
   -- similar to a case above
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | nothing with fToℕ (a *f (ℕtoF x)) ≟ℕ fToℕ d
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | nothing | yes p₁ = directSolveAux map irs
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | nothing | no ¬p₁ = directSolveAux (M.insert natOrd c 0 map) irs
   -- a * x * ⟦ c ⟧ = d * x₁
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | just x₁ with (fToℕ (a *f ℕtoF x)) ≟ℕ 0
 -- check whether or not d * x₁ ≡ 0 holds
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | just x₁ | yes p₁ with fToℕ (d *f (ℕtoF x₁)) ≟ℕ 0
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | just x₁ | yes p₁ | yes p₂ = directSolveAux map irs
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | just x₁ | yes p₁ | no ¬p₁ = inj₁ (("Unsatisfiable constraint " S++ showIntermediate (IMul a b c d e)) , map)
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | nothing | just x₁ | no ¬p₁ = directSolveAux (M.insert natOrd c (fToℕ ((d *f (ℕtoF x₁)) *f (1f/ (a *f (ℕtoF x))))) map) irs
   -- e must not be known, because there is exactly one unknown
   -- a * x * x₁ = d * ⟦ e ⟧
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | just x₁ with fToℕ d ≟ℕ 0
-- check whether or not a * x * x₁ ≡ 0 holds
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | just x₁ | yes p₁ with fToℕ ((a *f (ℕtoF x)) *f (ℕtoF x₁)) ≟ℕ 0
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | just x₁ | yes p₁ | yes p₂ = directSolveAux map irs
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | just x₁ | yes p₁ | no ¬p₁ = inj₁ (("Unsatisfiable constraint " S++ showIntermediate (IMul a b c d e)) , map)
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | yes p | just x | just x₁ | no ¬p₁ = directSolveAux (M.insert natOrd e (fToℕ (((a *f (ℕtoF x)) *f (ℕtoF x₁)) *f (1f/ d))) map) irs
directSolveAux map (IMul a b c d e ∷ irs) | unknowns | no ¬p | no ¬p₁ = inj₁ (("Cannot solve constraint " S++ showIntermediate (IMul a b c d e)) , map)
directSolveAux map (Hint x ∷ irs) = directSolveAux (x map) irs
directSolveAux map (Log x ∷ irs) = directSolveAux map irs

private
  showMap : M.Map Var ℕ → String
  showMap m = intercalate ", " (map (λ x → "(" S++ show (proj₁ x) S++ ", " S++ show (proj₂ x) S++ ")") (M.toList m))
directSolve : List (Var × ℕ) → List Intermediate → Error ⊎ (M.Map Var ℕ)
directSolve l ir with directSolveAux (M.insert natOrd 0 1 (M.fromList natOrd l)) ir
directSolve l ir | inj₁ (error , map) = inj₁ (error S++ "\n" S++ showMap map)
directSolve l ir | inj₂ y = inj₂ y


showSolve : Error ⊎ (M.Map Var ℕ) → List String
showSolve (inj₁ x) = ("Error: " S++ x) ∷ []
showSolve (inj₂ y) = map (λ x → show (proj₁ x) S++ " " S++ show (proj₂ x) S++ "\n") (M.toList y)

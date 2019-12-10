open import Data.Bool
open import Data.Field
open import Data.Finite
open import Data.Nat
open import Data.Nat.Show
open import Data.String hiding (show)
open import Data.Product
open import Data.Vec hiding (_++_)

open import Relation.Binary.PropositionalEquality
module Language.Source (f : Set) (finite : Finite f) (showf : f → String) where

open import Language.TySize f finite
open import Language.Universe f


data Source : U → Set where
  Ind : ∀ {u} {m} → m ≡ tySize u → Vec ℕ m → Source u
  Lit : ∀ {u} → ⟦ u ⟧ → Source u
  Add Mul : Source `Base → Source `Base → Source `Base

showVec : ∀ {ℓ} {n} {A : Set ℓ} → (A → String) → Vec A n → String
showVec f [] = "[]"
showVec f (x ∷ v) = f x ++ " ∷ " ++ showVec f v

showSource : ∀ {u} → Source u → String
showSource (Ind x x₁) = "Ind (" ++ showVec show x₁ ++ ")"
showSource {`One} (Lit x) = "Lit `One tt"
showSource {`Two} (Lit false) = "Lit `Two false"
showSource {`Two} (Lit true) = "Lit `Two true"
showSource {`Base} (Lit x) = "Lit `Base " ++ showf x
showSource {`Vec u zero} (Lit x) = "[]"
showSource {`Vec u (suc x₁)} (Lit (x ∷ x₂)) = "VecLit (" ++ showSource (Lit x) ++ " ∷ " ++ showSource (Lit x₂) ++ ")"
showSource {`Σ u x₁} (Lit (fst , snd)) = "SigmaLit (" ++ showSource (Lit fst) ++ " , " ++ showSource (Lit snd) ++ ")"
showSource {`Π u x₁} (Lit f) = "PiLit ([redacted])"
showSource (Add s s₁) = "((" ++ showSource s ++ ") + (" ++ showSource s₁ ++ "))"
showSource (Mul s s₁) = "((" ++ showSource s ++ ") * (" ++ showSource s₁ ++ "))"

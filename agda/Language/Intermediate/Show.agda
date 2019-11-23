open import Data.List hiding (_++_)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product
open import Data.String

open import Function

open import Language.Common

module Language.Intermediate.Show (f : Set) (showf : f → String) where

open import Language.Intermediate f



showIntermediate : Intermediate → String
showIntermediate (IAdd x x₁) = "IAdd " ++ showf x ++ " " ++ aux x₁
  where
    aux : List (f × Var) → String
    aux [] = "[]"
    aux ((f , n) ∷ l) = "(" ++ showf f ++ ", " ++ showℕ n ++ ")" ++ " ∷ " ++ aux l
    
showIntermediate (IMul a b c d e) = "IMul " ++ showf a ++ " " ++ showℕ b ++ " " ++ showℕ c ++ " " ++ showf d ++ " " ++ showℕ e
showIntermediate (Log x) = "Log " ++ x

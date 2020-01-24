open import Data.List hiding (_++_)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product
open import Data.String

open import Function

open import Language.Common

module Language.R1CS.Show (f : Set) (showf : f → String) where

open import Language.R1CS f



showR1CS : R1CS → String
showR1CS (IAdd x x₁) = "IAdd " ++ showf x ++ " " ++ aux x₁
  where
    aux : List (f × Var) → String
    aux [] = "[]"
    aux ((f , n) ∷ l) = "(" ++ showf f ++ ", " ++ showℕ n ++ ")" ++ " ∷ " ++ aux l
    
showR1CS (IMul a b c d e) = "IMul " ++ showf a ++ " " ++ showℕ b ++ " " ++ showℕ c ++ " " ++ showf d ++ " " ++ showℕ e
showR1CS (Hint x) = "Hint [redacted]"
showR1CS (Log x) = "Log " ++ x


serializeR1CS : R1CS → String
serializeR1CS (IAdd x x₁) = "IAdd " ++ showf x ++ " " ++ aux x₁
  where
    aux : List (f × Var) → String
    aux [] = ""
    aux ((f , n) ∷ l) = showf f ++ " " ++ showℕ n ++ " " ++ aux l
serializeR1CS (IMul a b c d e) = "IMul " ++ showf a ++ " " ++ showℕ b ++ " " ++ showℕ c ++ " " ++ showf d ++ " " ++ showℕ e
serializeR1CS (Hint x) = "Hint [redacted]"
serializeR1CS (Log x) = "Log " ++ x

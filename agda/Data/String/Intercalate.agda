module Data.String.Intercalate where

open import Data.List hiding (intercalate; _++_)
open import Data.String

intercalate : String → List String -> String
intercalate s [] = ""
intercalate s (x ∷ []) = x
intercalate s (x ∷ x₁ ∷ l) = x ++ s ++ intercalate s (x₁ ∷ l)

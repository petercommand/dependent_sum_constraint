module Magma.Poly where

open import Data.Nat using (ℕ; suc)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.String

data MagmaPoly : Set where
  lit : ℕ → MagmaPoly
  var : ℕ → MagmaPoly
  _+_ _-_ _*_ : MagmaPoly → MagmaPoly → MagmaPoly
  
magmaPolyToString : MagmaPoly → String
magmaPolyToString (lit x) = showℕ x
magmaPolyToString (var x) = "R." ++ showℕ (suc x)
magmaPolyToString (mp + mp₁) = "(" ++ magmaPolyToString mp ++ " + " ++ magmaPolyToString mp₁ ++ ")"
magmaPolyToString (mp - mp₁) =  "(" ++ magmaPolyToString mp ++ " - " ++ magmaPolyToString mp₁ ++ ")"
magmaPolyToString (mp * mp₁) =  "(" ++ magmaPolyToString mp ++ " * " ++ magmaPolyToString mp₁ ++ ")"

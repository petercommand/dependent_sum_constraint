module Z3.Cmd where

open import Data.Nat hiding (_+_; _*_)
open import Data.String

Z3Var = String



data Z3Expr : Set where
  _+_ _*_ _mod_ Gt Ge Le Lt : Z3Expr → Z3Expr → Z3Expr
  not : Z3Expr → Z3Expr
  eq : Z3Expr → Z3Expr → Z3Expr
  lit : String → Z3Expr

infixl 10 _+_
infixl 10 _*_


data Z3Type : Set where
  Int : Z3Type

data Z3Cmd : Set where
  DeclConst : Z3Var → Z3Type → Z3Cmd
  Assert : Z3Expr → Z3Cmd
  CheckSat : Z3Cmd
  GetModel : Z3Cmd

showZ3Type : Z3Type → String
showZ3Type Int = "Int"


showZ3Expr : Z3Expr → String
showZ3Expr (expr + expr₁) = "(+ " ++ showZ3Expr expr ++ " " ++ showZ3Expr expr₁ ++ ")"
showZ3Expr (expr * expr₁) = "(* " ++ showZ3Expr expr ++ " " ++ showZ3Expr expr₁ ++ ")"
showZ3Expr (expr mod expr₁) = "(mod " ++ showZ3Expr expr ++ " " ++ showZ3Expr expr₁ ++ ")"
showZ3Expr (Gt expr expr₁) = "(> " ++ showZ3Expr expr ++ " " ++ showZ3Expr expr₁ ++ ")"
showZ3Expr (Ge expr expr₁) = "(>= " ++ showZ3Expr expr ++ " " ++ showZ3Expr expr₁ ++ ")"
showZ3Expr (Lt expr expr₁) = "(< " ++ showZ3Expr expr ++ " " ++ showZ3Expr expr₁ ++ ")"
showZ3Expr (Le expr expr₁) = "(<= " ++ showZ3Expr expr ++ " " ++ showZ3Expr expr₁ ++ ")"
showZ3Expr (not expr) = "(not " ++ showZ3Expr expr ++ ")"
showZ3Expr (eq expr expr₁) = "(= " ++ showZ3Expr expr ++ " " ++ showZ3Expr expr₁ ++ ")"
showZ3Expr (lit x) = x

showZ3 : Z3Cmd → String
showZ3 (DeclConst x x₁) = "(declare-const " ++ x ++ " " ++ showZ3Type x₁ ++ ")"
showZ3 (Assert x) = "(assert " ++ showZ3Expr x ++ ")"
showZ3 CheckSat = "(check-sat)"
showZ3 GetModel = "(get-model)"

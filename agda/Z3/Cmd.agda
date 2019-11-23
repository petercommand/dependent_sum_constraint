module Z3.Cmd where

open import Data.Nat hiding (_+_; _*_)
open import Data.String

Z3Var = String



data Z3Expr : Set where
  _+_ _*_ _mod_ : Z3Expr → Z3Expr → Z3Expr
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
  CheckSet : Z3Cmd
  GetModel : Z3Cmd



module Z3.Cmd where

open import Data.Binary

open import Data.Nat hiding (_+_; _*_)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.String

Z3Var = String



data Z3Expr : Set where
  _+_ _*_ _mod_ Gt Ge Le Lt : Z3Expr → Z3Expr → Z3Expr
  not : Z3Expr → Z3Expr
  eq : Z3Expr → Z3Expr → Z3Expr
  lit : ℕ → Z3Expr
  var : String → Z3Expr

infixl 10 _+_
infixl 10 _*_

{-
data Z3Type : Set where
  Int : Z3Type
-}
data Z3Cmd : Set where
  DeclConst : Z3Var → Z3Cmd
  Assert : Z3Expr → Z3Cmd
  CheckSat : Z3Cmd
  GetModel : Z3Cmd
{-
showZ3Type : Z3Type → String
showZ3Type Int = "Int"
-}

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
showZ3Expr (lit x) = showℕ x
showZ3Expr (var x) = x

showBitZ3Expr : Z3Expr → String
showBitZ3Expr (expr + expr₁) = "(bvadd " ++ showBitZ3Expr expr ++ " " ++ showBitZ3Expr expr₁ ++ ")"
showBitZ3Expr (expr * expr₁) = "(bvmul " ++ showBitZ3Expr expr ++ " " ++ showBitZ3Expr expr₁ ++ ")"
showBitZ3Expr (expr mod expr₁) = "(bvurem " ++ showBitZ3Expr expr ++ " " ++ showBitZ3Expr expr₁ ++ ")"
showBitZ3Expr (Gt expr expr₁) = "(bvugt " ++ showBitZ3Expr expr ++ " " ++ showBitZ3Expr expr₁ ++ ")"
showBitZ3Expr (Ge expr expr₁) = "(bvuge " ++ showBitZ3Expr expr ++ " " ++ showBitZ3Expr expr₁ ++ ")"
showBitZ3Expr (Lt expr expr₁) = "(bvult " ++ showBitZ3Expr expr ++ " " ++ showBitZ3Expr expr₁ ++ ")"
showBitZ3Expr (Le expr expr₁) = "(bvule " ++ showBitZ3Expr expr ++ " " ++ showBitZ3Expr expr₁ ++ ")"
showBitZ3Expr (not expr) = "(bvnot " ++ showBitZ3Expr expr ++ ")"
showBitZ3Expr (eq expr expr₁) = "(= " ++ showBitZ3Expr expr ++ " " ++ showBitZ3Expr expr₁ ++ ")"
showBitZ3Expr (lit x) = "(_ bv" ++ showℕ x ++ " 509)"
showBitZ3Expr (var x) = x


showZ3 : Z3Cmd → String
showZ3 (DeclConst x) = "(declare-const " ++ x ++ " " ++ "Int" ++ ")"
showZ3 (Assert x) = "(assert " ++ showZ3Expr x ++ ")"
showZ3 CheckSat = "(check-sat)"
showZ3 GetModel = "(get-model)"


showBitZ3 : Z3Cmd → String
showBitZ3 (DeclConst x) = "(declare-const " ++ x ++ " " ++ "(_ BitVec 509)" ++ ")"
showBitZ3 (Assert x) = "(assert " ++ showBitZ3Expr x ++ ")"
showBitZ3 CheckSat = "(check-sat)"
showBitZ3 GetModel = "(get-model)"

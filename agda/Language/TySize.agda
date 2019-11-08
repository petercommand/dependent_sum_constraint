open import Data.Bool
open import Data.Finite
open import Data.List
open import Data.Nat
open import Data.Nat.Max
open import Data.Product
open import Data.Unit
open import Data.Vec hiding ([_]; _>>=_)


module Language.TySize (f : Set) (finite : Finite f) where

import Language.Universe



open Language.Universe f

module Enum where
  open import Data.List.Monad
  enum : (u : U) → List ⟦ u ⟧
  enum `Zero = []
  enum `One = [ tt ]
  enum `Two = false ∷ true ∷ []
  enum `Base = Finite.elems finite
  enum (`Vec u zero) = [ [] ]
  enum (`Vec u (suc x)) = do
    r ← enum u
    rs ← enum (`Vec u x)
    return (r ∷ rs)
  enum (`Σ u x) = do
    r ← enum u
    rs ← enum (x r)
    return (r , rs)

open Enum public

maxTySizeOver : ∀ {u} → List ⟦ u ⟧ → (⟦ u ⟧ → U) → ℕ
tySize : U → ℕ


tySize `Zero = 0
tySize `One = 1
tySize `Two = 1
tySize `Base = 1
tySize (`Vec u x) = x * tySize u
tySize (`Σ u x) = tySize u + maxTySizeOver (enum u) x

maxTySizeOver [] fam = 0
maxTySizeOver (x ∷ l) fam = max (tySize (fam x)) (maxTySizeOver l fam)

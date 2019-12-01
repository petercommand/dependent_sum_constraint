module Data.Map where

open import Data.List hiding (lookup)
open import Data.MaybeC
open import Data.Nat
open import Data.Product
open import Data.String hiding (show; fromList; toList)
open import TypeClass.Ord
open import TypeClass.Show
open import Level

{-# FOREIGN GHC 

import Data.Map.Strict 
import qualified Data.Text as T
#-}

{-# FOREIGN GHC data ShowDict w = Show w => ShowDict #-}
postulate
  Map : ∀ (A B : Set) → Set
  mapShow : ∀ {A B : Set} → Show A → Show B → Show (Map A B)


{-# COMPILE GHC Map = type Map #-}
{-# COMPILE GHC mapShow = \ _ _ ShowDict ShowDict -> ShowDict #-}

postulate 
  insert : ∀ {K A : Set} → (_ : Ord K) → K → A → Map K A → Map K A
  lookup : ∀ {K A : Set} → (_ : Ord K) → K → Map K A → MaybeC A
  size : ∀ {K A : Set} → Map K A → ℕ
  empty : ∀ {K A : Set} → Map K A
  toList : ∀ {K A : Set} → Map K A → List (K × A)
{-# COMPILE GHC insert = \ _ _ OrdDict -> insert #-}
{-# COMPILE GHC lookup = \ _ _ OrdDict -> Data.Map.Strict.lookup #-}
{-# COMPILE GHC size = \ _ _ -> size #-}
{-# COMPILE GHC empty = \ _ _ -> empty #-}
{-# COMPILE GHC toList = \ _ _ -> toList #-}


fromList : ∀ {K A : Set} → Ord K → List (K × A) → Map K A
fromList ord [] = empty
fromList ord ((fst , snd) ∷ l) = insert ord fst snd (fromList ord l)

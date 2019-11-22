module Data.Map where

open import Data.MaybeC

open import Data.Nat

open import Data.String hiding (show)

open import Level

{-# FOREIGN GHC 

import Data.Map.Strict 
import qualified Data.Text as T
#-}

{-# FOREIGN GHC data OrdDict w = Ord w => OrdDict #-}
{-# FOREIGN GHC data ShowDict w = Show w => ShowDict #-}
postulate
  Map : ∀ (A B : Set) → Set
  Ord : Set → Set
  Show : Set → Set
  mapShow : ∀ {A B : Set} → Show A → Show B → Show (Map A B)
  natShow : Show ℕ
  show : ∀ {A : Set} → Show A → A → String
  natOrd : Ord ℕ
{-# COMPILE GHC Map = type Map #-}
{-# COMPILE GHC Ord = type OrdDict #-}
{-# COMPILE GHC Show = type ShowDict #-}
{-# COMPILE GHC mapShow = \ _ _ ShowDict ShowDict -> ShowDict #-}
{-# COMPILE GHC natShow = ShowDict #-}
{-# COMPILE GHC show = \ _ ShowDict -> T.pack . show #-}
{-# COMPILE GHC natOrd = OrdDict #-}
postulate 
  insert : ∀ {K A : Set} → (_ : Ord K) → K → A → Map K A → Map K A
  lookup : ∀ {K A : Set} → (_ : Ord K) → K → Map K A → MaybeC A
  empty : ∀ {K A : Set} → Map K A
{-# COMPILE GHC insert = \ _ _ OrdDict -> insert #-}
{-# COMPILE GHC lookup = \ _ _ OrdDict -> Data.Map.Strict.lookup #-}
{-# COMPILE GHC empty = \ _ _ -> empty #-}

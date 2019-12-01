module Data.Sets where


open import Data.Bool
open import TypeClass.Ord

postulate
  Sets : Set → Set

{-# FOREIGN GHC

import Data.Set

#-}

{-# COMPILE GHC Sets = type Set #-}


postulate
  empty : ∀ {A : Set} → Sets A
  insert : ∀ {A : Set} → (_ : Ord A) → A → Sets A → Sets A
  member : ∀ {A : Set} → (_ : Ord A) → A → Sets A → Bool
{-# COMPILE GHC empty = \ _ -> empty #-}
{-# COMPILE GHC insert = \ _ OrdDict -> insert #-}
{-# COMPILE GHC member = \ _ OrdDict -> member #-}

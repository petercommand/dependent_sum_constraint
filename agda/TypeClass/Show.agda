module TypeClass.Show where

open import Data.Nat
open import Data.String hiding (show)

{-# FOREIGN GHC

import qualified Data.Text as T
#-}

postulate
  Show : Set → Set
--  mapShow : ∀ {A B : Set} → Show A → Show B → Show (Map A B)
  natShow : Show ℕ
  show : ∀ {A : Set} → Show A → A → String

{-# FOREIGN GHC data ShowDict w = Show w => ShowDict #-}

{-# COMPILE GHC Show = type ShowDict #-}
{-# COMPILE GHC show = \ _ ShowDict -> T.pack . show #-}
{-# COMPILE GHC natShow = ShowDict #-}

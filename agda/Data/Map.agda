module Data.Map where

open import Data.List hiding (lookup)
open import Data.MaybeC
open import Data.Nat hiding (_⊔_)
open import Data.Product hiding (map)
open import Data.String hiding (show; fromList; toList)
open import TypeClass.Ord
open import TypeClass.Show
open import Level

{-# FOREIGN GHC 

import Data.Map.Strict 
import qualified Data.Text as T
import qualified MAlonzo.Code.TypeClass.Ord as Ord
import qualified MAlonzo.Code.TypeClass.Show as Show
#-}
postulate
  Map : ∀ (A B : Set) → Set
  mapShow : ∀ {A B : Set} → Show A → Show B → Show (Map A B)


{-# COMPILE GHC Map = type Map #-}
{-# COMPILE GHC mapShow = \ _ _ Show.ShowDict Show.ShowDict -> Show.ShowDict #-}

module Product where
  postulate
    _×C_ : ∀ {a} {b} (A : Set a) (B : Set b) → Set (a ⊔ b)
    _,C_ : ∀ {a} {b} {A : Set a} {B : Set b} → A → B → A ×C B

    fst : ∀ {a} {b} {A : Set a} {B : Set b} → A ×C B → A
    snd : ∀ {a} {b} {A : Set a} {B : Set b} → A ×C B → B
  {-# FOREIGN GHC type AgdaTuple a b = (,) #-}
  {-# COMPILE GHC _×C_ = type AgdaTuple #-}
  {-# COMPILE GHC fst = \ _ _ _ _ -> fst #-}
  {-# COMPILE GHC snd = \ _ _ _ _ -> snd #-}
postulate 
  insert : ∀ {K A : Set} → (_ : Ord K) → K → A → Map K A → Map K A
  lookup : ∀ {K A : Set} → (_ : Ord K) → K → Map K A → MaybeC A
  size : ∀ {K A : Set} → Map K A → ℕ
  empty : ∀ {K A : Set} → Map K A
  toListC : ∀ {K A : Set} → Map K A → List (K Product.×C A)
{-# COMPILE GHC insert = \ _ _ Ord.OrdDict -> insert #-}
{-# COMPILE GHC lookup = \ _ _ Ord.OrdDict -> Data.Map.Strict.lookup #-}
{-# COMPILE GHC size = \ _ _ -> toInteger . size #-}
{-# COMPILE GHC empty = \ _ _ -> empty #-}
{-# COMPILE GHC toListC = \ _ _ -> toList #-}


fromList : ∀ {K A : Set} → Ord K → List (K × A) → Map K A
fromList ord [] = empty
fromList ord ((fst , snd) ∷ l) = insert ord fst snd (fromList ord l)

open Product
toList : ∀ {K A : Set} → Map K A → List (K × A)
toList m = map (λ x → fst x , snd x) (toListC m)

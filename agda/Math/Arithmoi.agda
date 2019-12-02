module Math.Arithmoi where

open import Data.Nat hiding (_⊔_)

open import Level


module TripleProd where
  postulate
    TripProd : ∀ {a} {b} {c} (A : Set a) (B : Set b) (C : Set c) → Set (a ⊔ b ⊔ c)
    fst : ∀ {a} {b} {c} {A : Set a} {B : Set b} {C : Set c} → TripProd A B C → A
    snd : ∀ {a} {b} {c} {A : Set a} {B : Set b} {C : Set c} → TripProd A B C → B
    trd : ∀ {a} {b} {c} {A : Set a} {B : Set b} {C : Set c} → TripProd A B C → C


  {-# FOREIGN GHC type AgdaTriple a b c = (,,) #-}
  {-# COMPILE GHC TripProd = type AgdaTriple #-}
  {-# COMPILE GHC fst = \ _ _ _ _ _ _ (a , b , c) -> a #-}
  {-# COMPILE GHC snd = \ _ _ _ _ _ _ (a , b , c) -> b #-}
  {-# COMPILE GHC trd = \ _ _ _ _ _ _ (a , b , c) -> c #-}


{-# FOREIGN GHC
import Math.NumberTheory.Euclidean

getInv :: Integer -> Integer -> Integer
getInv a b = let (_ , r , _) = extendedGCD a b
             in r `Prelude.mod` b
#-}


postulate
  getInv : ℕ → ℕ → ℕ

{-# COMPILE GHC getInv = getInv #-}

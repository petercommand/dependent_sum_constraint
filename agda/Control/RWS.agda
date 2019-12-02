open import Data.Product
open import Data.Unit

open import Level

module Control.RWS {a} {b} {c} (R : Set a) (W : Set b) (S : Set c) (mempty : W) (mappend : W → W → W) where

RWSMonad : ∀ {d} → Set d → Set (a ⊔ b ⊔ c ⊔ d)
RWSMonad A = R × S → (S × W × A)

_>>=_ : ∀ {d} {e} {A : Set d} {B : Set e}
            → RWSMonad A
            → (A → RWSMonad B)
            → RWSMonad B
m >>= f = λ { (r , s) → let s' , w , a = m (r , s)
                            s'' , w' , b = f a (r , s')
                        in s'' , mappend w w' , b }

{-# INLINE _>>=_ #-}

_>>_ : ∀ {d} {e} {A : Set d} {B : Set e}
            → RWSMonad A
            → RWSMonad B
            → RWSMonad B
a >> b = a >>= λ _ → b

{-# INLINE _>>_ #-}


return : ∀ {a} {A : Set a}
            → A → RWSMonad A
return a = λ { (r , s) → s , mempty , a }

{-# INLINE return #-}


get : RWSMonad S
get = λ { (r , s) → s , mempty , s }

{-# INLINE get #-}

gets : ∀ {ℓ} {A : Set ℓ} → (S → A) → RWSMonad A
gets f = do
  r ← get
  return (f r)

{-# INLINE gets #-}


put : S → RWSMonad ⊤
put s = λ _ → s , mempty , tt

{-# INLINE put #-}

tell : W → RWSMonad ⊤
tell w = λ { (r , s) → s , w , tt }

{-# INLINE tell #-}


ask : RWSMonad R
ask = λ { (r , s) → s , mempty , r }


{-# INLINE ask #-}

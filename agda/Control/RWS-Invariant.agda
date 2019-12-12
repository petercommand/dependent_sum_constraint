{-# OPTIONS --prop #-}
open import Data.Product
open import Data.ProductPrime
open import Data.Unit

open import Level

module Control.RWS-Invariant {a} {b} {c} {d} (R : Set a) (W : Set b) (S : Set c) (P : W → Prop d)
   (mempty : W) (P-mempty : P mempty) (mappend : W → W → W) (P-mappend : ∀ {a} {b} → P a → P b → P (mappend a b)) where



RWSInvMonad : ∀ {e} → Set e → Set (a ⊔ b ⊔ c ⊔ d ⊔ e)
RWSInvMonad A = R × S → Σ′ (S × W × A) (λ prod → P (proj₁ (proj₂ prod)))

_>>=_ : ∀ {e} {f} {A : Set e} {B : Set f}
            → RWSInvMonad A
            → (A → RWSInvMonad B)
            → RWSInvMonad B
m >>= f = λ { (r , s) → let (s' , w , a) , inv = m (r , s)
                            (s'' , w' , b) , inv' = f a (r , s')
                        in (s'' , mappend w w' , b) , P-mappend inv inv' }

{-# INLINE _>>=_ #-}

_>>_ : ∀ {e} {f} {A : Set e} {B : Set f}
            → RWSInvMonad A
            → RWSInvMonad B
            → RWSInvMonad B
a >> b = a >>= λ _ → b

{-# INLINE _>>_ #-}


return : ∀ {a} {A : Set a}
            → A → RWSInvMonad A
return a = λ { (r , s) → (s , mempty , a) , P-mempty }

{-# INLINE return #-}


get : RWSInvMonad S
get = λ { (r , s) → (s , mempty , s) , P-mempty }

{-# INLINE get #-}

gets : ∀ {ℓ} {A : Set ℓ} → (S → A) → RWSInvMonad A
gets f = do
  r ← get
  return (f r)

{-# INLINE gets #-}


put : S → RWSInvMonad ⊤
put s = λ _ → (s , mempty , tt) , P-mempty

{-# INLINE put #-}

tell : (w : W) → (pw : P w) → RWSInvMonad ⊤
tell w pw = λ { (r , s) → (s , w , tt) , pw }

{-# INLINE tell #-}


ask : RWSInvMonad R
ask = λ { (r , s) → (s , mempty , r) , P-mempty }


{-# INLINE ask #-}

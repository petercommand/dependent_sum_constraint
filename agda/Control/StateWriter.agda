open import Data.Product
open import Data.Unit

open import Level

module Control.StateWriter {a} {b} (S : Set a) (W : Set b) (mempty : W) (mappend : W → W → W) where

StateWriterMonad : ∀ {c} → Set c → Set (a ⊔ b ⊔ c)
StateWriterMonad A = S → (S × W × A)

_>>=_ : ∀ {c} {d} {A : Set c} {B : Set d}
            → StateWriterMonad A
            → (A → StateWriterMonad B)
            → StateWriterMonad B
m >>= f = λ s → let s' , w , a = m s
                    s'' , w' , b = f a s'
                in s'' , mappend w w' , b

_>>_ : ∀ {c} {d} {A : Set c} {B : Set d}
            → StateWriterMonad A
            → StateWriterMonad B
            → StateWriterMonad B
a >> b = a >>= λ _ → b

return : ∀ {a} {A : Set a}
            → A → StateWriterMonad A
return a = λ s → s , mempty , a

get : StateWriterMonad S
get = λ s → s , mempty , s

put : S → StateWriterMonad ⊤
put s = λ _ → s , mempty , tt

tell : W → StateWriterMonad ⊤
tell w = λ s → s , w , tt


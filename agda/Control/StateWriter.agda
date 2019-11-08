open import Data.Product
open import Data.Unit

open import Level

module Control.StateWriter {a} {b} (S : Set a) (W : Set b) (mempty : W) (mappend : W → W → W) where

StateWriterMonad : ∀ {a} {b} {c} → Set a → Set b → Set c → Set (a ⊔ b ⊔ c)
StateWriterMonad s w a = s → (s × w × a)

_>>=_ : ∀ {c} {d} {A : Set c} {B : Set d}
            → StateWriterMonad S W A
            → (A → StateWriterMonad S W B)
            → StateWriterMonad S W B
m >>= f = λ s → let s' , w , a = m s
                    s'' , w' , b = f a s'
                in s'' , mappend w w' , b

_>>_ : ∀ {c} {d} {A : Set c} {B : Set d}
            → StateWriterMonad S W A
            → StateWriterMonad S W B
            → StateWriterMonad S W B
a >> b = a >>= λ _ → b

return : ∀ {a} {A : Set a}
            → A → StateWriterMonad S W A
return a = λ s → s , mempty , a

get : StateWriterMonad S W S
get = λ s → s , mempty , s

put : S → StateWriterMonad S W ⊤
put s = λ _ → s , mempty , tt

tell : W → StateWriterMonad S W ⊤
tell w = λ s → s , w , tt


module Control.State where

open import Data.Product
open import Data.Unit

State : Set → Set → Set
State s a = s → s × a

_>>=_ : ∀ {s} {a} {b} → State s a → (a → State s b) → State s b
m >>= f = λ s → let s' , a = m s
                in f a s'

return : ∀ {s} {a} → a → State s a
return a = λ s → s , a

get : ∀ {s} → State s s
get s = s , s

gets : ∀ {s} {a} → (s → a) → State s a
gets f = do
  s ← get
  return (f s)

put : ∀ {s} → s → State s ⊤
put s = λ s' → s , tt

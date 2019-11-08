module Data.List.Monad where

open import Data.List

return : ∀ {a} {A : Set a} → A → List A
return a = [ a ]

_>>=_ : ∀ {a} {b} {A : Set a} {B : Set b} → List A → (A → List B) → List B
[] >>= f = []
(x ∷ ma) >>= f = f x ++ (ma >>= f)

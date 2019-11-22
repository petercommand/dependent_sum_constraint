module Test.MapTest where



open import Data.Map
open import Data.MaybeC
open import Data.Nat

open import IO


main' : IO _
main' with lookup natOrd 1 (insert natOrd 1 0 (insert natOrd 1 0 empty))
main' | just x = putStrLn (show natShow x)
main' | nothing = putStrLn "Nothing"


-- putStrLn (show natShow (lookup natOrd 1 (insert natOrd 1 0 empty)))


main = run main'

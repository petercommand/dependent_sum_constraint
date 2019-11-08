module Data.Field where


record Field (f : Set) : Set where
  field
    _+_ _*_ : f → f → f
    zero : f
    one : f

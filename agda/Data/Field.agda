module Data.Field where


record Field {a} (f : Set a) : Set a where
  field
    _+_ _*_ : f → f → f
    zero : f
    one : f

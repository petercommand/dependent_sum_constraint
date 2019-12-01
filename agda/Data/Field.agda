module Data.Field where


record Field {a} (f : Set a) : Set a where
  field
    _+_ _*_ : f → f → f
    -_ : f → f
    1/_ : f → f
    zero : f
    one : f

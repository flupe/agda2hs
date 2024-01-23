module Issue264 {@0 name  : Set} where

postulate 
  Term : Set → Set

reduce : Term name → Term name
reduce = go
  where postulate
    go : Term name → Term name

{-# COMPILE AGDA2HS reduce #-}

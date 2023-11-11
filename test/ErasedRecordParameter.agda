module ErasedRecordParameter where

record Ok (@0 a : Set) (b : Set) : Set where
  constructor Thing
  field
    @0 unStuff : a
    unThing : b
    
open Ok public
{-# COMPILE AGDA2HS Ok #-}

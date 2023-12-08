module Erase where

open import Haskell.Prelude
open import Haskell.Extra.Erase

Scope : @0 Set → Set
Scope name = List (Erase name)
{-# COMPILE AGDA2HS Scope #-}

singleton : {@0 name : Set} → @0 name → Scope name
singleton x = Erased x ∷ []
{-# COMPILE AGDA2HS singleton #-}

rcong : {@0 x : a} → (f : a → b) → Rezz a x → Rezz b (f x)
rcong = rezzCong
{-# COMPILE AGDA2HS rcong #-}

rcong' : {@0 x : a} → Rezz a x → (f : a → b) → Rezz b (f x)
rcong' x f = rezzCong f x
{-# COMPILE AGDA2HS rcong' #-}

rcong2 : {@0 x : a} {@0 y : b} → (f : a → b → c) → Rezz a x → Rezz b y → Rezz c (f x y)
rcong2 = rezzCong2
{-# COMPILE AGDA2HS rcong2 #-}

rHead : {@0 x : a} {@0 xs : List a} → Rezz (List a) (x ∷ xs) → Rezz a x
rHead = rezzHead
{-# COMPILE AGDA2HS rHead #-}

rTail : {@0 x : a} {@0 xs : List a} → Rezz (List a) (x ∷ xs)  → Rezz (List a) xs
rTail = rezzTail
{-# COMPILE AGDA2HS rTail #-}

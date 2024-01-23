{-# LANGUAGE ScopedTypeVariables #-}
module ModuleParameters where

data Scope p = Empty
             | Bind p (Scope p)

unbind :: Integer -> Scope p -> Scope p
unbind x Empty = Empty
unbind x (Bind _ s) = s

thing :: forall a . a -> a
thing z = y
  where
    y :: a
    y = z

stuff :: forall p a . a -> Scope p -> a
stuff x Empty = x
stuff x (Bind _ _) = x

more :: b -> a -> Scope p -> Scope p
more _ _ Empty = Empty
more _ _ (Bind _ s) = s


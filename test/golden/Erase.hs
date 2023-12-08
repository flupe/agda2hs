module Erase where

type Scope = [()]

singleton :: Scope
singleton = [()]

rcong :: (a -> b) -> a -> b
rcong = \ f x -> f x

rcong' :: a -> (a -> b) -> b
rcong' x f = f x

rcong2 :: (a -> b -> c) -> a -> b -> c
rcong2 = \ f x y -> f x y

rHead :: [a] -> a
rHead = \ xs -> head xs

rTail :: [a] -> [a]
rTail = \ xs -> tail xs


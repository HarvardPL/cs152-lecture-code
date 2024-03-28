{-# LANGUAGE NoImplicitPrelude #-}

import System.IO (getLine, putStrLn)
import Prelude (IO, Int, Show, String, id, (+), (++))

data Bool = True | False

data Nat = Zero | Succ Nat
  deriving (Show)

data List a = Cons a (List a) | Nil
  deriving (Show)

listOfInts = Cons Zero (Cons (Succ Zero) (Cons (Succ (Succ Zero)) Nil))

data Pair a b = Pair a b

isEmpty :: List a -> Bool
isEmpty xs = case xs of
  Nil -> True
  Cons _ _ -> False

head :: List a -> a
head xs = case xs of
  Cons x xs -> x

tail :: List a -> List a
tail xs = case xs of
  Cons x xs -> xs

append :: List a -> List a -> List a
append xs ys = case xs of
  Nil -> ys
  (Cons x xs) -> Cons x (append xs ys)

class Monoid a where
  multiply :: a -> a -> a
  u :: a

instance Monoid (List a) where
  multiply = append
  u = Nil

instance Monoid String where
  multiply = (++)
  u = ""

instance Monoid Int where
  multiply = (+)
  u = 0

concat :: (Monoid m) => List m -> m
concat xs = case xs of
  Nil -> u
  Cons x xs -> multiply x (concat xs)

class Equality a where
  equal :: a -> a -> Bool

class Functor f where
  map :: (a -> b) -> f a -> f b

instance Functor List where
  map :: (a -> b) -> List a -> List b
  map f xs = case xs of
    Nil -> Nil
    (Cons x xs) -> Cons (f x) (map f xs)

data Maybe a = Just a | Nothing
  deriving (Show)

instance Functor Maybe where
  map :: (a -> b) -> Maybe a -> Maybe b
  map f xs = case xs of
    Nothing -> Nothing
    Just x -> Just (f x)

class Monad m where
  return :: a -> m a
  bind :: m a -> (a -> m b) -> m b

join :: (Monad m) => m (m a) -> m a
join xxs = bind xxs id

instance Monad List where
  return x = Cons x Nil
  bind x f = case x of
    Cons xs xss -> append (f xs) (bind xss f)
    Nil -> Nil

main :: IO ()
main = do
  x <- getLine
  putStrLn x

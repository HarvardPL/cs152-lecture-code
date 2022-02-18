{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
-- ghci -XTypeSynonymInstances -XFlexibleInstances -XScopedTypeVariables
-- :load m
-- :t mmconcat

-- mmconcat ["Hi", "there"]
-- mmconcat [3,4,5]


-- type classes

class MyMonoid g where
  mempty :: g
  mappend :: g -> g -> g



instance Num a => MyMonoid a where
  mempty = 0
  mappend x y = x + y

instance MyMonoid String where
  mempty = ""
  mappend = (++)

mmconcat :: (MyMonoid g) => [g] -> g
mmconcat [] = Main.mempty
mmconcat (x:xs) = x `Main.mappend` mmconcat xs

class MyMonad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b


instance MyMonad Maybe where
  return = Just
  (>>=) e f =
    case e of
      Nothing -> Nothing
      Just x  -> f x





















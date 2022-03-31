import Control.Monad (guard)

eg = do { x <- [1, 2, 3]; y <- [4, 5, 6]; guard (x*y <= 10); return (x+y) }

eg2 = [ x+y | x <- [1, 2, 3], y <- [4,5,6], x*y <= 10 ]

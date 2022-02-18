-- credit: https://gist.github.com/sdiehl/8d991a718f7a9c80f54b
-------------------------------------------------------------------------------
-- State Monad Implementation
-------------------------------------------------------------------------------

newtype State s a = State { runState :: s -> (a,s) }

instance Functor (State s) where
  fmap fn (State sa) = State (\s0 -> let (a, s1) = sa s0 in (fn a, s1))

instance Applicative (State s) where
  pure a = State (\s -> (a, s))
  (State sf) <*> (State sa) =
    State (\s0 -> let (fn,s1) = sf s0
                      (a, s2) = sa s1
                  in (fn a, s2))

instance Monad (State s) where
  return a = pure a

  State act >>= k = State (\s ->
    let (a, s') = act s
    in runState (k a) s')

get :: State s s
get = State $ \s -> (s, s)

put :: s -> State s ()
put s = State $ \_ -> ((), s)

modify :: (s -> s) -> State s ()
modify f = get >>= \x -> put (f x)

evalState :: State s a -> s -> a
evalState act = fst . runState act

execState :: State s a -> s -> s
execState act = snd . runState act

-------------------------------------------------------------------------------
-- Example
-------------------------------------------------------------------------------

type Stack = [Int]

empty :: Stack
empty = []

pop :: State Stack Int
pop = State $ \(x:xs) -> (x,xs)

push :: Int -> State Stack ()
push a = State $ \xs -> ((),a:xs)

tos :: State Stack Int
tos = State $ \(x:xs) -> (x,x:xs)

stackManip :: State Stack Int
stackManip = do
    push 10
    push 20
    a <- pop
    b <- pop
    push (a+b)
    tos

main :: IO ()
main = do
  let res = evalState stackManip empty
  print res

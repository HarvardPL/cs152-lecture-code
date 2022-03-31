import System.Random

up = (0, -1)
down = (0, 1)
left = (-1, 0)
right = (1, 0)

add (x1,y1) (x2,y2) = (x1+x2,y1+y2)

simulate1 pick point = do
  direction <- pick [up, down, left, right];
  return (add point direction)

simulate n pick point = if n==0 then return point else simulate1 pick point >>= simulate (n-1) pick

pickList xs = xs
egList = simulate 3 pickList (0,0)

randFrom :: [a] -> IO a
randFrom l = do
    i <- randomRIO (0, length l - 1)
    return $ l !! i
pickRand xs = randFrom xs
egRand = simulate 3 randFrom (0,0)

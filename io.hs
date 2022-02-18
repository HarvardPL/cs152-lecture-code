-- IO a: a computation that returns an a
-- approximately type IO a = World -> (a, World)
eg :: IO ()
eg = do c <- getChar
        putChar c

-- maintains equational reasoning

eg0 = let x = putStr "Hello " in putStrLn "World"

eg1 = let x = putStr "Hello " in do { x; putStrLn "World" }

eg2 = let x = putStr "Hello " in do { x; x; putStrLn "World" }

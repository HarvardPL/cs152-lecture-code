

ageDiff :: String -> String -> [(String, Integer)]-> Maybe Integer
ageDiff n1 n2 ages =
  case lookup n1 ages of
    Nothing -> Nothing
    Just a1 ->
      case lookup n2 ages of
        Nothing -> Nothing
        Just n2 -> Just (abs (a1 − a2))

























ageDiff' :: String -> String -> [(String, Integer)] -> Maybe Integer
ageDiff' n1 n2 ages =
  lookup n1 ages
  >>=
    \ a1 -> lookup n2 ages
  >>=
    \ a2 ->return (abs (a1 - a2)))






















ageDiff'' :: String -> String -> [(String, Integer)] -> Maybe Integer
ageDiff'' n1 n2 ages = do {
  a1 <- lookup n1 ages;
  a2 <- lookup n2 ages;
  return (abs (a1 − a2))
  }

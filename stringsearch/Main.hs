{-# LANGUAGE OverloadedStrings #-}

module Main where

import Grisette
import Utils.Timing

data RegEx
  = Empty
  | Epsilon
  | Atom Char
  | Star RegEx
  | Concat RegEx RegEx
  | Or RegEx RegEx
  deriving (Show)

match :: RegEx -> UnionM [UnionM Char] -> SymBool
match Empty _ = con False
match Epsilon s = s ==~ mrgReturn []
match (Atom c) s = s ==~ mrgReturn [mrgReturn c]
match x@(Star r) s = (\s1 -> foldl (||~) (s ==~ mrgReturn []) $ uncurry (match2' r x) <$> splits [1 .. length s1] s1) #~ s
match (Concat a b) s = (\s1 -> foldl1 (||~) $ uncurry (match2' a b) <$> splits [0 .. length s1] s1) #~ s
match (Or a b) s = match a s ||~ match b s

match2' :: RegEx -> RegEx -> [UnionM Char] -> [UnionM Char] -> SymBool
match2' r1 r2 s1 s2 = match r1 (mrgReturn s1) &&~ match r2 (mrgReturn s2)

splits :: [Int] -> [a] -> [([a], [a])]
splits ns x = map (`splitAt` x) ns

data StringsSpec = StringsSpec {maxLength :: Int, chars :: String}

newtype StringSearchSpace = StringSearchSpace (UnionM [UnionM Char]) deriving (Show)

instance GenSymSimple StringsSpec StringSearchSpace where
  simpleFresh (StringsSpec ml c) = StringSearchSpace <$> (go ml >>= chooseFresh)
    where
      go m
        | m <= 0 = return [[]]
        | otherwise = do
            m1 <- go (m - 1)
            case m1 of
              (m1h : m1t) -> do
                cv <- chooseFresh c
                return ((cv : m1h) : m1h : m1t)
              _ -> error "Should not happen"

stringSearch :: Int -> String -> RegEx -> IO (Maybe String)
stringSearch ml c regex = do
  let StringSearchSpace strings = genSymSimple (StringsSpec ml c) "strings"
  res <- solve (precise z3) $ match regex strings
  case res of
    Left _ -> return Nothing
    Right mo -> return $ Just $ evaluateSymToCon mo strings

increasingLengthSearch :: Int -> String -> RegEx -> IO (Maybe String)
increasingLengthSearch ml c regex = go 0
  where
    go i
      | i > ml = return Nothing
      | otherwise = do
          res <- stringSearch i c regex
          case res of
            Nothing -> go (i + 1)
            Just s -> return $ Just s

main :: IO ()
main = do
  res1 <-
    timeItAll "(a+b)*c(d+(ef)*)" $
      increasingLengthSearch
        10
        "abcdef"
        ( Concat
            ( Star
                (Or (Atom 'a') (Atom 'b'))
            )
            (Concat (Atom 'c') (Or (Atom 'd') (Star (Concat (Atom 'e') (Atom 'f')))))
        )
  print res1
  res2 <-
    timeItAll "abcdef" $
      increasingLengthSearch
        10
        "abcdef"
        ( Concat
            (Atom 'a')
            (Concat (Atom 'b') (Concat (Atom 'c') (Concat (Atom 'd') (Concat (Atom 'e') (Atom 'f')))))
        )
  print res2
  res3 <-
    timeItAll "a+b+c+d+e+f" $
      increasingLengthSearch
        10
        "abcdef"
        ( Or
            (Atom 'a')
            (Or (Atom 'b') (Or (Atom 'c') (Or (Atom 'd') (Or (Atom 'e') (Atom 'f')))))
        )
  print res3
  res4 <-
    timeItAll "a*b*c*d*e*f" $
      increasingLengthSearch
        10
        "abcdef"
        ( Concat
            (Star (Atom 'a'))
            ( Concat
                (Star (Atom 'b'))
                (Concat (Star (Atom 'c')) (Concat (Star (Atom 'd')) (Concat (Star (Atom 'e')) (Star (Atom 'f')))))
            )
        )
  print res4

{-# LANGUAGE OverloadedStrings #-}

module Main where

import Grisette
import Utils.Timing

type Queen = SymIntN 64

indexPairs :: Int -> [(Int, Int)]
indexPairs n =
  [(i, j) | i <- [0 .. n - 1], j <- [i + 1 .. n - 1]]

legal :: Int -> Queen -> SymBool
legal n qs = 1 <=~ qs &&~ qs <=~ toSym n

queenPairSafe :: Int -> [Queen] -> (Int, Int) -> SymBool
queenPairSafe _ qs (i, j) =
  let qs_i = qs !! i
      qs_j = qs !! j
   in (qs_i /=~ qs_j)
        &&~ (qs_j - qs_i /=~ toSym (j - i))
        &&~ (qs_j - qs_i /=~ toSym (i - j))

allQueensSafe :: Int -> [Queen] -> SymBool
allQueensSafe n qs =
  (n ==~ length qs)
    &&~ foldl1 (&&~) (legal n <$> qs)
    &&~ foldl1 (&&~) (queenPairSafe n qs <$> indexPairs n)

solveQueens :: Int -> IO [Int]
solveQueens n = do
  let qs = genSymSimple (SimpleListSpec n ()) "a" :: [Queen]
  res <- solve (precise z3) (allQueensSafe n qs)
  case res of
    Left _ -> error "Should not happen"
    Right mo -> return $ evaluateSymToCon mo qs

main :: IO ()
main = do
  q4 <- timeItAll "solveQueens 4" $ solveQueens 4
  print q4
  q5 <- timeItAll "solveQueens 5" $ solveQueens 5
  print q5
  q6 <- timeItAll "solveQueens 6" $ solveQueens 6
  print q6
  q7 <- timeItAll "solveQueens 7" $ solveQueens 7
  print q7
  q8 <- timeItAll "solveQueens 8" $ solveQueens 8
  print q8

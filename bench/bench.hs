module Main (main) where

import Criterion.Main

import Numeric.Peano
import Numeric.Church

toFrom :: Int -> Int
toFrom = (fromEnum :: Church -> Int) . toEnum

quotMeas :: (Int,Int) -> Int
quotMeas (x,y) = (fromEnum :: Church -> Int) (toEnum x `quot` toEnum y)

quotMeasBench xs = bench (show xs) $ nf quotMeas xs

toEnumBench :: Int -> Benchmark
toEnumBench n = bench (show n) $ nf (toEnum :: Int -> Peano) n

main :: IO ()
main =
    defaultMain
        [ bgroup "toEnum" (map toEnumBench [10000, 100000])
        , bgroup
              "quot"
              [ quotMeasBench (10, 20)
              , quotMeasBench (100, 10)
              , quotMeasBench (1000, 10)]]

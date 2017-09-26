module Main (main) where

import Criterion.Main

import Numeric.Peano

main :: IO ()
main =
    defaultMain
        [bench "enumFromThenTo" $ nf (const [10 :: Peano, 200, 1000000]) ()]

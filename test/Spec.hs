{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes   #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

import           Hedgehog
import qualified Hedgehog.Gen       as Gen
import qualified Hedgehog.Range     as Range
import           Test.DocTest

-- import           Numeric.WordOfSize
-- import           Numeric.IntOfSize
import           Numeric.Peano
import           Numeric.Church

import           Control.Monad

binaryProp
    :: forall a.
       Integral a
    => (forall t. Integral t => t -> t -> t)
    -> Integer
    -> Integer
    -> (Integer -> Integer -> Bool)
    -> Property
binaryProp op lb ub cond = property $ do
    x <- forAll (Gen.integral (Range.linear lb ub))
    y <- forAll (Gen.integral (Range.linear lb ub))
    guard (cond x y)
    let zb = op x y
    let zt = op (fromInteger @a x) (fromInteger y)
    zb === toInteger zt

prop_PeanoAdd :: Property
prop_PeanoAdd = binaryProp @Peano (+) 0 1000 (\_ _ -> True)

prop_PeanoMul :: Property
prop_PeanoMul = binaryProp @Peano (*) 0 1000 (\_ _ -> True)

prop_PeanoSub :: Property
prop_PeanoSub = withDiscards 1000 $ binaryProp @Peano (-) 0 1000 (>=)

prop_PeanoRem :: Property
prop_PeanoRem = binaryProp @Peano rem 1 1000 (\_ _ -> True)

prop_PeanoQuot :: Property
prop_PeanoQuot = binaryProp @Peano quot 1 1000 (\_ _ -> True)

prop_ChurchAdd :: Property
prop_ChurchAdd = binaryProp @Church (+) 0 1000 (\_ _ -> True)

prop_ChurchMul :: Property
prop_ChurchMul = binaryProp @Church (*) 0 1000 (\_ _ -> True)

prop_ChurchSub :: Property
prop_ChurchSub = withDiscards 1000 $ binaryProp @Church (-) 0 1000 (>=)

prop_ChurchRem :: Property
prop_ChurchRem = binaryProp @Church rem 1 1000 (\_ _ -> True)

prop_ChurchQuot :: Property
prop_ChurchQuot = binaryProp @Church quot 1 1000 (\_ _ -> True)

main :: IO Bool
main = do
    doctest ["-isrc","src/"]
    $$(checkConcurrent)

{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}

import           Hedgehog
import qualified Hedgehog.Gen       as Gen
import qualified Hedgehog.Range     as Range
import           Test.DocTest

import           Numeric.WordOfSize
import           Numeric.IntOfSize
import           Numeric.Decimal

import           Data.Word
import           Data.Int

plusSame
    :: (Integral a, Integral b)
    => (Integer -> a) -> (Integer -> b) -> Property
plusSame toBase toTest = property $ do
    x <- forAll (Gen.integral (Range.linear (-1000) 1000))
    y <- forAll (Gen.integral (Range.linear (-1000) 1000))
    let zb = toBase x + toBase y
    let zt = toTest x + toTest y
    toInteger zb === toInteger zt

prop_WordPlusSame :: Property
prop_WordPlusSame =
    plusSame
        ((fromInteger @ Word8) . abs)
        ((fromInteger @ (WordOfSize 8)) . abs)

prop_IntPlusSame :: Property
prop_IntPlusSame =
    plusSame
        (fromInteger @ Int8)
        (fromInteger @ (IntOfSize 8))

prop_sumDig :: Property
prop_sumDig = property $ do
    x <- forAll (Gen.integral (Range.linear 0 9))
    y <- forAll (Gen.integral (Range.linear 0 9))
    z <- forAll (Gen.integral (Range.linear 0 9))
    fromEnum (sumDig (toEnum x) (toEnum y) (toEnum z)) === ((x + y + z) `rem` 10)

prop_carryDig :: Property
prop_carryDig = property $ do
    x <- forAll (Gen.integral (Range.linear 0 9))
    y <- forAll (Gen.integral (Range.linear 0 9))
    z <- forAll (Gen.integral (Range.linear 0 9))
    fromEnum (carryDig (toEnum x) (toEnum y) (toEnum z)) === ((x + y + z) `quot` 10)

main :: IO Bool
main = do
    doctest ["-isrc","src/"]
    $$(checkConcurrent)

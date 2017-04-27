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
import           Numeric.Natural

import           Data.Word
import           Data.Int

plusSame
    :: (Integral a, Num b)
    => (Integer -> a) -> (Integer -> b) -> (b -> Integer) -> Property
plusSame toBase toTest back = property $ do
    x <- forAll (Gen.integral (Range.linear (-1000) 1000))
    y <- forAll (Gen.integral (Range.linear (-1000) 1000))
    let zb = toBase x + toBase y
    let zt = toTest x + toTest y
    toInteger zb === back zt

multSame
    :: (Integral a, Num b)
    => (Integer -> a) -> (Integer -> b) -> (b -> Integer) -> Property
multSame toBase toTest back = property $ do
    x <- forAll (Gen.integral (Range.linear (-1000) 1000))
    y <- forAll (Gen.integral (Range.linear (-1000) 1000))
    let zb = toBase x * toBase y
    let zt = toTest x * toTest y
    toInteger zb === back zt

prop_WordPlusSame :: Property
prop_WordPlusSame =
    plusSame
        ((fromInteger @ Word8) . abs)
        ((fromInteger @ (WordOfSize 8)) . abs)
        toInteger

prop_IntPlusSame :: Property
prop_IntPlusSame =
    plusSame
        (fromInteger @ Int8)
        (fromInteger @ (IntOfSize 8))
        toInteger

prop_DecimalPlusSame :: Property
prop_DecimalPlusSame =
    plusSame
        (fromInteger @ Natural . abs)
        (fromInteger @ Nat . abs)
        (foldr (\e a -> toInteger (fromEnum e) + 10 * a) 0 . getNat)

prop_WordMultSame :: Property
prop_WordMultSame =
    multSame
        ((fromInteger @ Word8) . abs)
        ((fromInteger @ (WordOfSize 8)) . abs)
        toInteger

prop_IntMultSame :: Property
prop_IntMultSame =
    multSame
        (fromInteger @ Int8)
        (fromInteger @ (IntOfSize 8))
        toInteger

prop_DecimalMultSame :: Property
prop_DecimalMultSame =
    multSame
        (fromInteger @ Natural . abs)
        (fromInteger @ Nat . abs)
        (foldr (\e a -> toInteger (fromEnum e) + 10 * a) 0 . getNat)
main :: IO Bool
main = do
    doctest ["-isrc","src/"]
    $$(checkConcurrent)

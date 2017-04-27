{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Numeric.WordOfSize where

import           Data.Word
import           GHC.TypeLits
import           Numeric.Natural

import           Data.Bits

import           Data.Coerce

import           Data.Function
import           Data.Proxy

import           Control.DeepSeq
import           Data.Ix

-- $setup
-- >>> :set -XDataKinds


type family BoundingWord (n :: Nat) :: * where
    BoundingWord 0  = Word8
    BoundingWord 1  = Word8
    BoundingWord 2  = Word8
    BoundingWord 3  = Word8
    BoundingWord 4  = Word8
    BoundingWord 5  = Word8
    BoundingWord 6  = Word8
    BoundingWord 7  = Word8
    BoundingWord 8  = Word8
    BoundingWord 9  = Word16
    BoundingWord 10 = Word16
    BoundingWord 11 = Word16
    BoundingWord 12 = Word16
    BoundingWord 13 = Word16
    BoundingWord 14 = Word16
    BoundingWord 15 = Word16
    BoundingWord 16 = Word16
    BoundingWord 17 = Word32
    BoundingWord 18 = Word32
    BoundingWord 19 = Word32
    BoundingWord 20 = Word32
    BoundingWord 21 = Word32
    BoundingWord 22 = Word32
    BoundingWord 23 = Word32
    BoundingWord 24 = Word32
    BoundingWord 25 = Word32
    BoundingWord 26 = Word32
    BoundingWord 27 = Word32
    BoundingWord 28 = Word32
    BoundingWord 29 = Word32
    BoundingWord 30 = Word32
    BoundingWord 31 = Word32
    BoundingWord 32 = Word32
    BoundingWord 33 = Word64
    BoundingWord 34 = Word64
    BoundingWord 35 = Word64
    BoundingWord 36 = Word64
    BoundingWord 37 = Word64
    BoundingWord 38 = Word64
    BoundingWord 39 = Word64
    BoundingWord 40 = Word64
    BoundingWord 41 = Word64
    BoundingWord 42 = Word64
    BoundingWord 43 = Word64
    BoundingWord 44 = Word64
    BoundingWord 45 = Word64
    BoundingWord 46 = Word64
    BoundingWord 47 = Word64
    BoundingWord 48 = Word64
    BoundingWord 49 = Word64
    BoundingWord 50 = Word64
    BoundingWord 51 = Word64
    BoundingWord 52 = Word64
    BoundingWord 53 = Word64
    BoundingWord 54 = Word64
    BoundingWord 55 = Word64
    BoundingWord 56 = Word64
    BoundingWord 57 = Word64
    BoundingWord 58 = Word64
    BoundingWord 59 = Word64
    BoundingWord 60 = Word64
    BoundingWord 61 = Word64
    BoundingWord 62 = Word64
    BoundingWord 63 = Word64
    BoundingWord 64 = Word64
    BoundingWord n = Natural

newtype WordOfSize (n :: Nat) = WordOfSize { getWordOfSize :: BoundingWord n }

type MaxBoundForSize n = (2 ^ n) - 1

type KnownSize n = (KnownNat (MaxBoundForSize n), Integral (BoundingWord n), Bits (BoundingWord n), KnownNat n, Show (BoundingWord n))

instance KnownSize n =>
         Bounded (WordOfSize n) where
    minBound = WordOfSize 0
    maxBound = WordOfSize (fromInteger (natVal (Proxy :: Proxy (MaxBoundForSize n))))

type CoerceBinary a b = (a -> a -> a) -> (b -> b -> b)

instance KnownSize n =>
         Bits (WordOfSize n) where
    (.&.) = (coerce :: CoerceBinary (BoundingWord n) (WordOfSize n)) (.&.)
    (.|.) = (coerce :: CoerceBinary (BoundingWord n) (WordOfSize n)) (.|.)
    xor = trunc .: (coerce :: CoerceBinary (BoundingWord n) (WordOfSize n)) xor
    complement =
        trunc . (coerce :: (BoundingWord n -> BoundingWord n) -> WordOfSize n -> WordOfSize n) complement
    shift =
        trunc .:
        (coerce :: (BoundingWord n -> Int -> BoundingWord n) -> WordOfSize n -> Int -> WordOfSize n)
            shift
    rotate =
        trunc .:
        (coerce :: (BoundingWord n -> Int -> BoundingWord n) -> WordOfSize n -> Int -> WordOfSize n)
            rotate
    bit = trunc . WordOfSize . bit
    bitSize = fromInteger . natVal
    bitSizeMaybe = Just . fromInteger . natVal
    isSigned _ = False
    testBit =
        (coerce :: (BoundingWord n -> Int -> Bool) -> WordOfSize n -> Int -> Bool)
            testBit
    popCount =
        (coerce :: (BoundingWord n -> Int) -> WordOfSize n -> Int) popCount

trunc
    :: KnownSize n
    => WordOfSize n -> WordOfSize n
trunc = (.&.) maxBound

convBinary
    :: KnownSize n
    => CoerceBinary (BoundingWord n) (WordOfSize n)
convBinary f = trunc .: coerce f

instance KnownSize n =>
         Num (WordOfSize n) where
    (+) = convBinary (+)
    {-# INLINE (+) #-}
    (*) = convBinary (*)
    {-# INLINE (*) #-}
    negate y = (maxBound `xor` y) + 1
    {-# INLINE negate #-}
    fromInteger = trunc . WordOfSize . fromInteger . abs
    abs = id
    signum (WordOfSize x) = WordOfSize (signum x)

instance KnownSize n =>
         Eq (WordOfSize n) where
    (==) = (==) `on` getWordOfSize . trunc

instance KnownSize n =>
         Show (WordOfSize n) where
    showsPrec n = showsPrec n . getWordOfSize . trunc

instance KnownSize n =>
         Ord (WordOfSize n) where
    compare = compare `on` getWordOfSize . trunc

instance KnownSize n =>
         Real (WordOfSize n) where
    toRational = toRational . getWordOfSize

instance KnownSize n =>
         Enum (WordOfSize n) where
    fromEnum = fromEnum . getWordOfSize
    toEnum = trunc . WordOfSize . toEnum
    enumFrom x = [x .. maxBound]

instance KnownSize n =>
         Integral (WordOfSize n) where
    toInteger = toInteger . getWordOfSize . trunc
    quotRem x y = (convBinary quot x y, convBinary rem x y)

(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) = (.) . (.)

instance KnownSize n =>
         FiniteBits (WordOfSize n) where
    finiteBitSize = fromInteger . natVal

-- | Generates all words of a given size
--
-- >>> allWordsOfSize :: [WordOfSize 3]
-- [0,1,2,3,4,5,6,7]
allWordsOfSize
    :: KnownSize n
    => [WordOfSize n]
allWordsOfSize = [minBound .. maxBound]

instance NFData (BoundingWord n) => NFData (WordOfSize n) where
    rnf (WordOfSize n) = rnf n

deriving instance (KnownSize n, Ix (BoundingWord n)) => Ix (WordOfSize n)

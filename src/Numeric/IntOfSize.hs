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

module Numeric.IntOfSize where

import           GHC.TypeLits

import           Data.Int

import           Control.DeepSeq
import           Data.Bits
import           Data.Coerce
import           Data.Function
import           Data.Proxy
import           Data.Ix

-- $setup
-- >>> :set -XDataKinds

type family BoundingInt (n :: Nat) :: * where
    BoundingInt 0  = Int8
    BoundingInt 1  = Int8
    BoundingInt 2  = Int8
    BoundingInt 3  = Int8
    BoundingInt 4  = Int8
    BoundingInt 5  = Int8
    BoundingInt 6  = Int8
    BoundingInt 7  = Int8
    BoundingInt 8  = Int8
    BoundingInt 9  = Int16
    BoundingInt 10 = Int16
    BoundingInt 11 = Int16
    BoundingInt 12 = Int16
    BoundingInt 13 = Int16
    BoundingInt 14 = Int16
    BoundingInt 15 = Int16
    BoundingInt 16 = Int16
    BoundingInt 17 = Int32
    BoundingInt 18 = Int32
    BoundingInt 19 = Int32
    BoundingInt 20 = Int32
    BoundingInt 21 = Int32
    BoundingInt 22 = Int32
    BoundingInt 23 = Int32
    BoundingInt 24 = Int32
    BoundingInt 25 = Int32
    BoundingInt 26 = Int32
    BoundingInt 27 = Int32
    BoundingInt 28 = Int32
    BoundingInt 29 = Int32
    BoundingInt 30 = Int32
    BoundingInt 31 = Int32
    BoundingInt 32 = Int32
    BoundingInt 33 = Int64
    BoundingInt 34 = Int64
    BoundingInt 35 = Int64
    BoundingInt 36 = Int64
    BoundingInt 37 = Int64
    BoundingInt 38 = Int64
    BoundingInt 39 = Int64
    BoundingInt 40 = Int64
    BoundingInt 41 = Int64
    BoundingInt 42 = Int64
    BoundingInt 43 = Int64
    BoundingInt 44 = Int64
    BoundingInt 45 = Int64
    BoundingInt 46 = Int64
    BoundingInt 47 = Int64
    BoundingInt 48 = Int64
    BoundingInt 49 = Int64
    BoundingInt 50 = Int64
    BoundingInt 51 = Int64
    BoundingInt 52 = Int64
    BoundingInt 53 = Int64
    BoundingInt 54 = Int64
    BoundingInt 55 = Int64
    BoundingInt 56 = Int64
    BoundingInt 57 = Int64
    BoundingInt 58 = Int64
    BoundingInt 59 = Int64
    BoundingInt 60 = Int64
    BoundingInt 61 = Int64
    BoundingInt 62 = Int64
    BoundingInt 63 = Int64
    BoundingInt 64 = Int64
    BoundingInt n = Integer

newtype IntOfSize (n :: Nat) = IntOfSize
  { getIntOfSize :: BoundingInt n }

type MaxBoundForSize n = (2 ^ (n - 1)) - 1

type KnownSize n = (KnownNat (MaxBoundForSize n), Integral (BoundingInt n), Bits (BoundingInt n), KnownNat n, Show (BoundingInt n))

instance KnownSize n =>
         Bounded (IntOfSize n) where
    minBound = IntOfSize (shift (-1) (fromInteger (natVal (Proxy :: Proxy n) - 1)))
    maxBound = IntOfSize (fromInteger (natVal (Proxy :: Proxy (MaxBoundForSize n))))

type CoerceBinary a b = (a -> a -> a) -> (b -> b -> b)

trunc
    :: KnownSize n
    => IntOfSize n -> IntOfSize n
trunc x
  | testBit' x (fromInteger (natVal x) - 1) = x .|.. minBound
  | otherwise = x .&.. maxBound
  where
    (.&..) = (coerce :: CoerceBinary (BoundingInt n) (IntOfSize n)) (.&.)
    (.|..) = (coerce :: CoerceBinary (BoundingInt n) (IntOfSize n)) (.|.)
    testBit' =
        (coerce :: (BoundingInt n -> Int -> Bool) -> IntOfSize n -> Int -> Bool)
            testBit

convBinary
    :: KnownSize n
    => CoerceBinary (BoundingInt n) (IntOfSize n)
convBinary f x y = trunc (coerce f x y)

instance KnownSize n =>
         Num (IntOfSize n) where
    (+) = convBinary (+)
    (*) = convBinary (*)
    negate y = complement' y + 1 where
      complement' =
          trunc . (coerce :: (BoundingInt n -> BoundingInt n) -> IntOfSize n -> IntOfSize n) complement
    fromInteger = trunc . IntOfSize . fromInteger
    abs = id
    signum (IntOfSize x) = IntOfSize (signum x)

instance KnownSize n =>
         Eq (IntOfSize n) where
    (==) = (==) `on` getIntOfSize . trunc

instance KnownSize n =>
         Ord (IntOfSize n) where
    compare = compare `on` getIntOfSize . trunc

instance KnownSize n =>
         Real (IntOfSize n) where
    toRational = toRational . getIntOfSize

instance KnownSize n =>
         Enum (IntOfSize n) where
    fromEnum = fromEnum . getIntOfSize
    toEnum = trunc . IntOfSize . toEnum
    enumFrom x = [x .. maxBound]

instance KnownSize n =>
         Integral (IntOfSize n) where
    toInteger = toInteger . getIntOfSize
    quotRem x y = (convBinary quot x y, convBinary rem x y)

-- | Generate all values, in a sensible order
--
-- >>> allIntsOfSize :: [IntOfSize 4]
-- [0,-1,1,-2,2,-3,3,-4,4,-5,5,-6,6,-7,7,-8]
allIntsOfSize
    :: KnownSize n
    => [IntOfSize n]
allIntsOfSize = f [0 .. maxBound ] (drop 1 [0,-1 .. minBound])
  where
    f (x:xs) ys = x : f ys xs
    f [] ys     = ys

instance KnownSize n =>
         Show (IntOfSize n) where
    showsPrec n = showsPrec n . getIntOfSize . trunc

instance NFData (BoundingInt n) => NFData (IntOfSize n) where
    rnf (IntOfSize n) = rnf n

deriving instance (KnownSize n, Ix (BoundingInt n)) => Ix (IntOfSize n)

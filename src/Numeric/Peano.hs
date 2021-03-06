{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Peano numerals. Effort is made to make them as efficient as
-- possible, and as lazy as possible, but they are many orders of
-- magnitude less efficient than machine integers. They are primarily
-- used for type-level programming, and occasionally for calculations
-- which can be short-circuited.
--
-- For instance, to check if two lists are the same length, you could
-- write:
--
-- @
-- 'length' xs == 'length' ys
-- @
--
-- But this unnecessarily traverses both lists. The more efficient
-- version, on the other hand, is less clear:
--
-- @
-- sameLength [] [] = True
-- sameLength (_:xs) (_:ys) = sameLength xs ys
-- sameLength _ _ = False
-- @
--
-- Using @'Data.List.genericLength'@, on the other hand, the laziness of
-- @'Peano'@ will indeed short-circuit:
--
-- >>> genericLength [1,2,3] == genericLength [1..]
-- False
module Numeric.Peano where

import           Data.List                   (unfoldr)

import           Control.DeepSeq             (NFData (rnf))

import           Data.Data                   (Data, Typeable)
import           GHC.Generics                (Generic)

import           Data.Promotion.Prelude
import           Data.Promotion.Prelude.Enum
import           Data.Promotion.TH
import           Data.Singletons.TH

import           Numeric.Natural

import           Data.Ix

import           Data.Function
import           Text.Read

-- $setup
-- >>> import Test.QuickCheck
-- >>> import Data.List (genericLength)
-- >>> default (Peano)
-- >>> :{
-- instance Arbitrary Peano where
--     arbitrary = fmap (fromInteger . getNonNegative) arbitrary
-- :}

-- | Peano numbers. Care is taken to make operations as lazy as
-- possible:
--
-- >>> 1 > S (S undefined)
-- False
-- >>> Z > undefined
-- False
-- >>> 3 + undefined >= 3
-- True
$(singletons [d|
  data Peano
      = Z
      | S Peano
      deriving (Eq,Generic,Data,Typeable)
  |])

toChurch :: Peano -> (a -> a) -> a -> a
toChurch p f k = go p where
  go Z     = k
  go (S n) = f (go n)
{-# INLINE toChurch #-}

-- | As lazy as possible
instance Ord Peano where
    compare Z Z         = EQ
    compare (S n) (S m) = compare n m
    compare Z (S _)     = LT
    compare (S _) Z     = GT
    Z <= _ = True
    S n <= S m = n <= m
    S _ <= Z = False
    Z > _ = False
    S n > S m = n > m
    S _ > Z = True
    (>=) = flip (<=)
    (<) = flip (>)

-- | Subtraction stops at zero.
--
-- prop> n >= m ==> m - n == Z
instance Num Peano where
    (+) n = toChurch n S
    n * m = toChurch n (m+) Z
    abs = id
    signum Z = 0
    signum _ = 1
    fromInteger n
        | n < 0 = error "cannot convert negative integers to Peano numbers"
        | otherwise = go n where
            go 0 = Z
            go m = S (go (m-1))
    S n - S m = n - m
    n - _ = n

-- | The maximum bound here is infinity.
--
-- prop> maxBound > (n :: Peano)
instance Bounded Peano where
    minBound = Z
    maxBound = fix S

$(promoteOnly [d|
  instance Ord Peano where
      compare Z Z         = EQ
      compare (S n) (S m) = compare n m
      compare Z (S _)     = LT
      compare (S _) Z     = GT
      min Z _         = Z
      min (S n) (S m) = S (min n m)
      min _ Z         = Z
      max Z m         = m
      max (S n) (S m) = S (max n m)
      max n Z         = n
      Z <= _ = True
      S n <= S m = n <= m
      S _ <= Z = False
      Z > _ = False
      S n > S m = n > m
      S _ > Z = True
      _ >= Z = True
      Z >= S _ = False
      S n >= S m = n >= m
      _ < Z = False
      S n < S m = n < m
      Z < S _ = True

  instance Num Peano where
      Z + m = m
      S n + m = S (n + m)
      Z * _ = Z
      S n * m = m + n * m
      abs = id
      signum Z = 0
      signum _ = 1
      fromInteger 0 = Z
      fromInteger n = S (fromInteger (n-1))
      S n - S m = n - m
      n - _ = n

  instance Bounded Peano where
      minBound = Z
      maxBound = S maxBound
  |])

-- | Shows integer representation.
instance Show Peano where
    showsPrec n = showsPrec n . toInteger

-- | Reads the integer representation.
instance Read Peano where
    readPrec = fmap (fromIntegral :: Natural -> Peano) readPrec

-- | Will obviously diverge for values like `maxBound`.
instance NFData Peano where
    rnf Z     = ()
    rnf (S n) = rnf n

-- | Reasonably expensive.
instance Real Peano where
    toRational = toRational . toInteger

-- | Uses custom 'enumFrom', 'enumFromThen', 'enumFromThenTo' to avoid
-- expensive conversions to and from 'Int'.
--
-- >>> [1..3]
-- [1,2,3]
-- >>> [1..1]
-- [1]
-- >>> [2..1]
-- []
-- >>> take 3 [1,2..]
-- [1,2,3]
-- >>> take 3 [5,4..]
-- [5,4,3]
-- >>> [1,3..7]
-- [1,3,5,7]
-- >>> [5,4..1]
-- [5,4,3,2,1]
-- >>> [5,3..1]
-- [5,3,1]
instance Enum Peano where
    succ = S
    pred (S n) = n
    pred Z = error "pred called on zero nat"
    fromEnum = go 0
      where
        go !n Z = n
        go !n (S m) = go (1 + n) m
    toEnum m
      | m < 0 = error "cannot convert negative number to Peano"
      | otherwise = go m
      where
        go 0 = Z
        go n = S (go (n - 1))
    enumFrom = iterate S
    enumFromTo n m = unfoldr f (n, S m - n)
      where
        f (_,Z) = Nothing
        f (e,S l) = Just (e, (S e, l))
    enumFromThen n m = iterate t n
      where
        ts Z mm = (+) mm
        ts (S nn) (S mm) = ts nn mm
        ts nn Z = subtract nn
        t = ts n m
    enumFromThenTo n m t = unfoldr f (n, jm)
      where
        ts (S nn) (S mm) = ts nn mm
        ts Z mm = (S t - n, (+) mm, mm)
        ts nn Z = (S n - t, subtract nn, nn)
        (jm,tf,tt) = ts n m
        td = subtract tt
        f (_,Z) = Nothing
        f (e,l@(S _)) = Just (e, (tf e, td l))


$(promoteOnly [d|
  instance Enum Peano where
      succ = S
      pred (S n) = n
      pred Z     = error "pred called on zero nat"
      fromEnum Z     = 0
      fromEnum (S n) = 1 + fromEnum n
      toEnum 0 = Z
      toEnum n = S (toEnum (n-1))
  |])

-- | Errors on zero.
--
-- >>> 5 `div` 2
-- 2
instance Integral Peano where
    toInteger = go 0
      where
        go !p Z     = p
        go !p (S n) = go (p + 1) n
    quotRem _ Z = (maxBound, error "divide by zero")
    quotRem x y = qr Z x y
      where
        qr q n m = go n m
          where
            go nn Z          = qr (S q) nn m
            go (S nn) (S mm) = go nn mm
            go Z (S _)       = (q, n)
    quot n m = go n where
      go = subt m where
        subt Z nn          = S (go nn)
        subt (S mm) (S nn) = subt mm nn
        subt (S _) Z       = Z
    rem _ Z = error "divide by zero"
    rem nn mm = r nn mm where
      r n m = go n m where
        go nnn Z           = r nnn m
        go (S nnn) (S mmm) = go nnn mmm
        go Z (S _)         = n
    div = quot
    mod = rem
    divMod = quotRem

instance Ix Peano where
    range = uncurry enumFromTo
    inRange = uncurry go where
      go (S _) _ Z         = False
      go Z y x             = x <= y
      go (S x) (S y) (S z) = go x y z
      go (S _) Z (S _)     = False
    index = uncurry go where
      go Z h i             = lim 0 h i
      go (S _) _ Z         = error "out of range"
      go (S l) (S h) (S i) = go l h i
      go (S _) Z (S _)     = error "out of range"
      lim _ Z (S _)      = error "out of range"
      lim !a (S n) (S m) = lim (a + 1) n m
      lim !a _ Z         = a

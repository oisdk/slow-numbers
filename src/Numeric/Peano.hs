{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables  #-}

module Numeric.Peano where

import           Data.List              (unfoldr)

import           Control.DeepSeq        (NFData (rnf))

import           Data.Data              (Data, Typeable)
import           GHC.Generics           (Generic)

import           Data.Promotion.Prelude
import           Data.Promotion.Prelude.Enum
import           Data.Promotion.TH
import           Data.Singletons.TH

import           Numeric.Natural

-- $setup
-- >>> import Test.QuickCheck
-- >>> :{
-- instance Arbitrary Nat where
--     arbitrary = fmap (fromInteger . getNonNegative) arbitrary
-- :}

-- | Nat numbers. Care is taken to make operations as lazy as
-- possible:
--
-- >>> 1 > S (S undefined)
-- False
-- >>> Z > undefined
-- False
-- >>> 3 + (undefined :: Nat) >= 3
-- True
$(singletons [d|
  data Nat
      = Z
      | S Nat
      deriving (Eq,Generic,Data,Typeable)
  |])
-- | As lazy as possible
instance Ord Nat where
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
    (>=) = flip (<=)
    (<) = flip (>)

-- | Subtraction stops at zero.
--
-- prop> n >= m ==> m - n == Z
instance Num Nat where
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

-- | The maximum bound here is infinity.
--
-- prop> (maxBound :: Nat) > n
instance Bounded Nat where
    minBound = Z
    maxBound = S maxBound

$(promoteOnly [d|
  instance Ord Nat where
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

  instance Num Nat where
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

  instance Bounded Nat where
      minBound = Z
      maxBound = S maxBound
  |])

-- | Shows integer representation.
instance Show Nat where
    showsPrec n = showsPrec n . toInteger

-- | Reads the integer representation.
instance Read Nat where
    readsPrec d r =
        [ (fromIntegral (n :: Natural), xs)
        | (n,xs) <- readsPrec d r ]

-- | Will obviously diverge for values like `maxBound`.
instance NFData Nat where
    rnf Z     = ()
    rnf (S n) = rnf n

-- | Reasonably expensive.
instance Real Nat where
    toRational = fromInteger . toInteger

-- | Uses custom 'enumFrom', 'enumFromThen', 'enumFromThenTo' to avoid
-- expensive conversions to and from 'Int'.
--
-- >>> [1..3] :: [Nat]
-- [1,2,3]
-- >>> [1..1] :: [Nat]
-- [1]
-- >>> [2..1] :: [Nat]
-- []
-- >>> take 3 [1,2..] :: [Nat]
-- [1,2,3]
-- >>> take 3 [5,4..] :: [Nat]
-- [5,4,3]
-- >>> [1,3..7] :: [Nat]
-- [1,3,5,7]
-- >>> [5,4..1] :: [Nat]
-- [5,4,3,2,1]
-- >>> [5,3..1] :: [Nat]
-- [5,3,1]
instance Enum Nat where
    succ = S
    pred (S n) = n
    pred Z = error "pred called on zero nat"
    fromEnum = go 0
      where
        go !n Z = n
        go !n (S m) = go (1 + n) m
    toEnum = go . abs
      where
        go 0 = Z
        go n = S (go (n-1))
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
    enumFromThenTo n m t =
        unfoldr
            f
            (n,either (const (S n - t)) (const (S t - n)) tt)
      where
        ts Z mm = Right mm
        ts (S nn) (S mm) = ts nn mm
        ts nn Z = Left nn
        tt = ts n m
        tf = either subtract (+) tt
        td = either subtract subtract tt
        f (_,Z) = Nothing
        f (e,l@(S _)) = Just (e, (tf e,td l))


$(promoteOnly [d|
  instance Enum Nat where
      succ = S
      pred (S n) = n
      pred Z = error "pred called on zero nat"
      fromEnum Z = 0
      fromEnum (S n) = 1 + fromEnum n
      toEnum 0 = Z
      toEnum n = S (toEnum (n-1))
  |])

-- | Errors on zero.
--
-- >>> 5 `div` 2 :: Nat
-- 2
instance Integral Nat where
    toInteger = go 0
      where
        go !p Z     = p
        go !p (S n) = go (p + 1) n
    quotRem _ Z = error "divide by zero"
    quotRem x (S y) = qr Z x (S y)
      where
        qr q n m = go n m
          where
            go nn Z          = qr (S q) nn m
            go (S nn) (S mm) = go nn mm
            go Z (S _)       = (q, n)
    quot _ Z = error "divide by zero"
    quot n m = go n where
      go = subt m where
        subt Z nn          = S (go nn)
        subt (S mm) (S nn) = subt mm nn
        subt (S _) Z       = Z
    rem _ Z = error "divide by zero"
    rem nn mm = r nn mm where
      r n m = go n m where
        go nnn Z = r nnn m
        go (S nnn) (S mmm) = go nnn mmm
        go Z (S _) = n
    div = quot
    mod = rem
    divMod = quotRem

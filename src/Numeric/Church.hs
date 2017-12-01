{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Basic church numerals. These are even less efficient than
-- "Numeric.Peano", and no more lazy.
module Numeric.Church
  (Church(..))
  where

import Data.Function (fix)

-- $setup
-- >>> import Test.QuickCheck
-- >>> default (Church)
-- >>> :{
-- instance Arbitrary Church where
--     arbitrary = fmap (fromInteger . getNonNegative) arbitrary
-- :}

-- | Church numerals.
newtype Church = Church { runChurch :: forall a. (a -> a) -> a -> a }

-- | Quite lazy
--
-- >>> 4 == maxBound
-- False
-- >>> maxBound == 4
-- False
--
-- prop> n === (n :: Church)
instance Eq Church where
    (==) n =
        runChurch
            n
            (\c m ->
                  runChurch m (const (c (pred m))) False)
            (\(Church nn) ->
                  nn (const False) True)

-- | Fully lazy
--
-- >>> compare 2 2
-- EQ
--
-- >>> compare 2 1
-- GT
--
-- >>> compare 1 2
-- LT
--
-- prop> n < (maxBound :: Church)
instance Ord Church where
    (<=) = flip (>=)
    (>=) n =
        runChurch
            n
            (\c m ->
                  runChurch m (const (c (pred m))) True)
            (\(Church m) ->
                  m (const False) True)
    compare n =
        runChurch
            n
            (\c m ->
                  runChurch m (const (c (pred m))) GT)
            (\(Church m) ->
                  m (const LT) EQ)

-- | Laziness is maintained
--
-- prop> n + maxBound > (n :: Church)
--
-- Subtraction stops at zero
--
-- >>> 5 - 6
-- 0
--
-- prop> n >= m ==> m - n === (0 :: Church)
instance Num Church where
    abs = id
    signum (Church n) = n (const 1) 0
    fromInteger n = Church (go (abs n))
      where
        go 0 _ = id
        go m f = f . go (m - 1) f
    Church n + Church m =
        Church (\f -> n f . m f)
    Church n * Church m = Church (n . m)
    n - Church m = m pred n

instance Enum Church where
    fromEnum (Church n) = n succ 0
    toEnum n = Church (go (abs n)) where
      go 0 _ = id
      go m f = f . go (m-1) f
    pred (Church n) = Church (\f x -> n (\g h -> h (g f)) (const x) id)
    {-# INLINE pred #-}
    succ (Church n) = Church (\f -> f . n f)
    enumFrom = iterate succ

instance Real Church where
    toRational = toRational . toInteger

isZero :: Church -> a -> a -> a
isZero (Church n) t f = n (const f) t

divide1 :: Church -> Church -> Church
divide1 n m =
    Church
        (\f x ->
              (\d -> isZero d x (f (runChurch (divide1 d m) f x))) (n - m))

rem1 :: Church -> Church -> Church
rem1 n m =
    let d = n - m
    in case compare d 1 of
           LT -> n
           EQ -> 0
           GT -> rem1 d m

instance Integral Church where
    div = divide1 . succ
    toInteger (Church n) = n succ 0
    quot = divide1 . succ
    rem n = pred . rem1 (succ n)
    quotRem n m = (quot n m, rem n m)

instance Show Church where
    showsPrec n = showsPrec n . toInteger

instance Bounded Church where
    minBound = 0
    maxBound = Church (const . fix)

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

quotRem1 :: Church -> Church -> (Church -> Church -> a) -> a
quotRem1 n m k =
    let d = n - m
    in cmp1 d
      (k 0 n)
      (k 1 0)
      (quotRem1 d m (k . succ))

newtype MB = MB
    { runMB :: forall b. ((b -> b -> b) -> b) -> b -> b
    }

cmp1 :: Church -> a -> a -> a -> a
cmp1 c l e g =
    runMB
        (runChurch c (\x -> MB (f (runMB x))) (MB (const id)))
        (\bb ->
              bb g e) l
  where
    f x k _ = k (x . const)


instance Integral Church where
    toInteger (Church n) = n succ 0
    quot n m = quotRem1 (succ n) m const
    rem n m = quotRem1 (succ n) m (const pred)
    quotRem n m = quotRem1 (succ n) m (\n' m' -> (n', pred m'))

instance Show Church where
    showsPrec n = showsPrec n . toInteger

instance Bounded Church where
    minBound = 0
    maxBound = Church (const . fix)

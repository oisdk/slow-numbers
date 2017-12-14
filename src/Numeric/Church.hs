{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Basic church numerals. These are even less efficient than
-- "Numeric.Peano", and no more lazy.
module Numeric.Church
  (Church(..)
  ,runChurch')
  where

import           Data.Function (fix)
import           Numeric.Natural
import           Text.Read
import           Numeric.Church.Prelude
import           GHC.Base (build)

-- $setup
-- >>> import Test.QuickCheck
-- >>> default (Church)
-- >>> :{
-- instance Arbitrary Church where
--     arbitrary = fmap (fromInteger . getNonNegative) arbitrary
-- :}

-- | Church numerals.
newtype Church = Church
    { runChurch :: forall a. (a -> a) -> a -> a
    }

-- | Run a church numeral, strictly.
runChurch' :: Church -> (a -> a) -> a -> a
runChurch' n f = runChurch n (\a !i -> a (f i)) id

-- | Quite lazy
--
-- >>> 4 == maxBound
-- False
-- >>> maxBound == 4
-- False
--
-- prop> n === (n :: Church)
instance Eq Church where
    (==) = cmpC False True False

cmpC :: a -> a -> a -> Church -> Church -> a
cmpC l e g = go
  where
    go n =
        runChurch
            n
            (\c m ->
                  runChurch m (const (c (pred m))) g)
            (\(Church m) ->
                  m (const l) e)

cmpSub :: (Church -> a) -> (Church -> a) -> a -> Church -> Church -> a
cmpSub l g e n m =
    runChurch ntm (const (g ntm)) (runChurch mtn (const (l mtn)) e)
  where
    ntm = n - m
    mtn = m - n

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
-- >>> compare maxBound 1
-- GT
--
-- >>> compare 1 maxBound
-- LT
--
-- prop> n < (maxBound :: Church)
instance Ord Church where
    (<=) n =
        runChurch
            n
            (\a m ->
                  runChurch m (const (a (pred m))) False)
            (const True)
    (>=) = flip (<=)
    compare = cmpC LT EQ GT

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
    fromEnum n = runChurch' n succ 0
    toEnum n = Church (go (abs n)) where
      go 0 _ = id
      go m f = f . go (m-1) f
    pred (Church n) = Church (\f x -> n (\g h -> h (g f)) (const x) id)
    {-# INLINE pred #-}
    succ (Church n) = Church (\f -> f . n f)
    enumFrom = iterate succ
    enumFromTo n m = build (\c nl -> runChurch (m - n) (\a e -> e `c` a (succ e)) (`c` nl) n)
    enumFromThen n = cmpSub (flip iterate n . (+)) (flip iterate n . subtract) (repeat n) n

instance Real Church where
    toRational = toRational . toInteger

quot1 :: Church -> Church -> Church
quot1 n m =
    let d = n - m
    in cmp1 d 0 1 (succ (quot1 d m))

rem1 :: Church -> Church -> Church
rem1 n m =
    let d = n - m
    in cmp1 d n 0 (rem1 d m)

quotRem1 :: (Church -> Church -> a) -> Church -> Church -> a
quotRem1 k n m =
    let d = n - m
    in cmp1 d
      (k 0 n)
      (k 1 0)
      (quotRem1 (k . succ) d m)

cmp1 :: Church -> a -> a -> a -> a
cmp1 c l e g =
    runMaybeBoolFold
        (runChurch
             c
             (\x ->
                   MaybeBoolFold
                       (\k ->
                             const (k (runMaybeBoolFold x . const))))
             (MaybeBoolFold (const id)))
        (\bb ->
              bb g e)
        l

instance Integral Church where
    toInteger n = runChurch' n succ 0
    quot = quot1 . succ
    rem n = pred . rem1 (succ n)
    quotRem = quotRem1 (\n m -> (n, pred m)) . succ

instance Show Church where
    showsPrec n = showsPrec n . toInteger

instance Read Church where
    readPrec = fmap (fromIntegral :: Natural -> Church) readPrec

instance Bounded Church where
    minBound = 0
    maxBound = Church (const . fix)

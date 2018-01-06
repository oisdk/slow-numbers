{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes   #-}

module Numeric.Scott where

import Numeric.Church.Prelude
import Data.Function (fix)
import Numeric.Natural
import Text.Read
import Data.Ix

newtype Scott = Scott
    { runScott :: forall a. a -> (Scott -> a) -> a
    }

instance Num Scott where
    n + m = runScott n m (\s -> succ (s + m))
    n * m = runScott n 0 (\s -> m + s * m)
    abs = id
    signum n = runScott n 0 (const 1)
    fromInteger 0 = Scott const
    fromInteger n = Scott (\_ f -> f (fromInteger (n-1)))
    n - m = runScott n 0 (runScott m n . (-))

instance Show Scott where
    showsPrec n = showsPrec n . toInteger

instance Read Scott where
    readPrec = fmap (fromIntegral :: Natural -> Scott) readPrec

instance Eq Scott where
    n == m =
        runScott n (runScott m True (const False)) (runScott m False . (==))

instance Ord Scott where
    compare n m =
        runScott n (runScott m EQ (const LT)) (runScott m GT . compare)
    min n m = runScott n n (\s -> runScott m m (succ . min s))
    max n m = runScott n m (\s -> runScott m n (succ . max s))
    n <= m = runScott n True (runScott m False . (<=))
    (>=) = flip (<=)
    n > m = runScott n False (runScott m True . (>))
    (<) = flip (>)

instance Enum Scott where
    succ n = Scott (\_ s -> s n)
    pred n = runScott n 0 id
    fromEnum = go 0
      where
        go !i n = runScott n i (go (i + 1))
    toEnum 0 = Scott const
    toEnum n =
        Scott
            (\_ f ->
                  f (toEnum (n - 1)))
    enumFrom = iterate succ
    enumFromTo n m = unfoldr3 f n (succ m - n)
      where
        f e x nt js = runScott x nt (js e (succ e))
    enumFromThen n m = iterate (t n m) n
      where
        t nn mm = runScott nn (mm +) (runScott mm (subtract nn) . t)
    enumFromThenTo n m t =
        fix (\ts nn mm -> runScott nn (k (+) mm (succ t - n)) (runScott mm (k subtract nn (succ n - t)) . ts)) n m
      where
        k tf tt = unfoldr3 (\e l nt js -> runScott l nt (const (js e (tf tt e) (l - tt)))) n

instance Bounded Scott where
    minBound = Scott const
    maxBound = Scott (\_ f -> f maxBound)

instance Real Scott where
    toRational = toRational . toInteger

instance Integral Scott where
    toInteger = go 0
      where
        go !i n = runScott n i (go (i + 1))
    quotRem = qr 0
      where
        qr q n m = go m n
          where
            go mm nn = runScott mm (qr (succ q) nn m) (runScott nn (q, n) . go)
    quot n m = go n
      where
        go = subt m
          where
            subt mm nn = runScott mm (succ (go nn)) (runScott nn 0 . subt)
    rem n m = go m n where
      go mm nn = runScott mm (rem nn m) (runScott nn n . go)
    div = quot
    mod = rem
    divMod = quotRem

instance Ix Scott where
    range = uncurry enumFromTo
    inRange = uncurry go
      where
        go x y z =
            runScott x (z <= y) (runScott y False . (runScott z False .) . go)
    index = uncurry go
      where
        go l h i = runScott l (lim 0 i h) (inr h . (inr i .) . go)
        lim !a m n = runScott m a (inr n . lim (a + 1))
        inr n = runScott n (error "out of range")

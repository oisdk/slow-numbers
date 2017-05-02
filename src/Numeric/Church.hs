{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Numeric.Church where

import Data.Function (fix)

-- | Church numerals.
newtype Nat = Nat { runNat :: forall a. (a -> a) -> a -> a }

instance Eq Nat where
    (==) n =
        runNat
            n
            (\c m ->
                  runNat m (const (c (pred m))) False)
            (\(Nat nn) ->
                  nn (const False) True)

instance Ord Nat where
    (<=) = flip (>=)
    (>=) (Nat n) =
        n
            (\c m ->
                  runNat m (const (c (pred m))) True)
            (\(Nat m) ->
                  m (const False) True)

instance Num Nat where
    abs = id
    signum (Nat n) = n (const 1) 0
    fromInteger n = Nat (go (abs n))
      where
        go 0 _ = id
        go m f = f . go (m - 1) f
    Nat n + Nat m =
        Nat
            (\f ->
                  n f . m f)
    Nat n * Nat m = Nat (n . m)
    n - Nat m = m pred n

instance Enum Nat where
    fromEnum (Nat n) = n succ 0
    toEnum n = Nat (go (abs n)) where
      go 0 _ = id
      go m f = f . go (m-1) f
    pred (Nat n) = Nat (\f x -> n (\g h -> h (g f)) (const x) id)
    succ (Nat n) = Nat (\f -> f . n f)

instance Real Nat where
    toRational = toRational . toInteger

isZero :: Nat -> a -> a -> a
isZero (Nat n) t f = n (const f) t

divide1 :: Nat -> Nat -> Nat
divide1 n m =
    Nat
        (\f x ->
              (\d -> isZero d x (f (runNat (divide1 d m) f x))) (n - m))

rem1 :: Nat -> Nat -> Nat
rem1 n m = let d = n - m in case compare d 1 of
  LT -> n
  EQ -> 0
  GT -> rem1 d m

instance Integral Nat where
    div = divide1 . succ
    toInteger (Nat n) = n succ 0
    quot = divide1 . succ
    rem n = pred . rem1 (succ n)
    quotRem n m = (quot n m, rem n m)

instance Show Nat where
    showsPrec n = showsPrec n . toInteger

instance Bounded Nat where
    minBound = 0
    maxBound = Nat (const . fix)

{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Numeric.Positional where

import           Data.Coerce
import           Data.List
import           Data.Proxy
import           GHC.TypeNats
import           Numeric.Natural

newtype Positional (n :: Nat) = Positional
    { runPositional :: [Natural]
    } deriving (Eq,Show)

infixl 0 `upon`
upon :: Coercible a b
     => (b -> b -> b)
     -> (a -> b)
     -> (a -> a -> a)
upon f _ = coerce f

unPositional :: forall n. KnownNat n => Positional n -> Integer
unPositional (Positional xs) = foldr f 0 xs
  where
    b = toInteger (natVal (Proxy :: Proxy n))
    f e a = toInteger e + b * a


instance Ord (Positional n) where
    compare = coerce (go EQ)
      where
        go :: Ordering -> [Natural] -> [Natural] -> Ordering
        go !a [] []         = a
        go !_ (_:_) []      = GT
        go !_ [] (_:_)      = LT
        go !a (x:xs) (y:ys) = go (compare x y `mappend` a) xs ys

instance KnownNat n =>
         Num (Positional n) where
    abs = id
    signum (Positional []) = Positional []
    signum _ = Positional [1]
    (+) = go `upon` runPositional
      where
        b = natVal (Proxy :: Proxy n)
        go [] ys = ys
        go xs [] = xs
        go (x:xs) (y:ys)
          | xy >= b = (xy - b) : goc xs ys
          | otherwise = xy : go xs ys
          where
            xy = x + y
        goc [] ys = c ys
        goc xs [] = c xs
        goc (x:xs) (y:ys)
          | xy >= b = (xy - b) : goc xs ys
          | otherwise = xy : go xs ys
          where
            xy = x + y + 1
        c [] = [1]
        c (x:xs)
          | x' >= b = 0 : c xs
          | otherwise = x' : xs
          where
            x' = x + 1
    fromInteger = Positional . unfoldr f . fromInteger
      where
        b = natVal (Proxy :: Proxy n)
        f 0 = Nothing
        f m =
            Just
                (case m `quotRem` b of
                     (q,r) -> (r, q))
    _ * Positional [] = Positional []
    Positional xs * Positional (yh:ys) = Positional (wrap (foldr f [] xs))
      where
        f x zs = (x * yh) : foldr (g x) id ys zs
        g x y a (z:zs) = (x * y + z) : a zs
        g x y a [] = (x * y) : a []
        b = natVal (Proxy :: Proxy n)
        wrap [] = []
        wrap (z:zs)
          | z < b = z : wrap zs
          | otherwise =
              case z `quotRem` b of
                  (q,r) -> r : carry q zs
        carry c [] = [c]
        carry c (z:zs)
          | z' < b = z' : wrap zs
          | otherwise =
              case z' `quotRem` b of
                  (q,r) -> r : carry q zs
          where
            z' = c + z
    (-) = go (0 :: Word) `upon` runPositional
      where
        i = natVal (Proxy :: Proxy n)
        go p (x:xs) (y:ys) =
            case compare x y of
                GT -> pad p (x - y : go 0 xs ys)
                EQ -> go (succ p) xs ys
                LT -> pad p ((i + x) - y : goc 0 xs ys)
        go _ [] [] = []
        go p xs [] = pad p xs
        go _ [] (_:_) = error "numeric underflow"

        goc p (x:xs) (y':ys) =
            case compare x y of
                GT -> pad p (x - y : go 0  xs ys)
                EQ -> go (succ p)  xs ys
                LT -> pad p ((i + x) - y : goc 0  xs ys)
          where
            y = y' + 1

        goc _ xs [] = para go' [] xs
        goc _ [] (_:_) = error "numeric underflow"

        go' x xs a = case compare x 1 of
          LT -> (i - 1) : a
          GT -> (x - 1) : xs
          EQ -> case xs of
            [] -> []
            _  -> 0 : xs

        pad 0 xs = xs
        pad n xs = 0 : pad (pred n) xs

para :: (a -> [a] -> b -> b) -> b -> [a] -> b
para f b = go
  where
    go [] = b
    go (x:xs) = f x xs (go xs)
{-# INLINE para #-}

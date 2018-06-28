{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Numeric.PAdic where

import           Data.Proxy
import           GHC.TypeNats
import           Numeric.Natural

infixr 5 :+
data PAdic (n :: Nat)
    = Natural :+ PAdic n
    | Zero
    | Repeating

instance KnownNat n => Show (PAdic n) where
    showsPrec _ Zero = (:) '0'
    showsPrec _ zs = go zs
      where
        go (x :+ xs) s = go xs (shows x s)
        go Zero s      = s
        go Repeating s = shows (natVal (Proxy :: Proxy n) - 1) ('\773' : s)

instance KnownNat n => Eq (PAdic n) where
    (x :+ xs) == (y :+ ys) = x == y && xs == ys
    Repeating == Repeating = True
    Zero == Zero = True
    (x :+ xs) == Zero = x == 0 && xs == Zero
    (x :+ xs) == Repeating = x == (natVal (Proxy :: Proxy n) - 1) && xs == Repeating
    Zero == (y :+ ys) = 0 == y && ys == Zero
    Repeating == (y :+ ys) = (natVal (Proxy :: Proxy n) - 1 == y) && Repeating == ys
    _ == _ = False

instance KnownNat n => Ord (PAdic n) where
    compare (x :+ xs) (y :+ ys) = compare x y `mappend` compare xs ys
    compare Zero Zero = EQ
    compare Repeating Repeating = EQ
    compare Zero Repeating = LT
    compare Repeating Zero = GT
    compare (x :+ xs) Zero = compare x 0 `mappend` compare xs Zero
    compare (x :+ xs) Repeating = compare x (natVal (Proxy :: Proxy n) - 1) `mappend` compare xs Repeating
    compare Zero (y :+ ys) = compare 0 y `mappend` compare Zero ys
    compare Repeating (y :+ ys) = compare (natVal (Proxy :: Proxy n) - 1) y `mappend` compare Repeating ys

instance KnownNat n =>
         Num (PAdic n) where
    fromInteger 0 = Zero
    fromInteger n =
        case compare n 0 of
            LT -> negate (go (fromInteger (abs n)))
            EQ -> Zero
            GT -> go (fromInteger n)
      where
        b = natVal (Proxy :: Proxy n)
        go 0 = Zero
        go m =
            case m `quotRem` b of
                (q,r) -> r :+ go q
    (+) = go
      where
        b = natVal (Proxy :: Proxy n)
        go (x :+ xs) (y :+ ys)
          | xy >= b = (xy - b) :+ goc xs ys
          | otherwise = xy :+ go xs ys
          where
            xy = x + y
        go xs Zero = xs
        go Zero ys = ys
        go Repeating Repeating = (b - 2) :+ Repeating
        go (0 :+ xs) Repeating = (b - 1) :+ go xs Repeating
        go (x :+ xs) Repeating = (x - 1) :+ goc xs Repeating
        go Repeating (0 :+ ys) = (b - 1) :+ go Repeating ys
        go Repeating (y :+ ys) = (y - 1) :+ goc Repeating ys
        goc (x :+ xs) (y :+ ys)
          | xy >= b = (xy - b) :+ goc xs ys
          | otherwise = xy :+ go xs ys
          where
            xy = x + y + 1
        goc Zero ys = c ys
        goc xs Zero = c xs
        goc (x :+ xs) Repeating = x :+ goc xs Repeating
        goc Repeating (y :+ ys) = y :+ goc Repeating ys
        goc Repeating Repeating = Repeating
        c Zero = 1 :+ Zero
        c Repeating = Zero
        c (x :+ xs)
          | x' >= b = 0 :+ c xs
          | otherwise = x' :+ xs
          where
            x' = x + 1
    negate Zero = Zero
    negate Repeating = 1 :+ Zero
    negate (0 :+ xs) = 0 :+ negate xs
    negate (x :+ xs) = (b - x) :+ go xs
      where
        b = natVal (Proxy :: Proxy n)
        go Zero      = Repeating
        go Repeating = Zero
        go (y :+ ys) = b - (y + 1) :+ go ys
    (*) xs =
        \case
            Zero -> Zero
            Repeating -> negate xs
            yh :+ ys -> foldrP f (negate (yh :+ ys)) Zero xs
                where b = natVal (Proxy :: Proxy n)
                      f x zs = (x * yh) `cons` foldrP (g x) (e x) id ys zs
                      e x zs = negate (x :+ Zero) + zs
                      g x y a (z :+ zs) = (x * y + z) `cons` a zs
                      g x y a Zero      = (x * y) `cons` a Zero
                      g x y a Repeating = (x * y + (b - 1)) `cons` a Repeating
                      cons z zs =
                          case quotRem z b of
                              (0,r) -> r :+ zs
                              (q,r) -> r :+ (fromIntegral q + zs)
                      foldrP _ _ b' Zero       = b'
                      foldrP _ r _ Repeating   = r
                      foldrP f' r b' (z :+ zs) = f' z (foldrP f' r b' zs)
    abs = error "abs not defined on P-adic numbers"
    signum = error "signum not defined on P-adic numbers"

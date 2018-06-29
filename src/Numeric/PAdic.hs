{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards       #-}

-- | \(p\)-adic numbers.
module Numeric.PAdic (PAdic(..)) where

import           Data.Proxy
import           GHC.TypeNats
import           Numeric.Natural
{-|
The \(p\)-adic numbers are represented as in a normal positional
number system (with base \(p\)), with a different notion of "distance"
than most systems. Basically, numbers are closer if their least
significant digits are closer. So, when \(p=10\), \(362_{10}\) is
"closer" to \(2_{10}\) than it is to \(363_{10}\). One way to think
about this is that the numbers are ordered lexicographically (from
least-significant to most-significant digit).

The 'Ord' instance reflects this:

>>> 362 < (3 :: PAdic 10)
True

In many cases, \(p\)-adic numbers behave as normal positional numbers:

>>> 45 + 63 :: PAdic 10
108

However, they diverge when it comes to representing negative numbers.
In decimal, an infinitely repeating digit goes to the right:

\[\frac{1}{3} = 0.333333\overline{3}\]

The <https://en.wikipedia.org/wiki/Vinculum_(symbol) vinculum> is
placed at the right end of the number.

However, in \(p\)-adic numbers, because of the implications of the
ordering, infinitely repeating digits trail to the left.

>>> 5 :+ Repeating :: PAdic 10
9̅5

For this reason, a negative number can be represented as a sequence
of digits terminated by an infinitely repeated \(p-1\). For instance,
 \(-1_{10}\) is:

>>> -1 :: PAdic 10
9̅

Addition and subtraction still work as you would expect:

prop> x - x === Zero @10
-}
infixr 5 :+
data PAdic (n :: Nat)
    = !Natural :+ PAdic n
    | Zero
    | Repeating

foldPAdic :: (Natural -> b -> b) -> b -> b -> PAdic n -> b
foldPAdic f z r = go
  where
    go Zero = z
    go Repeating = r
    go (x :+ xs) = f x (go xs)

compress :: forall n. KnownNat n => PAdic n -> PAdic n
compress = foldPAdic f Zero Repeating
  where
    f x xs
      | x == 0   , Zero      <- xs = Zero
      | x == nine, Repeating <- xs = Repeating
      | otherwise                  = x :+ xs
    nine = natVal (Proxy :: Proxy n) - 1

instance KnownNat n =>
         Show (PAdic n) where
    showsPrec _ = go . compress
      where
        go Zero = (:) '0'
        go zs = foldPAdic f id r zs
        f x xs s = xs (shows x s)
        r s =
            foldr
                (\x xs ->
                      x : '\773' : xs)
                s
                (show (natVal (Proxy :: Proxy n) - 1))

instance KnownNat n =>
         Eq (PAdic n) where
    (x :+ xs) == (y :+ ys) = x == y && xs == ys
    Repeating == Repeating = True
    Zero == Zero = True
    (x :+ xs) == Zero = x == 0 && xs == Zero
    (x :+ xs) == Repeating =
        x == (natVal (Proxy :: Proxy n) - 1) && xs == Repeating
    Zero == (y :+ ys) = 0 == y && ys == Zero
    Repeating == (y :+ ys) =
        (natVal (Proxy :: Proxy n) - 1 == y) && Repeating == ys
    _ == _ = False

instance KnownNat n =>
         Ord (PAdic n) where
    compare (x :+ xs) (y :+ ys) = compare x y `mappend` compare xs ys
    compare Zero Zero = EQ
    compare Repeating Repeating = EQ
    compare Zero Repeating = LT
    compare Repeating Zero = GT
    compare (x :+ xs) Zero = compare x 0 `mappend` compare xs Zero
    compare (x :+ xs) Repeating =
        compare x (natVal (Proxy :: Proxy n) - 1) `mappend`
        compare xs Repeating
    compare Zero (y :+ ys) = compare 0 y `mappend` compare Zero ys
    compare Repeating (y :+ ys) =
        compare (natVal (Proxy :: Proxy n) - 1) y `mappend`
        compare Repeating ys

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
            yh :+ ys -> foldPAdic f Zero (negate (yh :+ ys)) xs
                where b = natVal (Proxy :: Proxy n)
                      f x zs = (x * yh) `cons` foldPAdic (g x) id (e x) ys zs
                      e x zs = negate (x :+ Zero) + zs
                      g x y a (z :+ zs) = (x * y + z) `cons` a zs
                      g x y a Zero      = (x * y) `cons` a Zero
                      g x y a Repeating = (x * y + (b - 1)) `cons` a Repeating
                      cons z zs =
                          case quotRem z b of
                              (0,r) -> r :+ zs
                              (q,r) -> r :+ (fromIntegral q + zs)
    abs = error "abs not defined on P-adic numbers"
    signum = error "signum not defined on P-adic numbers"

-- $setup
-- >>> :set -XDataKinds
-- >>> :set -XScopedTypeVariables
-- >>> :set -XTypeApplications
-- >>> import GHC.TypeNats
-- >>> import Test.QuickCheck
-- >>> import Control.Applicative
-- >>> :{
-- instance KnownNat n => Arbitrary (PAdic n) where
--   arbitrary = liftA2 (foldr f) (elements [Zero,Repeating]) arbitrary
--     where
--       f (NonNegative n) xs = (fromInteger n `mod` natVal (Proxy :: Proxy n)) :+ xs
-- :}

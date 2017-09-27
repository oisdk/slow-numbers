{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

import           Hedgehog
import qualified Hedgehog.Gen       as Gen
import qualified Hedgehog.Range     as Range
import           Test.DocTest

import           Numeric.Peano
import           Numeric.Church

import           Control.Monad

import           Data.Data
import           Data.Ix

binaryProp
    :: forall a.
       Integral a
    => (forall t. Integral t => t -> t -> t)
    -> Integer
    -> Integer
    -> (Integer -> Integer -> Bool)
    -> Property
binaryProp op lb ub cond = property $ do
    x <- forAll (Gen.integral (Range.linear lb ub))
    y <- forAll (Gen.integral (Range.linear lb ub))
    guard (cond x y)
    let zb = op x y
    let zt = op (fromInteger @a x) (fromInteger y)
    zb === toInteger zt

ordProps
    :: forall a.
       (Ord a, Show a, Typeable a)
    => Gen IO a
    -> Property
ordProps xs = property $ do
    x <- forAll xs
    info "reflexive"
    x === x
    info "irreflexive"
    assert (not (x < x))
    y <- forAll xs
    info "Ord functions behave same as default implementations"
    case compare x y of
      LT -> do
          assert (x < y)
          assert (x /= y)
          assert (not (x == y))
          assert (x <= y)
          assert (not (x >= y))

          info "antisymmetric"
          assert (y > x)
          info "irreflexive"
          assert (not (x > y))
          info "transitive"
          z <- forAll xs
          when (z > y) (assert (z > x))
      EQ -> do
          assert (x == y)
          assert (not (x /= y))
          assert (not (x < y))
          assert (not (x > y))
          assert (x <= y)
          assert (x >= y)

          info "symmetric"
          assert (y == x)
          info "transitive"
          z <- forAll xs
          assert $ (x == z) == (y == z)
      GT -> do
          assert (x > y)
          assert (x /= y)
          assert (not (x == y))
          assert (x >= y)
          assert (not (x <= y))

          info "irreflexive"
          assert (not (x < y))
          info "antisymmetric"
          assert (y < x)
          info "transitive"
          z <- forAll xs
          when (z < y) (assert (z < x))

holdsForLength :: Foldable f => (a -> Bool) -> f a -> Int
holdsForLength p = flip (foldr f id ) 0 where
  f e a i | p e = a (i + 1)
          | otherwise = i

enumProps
    :: forall a.
       (Enum a, Show a, Typeable a, Ord a)
    => (Int -> Bool) -> Gen IO Int -> Gen IO a -> Property
enumProps p ig eg = property $ do
    x <- forAll ig
    info "from . to"
    (fromEnum . toEnum @a) x === x
    info "to . from"
    n <- forAll eg
    (toEnum . fromEnum) n === n
    info "[n..]"
    let lhs1 = take 100 $ map fromEnum [n..]
        rhs1 = take 100 $ [fromEnum n..]
        len1 = min (holdsForLength p lhs1) (holdsForLength p rhs1)
    take len1 lhs1 === take len1 rhs1
    info "[n,m..]"
    m <- forAll eg
    let lhs2 = take 100 $ map fromEnum [n,m..]
        rhs2 = take 100 $ [fromEnum n, fromEnum m..]
        len2 = min (holdsForLength p lhs2) (holdsForLength p rhs2)
    take len2 lhs2 === take len2 rhs2
    when (m >= n) $ do
        info "[n..m]"
        map fromEnum [n..m] === [fromEnum n..fromEnum m]
    l <- forAll eg
    when (((l > n) == (n > m)) && (l /= n)) $ do
        info "[l,n..m]"
        map fromEnum [l,n..m] === [fromEnum l, fromEnum n..fromEnum m]


prop_PeanoAdd :: Property
prop_PeanoAdd = binaryProp @Peano (+) 0 1000 (\_ _ -> True)

prop_PeanoMul :: Property
prop_PeanoMul = binaryProp @Peano (*) 0 1000 (\_ _ -> True)

prop_PeanoSub :: Property
prop_PeanoSub = withDiscards 1000 $ binaryProp @Peano (-) 0 1000 (>=)

prop_PeanoRem :: Property
prop_PeanoRem = binaryProp @Peano rem 0 1000 (\_ y -> y > 0)

prop_PeanoQuot :: Property
prop_PeanoQuot = binaryProp @Peano quot 0 1000 (\_ y -> y > 0)

prop_PeanoOrd :: Property
prop_PeanoOrd = ordProps (Gen.integral (Range.linear @Peano 0 1000))

prop_PeanoEnum :: Property
prop_PeanoEnum =
    enumProps
        (>= 0)
        (Gen.integral (Range.linear 0 1000))
        (Gen.integral (Range.linear @Peano 0 1000))

prop_ChurchAdd :: Property
prop_ChurchAdd = binaryProp @Church (+) 0 1000 (\_ _ -> True)

prop_ChurchMul :: Property
prop_ChurchMul = binaryProp @Church (*) 0 100 (\_ _ -> True)

prop_ChurchSub :: Property
prop_ChurchSub = withDiscards 1000 $ binaryProp @Church (-) 0 1000 (>=)

prop_ChurchRem :: Property
prop_ChurchRem = withTests 30 $ binaryProp @Church rem 0 50 (\_ y -> y > 0)

prop_ChurchQuot :: Property
prop_ChurchQuot = withTests 30 $ binaryProp @Church quot 0 50 (\_ y -> y > 0)

prop_ChurchOrd :: Property
prop_ChurchOrd = ordProps (Gen.integral (Range.linear @Church 0 50))

prop_ChurchEnum :: Property
prop_ChurchEnum =
    enumProps
        (>= 0)
        (Gen.integral (Range.linear 0 50))
        (Gen.integral (Range.linear @Church 0 50))

prop_PeanoInRange :: Property
prop_PeanoInRange = property $ do
    l <- forAll (Gen.integral (Range.linear Z 100))
    u <- forAll (Gen.integral (Range.linear l (l+100)))
    i <- forAll (Gen.integral (Range.linear 0 300))
    inRange (l,u) i === (l <= i &&  i <= u)

prop_PeanoIndex :: Property
prop_PeanoIndex = property $ do
    l <- forAll (Gen.integral (Range.linear Z 100))
    u <- forAll (Gen.integral (Range.linear l (l+100)))
    i <- forAll (Gen.integral (Range.linear l u))
    unless (inRange (l,u) i) discard
    index (l,u) i === fromEnum (i - l)

main :: IO Bool
main = do
    doctest ["-isrc","src/"]
    $$(checkConcurrent)

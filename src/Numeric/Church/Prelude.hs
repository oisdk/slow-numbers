{-# LANGUAGE RankNTypes #-}

module Numeric.Church.Prelude where

import GHC.Base (build)
import Data.Function (fix)

type Pair' a b = forall c. (a -> b -> c) -> c
newtype Pair a b = Pair { runPair :: Pair' a b }

pairFold :: (a,b) -> Pair' a b
pairFold = flip uncurry

pairBuild :: Pair' a b -> (a,b)
pairBuild p = p (,)

type BoolFold' = forall a. a -> a -> a
newtype BoolFold = BoolFold { runBoolFold :: BoolFold' }

boolFold :: Bool -> BoolFold'
boolFold True t _ = t
boolFold False _ f = f

boolBuild :: BoolFold' -> Bool
boolBuild b = b True False


type OrdFold' = forall a. a -> a -> a -> a
newtype OrdFold = OrdFold { runOrdFold :: OrdFold' }

ordFold :: Ordering -> OrdFold'
ordFold LT lt _ _ = lt
ordFold EQ _ eq _ = eq
ordFold GT _ _ gt = gt

ordBuild :: OrdFold' -> Ordering
ordBuild o = o LT EQ GT

type MaybeFold' a = forall b. b -> (a -> b) -> b
newtype MaybeFold a = MaybeFold { runMaybeFold :: MaybeFold' a }

maybeFold :: Maybe a -> MaybeFold' a
maybeFold Nothing b _ = b
maybeFold (Just x) _ f = f x

maybeBuild :: MaybeFold' a -> Maybe a
maybeBuild m = m Nothing Just

type MaybePairFold' a b = forall c. c -> (a -> b -> c) -> c
newtype MaybePairFold a b = MaybePairFold
    { runMaybePairFold :: MaybePairFold' a b
    }

maybePairFold :: Maybe (a,b) -> MaybePairFold' a b
maybePairFold Nothing b _ = b
maybePairFold (Just (x,y)) _ f = f x y

maybePairBuild :: MaybePairFold' a b -> Maybe (a,b)
maybePairBuild m = m Nothing (curry Just)

unfoldr :: (b -> MaybePairFold' a b) -> b -> [a]
{-# INLINE unfoldr #-}
unfoldr f b0 =
    build
        (\c n -> let go b = f b n (\a new_b -> a `c` go new_b) in go b0)

type MaybeBoolFold' = forall b. ((b -> b -> b) -> b) -> b -> b
newtype MaybeBoolFold = MaybeBoolFold { runMaybeBoolFold :: MaybeBoolFold' }

maybeBoolFold :: Maybe Bool -> MaybeBoolFold'
maybeBoolFold Nothing _ b = b
maybeBoolFold (Just p) k _ = k (\t f -> if p then t else f)

type MaybeThreeFold' a b c = forall d. d -> (a -> b -> c -> d) -> d
newtype MaybeThreeFold a b c = MaybeThreeFold
    { runMaybeThreeFold :: MaybeThreeFold' a b c
    }

unfoldr3 :: (b -> c -> MaybeThreeFold' a b c) -> b -> c -> [a]
{-# INLINE unfoldr3 #-}
unfoldr3 f b0 c0 =
    build
        (\c n -> let go b c' = f b c' n (\a new_b new_c -> a `c` go new_b new_c) in go b0 c0)

unfoldl :: (b -> MaybePairFold' a b) -> b -> [a]
{-# INLINE unfoldl #-}
unfoldl f b = build (\c nl -> fix (\r a x -> f x a (r . (`c` a))) nl b)

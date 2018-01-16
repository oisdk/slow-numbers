{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}

module Numeric.Peano.Proofs where

import           Numeric.Peano

import           Data.Type.Equality

import           Data.Promotion.Prelude

import           Unsafe.Coerce

-- | Addition is associative.
plusAssoc :: Sing (x :: Peano) -> p y -> q z -> ((x :+  y) :+ z) :~: (x :+ (y :+ z))
plusAssoc SZ _ _ = Refl
plusAssoc (SS x) y z = case plusAssoc x y z of
  Refl -> Refl
{-# NOINLINE plusAssoc #-}

-- | Zero is the identity of addition.
plusZeroNeutral :: Sing n -> n :+ Z :~: n
plusZeroNeutral SZ = Refl
plusZeroNeutral (SS n) = case plusZeroNeutral n of
  Refl -> Refl
{-# NOINLINE plusZeroNeutral #-}

-- | Successor distributes over addition.
plusSuccDistrib :: Sing n -> proxy m -> n :+ S m :~: S (n :+ m)
plusSuccDistrib SZ _     = Refl
plusSuccDistrib (SS n) p = gcastWith (plusSuccDistrib n p) Refl
{-# NOINLINE plusSuccDistrib #-}

-- | Addition is commutative.
plusComm :: Sing (n :: Peano) -> Sing (m :: Peano) -> (n :+ m) :~: (m :+ n)
plusComm SZ m = gcastWith (plusZeroNeutral m) Refl
plusComm (SS n) m =
    gcastWith (plusSuccDistrib m n) (gcastWith (plusComm n m) Refl)
{-# NOINLINE plusComm #-}

{-# RULES
"plusAssoc" plusAssoc = \_ _ _ -> unsafeCoerce (Refl :: Z :~: Z)
"plusZeroNeutral" plusZeroNeutral = \_ -> unsafeCoerce (Refl :: Z :~: Z)
"plusSuccDistrib" plusSuccDistrib = \_ _ -> unsafeCoerce (Refl :: Z :~: Z)
"plusComm" plusComm = \_ _ -> unsafeCoerce (Refl :: Z :~: Z)
 #-}

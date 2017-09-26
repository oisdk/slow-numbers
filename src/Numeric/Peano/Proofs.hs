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

-- | Successor distributes over addition
plusSuccDistrib :: Sing n -> proxy m -> n :+ S m :~: S (n :+ m)
plusSuccDistrib SZ _     = Refl
plusSuccDistrib (SS n) p = gcastWith (plusSuccDistrib n p) Refl
{-# NOINLINE plusSuccDistrib #-}

{-# RULES
"plusAssoc" forall x y z. plusAssoc x y z = unsafeCoerce (Refl :: Z :~: Z)
"plusZeroNeutral" forall x. plusZeroNeutral x = unsafeCoerce (Refl :: Z :~: Z)
"plusSuccDistrib" forall x y. plusSuccDistrib x y = unsafeCoerce (Refl :: Z :~: Z)
 #-}

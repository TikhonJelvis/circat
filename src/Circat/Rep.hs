{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-} -- experiment
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.Rep
-- Copyright   :  (c) 2014 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Convert to and from standard representations
----------------------------------------------------------------------

module Circat.Rep (Rep,HasRep(..)) where

import Data.Monoid
import Control.Applicative (WrappedMonad(..))

import Control.Monad.Trans.State (StateT(..))
import Data.Functor.Identity (Identity(..))
-- TODO: more

-- import Data.Constraint

import Circat.Misc ((:*))
import TypeUnary.TyNat (Z,S)
import TypeUnary.Nat (Nat(..),IsNat(..))
import TypeUnary.Vec (Vec(..))

type family Rep a

-- | Convert to and from standard representations. Used for transforming case
-- expression scrutinees and constructor applications. The 'repr' method should
-- convert to a standard representation (unit, products, sums), or closer to
-- such a representation, via another type with a 'HasRep' instance. The 'abst'
-- method should reveal a constructor so that we can perform the
-- case-of-known-constructor transformation.
class HasRep a where
  repr :: Rep a ~ a' => a -> a'
  abst :: Rep a ~ a' => a' -> a

-- Note types:
-- 
--   repr :: forall a. HasRep a => forall a'. Rep a ~ a' => a' -> a
--   abst :: forall a. HasRep a => forall a'. Rep a ~ a' => a -> a'
-- 
-- Note: Using Rep a ~ a' rather than the reverse to make the calls a little to
-- construct (using normaliseType and no mkSymCo).

type instance Rep (a,b,c) = ((a,b),c)
instance HasRep (a,b,c) where
  repr (a,b,c) = ((a,b),c)
  abst ((a,b),c) = (a,b,c)

type instance Rep (a,b,c,d) = ((a,b),(c,d))
instance HasRep (a,b,c,d) where
  repr (a,b,c,d) = ((a,b),(c,d))
  abst ((a,b),(c,d)) = (a,b,c,d)

#if 1
type instance Rep (Vec Z a) = ()
instance HasRep (Vec Z a) where
  repr ZVec = ()
  abst () = ZVec

#if 1

type instance Rep (Vec (S n) a) = a :* Vec n a
instance HasRep (Vec (S n) a) where
  repr (a :< as) = (a, as)
  abst (a, as) = (a :< as)
#else
-- Trickier encoding, avoiding () base case when possible.
type instance Rep (Vec (S Z) a) = a
instance HasRep (Vec (S Z) a) where
  repr (a :< ZVec) = a
  repr (_ :< _) = error "repr on Vec (S Z) a: bogus case"
  abst a = (a :< ZVec)

type instance Rep (Vec (S (S n)) a) = a :* Vec (S n) a
instance HasRep (Vec (S (S n)) a) where
  repr (a :< as) = (a, as)
  abst (a, as) = (a :< as)
#endif

#else

type instance Rep (Vec Z a) = ()
type instance Rep (Vec (S n) a) = a :* Vec n a

instance IsNat n => HasRep (Vec n a) where
   repr = case (nat :: Nat n) of
            Zero -> \ ZVec -> ()
            Succ _ -> \ (a :< as) -> (a, as)
   abst = case (nat :: Nat n) of
            Zero -> \ () -> ZVec
            Succ _ -> \ (a, as) -> (a :< as)
#endif

#define WrapRep(abstT,reprT,con) \
type instance Rep (abstT) = reprT; \
instance HasRep (abstT) where { repr (con a) = a ; abst a = con a }

WrapRep(Sum a,a,Sum)
WrapRep(Product a,a,Product)
WrapRep(All,Bool,All)
WrapRep(Any,Bool,Any)
WrapRep(Dual a,a,Dual)
WrapRep(Endo a,a->a,Endo)
WrapRep(WrappedMonad m a,m a,WrapMonad)
WrapRep(Identity a,a,Identity)
WrapRep(StateT s m a, s -> m (a,s), StateT)

-- TODO: Generate these dictionaries on the fly during compilation, so we won't
-- have to list them here.

type instance Rep (Nat Z) = ()
instance HasRep (Nat Z) where
  repr Zero = ()
  abst () = Zero

type instance Rep (Nat (S n)) = () :* Nat n
instance IsNat n => HasRep (Nat (S n)) where
  repr (Succ n) = ((),n)
  abst ((),n) = Succ n
-- The IsNat constraint comes from Succ.
-- TODO: See about eliminating that constructor constraint.

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE FlexibleInstances, EmptyCase, LambdaCase #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-} -- experiment

-- -- Experiment
-- {-# LANGUAGE MagicHash #-}

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

module Circat.Rep (HasRep(..)) where

import Data.Monoid
-- import Data.Newtypes.PrettyDouble
import Control.Applicative (WrappedMonad(..))

import Data.Functor.Identity (Identity(..))
import Data.Void (Void)
import Control.Monad.Trans.Reader (ReaderT(..))
import Control.Monad.Trans.Writer (WriterT(..))
import Control.Monad.Trans.State (StateT(..))

import GHC.Generics ((:*:)(..), (:+:)(..), Generic)
import qualified GHC.Generics as G

-- import Data.Void (Void)
-- TODO: more

import Circat.Complex

-- -- Experiment
-- import GHC.Exts (Int(..),Int#)

-- TODO: Eliminate most of the following when I drop these types.
import Circat.Misc ((:*),(:+),Parity(..))

-- import TypeUnary.TyNat (Z,S)
-- import TypeUnary.Nat (Nat(..),IsNat(..))
-- import TypeUnary.Vec (Vec(..))

-- | Convert to and from standard representations. Used for transforming case
-- expression scrutinees and constructor applications. The 'repr' method should
-- convert to a standard representation (unit, products, sums), or closer to
-- such a representation, via another type with a 'HasRep' instance. The 'abst'
-- method should reveal a constructor so that we can perform the
-- case-of-known-constructor transformation.

-- | A type family that takes the 'GHC.Generics' representation of a
-- type to its representation in base types (tuples, sums... etc).
type family ToRep (a :: * -> *) :: *

-- Ignore the metadata Generics provides.
type instance ToRep (G.M1 i c f) = ToRep f

-- Basic algebraic data types: 0, 1, +, ×.
type instance ToRep G.V1      = Void
type instance ToRep G.U1      = ()
type instance ToRep (a :+: b) = Either (ToRep a) (ToRep b)
type instance ToRep (a :*: b) = (ToRep a, ToRep b)

-- Recursive types and base types like Int/Double:
type instance ToRep (G.Rec0 a) = a

-- This class 
class GHasRep f where
  type GRep f
  gRepr :: f a -> GRep f
  gAbst :: GRep f -> f a

instance GHasRep f => GHasRep (G.M1 i c f) where
  type GRep (G.M1 i c f) = GRep f
  gRepr (G.M1 x) = gRepr x
  gAbst x = G.M1 (gAbst x)

instance GHasRep G.V1 where
  type GRep G.V1 = Void
  gRepr = undefined
  gAbst = undefined

instance GHasRep G.U1 where
  type GRep G.U1 = ()
  gRepr G.U1 = ()
  gAbst () = G.U1

instance (GHasRep a, GHasRep b) => GHasRep (a :*: b) where
  type GRep (a :*: b) = (GRep a, GRep b)
  gRepr (a :*: b) = (gRepr a, gRepr b)
  gAbst (a, b) = (gAbst a :*: gAbst b)

instance (GHasRep a, GHasRep b) => GHasRep (a :+: b) where
  type GRep (a :+: b) = Either (GRep a) (GRep b)
  gRepr (L1 a) = Left (gRepr a)
  gRepr (R1 b) = Right (gRepr b)
  gAbst (Left a)  = L1 (gAbst a)
  gAbst (Right b) = R1 (gAbst b)

instance GHasRep (G.K1 f a) where
  type GRep (G.K1 f a) = a
  gRepr (G.K1 x) = x
  gAbst x = G.K1 x

class HasRep a where
  type Rep a :: *
  type Rep a = ToRep (G.Rep a)

  repr :: a -> Rep a
  abst :: Rep a -> a

  default repr :: (Generic a, GHasRep (G.Rep a), Rep a ~ GRep (G.Rep a)) => a -> Rep a
  repr a = gRepr (G.from a)

  default abst :: (Generic a, GHasRep (G.Rep a), Rep a ~ GRep (G.Rep a)) => Rep a -> a
  abst a = G.to (gAbst a)

instance HasRep Double where
  type Rep Double = Double
  repr = id
  abst = id

-- -- Identity as @'abst' . 'repr'@.
-- abstRepr :: HasRep a => a -> a
-- abstRepr = abst . repr

#define INLINES {-# INLINE repr #-};{-# INLINE abst #-}

instance HasRep (a,b,c) where
  type Rep (a,b,c) = ((a,b),c)
  repr (a,b,c) = ((a,b),c)
  abst ((a,b),c) = (a,b,c)
  INLINES

instance HasRep (a,b,c,d) where
  type Rep (a,b,c,d) = ((a,b),(c,d))
  repr (a,b,c,d) = ((a,b),(c,d))
  abst ((a,b),(c,d)) = (a,b,c,d)
  INLINES

#if 0
-- Switching to ShapedTypes.Vec
instance HasRep (Vec Z a) where
  type Rep (Vec Z a) = ()
  repr ZVec = ()
  abst () = ZVec
  INLINES

instance HasRep (Vec (S n) a) where
  type Rep (Vec (S n) a) = (a,Vec n a)
  repr (a :< as) = (a, as)
  abst (a, as) = (a :< as)
  INLINES

instance HasRep (Nat Z) where
  type Rep (Nat Z) = ()
  repr Zero = ()
  abst () = Zero
  INLINES

instance IsNat n => HasRep (Nat (S n)) where
  type Rep (Nat (S n)) = () :* Nat n
  repr (Succ n) = ((),n)
  abst ((),n) = Succ n
  INLINES
-- The IsNat constraint comes from Succ.
-- TODO: See about eliminating that constructor constraint.
#endif

#if 1

-- I'm now synthesizing HasRep instances for newtypes.
-- Oh! I still need support for explicit uses.

#define WrapRep(abstT,reprT,con) \
instance HasRep (abstT) where { type Rep (abstT) = reprT; repr (con a) = a ; abst a = con a }

WrapRep(Sum a,a,Sum)
-- WrapRep(PrettyDouble,Double,PrettyDouble)
WrapRep(Product a,a,Product)
WrapRep(All,Bool,All)
WrapRep(Any,Bool,Any)
WrapRep(Dual a,a,Dual)
WrapRep(Endo a,a->a,Endo)
WrapRep(WrappedMonad m a,m a,WrapMonad)
WrapRep(Identity a,a,Identity)
WrapRep(ReaderT e m a, e -> m a, ReaderT)
WrapRep(WriterT w m a, m (a,w), WriterT)
WrapRep(StateT s m a, s -> m (a,s), StateT)

WrapRep(Parity,Bool,Parity)
#endif

-- TODO: Generate these dictionaries on the fly during compilation, so we won't
-- have to list them here.

-- Experimental treatment of Maybe
instance HasRep (Maybe a) where
  type Rep (Maybe a) = Bool :* a
  repr (Just a) = (True,a)
  repr Nothing  = (False,undefined)
  abst (True,a ) = Just a
  abst (False,_) = Nothing 
  INLINES

-- TODO: LambdaCCC.Prim has an BottomP primitive. If the error ever occurs,
-- replace with ErrorP (taking a string argument) and tweak the reification.

-- Generalize Maybe to sums:

-- I use this version for circuits. Restore it later, after I'm handing :+ in reify-rules.

-- instance HasRep (a :+ b) where
--   type Rep (a :+ b) = Bool :* (a :* b)
--   repr (Left  a) = (False,(a,undefined)) -- error "repr on Maybe: undefined value"
--   repr (Right b) = (True,(undefined,b))
--   abst (False,(a,_)) = Left  a
--   abst (True ,(_,b)) = Right b

-- -- TODO: Redefine `Maybe` representation as sum:
-- 
-- type instance Rep (Maybe a) = Unit :+ a
-- ...

instance HasRep (Complex a) where
  type Rep (Complex a) = a :* a
  repr (a :+ a') = (a,a')
  abst (a,a') = (a :+ a')
  INLINES

-- instance HasRep (G.V1 p) where
--   type Rep (G.V1 p) = Void
--   repr = \ case
--   abst = \ case
--   INLINES

instance HasRep (G.U1 p) where
  type Rep (G.U1 p) = ()
  repr G.U1 = ()
  abst () = G.U1
  INLINES

instance HasRep (G.Par1 p) where
  type Rep (G.Par1 p) = p
  repr = G.unPar1
  abst = G.Par1
  INLINES

instance HasRep (G.K1 i c p) where
  type Rep (G.K1 i c p) = c
  repr = G.unK1
  abst = G.K1
  INLINES

instance HasRep (G.M1 i c f p) where
  type Rep (G.M1 i c f p) = f p
  repr = G.unM1
  abst = G.M1
  INLINES

instance HasRep ((f G.:+: g) p) where
  type Rep ((f G.:+: g) p) = f p :+ g p
  repr (G.L1  x) = Left  x
  repr (G.R1  x) = Right x
  abst (Left  x) = G.L1  x
  abst (Right x) = G.R1  x
  INLINES

instance HasRep ((f G.:*: g) p) where
  type Rep ((f G.:*: g) p) = f p :* g p
  repr (x G.:*: y) = (x,y)
  abst (x,y) = (x G.:*: y)
  INLINES

instance HasRep ((G.:.:) f g p) where
  type Rep ((G.:.:) f g p) = f (g p)
  repr = G.unComp1
  abst = G.Comp1
  INLINES

-- TODO: Can I *replace* HasRep with Generic?

{--------------------------------------------------------------------
    Experiments
--------------------------------------------------------------------}

#if 0
-- Represent unboxed types as boxed counterparts.

instance HasRep Int# where
  type Rep Int# = Int
  abst (I# n) = n
  repr n = I# n
  INLINES

--     • Expecting a lifted type, but ‘Int#’ is unlifted
--     • In the first argument of ‘HasRep’, namely ‘Int#’
--       In the instance declaration for ‘HasRep Int#’
#endif

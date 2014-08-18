{-# LANGUAGE GADTs, KindSignatures, CPP #-}
{-# LANGUAGE ScopedTypeVariables, Rank2Types, InstanceSigs, ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-} -- experiment

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Circat.LTree
-- Copyright   :  (c) 2012 Tabula, Inc.
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Right-folded trees. For now, just binary.
----------------------------------------------------------------------

module Circat.LTree (Tree(..),TreeCat(..)) where

-- #define VecsAndTrees

import Prelude hiding (id,(.),uncurry,zip)

import Data.Monoid (Monoid(..),(<>))
import Data.Functor ((<$),(<$>))
import Control.Applicative (Applicative(..),liftA2)
import Control.Monad (join)
import Data.Foldable
import Data.Traversable (Traversable(..))
import Control.Arrow (arr,Kleisli)
import Data.Typeable (Typeable)

import TypeUnary.Nat hiding ((:*:))

import Circat.Misc ((<~)) -- Unop,(:*)
import Circat.Show (showsApp1)
import Circat.Category
import Circat.Classes
import Circat.Pair
import Circat.Rep
import Circat.Scan

-- TODO: Use the generalization from numbers-vectors-trees, factoring out Pair

data Tree :: * -> * -> * where
  L :: a -> Tree Z a
  B :: Tree n (Pair a) -> Tree (S n) a

deriving instance Eq a => Eq (Tree n a)
deriving instance Typeable Tree

type instance Rep (Tree Z a) = a
instance HasRep (Tree Z a) where
  repr (L a) = a
  abst a = L a

#if 1
type instance Rep (Tree (S n) a) = Tree n (Pair a)
instance HasRep (Tree (S n) a) where
  repr (B ts) = ts
  abst ts = B ts
#else
-- Two steps:
type instance Rep (Tree (S n) a) = Tree n (a :* a)
instance HasRep (Tree (S n) a) where
  repr (B ts) = repr ts
  abst ts = B (abst ts)
#endif

-- The two-step formulation makes for simpler Core.

cant :: String -> a
cant str = error $ str ++ ": GHC doesn't know this case can't happen."

cantT :: String -> a
cantT str = cant (str ++ " on Tree")

instance Ord a => Ord (Tree n a) where
  L a  `compare` L b  = a  `compare` b
  B us `compare` B vs = us `compare` vs
  _    `compare` _   = cantT "compare"

instance Show a => Show (Tree n a) where
  showsPrec p (L a)  = showsApp1 "L" p a
  showsPrec p (B ts) = showsApp1 "B" p ts

-- TODO: Remove TreeCat

class PairCat k => TreeCat k where
  toL :: a `k` Tree Z a
  unL :: Tree Z a `k` a
  toB :: Tree n (Pair a) `k` Tree (S n) a
  unB :: Tree (S n) a `k` Tree n (Pair a)

-- toB' :: (TreeCat k) => (Tree n a :* Tree n a) `k` Tree (S n) a
-- toB' = toB . toPair

-- unB' :: (TreeCat k, IsNat n) => Tree (S n) a `k` (Tree n a :* Tree n a)
-- unB' = unPair . unB

instance TreeCat (->) where
  toL a     = L a
  unL (L a) = a
  toB p     = (B p)
  unB (B p) = p

instance Monad m => TreeCat (Kleisli m) where
  toL = arr toL
  unL = arr unL
  toB = arr toB
  unB = arr unB

#if 0
instance (TerminalCat k, TreeCat k) => TreeCat (StateFun k s) where
  toL = pureState toL
  unL = pureState unL
  toB = pureState toB
  unB = pureState unB

instance (ClosedCat k, TerminalCat k, TreeCat k) => TreeCat (StateExp k s) where
  toL = pureState toL
  unL = pureState unL
  toB = pureState toB
  unB = pureState unB
#endif

inL :: TreeCat k => (a `k` b) -> (Tree Z a `k` Tree Z b)
inL = toL <~ unL

inB :: TreeCat k =>
       (Tree m (Pair a) `k` Tree n (Pair b))
    -> (Tree (S m) a `k` Tree (S n) b)
inB = toB <~ unB

inL2 :: TreeCat k => (a -> b `k` c) -> (Tree Z a -> Tree Z b `k` Tree Z c)
inL2 = inL <~ unL

inB2 :: TreeCat k =>
        (Tree m (Pair a) -> Tree n (Pair b) `k` Tree o (Pair c))
     -> (Tree (S m) a -> Tree (S n) b `k` Tree (S o) c)
inB2 = inB <~ unB

-- TODO: Maybe resurrect my category-generalized Newtype and use in place of inL
-- etc. What would become of TreeCat and VecCat?

-- instance IsNat n => Functor (Tree n) where
--   fmap = fmap' nat
--    where
--      fmap' :: Nat m -> (a -> b) -> (Tree m a -> Tree m b)
--      fmap' Zero     = inL
--      fmap' (Succ n) = inB . fmap . fmap' n
--   {-# INLINE fmap #-}

instance Functor (Tree n) where
  fmap f (L a ) = L (f a)
  fmap f (B ts) = B ((fmap.fmap) f ts)
  {-# INLINE fmap #-}

-- TODO: Categorical generalization (easy)

instance IsNat n => Applicative (Tree n) where
  pure = pure' nat
  -- (<*>)  = ap' nat
  (<*>)  = liftA2' nat ($)
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

--   (<*>)  = ap' nat
--    where
--      ap' :: Nat m -> Tree m (a -> b) -> Tree m a -> Tree m b
--      ap' Zero     = inL2 ($)
--      ap' (Succ n) = inB2 (liftA2 (ap' n))
--      {-# INLINE ap' #-}

--   L f  <*> L x  = L (f x)
--   B fs <*> B xs = B (liftA2 (<*>) fs xs)

--   (<*>)  = ap

-- ap :: Tree n (a -> b) -> Tree n a -> Tree n b
-- L f  `ap` L x  = L (f x)
-- B fs `ap` B xs = B (liftA2 ap fs xs)
-- _    `ap` _    = error "(<*>) on Tree n: impossible case"
-- {-# INLINE ap #-}

liftA2' :: Nat m -> (a -> b -> c) -> Tree m a -> Tree m b -> Tree m c
liftA2' Zero     f = inL2 f
liftA2' (Succ n) f = inB2 (liftA2' n (liftA2 f))
{-# INLINE liftA2' #-}

-- ap' :: Nat m -> Tree m (a -> b) -> Tree m a -> Tree m b
-- ap' Zero     = inL2 ($)
-- -- ap' (Succ n) = inB2 (liftA2 (ap' n))
-- ap' (Succ n) = inB2 (liftA2' n (<*>))
-- {-# INLINE ap' #-}

pure' :: Nat n -> a -> Tree n a
pure' Zero     a = L a
pure' (Succ n) a = B (pure' n (pure a))
{-# INLINE pure' #-}

-- units :: Nat n -> Tree n ()
-- units Zero     = L ()
-- units (Succ n) = B (pure (units n))
-- {-# INLINE units #-}

#if 1
instance Foldable (Tree n) where
  foldMap f (L a ) = f a
  foldMap f (B ts) = (foldMap.foldMap) f ts
  {-# INLINE foldMap #-}

instance Traversable (Tree n) where
  traverse f (L a ) = L <$> f a
  traverse f (B ts) = B <$> (traverse.traverse) f ts
  {-# INLINE traverse #-}

#if 0

instance IsNat n => Monad (Tree n) where
  return = pure
  m >>= f = joinT (fmap f m)
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}

joinT :: Tree n (Tree n a) -> Tree n a
joinT (L t)  = t
joinT (B ts) = B . fmap join . joinT . fmap sequenceA . (fmap . fmap) unB $ ts

joinT' :: Tree n (Tree n a) -> Tree n a
joinT' (L t)  = t
joinT' (B (u :# v)) = B (joinT' ((fstP . unB) <$> u) :# joinT' ((sndP . unB) <$> v))

-- Type derivation:
B ts :: Tree (S n) (Tree (S n) a)
ts :: Pair (Tree n (Tree (S n) a))
(fmap.fmap) unB ts :: Pair (Tree n (Pair (Tree n a)))
sequenceA <$> ((fmap.fmap) unB ts) :: Pair (Pair (Tree n (Tree n a)))
joinT' (sequenceA <$> ((fmap.fmap) unB ts)) :: Pair (Tree n (Tree n a))
joinT' <$> joinT' (sequenceA <$> ((fmap.fmap) unB ts)) :: Pair (Tree n a)
B (joinT' <$> joinT' (sequenceA <$> ((fmap.fmap) unB ts))) :: Tree (S n) a

#endif

#else

instance IsNat n => Foldable (Tree n) where
{-
  foldMap :: forall a o. Monoid o => (a -> o) -> Tree n a -> o
  foldMap f = foldMap' nat
   where
     foldMap' :: Nat m -> Tree m a -> o
--      foldMap' Zero     = \ (L a ) -> f a
--      foldMap' (Succ m) = \ (B ts) -> foldMap (foldMap' m) ts
     foldMap' Zero     = f . unL
     foldMap' (Succ m) = foldMap (foldMap' m) . unB
-}
  foldMap = foldMap' nat

foldMap' :: Monoid o => Nat m -> (a -> o) -> Tree m a -> o
foldMap' Zero     f = f . unL
foldMap' (Succ m) f = foldMap (foldMap' m f) . unB
{-# INLINE foldMap' #-}


instance IsNat n => Traversable (Tree n) where
  traverse :: forall a f b. Applicative f => (a -> f b) -> Tree n a -> f (Tree n b)
  traverse f = traverse' nat
   where
     traverse' :: Nat m -> Tree m a -> f (Tree m b)
--      traverse' Zero = \ (L a ) -> L <$> f a
--      traverse' (Succ m) = \ (B ts) -> B <$> traverse (traverse' m) ts
     traverse' Zero = fmap L . f . unL
     traverse' (Succ m) = fmap B . traverse (traverse' m) . unB
  {-# INLINE traverse #-}

instance IsNat n => Monad (Tree n) where
  return = pure
  m >>= f = joinT nat (fmap f m)
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}

joinT :: Nat n -> Tree n (Tree n a) -> Tree n a
-- joinT Zero = \ (L t) -> t
-- joinT (Succ m) = \ (B ts) -> B . fmap (joinT m) . join . fmap sequenceA . (fmap . fmap) unB $ ts
joinT Zero = unL
joinT (Succ m) = B . fmap (joinT m) . join . fmap sequenceA . (fmap . fmap) unB . unB

{-# INLINE joinT #-}
#endif

-- TODO: Revisit joinT. Make sure it suits Tree as trie, matching the function
-- (reader) monad. Should be derivable.

-- TODO: fmap with IsNat

{-

-- joinT (B ts) = B . joinMMT . (fmap . fmap) unB $ ts

-- TODO: Generalize this construction past (->). Rework def without sequenceA.
-- TODO: Generalize past Tree. Use pack/unpack?

-- TODO: joinT' to use inB

joinT' :: Nat n -> Tree n (Tree n a) -> Tree n a
joinT' Zero = unL
joinT' (Succ m) = B . fmap (joinT' m) . join . fmap sequenceA . unB . fmap unB

-- ts :: P (Tree m (Tree (S m) a))

-- (fmap . fmap) unB $ ts :: P (Tree m (P (Tree m a)))

-- fmap sequenceA $ '' :: P (P (Tree m (Tree m a)))
-- join $ '' :: P (Tree m (Tree m a))
-- fmap join $ '' :: P (Tree m a)
-- B $ '' :: Tree (S m) a

--   B
-- . fmap join
-- . join
-- . fmap sequenceA
-- . (fmap . fmap) unB

-}

#if 0
instance Zippable (Tree Z) where
  -- L a `zip` L b = L (a,b)
  zip = inL2 (,)

instance Zippable (Tree n) => Zippable (Tree (S n)) where
  -- B u `zip` B v = B (uncurry zip <$> (u `zip` v))
  zip = inB2 (\ u v -> uncurry zip <$> zip u v)
#else
instance IsNat n => Zippable (Tree n) where
  zip = zip' nat

zip' :: Nat n -> Tree n a -> Tree n b -> Tree n (a,b)
zip' Zero     = inL2 (,)
zip' (Succ m) = inB2 (\ u v -> uncurry zip <$> zip' m u v)
{-# INLINE zip' #-}
#endif
-- TODO: rewrite via inL2, inB2.

-- u :: Tree n (f a)
-- v :: Tree n (f b)
-- zip (u,v) :: Tree n (f a, f b) 
-- zip <$> zip (u,v) :: Tree n (f (a,b))

#if 0
instance LScan (Tree Z) where
  lscan (L a) = (L mempty, a)

instance (Zippable (Tree n), LScan (Tree n)) => LScan (Tree (S n)) where
  lscan (B ts)  = first B (lscanGF ts)
#else
instance IsNat n => LScan (Tree n) where lscan = lscan' nat

lscan' :: Monoid a => Nat n -> Tree n a -> (Tree n a, a)
lscan' Zero     = \ (L a)  -> (L mempty, a)
lscan' (Succ m) = \ (B ts) -> first B (lscanGF' (lscan' m) lscan ts)
{-# INLINE lscan' #-}
#endif

#ifdef VecsAndTrees

instance CTraversable (Tree Z) where
  type CTraversableKon (Tree Z) k = TreeCat k
  traverseC = inL

instance (IsNat n, CTraversable (Tree n)) => CTraversable (Tree (S n)) where
  type CTraversableKon (Tree (S n)) k =
    (TreeCat k, CTraversableKon (Tree n) k)
  traverseC = inB . traverseC . traverseC

#endif

{--------------------------------------------------------------------
    Addition
--------------------------------------------------------------------}

#if 0

instance (ConstCat k, AddCat k, TreeCat k, IsNat n)
      => AddsCat k (Tree n) where
  adds = addTN nat

type AddTP n = forall k. (ConstCat k, AddCat k, TreeCat k) =>
               Adds k (Tree n)

addTN :: Nat n -> AddTP n
addTN Zero     = first toL . fullAdd . second unL
addTN (Succ n) =
    first toB' . lassocP . second (addTN n)
  . inLassocP (first (addTN n)) . second unB'

-- swapP because I want to consider the left as LSB.

{- Derivation:

-- C carry, A addend pair, R result

second unB'      :: C * As (S n) `k` C * (As n * As n)
lassocP          ::              `k` (C * As n) * As n
first (addTN n)  ::              `k` (Rs n * C) * As n
rassocP          ::              `k` Rs n * (C * As n)
second (addTN n) ::              `k` Rs n * (Rs n * C)
lassocP          ::              `k` (Rs n * Rs n) * C
first toB'       ::              `k` Rs (S n) * C

-}

#endif

{--------------------------------------------------------------------
    Miscellany. May remove later, or might prove useful.
--------------------------------------------------------------------}

#if 0
tree :: (a -> b)
     -> (forall m. (IsNat m, S m ~ n) => Pair (Tree m a) -> b)
     -> (Tree n a -> b)
tree l _ (L a) = l a
tree _ b (B u) = b u

-- Fold for trees. How does it relate to the Foldable instance? We can easily
-- define fold or foldMap via foldT. What about conversely?
foldT :: forall a b n. (a -> b) -> (Pair b -> b) -> (Tree n a -> b)
foldT l b = foldT'
 where
   foldT' :: forall m. Tree m a -> b
   foldT' = tree l (b . fmap foldT')
{-# INLINE foldT #-}
#endif

#if 0
-- Fold for trees. How does it relate to the Foldable instance? We can easily
-- define fold or foldMap via foldT. What about conversely?
foldT' :: forall a b n. (a -> b) -> (Pair b -> b) -> (Tree n a -> b)
foldT' l _ (L a)  = l a
foldT' l b (B ts) = b (fmap (foldT' l b) ts)
{-# INLINE foldT' #-}

foldT :: forall a b n. (a -> b) -> (b -> b -> b) -> (Tree n a -> b)
foldT l b = foldT' l (uncurryP b)
#endif

-- TODO: Eliminate foldT in favor of plain old fold or foldMap and helpers like
-- sum and product from Data.Foldable.

#if 0
retree :: (a -> b)
       -> (forall m. (IsNat m, S m ~ n) => Pair (Tree m a) -> Pair (Tree m b))
       -> (Tree n a -> Tree n b)
retree l _ (L a) = (L . l) a
retree _ b (B u) = (B . b) u

-- I'd rather say
--   retree l b = tree (L . l) (B . b)
-- but I get
--   Couldn't match type `S m' with `Z'

-- | Reverse a tree. Transform away later
reverseT :: Unop (Tree n a)
reverseT = retree id (inPair swapP . fmap reverseT)

#endif

-- Or
-- reverseT = retree id (fmap reverseT . swapP)

fromList :: IsNat n => [a] -> Tree n a
fromList = fromList' nat

fromList' :: Nat n -> [a] -> Tree n a
fromList' Zero     [a] = L a
fromList' Zero     _   = error "fromList': length mismatch"
fromList' (Succ n) as  = B (fromList' n (consecs as))

consecs :: [a] -> [Pair a]
consecs [] = []
consecs [_] = error "Circat.LTree.consecs: odd number of elements"
consecs (a:b:as) = (a :# b) : consecs as


{--------------------------------------------------------------------
    Numeric instances via the applicative-numbers package
--------------------------------------------------------------------}

-- Generate bogus (error-producing) Enum
#define INSTANCE_Enum

#define CONSTRAINTS IsNat n, 

#define APPLICATIVE Tree n
#include "ApplicativeNumeric-inc.hs"
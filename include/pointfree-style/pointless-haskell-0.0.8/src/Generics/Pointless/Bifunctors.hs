
-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.Pointless.Bifunctors
-- Copyright   :  (c) 2009 University of Minho
-- License     :  BSD3
--
-- Maintainer  :  hpacheco@di.uminho.pt
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Pointless Haskell:
-- point-free programming with recursion patterns as hylomorphisms
-- 
-- This module defines polymorphic data types as fixed points of bifunctor.
-- Pointless Haskell works on a view of data types as fixed points of functors, in the same style as the PolyP (<http://www.cse.chalmers.se/~patrikj/poly/polyp/>) library.
-- Instead of using an explicit fixpoint operator, a type function is used to relate the data types with their equivalent functor representations.
--
-----------------------------------------------------------------------------

module Generics.Pointless.Bifunctors where

import Generics.Pointless.Combinators
import Generics.Pointless.Functors

-- * Bifunctors

newtype BId a x = BId {unBId :: x}
newtype BConst t a x = BConst {unBConst :: t}
newtype BPar a x = Par {unPar :: a}
infixr 5 :+|
data (g :+| h) a x = BInl (g a x) | BInr (h a x)
infixr 6 :*|
data (g :*| h) a x = BProd (g a x) (h a x)
infixr 9 :@|
newtype (g :@| h) a x = BComp {unBComp :: g a (h a x)}

newtype BFix f = BFix { unBFix :: f (BFix f) (BFix f) }

type family BF (f :: * -> *) :: * -> * -> *

type family BRep (f :: * -> * -> *) a :: (* -> *)

-- | Representation of bifunctors with the @Rep@ functor representation class.
type instance Rep (BId a) x = x
type instance Rep ((BConst t) a) x = t
type instance Rep (BPar a) x = a
type instance Rep ((g :+| h) a) x = Rep (g a) x `Either` Rep (h a) x
type instance Rep ((g :*| h) a) x = (Rep (g a) x,Rep (h a) x)
type instance Rep ((g :@| h) a) x = Rep (g a) (Rep (h a) x)

-- | Representation of bifunctors with the @BRep@ bifunctor representation class.
type instance BRep BId a = Id
type instance BRep (BConst t) a = Const t
type instance BRep BPar a = Const a
type instance BRep (g :+| h) a = BRep g a :+: BRep h a
type instance BRep (g :*| h) a = BRep g a  :*: BRep h a
type instance BRep (g :@| h) a = BRep g a :@: BRep h a

-- | The polytypic bifunctor zipping combinator.
-- Just maps over the polymorphic parameter. To map over the recursive parameter we can use @fzip@.







class Bifunctor (f :: * -> * -> *) where
   bmap :: Ann (BFix f) -> (a -> b) -> (x -> y) -> Rep (BRep f a) x -> Rep (BRep f b) y
   bzip :: Ann x -> Ann (BFix f) -> (a -> c) -> (Rep (BRep f a) x,Rep (BRep f c) x) -> Rep (BRep f (a,c)) x

instance Bifunctor BId where
   bmap _ p f = f
   bzip x _ create = fst
instance Bifunctor (BConst t) where
   bmap _ p f = id
   bzip x _ create = fst
instance Bifunctor BPar where
   bmap _ p f = p
   bzip x _ create = id
instance (Bifunctor g,Bifunctor h) => Bifunctor (g :+| h) where
   bmap _ p f (Left x) = Left (bmap (ann :: Ann (BFix g)) p f x)
   bmap _ p f (Right x) = Right (bmap (ann :: Ann (BFix h)) p f x)
   bzip (x::Ann x) _ create = (l -|- r) . dists
       where l = bzip x g create \/ bmap g (id /\ create) idx . fst
             r = bmap h (id /\ create) idx . fst \/ bzip x h create
             idx = id :: x -> x
             g = ann::Ann (BFix g)
             h = ann::Ann (BFix h)
instance (Bifunctor g,Bifunctor h) => Bifunctor (g :*| h) where
   bmap _ p f (x,y) = (bmap (ann :: Ann (BFix g)) p f x,bmap (ann ::Ann (BFix h)) p f y)
   bzip x _ create = (bzip x (ann::Ann (BFix g)) create >< bzip x (ann::Ann (BFix h)) create) . distp
instance (Bifunctor g,Bifunctor h) => Bifunctor (g :@| h) where
   bmap _ p f x = bmap (ann :: Ann (BFix g)) p (bmap (ann :: Ann (BFix h)) p f) x
   bzip = fail "not defined"

type B d a x = Rep (BRep (BF d) a) x

class Bimu d where
    binn :: B d a (d a) -> d a
    bout :: d a -> B d a (d a)

pbmap :: Bifunctor (BF d) => Ann (d a) -> (a -> b) -> (x -> y) -> B d a x -> B d b y
pbmap (_::Ann (d a)) p f = bmap (ann :: Ann (BFix (BF d))) p f

-- * Fixpoint combinators

data BI x = FixBId

type instance BF BI = BId

instance Bimu BI where
   binn = id
   bout = id

data BK a x = FixBConst {unFixBConst :: a}

type instance BF (BK a) = BConst a

instance Bimu (BK a) where
   binn = FixBConst
   bout = unFixBConst

infixr 5 :+!|
data ((a :: * -> *) :+!| (b :: * -> *)) x = FixBSum {unFixBSum :: B (a :+!| b) x ((a :+!| b) x)}

type instance BF (a :+!| b) = BF a :+| BF b

instance Bimu (a :+!| b) where
   binn = FixBSum
   bout = unFixBSum

infixr 6 :*!|
data ((a :: * -> *) :*!| (b :: * -> *)) x = FixBProd {unFixBProd :: B (a :*!| b) x ((a :*!| b) x)}

type instance BF (a :*!| b) = BF a :*| BF b

instance Bimu (a :*!| b) where
   binn = FixBProd
   bout = unFixBProd

infixr 9 :@!|
data ((a :: * -> *) :@!| (b :: * -> *)) x = FixBComp {unFixBComp :: B (a :@!| b) x ((a :@!| b) x)}

type instance BF (a :@!| b) = BF a :@| BF b

instance Bimu (a :@!| b) where
   binn = FixBComp
   bout = unFixBComp

-- * Default definitions for commonly used data types

--instance (Bimu d, Rep (PF (d a)) (d a) ~ BRep (BF d) a (d a)) => Mu (d a) where
--    inn = binn
--    out = bout

-- ** Lists

type instance BF [] = BConst One :+| BPar :*| BId

instance Bimu [] where
    binn (Left _) = []
    binn (Right (x,xs)) = x:xs
    bout [] = Left _L
    bout (x:xs) = Right (x,xs)

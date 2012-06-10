-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.Pointless.HFunctors
-- Copyright   :  (c) 2011 University of Minho
-- License     :  BSD3
--
-- Maintainer  :  hpacheco@di.uminho.pt
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Pointless Haskell:
-- point-free programming with recursion patterns as hylomorphisms
-- 
-- This module defines polymorphic data types as fixed points of higher-order functor.
--
-----------------------------------------------------------------------------

module Generics.Pointless.HFunctors where

import Generics.Pointless.Combinators
import Generics.Pointless.Functors

import Prelude hiding (Functor(..))
import Data.Monoid

-- | The type of natural transformations
infixr 8 :~>
type s :~> v = forall a. s a -> v a

-- * Higher-order functors

-- | Identity higher-order functor
newtype Functor f => HId (f :: * -> *) a = IdH {unIdH :: f a}

-- | Constant higher-order functor
newtype HConst c (f :: * -> *) a = ConsH {unConsH :: c}

-- | Parameter higher-order functor
newtype HParam (f :: * -> *) a = HPar {unParH :: a}

newtype Functor g => HFun (g :: * -> *) (f :: * -> *) a = HFun {unFunH :: g a}

-- | Sum higher-order functor
infixr 5 :+~:
data ((g :: (* -> *) -> (* -> *)) :+~: (h :: (* -> *) -> (* -> *))) (f :: * -> *) a = InlH (g f a) | InrH (h f a)

-- | Product higher-order functor
infixr 6 :*~:
data ((g :: (* -> *) -> (* -> *)) :*~: (h :: (* -> *) -> (* -> *))) (f :: * -> *) a = ProdH (g f a) (h f a)

-- | Composition of a regular functor with an higher-order functor
infixr 9 :@~:
data ((g :: * -> *) :@~: (h :: (* -> *) -> (* -> *))) (f :: * -> *) a = CompH {unCompH :: g (h f a)}

-- | The fixpoint of an higher-order functor is a regular functor
newtype HFix (f :: (* -> *) -> (* -> *)) a = HInn { hOut :: (HRep f (HFix f)) a }

-- | Annotations of higher-order functors, only to provide type-level information to the compiler
data AnnH (f :: (* -> *) -> (* -> *))

-- * Application of higher-order functors to a regular functor
type family HRep (g :: (* -> *) -> (* -> *)) (f :: * -> *) :: * -> *

type instance HRep HId f = f
type instance HRep (HConst c) f = Const c
type instance HRep HParam f = Id
type instance HRep (HFun g) f = g
type instance HRep (g :+~: h) f = HRep g f :+: HRep h f
type instance HRep (g :*~: h) f = HRep g f :*: HRep h f
type instance HRep (g :@~: h) f = g :@: HRep h f

-- * Functor composition as the fixpoint of an higher-order functor (using the fixpoint of the first functor)

type family App (f :: (* -> *) -> (* -> *)) (g :: * -> *) :: (* -> *) -> (* -> *)
type instance App HId g = HId
type instance App (HConst t) g = HConst t
type instance App HParam g = HFun g
type instance App (HFun h) g = HFun (h :@: g)
type instance App (f :*~: g) h = App f h :*~: App g h
type instance App (f :+~: g) h = App f h :+~: App g h
type instance App (f :@~: g) h = f :@~: (App g h)

type instance HF (f :@: g) = App (HF f) g

-- * User-defined polymorphic types as fixed points of higher-order functors

type family HF (t :: * -> *) :: (* -> *) -> (* -> *)
type H t a = HRep (HF t) a

class Hu (t :: * -> *) where
    hinn :: (H t t) a -> t a
    hout :: t a -> (H t t) a

type instance HF [] = HConst One :+~: HParam :*~: HId
instance Hu [] where
    hout [] = InlF $ ConsF _L
    hout (x:xs) = InrF $ ProdF (IdF x) xs
    hinn (InlF (ConsF _)) = []
    hinn (InrF (ProdF (IdF x) xs)) = x:xs

type instance HF (HFix f) = f
instance Hu (HFix f) where
    hinn = HInn
    hout = hOut

-- * Foldable higher-order functors

-- | Polymorphic monoid class
class FMonoid f where
    fzero :: f a
    fplus :: f a -> f a -> f a

instance (FMonoid f,FMonoid g) => FMonoid (f :*: g) where
    fzero = ProdF fzero fzero
    fplus (ProdF x1 x2) (ProdF y1 y2) = ProdF (fplus x1 y1) (fplus x2 y2)

instance FMonoid f => FMonoid (f :@: g) where
    fzero = CompF fzero
    fplus (CompF x) (CompF y) = CompF (fplus x y)

instance FMonoid [] where
    fzero = mempty
    fplus = mappend

class HFoldable f where
    reduce :: FMonoid g => AnnH f -> (HRep f g) :~> g
    reduce' :: FMonoid g => AnnH f -> Ann (Fix g) -> (HRep f g) :~> g
    reduce' annf anns = reduce annf

instance HFoldable HId where
    reduce _ ga = ga
instance HFoldable (HConst a) where
    reduce _ x = fzero
instance HFoldable HParam where
    reduce _ x = fzero
instance HFoldable (HFun g) where
    reduce _ x = fzero
instance (HFoldable f,HFoldable g) => HFoldable (f :+~: g) where
    reduce (_::AnnH (f :+~: g)) (InlF x) = reduce (ann::AnnH f) x
    reduce (_::AnnH (f :+~: g)) (InrF y) = reduce (ann::AnnH g) y
instance (HFoldable f,HFoldable g) => HFoldable (f :*~: g) where
    reduce (_::AnnH (f :*~: g)) (ProdF x y) = reduce (ann::AnnH f) x `fplus` reduce (ann::AnnH g) y
    

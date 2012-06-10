-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.Pointless.Bifctrable
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
-- This module defines a class of representable bifunctors.
--
-----------------------------------------------------------------------------

module Generics.Pointless.Bifctrable where

import Prelude hiding (Functor(..),fmap)
import Generics.Pointless.Bifunctors
import Generics.Pointless.Combinators

-- | Functor GADT for polytypic recursive bifunctions.
-- At the moment it does not rely on a @Typeable@ instance for constants.
data Bifctr (f :: * -> * -> *) where
    BI :: Bifctr BId
    BK :: Bifctr (BConst c)
    BP :: Bifctr BPar
    (:*!|) :: (Bifunctor f,Bifunctor g) => Bifctr f -> Bifctr g -> Bifctr (f :*| g)
    (:+!|) :: (Bifunctor f,Bifunctor g) => Bifctr f -> Bifctr g -> Bifctr (f :+| g)
    (:@!|) :: (Bifunctor f,Bifunctor g) => Bifctr f -> Bifctr g -> Bifctr (f :@| g)

-- | Class of representable bifunctors.
class (Bifunctor f) => Bifctrable (f :: * -> * -> *) where
    bctr :: Bifctr f
instance Bifctrable BId where
    bctr = BI
instance Bifctrable (BConst c) where
    bctr = BK
instance Bifctrable BPar where
    bctr = BP
instance (Bifunctor f,Bifctrable f,Bifunctor g,Bifctrable g) => Bifctrable (f :*| g) where
    bctr = (:*!|) bctr bctr
instance (Bifunctor f,Bifctrable f,Bifunctor g,Bifctrable g) => Bifctrable (f :+| g) where
    bctr = (:+!|) bctr bctr

-- | The fixpoint of a representable bifunctor.
fixB :: Bifctr f -> BFix f
fixB (_::Bifctr f) = (_L :: BFix f)

-- | The representation of the fixpoint of a representable functor.
fctrB :: Bifctrable f => BFix f -> Bifctr f
fctrB (_::BFix f) = bctr :: Bifctr f

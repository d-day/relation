-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.Pointless.Fctrable
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
-- This module defines a class of representable functors.
--
-----------------------------------------------------------------------------

module Generics.Pointless.Fctrable where

import Prelude hiding (Functor(..),fmap)

import Generics.Pointless.Functors
import Generics.Pointless.Combinators

-- | Functor GADT for polytypic recursive functions.
-- At the moment it does not rely on a @Typeable@ instance for constants.
data Fctr (f :: * -> *) where
    I :: Fctr Id
    K :: Fctr (Const c)
    L :: Fctr []
    (:*!:) :: (Functor f,Functor g) => Fctr f -> Fctr g -> Fctr (f :*: g)
    (:+!:) :: (Functor f,Functor g) => Fctr f -> Fctr g -> Fctr (f :+: g)
    (:@!:) :: (Functor f,Functor g) => Fctr f -> Fctr g -> Fctr (f :@: g)

-- | Class of representable functors.
class (Functor f) => Fctrable (f :: * -> *) where
    fctr :: Fctr f
instance Fctrable Id where
    fctr = I
instance Fctrable (Const c) where
    fctr = K
instance Fctrable [] where
    fctr = L
instance (Functor f,Fctrable f,Functor g,Fctrable g) => Fctrable (f :*: g) where
    fctr = (:*!:) fctr fctr
instance (Functor f,Fctrable f,Functor g,Fctrable g) => Fctrable (f :+: g) where
    fctr = (:+!:) fctr fctr
instance (Functor f,Fctrable f,Functor g,Fctrable g) => Fctrable (f :@: g) where
    fctr = (:@!:) fctr fctr

-- | The fixpoint of a representable functor.
fixF :: Fctr f -> Fix f
fixF (_::Fctr f) = (_L :: Fix f)

-- | The representation of the fixpoint of a representable functor.
fctrF :: Fctrable f => Fix f -> Fctr f
fctrF (_::Fix f) = fctr :: Fctr f

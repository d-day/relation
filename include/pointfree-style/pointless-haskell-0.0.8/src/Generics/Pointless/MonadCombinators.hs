-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.Pointless.MonadCombinators
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
-- This module lifts many standard combinators used for point-free programming to combinators over monads.
--
-----------------------------------------------------------------------------

module Generics.Pointless.MonadCombinators where

import Generics.Pointless.Combinators
import Control.Monad

-- | The left-to-right monadic binding combinator.
infixl 1 <<=
(<<=) :: Monad m => (a -> m b) -> m a -> m b
(<<=) f m = m >>= f

-- | Higher-order monadic binding.
bind :: Monad m => (a -> m b,m a) -> m b
bind (f,m) = f <<= m

-- | The monadic left exponentiation combinator.
mlexp :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
mlexp f = curry (bind . (id >< f))

-- | The monadic right exponentiation combinator.
mrexp :: Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
mrexp f = curry ((f <<=) .  app)

-- | The monadic sum combinator.
infix 5 -||-
(-||-) :: Monad m => (a -> m b) -> (c -> m d) -> (Either a c -> m (Either b d))
(-||-) f g = (return . inl <=< f) \/ (return . inr <=< g)

-- | The strength combinator for strong monads.
-- In Haskell, every monad is a strong monad: <http://comonad.com/reader/2008/deriving-strength-from-laziness/>.
mstrength :: Monad m => (b,m a) -> m (b,a)
mstrength = uncurry (<<=) . (comp . (const return /\ dist) >< id)
    where dist = curry id

-- | The monadic fusion combinator.
-- Performs left-to-right distribution of a strong monad over a product.
mfuse :: Monad m => (m a,m b) -> m (a,b)
mfuse = uncurry (<<=) . (curry (mstrength . swap) >< id) . swap

-- | The monadic split combinator.
infix 6  /|\
(/|\) :: Monad m => (a -> m b) -> (a -> m c) -> a -> m (b,c)
(/|\) f g = mfuse . (f /\ g)

-- | The monadic product combinator.
infix 7  >|<
(>|<) :: Monad m => (a -> m c) -> (b -> m d) -> (a,b) -> m (c,d)
f >|< g = f . fst /|\ g . snd

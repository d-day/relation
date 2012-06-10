
-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.Pointless.Observe.RecursionPatterns
-- Copyright   :  (c) 2008 University of Minho
-- License     :  BSD3
--
-- Maintainer  :  hpacheco@di.uminho.pt
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Pointless Haskell:
-- point-free programming with recursion patterns as hylomorphisms
-- 
-- This module redefines recursion patterns with support for GHood observation of intermediate data structures.
--
-----------------------------------------------------------------------------

module Generics.Pointless.Observe.RecursionPatterns where

import Generics.Pointless.Combinators
import Generics.Pointless.Functors
import Generics.Pointless.RecursionPatterns
import Debug.Observe
import Generics.Pointless.Observe.Functors
import Prelude hiding (Functor (..))
import Data.Typeable

-- * Recursion patterns with observation of intermediate data structures

-- | Redefinition of hylomorphisms with observation of the intermediate data type.
hyloO :: (Mu b, Functor (PF b), FunctorO (PF b)) => Ann b -> (F b c -> c) -> (a -> F b a) -> a -> c
hyloO (b::Ann b) g h = cata f g . observe ("Recursion Tree Functor: " ++ functorOf f) . ana f h
   where f = ann :: Ann (Fix (PF b))

-- | Redefinition of catamorphisms as observable hylomorphisms.
cataO :: (Mu a, Functor (PF a), FunctorO (PF a)) => Ann a -> (F a b -> b) -> a -> b
cataO a f = hyloO a f out

-- | Redefinition of anamorphisms as observable hylomorphisms.
anaO :: (Mu b,Functor (PF b), FunctorO (PF b)) => Ann b -> (a -> F b a) -> a -> b
anaO b = hyloO b inn

-- | Redefinition of paramorphisms as observable hylomorphisms.
paraO :: (Mu a,Functor (PF a), FunctorO (PF a), Observable a, Typeable a) => Ann a -> (F a (b,a) -> b) -> a -> b
paraO (a::Ann a) f = hyloO (ann :: Ann (Para a)) f (pmap a (idA /\ idA) . out)
   where idA :: a -> a
         idA = id

-- | Redefinition of apomorphisms as observable hylomorphisms.
apoO :: (Mu b,Functor (PF b), FunctorO (PF b), Observable b, Typeable b) => Ann b -> (a -> F b (Either a b)) -> a -> b
apoO (b::Ann b) f = hyloO (ann :: Ann (Apo b)) (inn . pmap b (idB \/ idB)) f
   where idB :: b -> b
         idB = id

-- | Redefinition of zygomorphisms as observable hylomorphisms.
zygoO :: (Mu a, Functor (PF a), FunctorO (PF a), Observable b, Typeable b, F a (a,b) ~ F (Zygo a b) a) => Ann a -> (F a b -> b) -> (F (Zygo a b) b -> b) -> a -> b
zygoO a g f = aux a (ann :: Ann b) g f
   where aux :: (Mu a,Functor (PF a), FunctorO (PF a),Observable b, Typeable b, F a (a,b) ~ F (Zygo a b) a) => Ann a -> Ann b -> (F a b -> b) -> (F (Zygo a b) b -> b) -> a -> b
         aux (a::Ann a) (b::Ann b) g f = hyloO (ann :: Ann (Zygo a b)) f (pmap a (id /\ cata a g) . out)

-- | Redefinition of accumulations as observable hylomorphisms.
accumO :: (Mu a,Functor (PF d), FunctorO (PF d), Observable b, Typeable b) => Ann d -> ((F a a,b) -> F d (a,b)) -> (F (Accum d b) c -> c) -> (a,b) -> c
accumO (d::Ann d) g f = hyloO (ann :: Ann (Accum d b)) f ((g /\ snd) . (out >< id))

-- | Redefinition of histomorphisms as observable hylomorphisms.
histoO :: (Mu a,Functor (PF a), FunctorO (PF a), Observable a) => Ann a -> (F a (Histo a c) -> c) -> a -> c
histoO (a::Ann a) g = fst . outH . cataO a (inn . (g /\ id))
   where outH :: Histo a c -> F (Histo a c) (Histo a c)
         outH = out

-- | Redefinition of futumorphisms as observable hylomorphisms.
futuO :: (Mu b,Functor (PF b), FunctorO (PF b), Observable b) => Ann b -> (a -> F b (Futu b a)) -> a -> b
futuO (b::Ann b) g = anaO b ((g \/ id) . out) . innF . inl
   where innF :: F (Futu b a) (Futu b a) -> Futu b a
         innF = inn

-- | Redefinition of dynamorphisms as observable hylomorphisms.
dynaO :: (Mu b, Functor (PF b), FunctorO (PF b), Observable b) => Ann b -> (F b (Histo b c) -> c) -> (a -> F b a) -> a -> c
dynaO (b::Ann b) g h = fst . outH . hyloO b (inn . (g /\ id)) h
   where outH :: Histo b c -> F (Histo b c) (Histo b c)
         outH = out

-- | Redefinition of chronomorphisms as observable hylomorphisms.
chronoO :: (Mu c,Functor (PF c), FunctorO (PF c)) => Ann c -> (F c (Histo c b) -> b) -> (a -> F c (Futu c a)) -> a -> b
chronoO (c::Ann c) g h = fst . outH . hyloO c (inn . (g /\ id)) ((h \/ id) . out) . innF . inl
   where outH :: Histo c b -> F (Histo c b) (Histo c b)
         outH = out
         innF :: F (Futu c a) (Futu c a) -> (Futu c a)
         innF = inn


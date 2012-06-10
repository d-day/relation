
-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.Pointless.Examples.Observe
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
-- This module provides the same examples, but with support for GHood observations.
--
-----------------------------------------------------------------------------

module Generics.Pointless.Examples.Observe where

import Generics.Pointless.Combinators
import Generics.Pointless.Functors
import Generics.Pointless.RecursionPatterns
import Generics.Pointless.Observe.RecursionPatterns
import Generics.Pointless.Observe.Functors
import Generics.Pointless.Examples.Examples
import Debug.Observe
import Data.Typeable

-- | Definition of the observable length function as an hylomorphism.
lengthHyloO :: Observable a => [a] -> Int
lengthHyloO = hyloO (ann::Ann Int) f g
   where f = inn
         g = (id -|- snd) . out

-- | Definition of the observable length function as an anamorphism.
lengthAnaO :: Observable a => [a] -> Int
lengthAnaO = anaO (ann::Ann Int) f
   where f = (id -|- snd) . out

-- | Definition of the observable length function as a catamorphism.
lengthCataO :: (Typeable a, Observable a) => [a] -> Int
lengthCataO = cataO (ann ::Ann [a]) g
   where g = inn . (id -|- snd)

-- | Definition of the observable factorial function as an hylomorphism.
factHyloO :: Int -> Int
factHyloO = hyloO (ann::Ann [Int]) f g
    where g = (id -|- succ /\ id) . out
          f = one \/ prod

-- | Definition of the observable factorial function as a paramorphism.
factParaO :: Int -> Int
factParaO = paraO (ann::Ann Int) f
    where f = one \/ prod . (id >< succ)

-- | Definition of the observable factorial function as a zygomorphism.
factZygoO :: Int -> Int
factZygoO = zygoO (ann::Ann Int) inn f
   where f = one \/ (prod . (id >< succ))

-- | Definition of the observable fibonacci function as an hylomorphism.
fibHyloO :: Int -> Int
fibHyloO = hyloO (ann::Ann (LTree One)) f g
    where g = (bang -|- pred /\ pred . pred) . ((<=1)?)
	  f = one \/ add
	
-- | Definition of the observable fibonacci function as an histomorphism.
fibHistoO :: Int -> Int
fibHistoO = histoO (ann::Ann Int) f
   where f = (zero \/ (one . snd \/ add . (id >< outl)) . distr . out)

-- | Definition of the observable fibonacci function as a dynamorphism.
fibDynaO :: Int -> Int
fibDynaO = dynaO (ann::Ann Int) f g
   where f = (zero \/ (one . snd \/ add . (id >< outl)) . distr . out)
         g = out

-- | Definition of the observable quicksort function as an hylomorphism.
qsortHyloO :: (Typeable a, Observable a, Ord a) => [a] -> [a]
qsortHyloO = hyloO (ann::Ann (Tree a)) f g
    where g = (id -|- fst /\ partition) . out
	  f = nil \/ cat . (id >< cons) . assocr . (swap >< id) . assocl

-- | Definition of the observable tail function as a paramorphism.
tailParaO :: (Typeable a, Observable a) => [a] -> [a]
tailParaO = paraO (ann::Ann [a]) (nil \/ snd . snd)

-- | Definition of the observable add function as an accumulation.
addAccumO :: (Int,Int) -> Int
addAccumO = accumO (ann::Ann Int) t f
    where t = (fst -|- id >< succ) . distl
	  f = (snd \/ fst) . distl



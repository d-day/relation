
-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.Pointless.Observe.Functors
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
-- This module defines generic GHood observations for user-defined data types.
--
-----------------------------------------------------------------------------

module Generics.Pointless.Observe.Functors where

import Generics.Pointless.Combinators
import Generics.Pointless.Functors
import Debug.Observe
import qualified Data.Generics as G
import Prelude hiding (Functor(..))
import Control.Monad hiding (Functor(..))

-- * Definition of generic observations

-- | Class for mapping observations over functor representations.
class FunctorO f where
   -- | Derives a type representation for a functor. This is used for showing the functor for reursion trees.
   functorOf :: Ann (Fix f) -> String
   -- | Watch values of a functor. Since the fixpoint of a functor recurses over himself, we cannot use the 'Show' instance for functor values applied to their fixpoint.
   watch :: Ann (Fix f) -> Ann x -> Rep f x -> String
   -- | Maps an observation over a functor representation.
   fmapO :: Ann (Fix f) -> (x -> ObserverM y) -> Rep f x -> ObserverM (Rep f y)

instance FunctorO Id where
   functorOf _ = "Id"
   watch _ _ _ = ""
   fmapO _ f = f

instance (G.Typeable a,Observable a) => FunctorO (Const a) where
   functorOf _ = "Const " ++ show (G.typeOf (_L::a))
   watch _ _ _ = ""
   fmapO _ f = thunk


instance (FunctorO f, FunctorO g) => FunctorO (f :+: g) where
   functorOf (_::Ann (Fix (f:+:g))) = "(" ++ functorOf (ann::Ann (Fix f)) ++ ":+:" ++ functorOf (ann::Ann (Fix g)) ++ ")"
   watch (_::Ann (Fix (f:+:g))) _ (Left _) = "Left"
   watch (_::Ann (Fix (f:+:g))) _ (Right _) = "Right"
   fmapO (_::Ann (Fix (f:+:g))) f (Left x) = liftM Left (fmapO (ann::Ann (Fix f)) f x)
   fmapO (_::Ann (Fix (f:+:g))) f (Right x) = liftM Right (fmapO (ann::Ann (Fix g)) f x)

instance (FunctorO f, FunctorO g) => FunctorO (f :*: g) where
   functorOf (_::Ann (Fix (f:*:g))) = "(" ++ functorOf (ann::Ann (Fix f)) ++ ":*:" ++ functorOf (ann::Ann (Fix g)) ++ ")"
   watch _ _ _ = ""
   fmapO (_::Ann (Fix (f:*:g))) f (x,y) = do
       x' <- fmapO (ann::Ann (Fix f)) f x
       y' <- fmapO (ann::Ann (Fix g)) f y
       return (x',y')

instance (FunctorO g, FunctorO h) => FunctorO (g :@: h) where
   functorOf (_::Ann (Fix (g:@:h))) = "(" ++ functorOf (ann::Ann (Fix g)) ++ ":@:" ++ functorOf (ann::Ann (Fix h)) ++ ")"
   watch (_::Ann (Fix (g:@:h))) (x::Ann x) = watch (ann::Ann (Fix g)) (ann::Ann (Rep h x))
   fmapO (_::Ann (Fix (g:@:h))) = fmapO (ann::Ann (Fix g)) . fmapO (ann::Ann (Fix h))

-- | Polytypic mapping of observations.
omap :: FunctorO (PF a) => Ann a -> (x -> ObserverM y) -> F a x -> ObserverM (F a y)
omap (_::Ann a) = fmapO (ann::Ann (Fix (PF a)))

instance Observable One where
   observer = observeBase

instance Observable I where
   observer FixId = send "" (fmapO (ann :: Ann (Fix Id)) thunk FixId)

instance (G.Typeable a,Observable a) => Observable (K a) where
   observer (FixConst a) = send "" (liftM FixConst (fmapO (ann::Ann (Fix (Const a))) thk a))
      where thk = thunk :: a -> ObserverM a

instance (FunctorO (PF a),FunctorO (PF b)) => Observable (a :+!: b) where
   observer (FixSum f) = send "" (liftM FixSum (fmapO (ann::Ann (Fix (PF a :+: PF b))) thk f))
      where thk = thunk :: a :+!: b -> ObserverM (a :+!: b)

instance (FunctorO (PF a), FunctorO (PF b)) => Observable (a :*!: b) where
   observer (FixProd f) = send "" (liftM FixProd (fmapO (ann::Ann (Fix (PF a :*: PF b))) thk f))
      where thk = thunk :: a :*!: b -> ObserverM (a :*!: b)

instance (FunctorO (PF a), FunctorO (PF b)) => Observable (a :@!: b) where
   observer (FixComp f) = send "" (liftM FixComp (fmapO (ann::Ann (Fix (PF a :@: PF b))) thk f))
      where thk = thunk :: a :@!: b -> ObserverM (a :@!: b)

-- NOTE: The following commented instance causes overlapping problems with the specific ones defined for base types (One,Int,etc.).
-- The solution is to provide its specific case for each type when needed, or to uncomment the following code
-- and using the flag -XIncoherentInstances.

--instance (Mu a,FunctorO (PF a)) => Observable a where
--   observer x = send "" (omap (_L :: a) thk (out x) >>= return . inn)
--      where thk = thunk :: a -> ObserverM a

instance (Functor f, FunctorO f) => Observable (Fix f) where

   observer (Inn x) = send (watch f f x) (liftM Inn (fmapO f thk x))
      where thk = thunk :: Fix f -> ObserverM (Fix f)
            f = ann::Ann (Fix f)




-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.Pointless.RecursionPatterns
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
-- This module defines recursion patterns as hylomorphisms.
--
-- Recursion patterns can be seen as high-order functions that encapsulate typical forms of recursion.
-- The hylomorphism recursion pattern was first defined in <http://research.microsoft.com/~emeijer/Papers/CWIReport.pdf>,
-- along with its relation with derived more specific recursion patterns such as catamorphisms, anamorphisms and paramorphisms.
--
-- The seminal paper that introduced point-free programming and defined many of the laws for catamorphisms and anamorphisms
-- can be found in <http://eprints.eemcs.utwente.nl/7281/01/db-utwente-40501F46.pdf>.
--
-- More complex and exotic recursion patterns have been discovered later, such as accumulations, apomorphisms, zygomorphisms,
-- histomorphisms, futumorphisms, dynamorphisms or chronomorphisms.
--
-----------------------------------------------------------------------------

module Generics.Pointless.RecursionPatterns where

import Generics.Pointless.Combinators
import Generics.Pointless.Functors
import Control.Monad.Instances hiding (Functor(..))
import Prelude hiding (Functor(..))

-- | Definition of an hylomorphism
hylo :: Functor (PF b) => Ann b -> (F b c -> c) -> (a -> F b a) -> a -> c
hylo b g h = g . pmap b (hylo b g h) . h

-- | Definition of a catamorphism as an hylomorphism.
--
-- Catamorphisms model the fundamental pattern of iteration, where constructors for recursive datatypes are repeatedly consumed by arbitrary functions.
-- They are usually called folds.
cata :: (Mu a,Functor (PF a)) => Ann a -> (F a b -> b) -> a -> b
cata a f = hylo a f out

-- | Recursive definition of a catamorphism.
cataRec :: (Mu a,Functor (PF a)) => Ann a -> (F a b -> b) -> a -> b
cataRec a f = f . pmap a (cataRec a f) . out

-- | Definition of an anamorphism as an hylomorphism.
--
--  Anamorphisms resembles the dual of iteration and, hence, deﬁne the inverse of catamorphisms.
-- Instead of consuming recursive types, they produce values of those types.
ana :: (Mu b,Functor (PF b)) => Ann b -> (a -> F b a) -> a -> b
ana b = hylo b inn

-- | Recursive definition of an anamorphism.
anaRec :: (Mu b,Functor (PF b)) => Ann b -> (a -> F b a) -> a -> b
anaRec b f = inn . pmap b (anaRec b f) . f

-- | The functor of the intermediate type of a paramorphism is the functor of the consumed type 'a'
-- extended with an extra annotation to itself in recursive definitions.
type Para a = a :@!: (I :*!: K a)

-- | Definition of a paramorphism.
--
-- Paramorphisms supply the gene of a catamorphism with a recursively computed copy of the input.
--
-- The first introduction to paramorphisms is reported in <http://www.cs.uu.nl/research/techreps/repo/CS-1990/1990-04.pdf>.
para :: (Mu a,Functor (PF a)) => Ann a -> (F a (b,a) -> b) -> a -> b
para (a::Ann a) f = hylo (ann :: Ann (Para a)) f (pmap a (idA /\ idA) . out)
   where idA :: a -> a
         idA = id

-- | Recursive definition of a paramorphism.
paraRec :: (Mu a,Functor (PF a)) => Ann a -> (F a (b,a) -> b) -> a -> b
paraRec (a::Ann a) f = f . pmap a (paraRec a f >< idA) . pmap a (idA /\ idA) . out
   where idA :: a -> a
         idA = id

-- | The functor of the intermediate type of an apomorphism is the functor of the generated type 'b'
-- with an alternative annotation to itself in recursive definitions.
type Apo b = b :@!: (I :+!: K b)

-- | Definition of an apomorphism as an hylomorphism.
--
-- Apomorphisms are the dual recursion patterns of paramorphisms, and therefore they can express functions defined by primitive corecursion.
--
-- They were introduced independently in <http://www.cs.ut.ee/~varmo/papers/nwpt97.ps.gz> and /Program Construction and Generation Based on Recursive Types, MSc thesis/.
apo :: (Mu b,Functor (PF b)) => Ann b -> (a -> F b (Either a b)) -> a -> b
apo (b::Ann b) f = hylo (ann :: Ann (Apo b)) (inn . pmap b (idB \/ idB)) f
   where idB :: b -> b
         idB = id

-- | Recursive definition of an apomorphism.
apoRec :: (Mu b,Functor (PF b)) => Ann b -> (a -> F b (Either a b)) -> a -> b
apoRec (b::Ann b) f = inn . pmap b (idB \/ idB) . pmap b (apoRec b f -|- idB) . f
   where idB :: b -> b
         idB = id

-- | In zygomorphisms we extend the recursive occurences in the base functor functor of type 'a' with an extra annotation 'b'.
type Zygo a b = a :@!: (I :*!: K b)

-- | Definition of a zygomorphism as an hylomorphism.
--
-- Zygomorphisms were introduced in <http://dissertations.ub.rug.nl/faculties/science/1990/g.r.malcolm/>.
--
-- They can be seen as the asymmetric form of mutual iteration, where both a data consumer and an auxiliary function are defined (<http://www.fing.edu.uy/~pardo/papers/njc01.ps.gz>).
zygo :: (Mu a, Functor (PF a),F a (a,b) ~ F (Zygo a b) a) => Ann a -> (F a b -> b) -> (F (Zygo a b) b -> b) -> a -> b
zygo a g f = aux a (ann :: Ann b) g f
   where aux :: (Mu a,Functor (PF a),F a (a,b) ~ F (Zygo a b) a) => Ann a -> Ann b -> (F a b -> b) -> (F (Zygo a b) b -> b) -> a -> b
         aux (a::Ann a) (b::Ann b) g f = hylo (ann :: Ann (Zygo a b)) f (pmap a (id /\ cata a g) . out)

-- | In accumulations we add an extra annotation 'b' to the base functor of type 'a'.
type Accum a b = a :*!: K b

-- | Definition of an accumulation as an hylomorphism.
--
-- Accumulations <http://www.fing.edu.uy/~pardo/papers/wcgp02.ps.gz> are binary functions that use the second parameter to store intermediate results.
--
-- The so called "accumulation technique" is tipically used in functional programming to derive efficient implementations of some recursive functions.
accum :: (Mu a,Functor (PF a)) => Ann a -> (F (Accum a b) c -> c) -> ((F a a,b) -> F a (a,b)) -> (a,b) -> c
accum (a::Ann a) f g = hylo (ann :: Ann (Accum a b)) f ((g /\ snd) . (out >< id))

-- | In histomorphisms we add an extra annotation 'c' to the base functor of type 'a'.
type Histo a c = K c :*!: a

-- | Definition of an histomorphism as an hylomorphism (as long as the catamorphism is defined as an hylomorphism).
--
-- Histomorphisms (<http://cs.ioc.ee/~tarmo/papers/inf.ps.gz>) capture the powerfull schemes of course-of-value iteration, and differ from catamorphisms for being able to apply the gene function at a deeper depth of recursion.
-- In other words, they allow to reuse sub-sub constructor results.
histo :: (Mu a,Functor (PF a)) => Ann a -> (F a (Histo a c) -> c) -> a -> c
histo (a::Ann a) g = fst . outH . cata a (inn . (g /\ id))
   where outH :: Histo a c -> F (Histo a c) (Histo a c)
         outH = out

-- | The combinator 'outl' unpacks the functor of an histomorphism and selects the annotation.
outl :: Histo a c -> c
outl = fst . out

-- | The combinator 'outr' unpacks the functor of an histomorphism and discards the annotation.
outr :: Histo a c -> F a (Histo a c)
outr = snd . out

-- | In futumorphisms we add an alternative annotation 'c' to the base functor of type 'b'.
type Futu b c = K c :+!: b

-- | Definition of a futumorphism as an hylomorphism (as long as the anamorphism is defined as an hylomorphism).
--
-- Futumorphisms are the dual of histomorphisms and are proposed as 'cocourse-of-argument' coiterators by their creators (<http://cs.ioc.ee/~tarmo/papers/inf.ps.gz>).
--
-- In the same fashion as histomorphisms, it allows to seed the gene with multiple levels of depth instead of having to do 'all at once' with an anamorphism.
futu :: (Mu b,Functor (PF b)) => Ann b -> (a -> F b (Futu b a)) -> a -> b
futu (b::Ann b) g = ana b ((g \/ id) . out) . innF . inl
   where innF :: F (Futu b a) (Futu b a) -> Futu b a
         innF = inn

-- | The combinator 'innl' packs the functor of a futumorphism from the base functor.
innl :: c -> Futu b c
innl = inn . inl

-- | The combinator 'innr' packs the functor of an futumorphism from an annotation.
innr :: F b (Futu b c) -> Futu b c
innr = inn . inr

-- | Definition of a dynamorphism as an hylomorphisms.
--
-- Dynamorphisms (<http://math.ut.ee/~eugene/kabanov-vene-mpc-06.pdf>) are a more general form of histomorphisms for capturing dynaming programming constructions.
--
-- Instead of following the recursion pattern of the input via structural recursion (as in histomorphisms),
-- dynamorphisms allow us to reuse the annotated structure in a bottom-up approach and avoiding rebuilding
-- it every time an annotation is needed, what provides a more efficient dynamic algorithm.
dyna :: (Mu b, Functor (PF b)) => Ann b -> (F b (Histo b c) -> c) -> (a -> F b a) -> a -> c
dyna (b::Ann b) g h = fst . outH . hylo b (inn . (g /\ id)) h
   where outH :: Histo b c -> F (Histo b c) (Histo b c)
         outH = out

-- | Definition of a chronomorphism as an hylomorphism.
--
-- This recursion pattern subsumes histomorphisms, futumorphisms and dynamorphisms
-- and can be seen as the natural hylomorphism generalization from composing an histomorphism after a futumorphism.
-- Therefore, chronomorphisms can 'look back' when consuming a type and 'jump forward' when generating one, via it's fold/unfold operations, respectively.
--
-- The notion of chronomorphism is a recent recursion pattern (at least known as such).
-- The first and single reference available is <http://comonad.com/reader/2008/time-for-chronomorphisms/>.
chrono :: (Mu c,Functor (PF c)) => Ann c -> (F c (Histo c b) -> b) -> (a -> F c (Futu c a)) -> a -> b
chrono (c::Ann c) g h = fst . outH . hylo c (inn . (g /\ id)) ((h \/ id) . out) . innF . inl
   where outH :: Histo c b -> F (Histo c b) (Histo c b)
         outH = out
         innF :: F (Futu c a) (Futu c a) -> (Futu c a)
         innF = inn

-- | The Fixpoint combinator as an hylomorphism.
--
-- 'fix' is a fixpoint combinator if @'fix' = 'app' '.' ('id' '/\' 'fix')@.
--
-- After expanding the deﬁnitions of '.', '/\' and 'app' we see that this corresponds to the expected pointwise equation @'fix' f = f ('fix' f)@.
fix :: (a -> a) -> a
fix = hylo (ann :: Ann (K (a -> a) :*!: I)) app (id /\ id)

-- | The combinator for isomorphic type transformations.
--
-- It can translate between types that share the same functor.
nu d = inn . pmap d (nu d) . out

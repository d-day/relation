-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.Pointless.Functors
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
-- This module defines data types as fixed points of functor.
-- Pointless Haskell works on a view of data types as fixed points of functors, in the same style as the PolyP (<http://www.cse.chalmers.se/~patrikj/poly/polyp/>) library.
-- Instead of using an explicit fixpoint operator, a type function is used to relate the data types with their equivalent functor representations.
--
-----------------------------------------------------------------------------

module Generics.Pointless.Functors where

import Prelude hiding (Functor(..))
import qualified Data.Generics as G
import qualified Data.Typeable as G
import qualified Data.Data as G
import qualified Data.Functor as F
import Generics.Pointless.Combinators

-- * Functors

-- ** Definition and operations over functors

-- | Identity functor.
data Id x = IdF {unIdF :: x} deriving (Eq,Show,G.Typeable)

-- | Constant functor.
data Const t x = ConsF {unConsF :: t} deriving (Eq,Show,G.Typeable)

-- | Sum of functors.
infixr 5 :+:
data (g :+: h) x = InlF (g x) | InrF (h x) deriving (Eq,Show)

instance (G.Typeable (g x),G.Typeable (h x)) => G.Typeable ((g :+: h) x) where
   typeOf _ = G.mkTyCon ":+:" `G.mkTyConApp` [G.typeOf (ann::g x),G.typeOf (ann::h x)]

-- | Product of functors.
infixr 6 :*:
data (g :*: h) x = ProdF (g x) (h x) deriving (Eq,Show)

instance (G.Typeable (g x),G.Typeable (h x)) => G.Typeable ((g :*: h) x) where
   typeOf _ = G.mkTyCon ":*:" `G.mkTyConApp` [G.typeOf (ann::g x),G.typeOf (ann::h x)]

-- | Composition of functors.
infixr 9 :@:
data (g :@: h) x = CompF {unCompF :: g (h x)} deriving (Eq,Show)

instance (G.Typeable (g x),G.Typeable (h x)) => G.Typeable ((g :@: h) x) where
   typeOf _ = G.mkTyCon ":@:" `G.mkTyConApp` [G.typeOf (ann::g x),G.typeOf (ann::h x)]

-- | Explicit fixpoint operator.
newtype Fix f = Inn { -- | The unfolding of the fixpoint of a functor is the functor applied to its fixpoint.
	                   --
	                   -- 'unFix' is specialized with the application of 'Rep' in order to subsume functor application
                         ouT :: Rep f (Fix f)
                    }

instance ShowRep f => Show (Fix f) where
    show f@(Inn r) = "(Fix " ++ showrep (vnn f) showfix r ++ ")"
        where showfix = show :: Fix f -> String

-- | Family of patterns functors of data types.
--
-- The type function is not necessarily injective, this is, different data types can have the same base functor.
type family PF a :: * -> *
-- ^ Semantically, we can say that @a = 'Fix' f@.

type instance PF (Fix f) = f
-- ^ The pattern functor of the fixpoint of a functor is the functor itself.

-- | Family of functor representations.
--
-- The 'Rep' family implements the implicit coercion between the application of a functor and the structurally equivalent sum of products.
type family Rep (f :: * -> *) x :: *
-- ^ Functors applied to types can be represented as sums of products.

type instance Rep Id x = x
-- ^ The identity functor applied to some type is the type itself.

type instance Rep (Const t) x = t
-- ^ The constant functor applied to some type is the type parameterized by the functor.

type instance Rep (g :+: h) x = Rep g x `Either` Rep h x
-- ^ The application of a sum of functors to some type is the sum of applying the functors to the argument type.

type instance Rep (g :*: h) x = (Rep g x,Rep h x)
-- ^ The application of a product of functors to some type is the product of applying the functors to the argument type.

type instance Rep (g :@: h) x = Rep g (Rep h x)
-- ^ The application of a composition of functors to some type is the nested application of the functors to the argument type.
--
-- This particular instance requires that nexted type function application is enabled as a type system extension.

type instance Rep [] x = [x]
-- ^ The application of the list functor to some type returns a list of the argument type.

-- | A specific @Show@ class for functor representations that receives a show function for recursive instances.
-- This avoids infinite loops in the type inference of fixpoints.
class ShowRep f where
    showrep :: Ann (Fix f) -> (x -> String) -> Rep f x -> String
instance ShowRep Id where
    showrep _ f x = f x
instance Show t => ShowRep (Const t) where
    showrep _ _ t = show t
instance (ShowRep f,ShowRep g) => ShowRep (f :*: g) where
    showrep (_ :: Ann (Fix (f :*: g))) f (x,y) = "("++l++","++r++")"
        where l = showrep (ann :: Ann (Fix f)) f x
              r = showrep (ann :: Ann (Fix g)) f y
instance (ShowRep f,ShowRep g) => ShowRep (f :+: g) where
    showrep (_ :: Ann (Fix (f :+: g))) f (Left x) = "(Left "++l++")"
        where l = showrep (ann :: Ann (Fix f)) f x
    showrep (_ :: Ann (Fix (f :+: g))) f (Right y) = "(Right "++r++")"
        where r = showrep (ann :: Ann (Fix g)) f y
instance (ShowRep f,ShowRep g) => ShowRep (f :@: g) where
    showrep (_ :: Ann (Fix (f:@:g))) f x = showrep (ann :: Ann (Fix f)) r x
        where r = showrep (ann :: Ann (Fix g)) f

class ToRep f where
    rep :: f x -> Rep      f  x
    fun :: f x -> Ann (Fix f)
    val :: f x -> Ann         x
    unrep ::      Ann (Fix f) 
               -> Ann         x 
               -> Rep       f x -> f x

instance ToRep [] where
	rep l = l
	fun l = ann
	val l = ann
	unrep _ _ l = l

instance ToRep Id where
    rep (IdF x)      = x
    fun _            = ann::Ann (Fix Id)
    val (IdF (x::x)) = ann::Ann x
    unrep _ _ x      = IdF x

instance ToRep (Const c) where
    rep (ConsF x)             = x
    fun _                     = ann::Ann (Fix (Const c))
    val (ConsF _::Const c x)  = ann::Ann x
    unrep _ _ x               = ConsF x

instance (ToRep f,ToRep g) => ToRep (f :*: g) where
    rep (ProdF x y)                          = (rep x,rep y)
    fun _                                    = ann::Ann (Fix (f:*:g))
    val (ProdF (x::f x) (y::g x))            = ann::Ann x
    unrep (_::Ann (Fix (f:*:g))) a (x,y)     = ProdF (unrep (ann::Ann (Fix f)) a x) (unrep (ann::Ann (Fix g)) a y)

instance (ToRep f,ToRep g) => ToRep (f :+: g) where
    rep (InlF l)                             = Left (rep l)
    rep (InrF r)                             = Right (rep r)
    fun _                                    = ann::Ann (Fix (f:+:g))
    val (InlF (l::f x))                      = ann::Ann x
    val (InrF (r::g x))                      = ann::Ann x
    unrep (_::Ann (Fix (f:+:g))) a (Left l)  = InlF (unrep (ann::Ann (Fix f)) a l)
    unrep (_::Ann (Fix (f:+:g))) a (Right r) = InrF (unrep (ann::Ann (Fix g)) a r)


instance (Functor f,F.Functor f,ToRep f,ToRep g) => ToRep (f :@: g) where
    rep (CompF x)                            = rep $ F.fmap rep x
    fun _                                    = ann::Ann (Fix (f:@:g))
    val (CompF x::(f:@:g) x)                 = ann::Ann x
    unrep (_::Ann (Fix (f:@:g))) a x         = CompF $ (unrep (ann::Ann (Fix f)) (ann::Ann (g a))) $ fmap (ann::Ann (Fix f)) (unrep (ann::Ann (Fix g)) a) x

-- | Polytypic 'Prelude.Functor' class for functor representations
class Functor (f :: * -> *) where
   fmap :: Ann (Fix f)                          -- ^ For desambiguation purposes, the type of the functor must be passed as an explicit parameter to 'fmap'
        -> (x -> y) -> Rep f x -> Rep f y -- ^ The mapping over representations
   fzip :: Ann (Fix f) -> (a -> c) -> (Rep f a,Rep f c) -> Rep f (a,c)      -- ^ The polytypic functor zipping combinator.
        -- Gives preference to the abstract (first) F-structure.

instance F.Functor Id where
   fmap f (IdF x) = IdF $ f x
instance Functor Id where
   fmap _ f = f
   fzip _ create = id
-- ^ The identity functor applies the mapping function the argument type

instance F.Functor (Const t) where
   fmap f (ConsF x) = ConsF x
instance Functor (Const t) where
   fmap _ f = id
   fzip _ create = fst
-- ^ The constant functor preserves the argument type

instance (F.Functor g,F.Functor h) => F.Functor (g :+: h) where
   fmap f (InlF x) = InlF (F.fmap f x)
   fmap f (InrF x) = InrF (F.fmap f x)
instance (Functor g,Functor h) => Functor (g :+: h) where
   fmap (_::Ann (Fix (g:+:h))) f (Left x) = Left (fmap (ann :: Ann (Fix g)) f x)
   fmap (_::Ann (Fix (g:+:h))) f (Right x) = Right (fmap (ann :: Ann (Fix h)) f x)
   fzip (_::Ann (Fix (g:+:h))) create = (l -|- r) . dists
    where l = fzip (ann::Ann (Fix g)) create \/ fmap (ann::Ann (Fix g)) (id /\ create) . fst
          r = fmap (ann::Ann (Fix h)) (id /\ create) . fst \/ fzip (ann::Ann (Fix h)) create
-- ^ The sum functor recursively applies the mapping function to each alternative

instance (F.Functor g,F.Functor h) => F.Functor (g :*: h) where
   fmap f (ProdF x y) = ProdF (F.fmap f x) (F.fmap f y)
instance (Functor g,Functor h) => Functor (g :*: h) where
   fmap (_::Ann (Fix (g:*:h))) f (x,y) = (fmap (ann :: Ann (Fix g)) f x,fmap (ann :: Ann (Fix h)) f y)
   fzip (_::Ann (Fix (g:*:h))) create = (fzip (ann::Ann (Fix g)) create >< fzip (ann::Ann (Fix h)) create) . distp
-- ^ The product functor recursively applies the mapping function to both sides

instance (F.Functor g,F.Functor h) => F.Functor (g :@: h) where
   fmap f (CompF x) = CompF $ F.fmap (F.fmap f) x
instance (Functor g,Functor h) => Functor (g :@: h) where
   fmap (_::Ann (Fix (g:@:h))) f x = fmap (ann :: Ann (Fix g)) (fmap (ann :: Ann (Fix h)) f) x
   fzip (_::Ann (Fix (g:@:h))) create = fmap g (fzip h create) . fzip g (fmap h create)
    where g = ann::Ann (Fix g)
          h = ann::Ann (Fix h)
-- ^ The composition functor applies in the nesting of the mapping function to the nested functor applications

instance Functor [] where
   fmap _ = map
   fzip _ create = lzip create
-- ^ The list functor maps the specific 'map' function over lists of types

lzip :: (a -> c) -> ([a],[c]) -> [(a,c)]
lzip create ([],lc) = []
lzip create (a:la,[]) = (a,create a) : lzip create (la,[])
lzip create (a:la,c:lc) = (a,c) : lzip create (la,lc)

-- | Short alias to express the structurally equivalent sum of products for some data type
type F a x = Rep (PF a) x

-- | Polytypic map function
pmap :: Functor (PF a) => Ann a                          -- ^ A value of a data type that is the fixed point of the desired functor
                       -> (x -> y) -> F a x -> F a y -- ^ The mapping over the equivalent sum of products
pmap (_::Ann a) f = fmap (ann:: Ann (Fix (PF a))) f

-- | The 'Mu' class provides the value-level translation between data types and their sum of products representations
class Mu a where
    -- | Packs a sum of products into one equivalent data type
    inn :: F a a -> a
    -- | unpacks a data type into the equivalent sum of products
    out :: a -> F a a

inn' :: Mu a => Ann a -> F a a -> a
inn' _ = inn

out' :: Mu a => Ann a -> a -> F a a
out' _ = out

instance Mu (Fix f) where
   inn = Inn
   out = ouT
-- ^ Expanding/contracting the fixed point of a functor is the same as consuming/applying it's single type constructor

-- ** Fixpoint combinators

-- | In order to simplify type-level composition of functors, we can create fixpoint combinators that implicitely assume fixpoint application.

data I = FixId
-- ^ Semantically, we can say that @'I' = 'Fix' 'Id'@.
type instance PF I = Id

instance Mu I where
   inn = id
   out = id

data K a = FixConst {unFixConst :: a}
-- ^ Semantically, we can say that @'K' t = 'Fix' ('Const' t)@.
type instance PF (K a) = Const a

instance Mu (K a) where
   inn = FixConst
   out = unFixConst

infixr 5 :+!:
data (a :+!: b) = FixSum {unFixSum :: F (a :+!: b) (a :+!: b)}
-- ^ Semantically, we can say that @'Fix' f :+!: 'Fix' g = 'Fix' (f :+: g)@.
type instance PF (a :+!: b) = PF a :+: PF b

instance Mu (a :+!: b) where
   inn = FixSum
   out = unFixSum

infixr 6 :*!:
data (a :*!: b) = FixProd {unFixProd :: F (a :*!: b) (a :*!: b)}
-- ^ Semantically, we can say that @'Fix' f :*!: 'Fix' g = 'Fix' (f :*: g)@.
type instance PF (a :*!: b) = PF a :*: PF b

instance Mu (a :*!: b) where
   inn = FixProd
   out = unFixProd

infixr 9 :@!:
data (a :@!: b) = FixComp {unFixComp :: F (a :@!: b) (a :@!: b)}
-- ^ Semantically, we can say that @'Fix' f :\@!: 'Fix' g = 'Fix' (f ':\@: g)@.
type instance PF (a :@!: b) = PF a :@: PF b

instance Mu (a :@!: b) where
   inn = FixComp
   out = unFixComp

-- * Default definitions for commonly used data types

-- ** List

type instance PF [a] = Const One :+: Const a :*: Id

instance Mu [a] where
    inn (Left _)         = []
    inn (Right (x,xs))   = x:xs
    out []               = Left _L
    out (x:xs)           = Right (x,xs)

nil :: One -> [a]
nil = inn . inl

cons :: (a,[a]) -> [a]
cons = inn . inr

-- ** Natural Numbers

-- Implemented as "boxed" integers for efficiency
data Nat = Nat Int deriving (Eq,Show,Read,G.Typeable,G.Data)

type instance PF Nat = Const One :+: Id

instance Mu Nat where
    inn (Left _) = Nat 0
    inn (Right (Nat n)) = Nat (succ n)
    out (Nat 0) = Left _L
    out (Nat n) = if n < 1 then error "negative natural not expected" else Right (Nat $ pred n)

nzero = Nat 0
nsucc (Nat n) = Nat (succ n)

-- ** Int (positive only)

type instance PF Int = Const One :+: Id

instance (Mu Int) where
    inn (Left _) = 0
    inn (Right n) = succ n
    out 0 = Left _L
    out n = Right (pred n)

zero :: One -> Int
zero = inn . inl

suck :: Int -> Int
suck = inn . inr

natInt :: Nat -> Int
natInt (Nat n) = n

intNat :: Int -> Nat
intNat n = if n < 0 then error "negative natural not expected" else Nat n

-- ** Bool

type instance PF Bool = Const One :+: Const One

instance Mu Bool where
	inn (Left _) = True
	inn (Right _) = False
	out True = Left _L
	out False = Right _L

true :: One -> Bool
true = inn . inl

false :: One -> Bool
false = inn . inr

-- ** Maybe

type instance PF (Maybe a) = Const One :+: Const a

instance Mu (Maybe a) where
    inn (Left _)    = Nothing
    inn (Right x)   = Just x
    out Nothing     = Left _L
    out (Just x)    = Right x

maybe2bool :: Maybe a -> Bool
maybe2bool = inn . (id -|- bang) . out

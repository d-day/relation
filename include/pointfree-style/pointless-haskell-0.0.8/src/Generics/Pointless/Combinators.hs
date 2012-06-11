
-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.Pointless.Combinators
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
-- This module defines many standard combinators used for point-free programming.
--
-----------------------------------------------------------------------------

module Generics.Pointless.Combinators where

import Prelude hiding (or,and)
import qualified Data.Generics as G

-- * Type annotations

-- type annotation
data Ann a
ann = _L
vnn :: a -> Ann a
vnn _ = ann

instance Show (Ann a) where
    show = const "ann"

-- * Terminal object

-- | The bottom value for any type.
-- It is many times used just for type annotations.
_L :: a
_L = undefined

_LCR :: a -> a -> a
_LCR = undefined . undefined . undefined

-- | The final object.
-- The only possible value of type 'One' is '_L'.

-- {{{ 
data I deriving G.Typeable

instance Show I where
    show _ = "_I_"

instance Eq I where
    (==) _ _ = True
-- }}}

-- should have the same structure as the generators for S3
data III d r = DCR
             | D
             |  C
             |   R 
         deriving G.Typeable


{-
instance Show III where
     show _ _ _   = "_III_"
     show One _ _ = "_RII_"
     show _ One _ = "_IGI_"
     show _ _ One = "_IIB_"
-}


-- * Points

-- | Creates a point to the terminal object.
bang :: a -> I
bang = const _L

-- | Converts elements into points.
pnt :: a -> I -> a
pnt = const

-- * Products

infix 6  /\
-- | The infix split combinator.
(/\) :: (a -> b) -> (a -> c) -> a -> (b,c)
(/\) f g x = (f x, g x)

(/\/\) f c g x = (f x, (c x, c x, c x), g x)


infix 7  ><
-- The infix product combinator.
(><) :: (a -> b) -> (c -> d) -> (a,c) -> (b,d)
f >< g = f . fst /\ g . snd

-- * Sums

-- | Injects a value to the left of a sum.
inl :: a -> Either a b
inl = Left

-- | Injects a value to the right of a sum.
inr :: b -> Either a b
inr = Right

infix 4 \/
-- | The infix either combinator.
(\/) :: (b -> a) -> (c -> a) -> Either b c -> a
(\/) = either

infix 5 -|-
-- | The infix sum combinator.
(-|-) :: (a -> b) -> (c -> d) -> Either a c -> Either b d
f -|- g = inl . f \/ inr . g

infix 5 <>
-- | Alias for the infix sum combinator.
(<>) :: (a -> b) -> (c -> d) -> Either a c -> Either b d
(<>) = (-|-)


curry1   :: ((a) -> b)        -> a -> b                     -- or b -> a
curry2   :: ((a,b) -> c)      -> a -> b -> c                
curry3   :: ((a,b,c) -> d)    -> a -> b -> c -> d
curry4   :: ((a,b,c,d) -> e)  -> a -> b -> c -> d -> e
curry5   :: ((a,b,c,d,e) -> f)-> a -> b -> c -> d -> e -> f


uncurry1 :: (a -> b)                     -> (a)     -> b
uncurry2 :: (a -> b -> c)                -> (a,b)   -> c
uncurry3 :: (a -> b -> c -> d)           -> (a,b,c) -> d
uncurry4 :: (a -> b -> c -> d -> e)      -> (a,b,c,d)   -> e
uncurry5 :: (a -> b -> c -> d -> e -> f) -> (a,b,c,d,e) -> f

curry1 f x          = f (x)
curry2 f x y        = f (x,y)
curry3 f x y z      = f (x,y,z)
curry4 f x y z a    = f (x,y,z,a)
curry5 f x y z a b  = f (x,y,z,a,b)

uncurry1 f (x) = f x
uncurry2 f (x,y) = f x y
uncurry3 f (x,y,z) = f x y z
uncurry4 f (x,y,z,a) = f x y z a
uncurry5 f (x,y,z,a,b) = f x y z a b


-- * Exponentials

-- | The application combinator.
app :: (a -> b,a) -> b
app (f,x) = f x

app2 :: (a, a -> b) -> b
app2 (x,f) = f x

-- | The left exponentiation combinator.
lexp :: (a -> b) -> (b -> c) -> (a -> c)
lexp f = curry2 (app . (id >< f))

-- | The right exponentiation combinator.
rexp :: (b -> c) -> (a -> b) -> (a -> c)
rexp f = curry2 (f . app)


infix 0 !
-- | The infix combinator for a constant point.
(!) :: a -> b -> a
(!) = const
 
-- * Guards

-- | Guard combinator that operates on Haskell booleans.
grd :: (a -> Bool) -> a -> Either a a
grd p x = if p x then inl x else inr x

-- | Infix guard combinator that simulates the postfix syntax.
(?) :: (a -> Bool) -> a -> Either a a
(?) = grd

infix 1 ??
(??) :: (a -> Either I I) -> a -> Either a a
(??) p = (snd -|- snd) . distl . (p /\ id)
-- * Point-free definitions of uncurried versions of the basic combinators


-- | The uncurried split combinator.
split :: (a -> b, a -> c) -> (a -> (b,c))
split = curry2 (app_X_app . (fst_X_idf /\ snd_X_idf))

app_X_app = app >< app

idf_X_app = id  >< app


fst_X_idf = fst >< id
idf_X_fst = id  >< fst
snd_X_idf = snd >< id
idf_X_snd = id  >< snd


app_V_app = app \/ app
fst_V_idf = fst \/ id
idf_V_fst = id  \/ fst
snd_V_idf = snd \/ id
idf_V_snd = id  \/ snd


-- | The uncurried either combinator.
eithr :: (a -> c, b -> c) -> Either a b -> c
eithr = curry2 (app_V_app . (fst_X_idf -|- snd_X_idf) . distr)

-- | The uncurried composition combinator.
comp :: (b -> c, a -> b) -> (a -> c)
comp = curry2 (app . idf_X_app . assocr)

-- | Binary @or@ of boolean functions.
orf :: (a -> Bool,a -> Bool) -> (a -> Bool)
orf = curry2 (or . (app . fst_X_idf /\ app . snd_X_idf))

-- | Binary @and@ of boolean functions.
andf :: (a -> Bool,a -> Bool) -> (a -> Bool)
andf = curry2 (and . (app . fst_X_idf /\ app . snd_X_idf))

-- | Binary @or@ point-free combinator.
or :: (Bool,Bool) -> Bool
or = uncurry2 (||)

-- | Binary @and@ point-free combinator.
and :: (Bool,Bool) -> Bool
and = uncurry2 (&&)

-- | Binary equality point-free combinator.
eq :: Eq a => (a,a) -> Bool
eq = uncurry2 (==)

-- | Binary inequality point-free combinator.
neq :: Eq a => (a,a) -> Bool
neq = not . eq

-- * Point-free isomorphic combinators

-- | Swap the elements of a product.
swap :: (a,b) -> (b,a)
swap = snd /\ fst

-- | Swap the elements of a sum.
coswap :: Either a b -> Either b a
coswap = inr \/ inl

-- | Distribute products over the left of sums.
distl :: (Either a b,c) -> Either (a,c) (b,c)
distl = app . ((curry2 inl \/ curry2 inr) >< id)

-- | Distribute sums over the left of products.
undistl :: Either (a,c) (b,c) -> (Either a b, c)
undistl = inl >< id \/ inr >< id

-- | Distribute products over the right of sums.
distr :: (c, Either a b) -> Either (c,a) (c,b)
distr = (swap -|- swap) . distl . swap

-- | Distribute sums over the right of products.
undistr :: Either (c,a) (c,b) -> (c, Either a b)
undistr = (id >< inl) \/ (id >< inr)

-- | Associate nested products to the left.
assocl :: (a,(b,c)) -> ((a,b),c)
assocl = idf_X_fst /\ snd . snd

-- | Associates nested products to the right.
assocr :: ((a,b),c) -> (a,(b,c))
assocr = fst . fst  /\  snd_X_idf

-- | Associates nested sums to the left.
coassocl :: Either a (Either b c) -> Either (Either a b) c
coassocl = (inl . inl) \/ (inr -|- id)

-- | Associates nested sums to the right.
coassocr :: Either (Either a b) c -> Either a (Either b c)
coassocr = (id -|- inl) \/ (inr . inr)

-- | Shifts the an element to the right of a nested pair.
subr :: (a,(b,c)) -> (b,(a,c))
subr = assocr . (swap >< id) . assocl

-- | Shifts the an element to the left of a nested pair.
subl :: ((a,b),c) -> ((a,c),b)
subl = assocl . (id >< swap) . assocr

-- | Shifts an option to the right of a nested sum.
cosubr :: Either a (Either b c) -> Either b (Either a c)
cosubr = coassocr . (coswap -|- id) . coassocl


-- | Shifts an option to the left of a nested sum.
cosubl :: Either (Either a b) c -> Either (Either a c) b
cosubl = coassocl . (id -|- coswap) . coassocr


cosubrA :: Either a (Either b (Either c d)) -> Either a (Either b (Either d c))
cosublA :: Either (Either (Either a d) b) c -> Either (Either (Either d a) b) c

cosubrA = coassocr . (id -|- coswap) . coassocl
cosublA = coassocl . (coswap -|- id) . coassocr


-- | The product distribution combinator
distp :: ((c,d),(a,b)) -> ((c,a),(d,b))
distp = fst_X_fst /\ snd_X_snd

fst_X_fst = fst >< fst
snd_X_snd = snd >< snd



-- | The sum distribution combinator.
dists ::       (Either a b,Either c d) -> Either (Either (a,c) (a,d)) (Either (b,c) (b,d))
distsAlt ::    (Either a b,Either c d) -> Either (Either (a,c) (b,c)) (Either (a,d) (b,d))

dists     = (distr -|- distr) . distl
distsAlt  = (distl -|- distl) . distr



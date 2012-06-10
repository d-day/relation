-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.Pointless.Examples.Examples
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
-- This module provides examples, examples and more examples.
--
-----------------------------------------------------------------------------

module Generics.Pointless.Examples.Examples where

import Generics.Pointless.Combinators
import Generics.Pointless.Functors
import Generics.Pointless.RecursionPatterns
import Prelude hiding (Functor(..),filter,concat,tail,length)
import Data.List hiding (filter,concat,tail,length,partition)

-- * Integers

-- | The number 1.
one = suck . zero

-- ** Addition

-- | Pre-defined algebraic addition.
add :: (Int,Int) -> Int
add = uncurry (+)

-- | Definition of algebraic addition as an anamorphism in the point-wise style.
addAnaPW :: (Int,Int) -> Int
addAnaPW = ana (ann::Ann Int) h 
   where h (0,0) = Left _L 
         h (n,0) = Right (n-1,0) 
         h (0,m) = Right (0,m-1) 
         h (n,m) = Right (n,m-1)

-- | Defition of algebraic addition as an anamorphism.
addAna :: (Int,Int) -> Int
addAna = ana (ann::Ann Int) f
   where f = (bang -|- (id >< zero \/ (zero >< id \/ succ >< id))) . aux . (out >< out)
         aux = coassocr . (distl -|- distl) . distr

-- | The fixpoint of the functor that is either a constant or defined recursively.
type From a = K a :+!: I

-- | Definition of algebraic addition as an hylomorphism.
addHylo :: (Int,Int) -> Int
addHylo = hylo (ann::Ann (From Int)) f g
   where f = id \/ succ
         g = (snd -|- id) . distl . (out >< id)

-- | Definition of algebraic addition as an accumulation.
addAccum :: (Int,Int) -> Int
addAccum = accum (ann::Ann Int) f t
   where t = (fst -|- id >< succ) . distl
         f = (snd \/ fst) . distl

addApoPW :: (Int,Int) -> Int
addApoPW = apo (ann :: Ann Int) h
    where h (0,0) = Left _L
          h (n,0) = Right $ Right $ n-1
          h (n,m) = Right $ Left (n,m-1)

-- | Definition of algebraic addition as an apomorphism.
addApo :: (Int,Int) -> Int
addApo = apo (ann::Ann Int) h
   where h = (id -|- coswap) . coassocr . (fst -|- inn >< id) . distr . (out >< out)
         
-- ** Product

-- | Pre-defined algebraic product.
prod :: (Int,Int) -> Int
prod = uncurry (*)

-- | Definition of algebraic product as an hylomorphism
prodHylo :: (Int,Int) -> Int
prodHylo = hylo (ann::Ann [Int]) f g
   where f = zero \/ add
         g = (snd -|- fst /\ id) . distr . (id >< out)

-- ** 'Greater than' comparison

-- | Pre-defined 'greater than' comparison.
gt :: Ord a => (a,a) -> Bool
gt = uncurry (>)

-- | Definition of 'greater than' as an hylomorphism.
gtHylo :: (Int,Int) -> Bool
gtHylo = hylo (ann :: Ann (From Bool)) f g
    where g = ((((False!) \/ (True!)) \/ (False!)) -|- id) . coassocl . (distl -|- distl) . distr . (out >< out)
	  f = id \/ id

-- ** Factorial

-- | Native recursive definition of the factorial function.
fact :: Int -> Int
fact 0 = 1
fact n = n * fact (n-1)

-- | Recursive definition of the factorial function in the point-free style.
factPF :: Int -> Int
factPF = ((1!) \/ prod) .
         (id -|- id >< factPF) . 
         (id -|- id /\ pred) . (iszero?)
   where iszero = (==0)

-- | Recursive definition of the factorial function in the point-free style with structural recursion.
factPF' :: Int -> Int
factPF' = (one \/ prod) . (id -|- id >< factPF') . (id -|- succ /\ id) . out

-- | Definition of the factorial function as an hylomorphism.
factHylo :: Int -> Int
factHylo = hylo (ann :: Ann [Int]) f g
   where g = (id -|- succ /\ id) . out
         f = one \/ prod

-- | Definition of the factorial function as a paramorphism.
factPara :: Int -> Int
factPara = para (ann::Ann Int) f
   where f = one \/ (prod . (id >< succ))

-- | Definition of the factorial function as a zygomorphism.
factZygo :: Int -> Int
factZygo = zygo (ann::Ann Int) inn f
   where f = one \/ (prod . (id >< succ))

-- ** Fibonnaci

-- | Native recursive definition of the fibonacci function.
fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)

-- | Recursive definition of the fibonacci function in the point-free style.
fibPF :: Int -> Int
fibPF = (zero \/ (one \/ add)) . (bang -|- (bang -|- fibPF >< fibPF)) . (id -|- aux) . ((==0)?)
   where aux = (id -|- pred /\ pred . pred) . ((==1)?)

-- | Recursive definition of the fibonacci function in the point-free style with structural recursion.
fibPF' :: Int -> Int
fibPF' = (zero \/ (one \/ add)) . (id -|- (id -|- fibPF' >< fibPF')) . (id -|- aux) . out
   where aux = (id -|- succ /\ id) . out

-- | The fixpoint of the functor for a binary shape tree.
type BSTree = K One :+!: (K One :+!: I :*!: I)

-- | Definition of the fibonacci function as an hylomorphism.
fibHylo :: Int -> Int
fibHylo = hylo (ann :: Ann BSTree) f g
   where f = zero \/ (one \/ add)
         g = (id -|- ((id -|- succ /\ id) . out)) . out
         

-- | Definition of the fibonacci function as an histomorphism.
fibHisto :: Int -> Int
fibHisto = histo (ann::Ann Int) f
   where f = (zero \/ (one . snd \/ add . (id >< outl)) . distr . out)

-- | Definition of the fibonacci function as a dynamorphism.
fibDyna :: Int -> Int
fibDyna = dyna (ann::Ann Int) f g
   where f = (zero \/ (one . snd \/ add . (id >< outl)) . distr . out)
         g = out

-- ** Binary Partitioning

-- | Native recursive definition for the binary partitions of a number.
--
-- The number of binary partitions for a number n is the number of unique ways to partition
-- this number (ignoring the order) into powers of 2.
-- | Definition of the binary partitioning of a number as an hylomorphism.
bp :: Int -> Int
bp 0 = 1
bp n = if odd n then bp (n-1) else bp (n-1) + bp (div n 2)

-- | The fixpoint of the functor representing trees with maximal branching factor of two.
type BTree = K One :+!: (I :+!: (I :*!: I))

-- | Definition of the binary partitioning of a number as an hylomorphism.
bpHylo :: Int -> Int
bpHylo = hylo (ann :: Ann BTree) g h
   where g = one \/ (id \/ add)
         h = (id -|- h') . out
         h' = (id -|- id /\ (`div` 2) . succ) . (even?)

-- | Definition of the binary partitioning of a number as a dynamorphism.
bpDyna :: Int -> Int
bpDyna = dyna (ann :: Ann [Int]) (g . o) h
   where g = one \/ (id \/ add)
         o = id -|- oj
         oj = (o1 -|- o2) . ((odd . fst)?)
         o1 = outl . snd
         o2 = outl . snd /\ (outl . oi)
         oi = uncurry pi . ((pred . (`div` 2)) >< id)
         h = (id -|- succ /\ id) . out
         pi 0 x = x 
         pi k x = case outr x of
            Right (_,y) -> pi (pred k) y

-- ** Average

-- | Recursive definition of the average of a set of integers.
average :: [Int] -> Int
average = uncurry div . (sum /\ length)

-- | Definition of the average of a set of integers as a catamorphism.
averageCata :: [Int] -> Int
averageCata = uncurry div . cata (ann::Ann [Int]) f
   where f = (zero \/ add . (id >< fst)) /\ (zero \/ succ . snd . snd)

-- * Lists

-- ** Singleton list.

-- | Pre-defined wrapping of an element into a list.
wrap :: a -> [a]
wrap = (:[])

-- | Definition of wrapping in the point-free style.
wrapPF :: a -> [a]
wrapPF = cons . (id /\ nil . bang)

-- ** Tail

-- | Definition of the tail of a list as a total function.
tail :: [a] -> [a]
tail [] = []
tail (x:xs) = xs

-- | Definition of the tail of a list in the point-free style.
tailPF :: [a] -> [a]
tailPF = (([]!) \/ snd) . out

-- | Definition of the tail of a list as an anamorphism.
tailCata :: [a] -> [a]
tailCata = fst . cata (ann::Ann [a]) (f /\ inn . (id -|- id >< snd))
   where f = ([]!) \/ snd . snd

-- | Definition of the tail of a list as a paramorphism.
tailPara :: [a] -> [a]
tailPara = para (ann::Ann [a]) f
   where f = ([]!) \/ snd . snd

-- ** Length

-- | Native recursion definition of list length.
length :: [a] -> Int
length [] = 0
length (x:xs) = succ (length xs)

-- | Recursive definition of list length in the point-free style.
lengthPF :: [a] -> Int
lengthPF = (zero . bang \/ succ . lengthPF . tail) . (null?)

-- | Recursive definition of list length in the point-free style with structural recursion.
lengthPF' :: [a] -> Int
lengthPF' = inn . (id -|- (lengthPF' . snd)) . out

-- | Definition of list length as an hylomorphism.
lengthHylo :: [a] -> Int
lengthHylo = hylo (ann::Ann Int) f g
   where f = inn
         g = (id -|- snd) . out

-- | Definition of list length as an anamorphism.
lengthAna :: [a] -> Int
lengthAna = ana _L f
   where f = (id -|- snd) . out

-- | Definition of list length as a catamorphism.
lengthCata :: [a] -> Int
lengthCata = cata _L f
    where f = zero \/ succ . snd

-- ** Filtering

-- | Native recursive definition of list filtering.
filter :: (a -> Bool) -> [a] -> [a]
filter p [] = []
filter p (x:xs) = if p x then x : filter p xs else filter p xs

-- | Definition of list filtering as an catamorphism.
filterCata :: (a -> Bool) -> [a] -> [a]
filterCata p = cata (ann::Ann [a]) f
   where f = (nil \/ (cons \/ snd)) . (id -|- ((p . fst)?))

-- ** Generation

-- | Generation of infinite lists as an anamorphism.
repeatAna :: a -> [a]
repeatAna = ana (ann::Ann [a]) (inr . (id /\ id))

-- | Finite replication of an element as an anamorphism.
replicateAna :: (Int,a) -> [a]
replicateAna = ana (ann::Ann [a]) h
   where h = (bang -|- snd /\ id) . distl . (out >< id)

-- | Generation of a downwards list as an anamorphism.
downtoAna :: Int -> [Int]
downtoAna = ana _L f
   where f = (bang -|- (id /\ pred)) . ((==0) ?)

-- | Ordered list insertion as an apomorphism.
insertApo :: Ord a => (a,[a]) -> [a]
insertApo = apo (ann::Ann [a]) f
   where f = inr. undistr . (inr \/ (inr \/ inl)) . ((id >< nil) -|- ((id >< cons) . assocr -|- assocr . (swap >< id)) . distl . ((le?) >< id) . assocl) . distr . (id >< out)
         le = uncurry (<=)

-- | Ordered list insertion as a paramorphism.
insertPara :: Ord a => (a,[a]) -> [a]
insertPara (x,l) = para (ann::Ann [a]) f l
   where f = wrap . (x!) \/ ((x:) . cons . (id >< snd) \/ cons . (id >< fst)) . (((x <=) . fst)?)

-- | Append an element to the end of a list as an hylomorphism.
snoc :: (a,[a]) -> [a]
snoc = hylo (ann::Ann (NeList a a)) f g
   where g = (fst -|- subr) . distr . (id >< out)
         f = wrap \/ cons

-- | Append an element to the end of a list as an apomorphism.
snocApo :: (a,[a]) -> [a]
snocApo = apo (ann::Ann [a]) h
   where h = inr . undistr . coswap . (id >< nil  -|-  assocr . (swap >< id) . assocl) . distr . (id >< out)

-- ** Extraction

-- | Creates a bubble from a list. Used in the bubble sort algorithm.
bubble :: (Ord a) => [a] -> Either One (a,[a])
bubble = cata (ann::Ann [a]) f
   where f = id -|- ((id >< ([]!)) \/ ((id >< cons) . assocr . (id \/ (swap >< id)) . ((uncurry (<) . fst) ?) . assocl)) . distr

-- | Extraction of a number of elements from a list as an anamorphism.
takeAna :: (Int,[a]) -> [a]
takeAna = ana (ann::Ann [a]) h
   where h = (bang -|- assocr . (swap >< id) . assocl) . aux . (out >< out)
         aux = coassocl . (distl -|- distl) . distr

-- ** Partition

-- | Native recursive definition for partitioning a list at a specified element.
partition :: Ord a => (a,[a]) -> ([a],[a])
partition (a,xs) = foldr (select a) ([],[]) xs
   where select :: Ord a => a -> a -> ([a], [a]) -> ([a], [a])
         select a x (ts,fs) = if a > x then (x:ts,fs) else (ts, x:fs)

-- | Definition for partitioning a list at a specified element as an hylomorphism.
partitionHylo :: (Ord a) => (a,[a]) -> ([a],[a])  
partitionHylo = hylo (ann::Ann [(a,a)]) f g
   where g = (snd -|- ((id >< fst) /\ (id >< snd))) . distr . (id >< out)
         f = (nil /\ nil) \/ (((cons >< id) . assocl . (snd >< id) \/ (id >< cons) . ((fst . snd) /\ (id >< snd)) . (snd >< id)) . ((gt . fst)?))

-- **  Transformations

-- | Incremental summation as a catamorphism.
isum :: [Int] -> [Int]
isum = cata (ann::Ann [Int]) f
   where f = nil \/ isumOp . swap . (id >< cons . (zero . bang /\ id))
         isumOp (l,x) = map (x+) l

-- | Incrementation the elements of a list by a specified value as a catamorphism.
fisum :: [Int] -> Int -> [Int]
fisum = cata (ann::Ann [Int]) f
    where f = pnt (nil . bang) \/ comp . swap . (curry add >< (cons .) . split . (pnt id . bang /\ id))

data Some a = Wrap a | Insert a (Some a) deriving (Eq,Show)
type instance PF (Some a) = Const a :+: Const a :*: Id
instance Mu (Some a) where
    inn (Left x) = Wrap x
    inn (Right (x,xs)) = Insert x xs
    out (Wrap x) = Left x
    out (Insert x xs) = Right (x,xs)
neCons = uncurry Insert

-- | Incrementation the elements of a list by a specified value as an accumulation.
-- The result is always a non-empty list
isumsAccum :: ([Int],Int) -> Some Int
isumsAccum = accum _L h tau
    where h = inn . (snd -|- swap . (snd >< id)) . distl
          tau = (fst -|- aux) . distl
          aux = assocr . (fst /\ addAccum . (fst >< id))

isumsAna :: ([Int],Int) -> Some Int
isumsAna = ana _L h
    where h = (snd -|- (snd /\ aux)) . distl . (out >< id)
          aux = (id >< addAccum) . assocr . (swap >< id)

-- | Definition of list mapping as a catamorphism.
mapCata :: [a] -> (a -> b) -> [b]
mapCata = cata (ann::Ann [a]) f
   where f = (([]!)!) \/ curry (cons . (app . swap >< app) . ((fst >< id) /\ (snd >< id)))

-- | Definition of list reversion as a catamorphism.
reverseCata :: [a] -> [a]
reverseCata = cata (ann::Ann [a]) f 
    where f = nil \/ (cat . swap . (wrap >< id))

-- | Linear version of reverse using accumulations
reverseAccum l = reverseAccum' (l,[])

reverseAccum' :: ([a],[a]) -> [a]
reverseAccum' = accum (ann ::Ann [a]) h tau
    where h = (snd \/ snd . fst) . distl
          tau = (fst -|- aux) . distl
          aux = assocr . (id >< cons) . distp . ((id /\ id) >< id) . assocr

reverseHylo :: ([a],[a]) -> [a]
reverseHylo = hylo t g h
    where g = id \/ id
          h = (snd -|- aux) . distl . (out >< id)
          aux = (id >< inn . inr) . assocr . (swap >< id)
          t = ann :: Ann (K [a] :+!: I)

-- | Definition of the quicksort algorithm as an hylomorphism.
qsort :: (Ord a) => [a] -> [a]
qsort = hylo (ann::Ann (Tree a)) f g
   where g = (id -|- (fst /\ partition)) . out
         f = nil \/ (cat . (id >< cons) . assocr . (swap >< id) . assocl)

-- | Definition of the bubble sort algorithm as an anamorphism.
bsort :: (Ord a) => [a] -> [a]
bsort = ana (ann::Ann [a]) bubble
-- | Definition of the insertion sort algorithm as a catamorphism.
isort :: (Ord a) => [a] -> [a]
isort = cata (ann::Ann [a]) (nil \/ insertApo)

-- Auxiliary split function for the merge sort algorithm.
msplit :: [a] -> ([a],[a])
msplit = cata (ann::Ann [a]) f
    where f = (nil /\ nil) \/ (swap . (cons >< id) . assocl)

-- Definition of the merge sort algorithm as an hylomorphism.
msort :: (Ord a) => [a] -> [a]
msort = hylo (ann::Ann ((K One :+!: K a) :+!: (I :*!: I))) f g
    where g = coassocl . (id -|- (fst -|- msplit . cons) . ((null . snd)?)) . out 
	  f = (([]!) \/ wrap) \/ merge

-- | Definition of the heap sort algorithm as an hylomorphism.
hsort :: (Ord a) => [a] -> [a]
hsort = hylo f g h
    where f = ann :: Ann ((K One :+!: K a) :+!: (K a :*!: (I :*!: I)))
	  h = coassocl . (id -|- (fst -|- hsplit . cons) . ((null . snd)?)) . out
	  g = (([]!) \/ wrap) \/ cons . (id >< merge)

-- Auxiliary split function for the heap sort algorithm.
hsplit :: (Ord a) => [a] -> (a,([a],[a]))
hsplit [x] = (x,([],[]))
hsplit (h:t) | h < m     = (h,(m:l,r))
	     | otherwise = (m,(h:r,l))
	     where (m,(l,r)) = hsplit t

-- | Malcolm downwards accumulations on lists.
malcolm :: ((b, a) -> a) -> a -> [b] -> [a]
malcolm o e = map (cata (ann::Ann [b]) ((e!) \/ o)) . malcolmAna' cons . (id /\ nil . bang)

-- | Malcom downwards accumulations on lists as an anamorphism.
malcolmAna :: ((b, a) -> a) -> a -> [b] -> [a]
malcolmAna o e = malcolmAna' o . (id /\ (e!))

-- | Uncurried version of Malcom downwards accumulations on lists as an anamorphism.
malcolmAna' :: ((b, a) -> a) -> ([b], a) -> [a]
malcolmAna' o = ana (ann:: Ann [a]) g
   where g = (fst -|- (snd /\ (id >< o) . assocr . (swap >< id))) . distl . (out >< id)

-- ** Zipping

-- | Definition of the zip for lists of pairs as an anamorphism.
zipAna :: ([a],[b]) -> [(a,b)]
zipAna = ana (ann::Ann [(a,b)]) f
   where f = (bang -|- ((fst >< fst) /\ (snd >< snd))) . aux . (out >< out)
         aux = coassocl . (distl -|- distl) . distr

-- ** Subsequencing

-- | Definition of the subsequences of a list as a catamorphism.
subsequences :: Eq a => [a] -> [[a]]
subsequences = cata (ann::Ann [a]) f
   where f = cons . (nil /\ nil) \/ uncurry union . (snd /\ subsOp . swap . (wrap >< id))
         subsOp (r,l) = map (l++) r

-- ** Concatenation

-- | Pre-defined list concatenation.
cat :: ([a],[a]) -> [a]
cat = uncurry (++)

-- | List concatenation as a catamorphism.
catCata :: [a] -> [a] -> [a]
catCata = cata (ann::Ann [a]) f
   where f = (id!) \/ (comp . (curry cons >< id))

-- | The fixpoint of the list functor with a specific terminal element.
type NeList a b = K a :+!: (K b :*!: I)

-- | List concatenation as an hylomorphism.
catHylo :: ([a],[a]) -> [a]
catHylo = hylo (ann::Ann (NeList [a] a)) f g
   where g = (snd -|- assocr) . distl . (out >< id)
         f = id \/ cons

-- | Native recursive definition of lists-of-lists concatenation.
concat :: [[a]] -> [a]
concat [] = []
concat (l:ls) = l ++ concat ls

-- | Definition of lists-of-lists concatenation as an anamorphism.
concatCata :: [[a]] -> [a]
concatCata = cata (ann::Ann[[a]]) g
   where g = ([]!) \/ cat

-- | Sorted concatenation of two lists as an hylomorphism.
merge :: (Ord a) => ([a],[a]) -> [a]
merge = hylo (ann::Ann (NeList [a] a)) f g
   where g = ((id \/ id) -|- ((id \/ id) . (assocr -|- (assocr . (swap >< id) . assocl)) . (id >< cons -|- cons >< id) . ((uncurry (<) . (fst >< fst))?) )) . coassocl . (snd -|- (((cons . fst) -|- id) . distr . (id >< out))) . distl . (out >< id)
         f = id \/ cons

-- ** Summation

-- | Definition of inter addition as a catamorphism.
sumCata :: [Int] -> Int
sumCata = cata (ann::Ann [Int]) f
   where f = (0!) \/ add

-- ** Multiplication

-- | Native recursive definition of integer multiplication.
mult :: [Int] -> Int
mult [] = 1
mult (x:xs) = x * mult xs

-- | Definition of integer multiplication as a catamorphism.
multCata :: [Int] -> Int
multCata = cata _L f
	    where f = (1!) \/ prod

-- ** Predicates

-- Test if a list is sorted as a paramorphism.
sorted :: (Ord a) => [a] -> Bool
sorted = para (ann::Ann [a]) f
    where f = true \/ uncurry (&&) . ((true . bang \/ uncurry (<=) . (id >< head)) . ((null . snd)?) >< id) . assocl . (id >< swap)

-- ** Edit distance

-- | Native recursive definition of the edit distance algorithm.
--
-- Edit distance is a classical dynamic programming algorithm that calculates
-- a measure of “distance” or “diﬀerence” between lists with comparable elements.
editdist :: Eq a => ([a],[a]) -> Int
editdist ([],bs) = length bs
editdist (as,[]) = length as
editdist (a:as,b:bs) = minimum [m1,m2,m3]
   where m1 = editdist (as,b:bs) + 1
         m2 = editdist (a:as,bs) + 1
         m3 = editdist (as,bs) + (if a==b then 0 else 1)

-- | The fixpoint of the functor that represents a virtual matrix used to accumulate and look up values for the edit distance algorithm.
--
-- Since matrixes are not inductive types, a walk-through of a matrix is used, consisting in a list of values from the matrix ordered predictability.
--
-- For a more detailed explanation, please refer to <http://math.ut.ee/~eugene/kabanov-vene-mpc-06.pdf>.
type EditDist a = K [a] :+!: ((K a :*!: K a) :*!: I :*!: I :*!: I)
type EditDistL a = (K [a] :*!: K [a]) :*!: (K One :+!: I)

-- | The edit distance algorithm as an hylomorphism.
editdistHylo :: Eq a => ([a],[a]) -> Int
editdistHylo (x::([a],[a])) = hylo (ann::Ann (EditDist a)) g h x
   where g :: Eq a => F (EditDist a) Int -> Int
         g = length \/ g'
         g' ((a,b),(x1,(x2,x3))) = min m1 (min m2 m3)
            where m1 = succ x1
                  m2 = succ x2
                  m3 = add (x3,if a==b then 0 else 1)
         h ([],bs) = Left bs
         h (as,[]) = Left as
         h (a:as,b:bs) = Right ((a,b),((as,b:bs),((a:as,bs),(as,bs))))

-- | The edit distance algorithm as a dynamorphism.
editDistDyna :: Eq a => ([a],[a]) -> Int
editDistDyna (l1::[a],l2) = dyna (ann :: Ann (EditDistL a)) (g . o (length l1)) (h l1) (l1,l2)
   where g :: Eq a => F (EditDist a) Int -> Int
         g = length \/ g'
         g' ((a,b),(x1,(x2,x3))) = min m1 (min m2 m3)
            where m1 = succ x1
                  m2 = succ x2
                  m3 = add (x3,if a==b then 0 else 1)
         o :: Int -> F (EditDistL a) (Histo (EditDistL a) Int) -> F (EditDist a) Int
         o n ((as,bs),Left _) = Left []
         o n (([],bs),Right x) = Left bs
         o n ((as,[]),Right x) = Left as
         o n ((a:as,b:bs),Right x) = Right ((a,b),(j x,(j (pi n x),j (pi (succ n) x))))
         h :: [a] -> ([a],[a]) -> F (EditDistL a) ([a],[a])
         h cs ([],[]) = (([],[]),Left _L)
         h cs ([],b:bs) = (([],b:bs),Right (cs,bs))
         h cs (a:as,bs) = ((a:as,bs),Right (as,bs))
         pi :: Int -> Histo (EditDistL a) Int -> Histo (EditDistL a) Int
         pi 0 x = x
         pi k x = case outr x of
            (_,Right y) -> pi (pred k) y
         j = outl

-- * Streams

-- | The fixpoint of the functor of streams.
type Stream a = K a :*!: I

-- | Stream head.
headS :: Stream a -> a
headS = fst . out

-- | Stream tail.
tailS :: Stream a -> Stream a
tailS = snd . out

-- | Definition of a stream sequence generator as an anamorphism. 
generate :: Int -> Stream Int
generate = ana (ann::Ann(Stream a)) (id /\ succ)

-- | Identity o streams as an anamorphism.
idStream :: Stream a -> Stream a
idStream = ana (ann::Ann (Stream a)) out

-- | Mapping over streams as an anamorphism.
mapStream :: (a -> b) -> Stream a -> Stream b
mapStream f = ana (ann::Ann (Stream b)) g 
    where g = (f >< id) . out

-- | Malcolm downwards accumulations on streams.
malcolmS :: ((b,a) -> a) -> a -> Stream b -> Stream a
malcolmS o e = mapStream (cata (ann::Ann [b]) ((e!) \/ o)) . malcolmSAna' cons . (id /\ nil . bang)

-- | Malcom downwards accumulations on streams as an anamorphism.
malcolmSAna :: ((b,a) -> a) -> a -> Stream b -> Stream a
malcolmSAna o e = malcolmSAna' o . (id /\ (e!))

-- | Uncurried version of Malcom downwards accumulations on streams as an anamorphism.
malcolmSAna' :: ((b,a) -> a) -> (Stream b, a) -> Stream a
malcolmSAna' o = ana (ann::Ann (Stream a)) g
    where g = snd /\ swap . (o >< id) . assocl . (id >< swap) . assocr . (out >< id)

-- | Promotes streams elements to streams of singleton elements.
inits :: Stream a -> Stream [a]
inits = malcolmSAna' cons . (id /\ nil . bang)

-- | Definition of parwise exchange on streams as a futumorphism.
exchFutu :: Stream a -> Stream a
exchFutu = futu (ann::Ann (Stream a)) (f /\ (g . (h /\ i)))
   where f = headS . tailS
         g = innr
         h = headS
         i = innl . tailS . tailS

-- * Binary Tree

-- | Datatype declaration of a binary tree.
data Tree a = Empty | Node a (Tree a) (Tree a) deriving Show

-- | The functor of a binary tree.
type instance PF (Tree a) = Const One :+: (Const a :*: (Id :*: Id))

instance Mu (Tree a) where
   inn (Left _) = Empty
   inn (Right (a,(b,c))) = Node a b c
   out Empty = Left _L
   out (Node a b c) = Right (a,(b,c))

-- | Counting the number of leaves in a binary tree as a catamorphism.
nleaves :: Tree a -> Int
nleaves = cata (ann::Ann (Tree a)) f
    where f = (1!) \/ (add . snd)

-- | Counting the number of nodes in a binary tree as a catamorphism.
nnodes :: Tree a -> Int
nnodes = cata (ann::Ann (Tree a)) f
    where f = (0!) \/ (succ . add . snd)

-- | Generation of a binary tree with a specified height as an anamorphism.
genTree :: Int -> Tree Int
genTree = ana (ann::Ann (Tree Int)) f
    where f = (bang -|- (id /\ (pred /\ pred))) . ((==0)?)

-- | The preorder traversal on binary trees as a catamorphism.
preTree :: Tree a -> [a]
preTree = cata (ann::Ann (Tree a)) f
    where f = ([]!) \/ (cons . (id >< cat))

-- | The postorder traversal on binary trees as a catamorphism.
postTree :: Tree a -> [a]
postTree = cata (ann::Ann (Tree a)) f
    where f = ([]!) \/ (cat . swap . (wrap >< cat))

-- * Leaf Trees

-- | Datatype declaration of a leaf tree.
data LTree a = Leaf a | Branch (LTree a) (LTree a) deriving (Eq,Show)

-- | The functor of a leaf tree.
type instance PF (LTree a) = Const a :+: (Id :*: Id)

instance Mu (LTree a) where
   inn (Left x) = Leaf x
   inn (Right (x,y)) = Branch x y
   out (Leaf x) = Left x
   out (Branch x y) = Right (x,y)

-- | Extract the leaves of a leaf tree as a catamorphism.
leaves :: LTree a -> [a]
leaves = cata (ann::Ann (LTree a)) f
    where f = wrap \/ cat

-- | Generation of a leaft tree of a specified height as an anamorphism.
genLTree :: Int -> LTree Int
genLTree = ana (ann::Ann (LTree Int)) f
    where f = ((0!) -|- (id /\ id)) . out

-- | Calculate the height of a leaf tree as a catamorphism.
height :: LTree a -> Int
height = cata (ann::Ann (LTree a)) f
    where f = (0!) \/ (succ . uncurry max)

-- * Rose Trees

-- | Datatype declaration of a rose tree.
data Rose a = Forest a [Rose a] deriving Show

-- | The functor of a rose tree.
type instance PF (Rose a) = Const a :*: ([] :@: Id)

instance Mu (Rose a) where
   inn (a,l) = Forest a l
   out (Forest a l) = (a,l)

--	 The preorder traversal on rose trees as a catamorphism.
preRose :: Rose a -> [a]
preRose = cata (ann ::Ann (Rose a)) f
   where f = (cons . (id >< concat))

-- | The postorder traversal on rose trees as a catamorphism.
postRose :: Rose a -> [a]
postRose = cata (ann ::Ann (Rose a)) f
   where f = cat . swap . (wrap >< cata (ann::Ann [[a]]) (nil \/ cat))

-- | Generation of a rose tree of a specified height as an anamorphism.
genRose :: Int -> Rose Int
genRose = ana (ann ::Ann (Rose Int)) f
   where f = ((id /\ ([]!)) \/ (id /\ downtoAna . pred)) . ((==0)?)



















-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Relation.Examples.E02
-- Copyright   :  (c) DD.  2012
--                (c) LFL. 2009
-- License     :  BSD-style
-- Maintainer  :  Drew Day<drewday@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
--
module Data.Relation.Examples.E02 where 

import           Data.Relation 
import qualified Data.Set      as S
import           Text.Groom


-- | 
--
-- Documentation Tests
--
-- All examples in this module are tested automatically with Doctest, and pretty printed with "Text.Groom".
-- 
-- This output is provided as proof of the correctness of the REPL (@>>>@) text:
--
-- @
--   There are 12 tests, with 12 total interactions.
--   Examples: 12  Tried: 12  Errors: 0  Failures: 0
-- @



p f = putStrLn $ groom $ f

-- | Example 2:
--
-- A student x can take n classes.
--
-- * Each student must take at least 1 class
--
-- * Each class must have at least one student.

e :: Relation [Char] [Char]
e =  fromList 
         [ ("Rebeca" , "History"        )
         , ("Rebeca" , "Mathematics"    )
         , ("Rolando", "Religion"       )
         , ("Rolando", "Comunication"   )
         , ("Teresa" , "Religion"       )
         , ("Teresa" , "Architecture"   )
         , ("Antonio", "History"        )
         ]

-- ^
-- >>> p e
-- Relation{domain =
--            fromList
--              [("Antonio", fromList ["History"]),
--               ("Rebeca", fromList ["History", "Mathematics"]),
--               ("Rolando", fromList ["Comunication", "Religion"]),
--               ("Teresa", fromList ["Architecture", "Religion"])],
--          range =
--            fromList
--              [("Architecture", fromList ["Teresa"]),
--               ("Comunication", fromList ["Rolando"]),
--               ("History", fromList ["Antonio", "Rebeca"]),
--               ("Mathematics", fromList ["Rebeca"]),
--               ("Religion", fromList ["Rolando", "Teresa"])]}

-------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------

rebecaE :: S.Set [Char]
rebecaE = (S.singleton "Rebeca" |$> ran e) e 
-- ^
-- >>> p rebecaE
-- fromList ["History", "Mathematics"]

takingreligion :: S.Set [Char]
takingreligion = (dom e <$| S.singleton "Religion") e
-- ^
-- >>> p takingreligion
-- fromList ["Rolando", "Teresa"]


-- others courses for those taking religion
others :: S.Set [Char]
others   =  (takingreligion |$> ran e) e
-- ^
-- >>> p others
-- fromList ["Architecture", "Comunication", "Religion"]
--




test1 :: Bool
test1 =  (takingreligion <$| ran e) e == takingreligion
--
-- ^
-- >>> p test1
-- True

-- Exploring |> 
--
takingreligion2 :: Relation [Char] [Char]
takingreligion2 = e |> S.singleton "Religion"
-- ^
-- >>> p takingreligion2
-- Relation{domain =
--            fromList
--              [("Rolando", fromList ["Religion"]),
--               ("Teresa", fromList ["Religion"])],
--          range = fromList [("Religion", fromList ["Rolando", "Teresa"])]}


twoStudents = (<|) (S.union (S.singleton "Rolando") (S.singleton "Teresa")) e
-- ^
-- >>> p $ twoStudents
-- Relation{domain =
--            fromList
--              [("Rolando", fromList ["Comunication", "Religion"]),
--               ("Teresa", fromList ["Architecture", "Religion"])],
--          range =
--            fromList
--              [("Architecture", fromList ["Teresa"]),
--               ("Comunication", fromList ["Rolando"]),
--               ("Religion", fromList ["Rolando", "Teresa"])]}

-- ^
-- >>> p $ (|$>) (S.union (S.singleton "Rolando") (S.singleton "Teresa")) (ran e) e
-- fromList ["Architecture", "Comunication", "Religion"]

id1, id2, id3, id4 :: S.Set [Char] -> (Bool, S.Set [Char])


id1 s =  ( v1 == v2, v1 )
    where
    v1 =  (dom  e |$> s) e
    v2 =   ran (e |>  s)
   

id2 s = ( v1 == v2, v1 )
    where
    v1 =  (dom  e <$| s) e
    v2 =   dom (e |>  s) 


-- Exploring <|

id3 s = ( v1 == v2, v1 )
    where
    v1 =  (s       <$| ran e) e
    v2 =  dom (s <|  e)


id4 s = ( v1 == v2, v2 )
    where
    v1 =  (s       |$> ran e) e
    v2 =  ran (s <|  e)


religion  :: S.Set [Char]
religion  = S.singleton "Religion"  -- has students

teresa    :: S.Set [Char]
teresa    = S.singleton "Teresa" -- enrolled

--
-- ^
-- >>> p religion
-- fromList ["Religion"]


t11, t12, t13, t14 :: (Bool, S.Set [Char])

t11 = id1 religion 
--
-- ^
-- >>> p t11
-- (True, fromList ["Religion"])

t12 = id2 religion 
--
-- ^
-- >>> p t12
-- (True, fromList ["Rolando", "Teresa"])


t13 = id3 teresa 
--
-- ^
-- >>> p t13
-- (True, fromList ["Teresa"])

t14 = id4 teresa 
--
-- ^
-- >>> p t14
-- (True, fromList ["Architecture", "Religion"])


id1R, id2R 
 :: (Ord a, Ord b) => S.Set b -> Relation a b -> Bool

id3R , id4R
 :: (Ord a, Ord b) => S.Set a -> Relation a b -> Bool

id1R s r = (dom r |$> s) r == ran (r |>  s)
id2R s r = (dom r <$| s) r == dom (r |>  s) 
id3R s r = (s <$| ran r) r == dom (s <| r)
id4R s r = (s |$> ran r) r == ran (s <| r)

testAll :: Bool
testAll     = all id  [ id1R religion e
                      , id2R religion e
                      , id3R teresa   e
                      , id4R teresa   e
                      ]
-- ^
-- >>> p testAll
-- True


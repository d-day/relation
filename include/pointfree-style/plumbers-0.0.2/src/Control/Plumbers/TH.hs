-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Plumbers.TH
-- Copyright   :  (c) 2012 Michael Sloan 
-- License     :  BSD-style (see the LICENSE file)
-- Maintainer  :  Michael Sloan <mgsloan@gmail.com>
-- Stability   :  experimental
-- Portability :  GHC only
--
-- This module is used to generate operators that follow the plumbers symbolic
-- convention for routing parameters.
--
-----------------------------------------------------------------------------
module Control.Plumbers.TH
  ( PlumberSpec (..), baseSpec
  , PlumberTypes(..), baseTypes
  , implementPlumbers, implementPlumber
  , operatorNames, aritiesString

  -- * TH Utilities
  , appsT, arrowsT, tuplesT
  , mkVE, mkVP, mkVT, mkVB
  , addForalls
  ) where

import Control.Applicative ((<$>))
import Data.Bits (testBit)
import Data.List (intersperse)
import Language.Haskell.TH

-- | Specifies all of the information needed to construct type declarations
--   for the plumber.
data PlumberTypes = PlumberTypes
 { leftType   :: Type  -- ^ Type of the left argument's result
 , rightType  :: Type  -- ^ Type of the right argument's result
 , resultType :: Type  -- ^ Results type.  This needs to be wrapped in a
                       --   forall naming all of the utilized type variables.
 }

-- | A basic set of types, which make r' the left type, and r'' the right type.
--   The resultType is a forall that introduces these type variables, and has 
--   undefined content.  Therefore any implementation in terms of baseTypes
--   needs to redefine resultType, as the Forall has undefined as its content.
baseTypes :: PlumberTypes
baseTypes = PlumberTypes
  { leftType   = mkVT "r'"
  , rightType  = mkVT "r''"
  , resultType = ForallT [mkVB "r'", mkVB "r''"] [] undefined
  }

-- | Specifies all of the information needed to implement a plumber.
data PlumberSpec = PlumberSpec
 { plumberOpE     :: Exp -> Exp -> Exp  -- ^ The plumber implementation
 , plumberTypes   :: Maybe PlumberTypes -- ^ Optional explicit type signatures
 , plumberArities :: [Int]              -- ^ Arities to generate - 26 is max
 , plumberPrefix  :: String             -- ^ Prefix to use for operator
 }

-- | Creates a plumber spec for the given prefix for the generated operators,
--   and the name of the infix operator to use to construct the implementation.
baseSpec :: String -> String -> PlumberSpec
baseSpec p e = PlumberSpec
  { plumberOpE      = (\l r -> InfixE (Just l) (mkVE e) (Just r))
  , plumberTypes    = Nothing
  , plumberArities  = [1..3]
  , plumberPrefix   = p
  }

-- | All of the operator names that the given PlumberSpec would implement.
operatorNames :: PlumberSpec -> [[String]]
operatorNames s
  = map (map (plumberPrefix s ++) . sequence . (`replicate` "^<>&*"))
  $ plumberArities s

-- | For now this is just a string-yielding function, to be evaluated by the
--   user, to generate the line defining the fixities.  This code should be
--   pasted below the TH invocation of implementPlumbers
aritiesString :: PlumberSpec -> String
aritiesString
  = unlines
  . map (("infixr 9 "++) . concat . intersperse ", ")
  . operatorNames

-- | Implements all of the plumbers specified by the given @PlumberSpec@.
implementPlumbers :: PlumberSpec -> DecsQ
implementPlumbers spec
  = concat <$> mapM (implementPlumber spec)
                    (concat $ operatorNames spec)

-- | Implement only the specific plumber requested.
implementPlumber :: PlumberSpec -> String -> DecsQ
implementPlumber spec name
  = return $ maybe [] ((:[]) . sig) (plumberTypes spec) ++ [func] 
 where
  directives :: [(Int, Either String (String, String))]
  directives = rec dirs (map (:[]) ['a'..'z'])
   where
    dirs = drop (length $ plumberPrefix spec) name
    rec [] _ = []
    rec ('^':xs) (y  :ys) = (0, Left y)       : rec xs ys
    rec ('<':xs) (y  :ys) = (1, Left y)       : rec xs ys
    rec ('>':xs) (y  :ys) = (2, Left y)       : rec xs ys
    rec ('&':xs) (y  :ys) = (3, Left y)       : rec xs ys
    rec ('*':xs) (y:z:ys) = (3, Right (y, z)) : rec xs ys

  params = map snd directives
  names = concatMap (either (:[]) (\(y, z) -> [y, z])) params
  args1 = [either id fst x | (i, x) <- directives, testBit i 0]
  args2 = [either id snd x | (i, x) <- directives, testBit i 1]

  sig types
    = SigD (mkName name)
    . ForallT (map mkVB names ++ bs) ctx
    . arrowsT
    $ [ arrowsT $ map mkVT args1 ++ [leftType  types]
      , arrowsT $ map mkVT args2 ++ [rightType types] ]
      ++ map mkTyp params
      ++ [rt]
   where
    (ForallT bs ctx rt) = resultType types

  mkTyp (Right (a, b)) = tuplesT [mkVT a, mkVT b]
  mkTyp (Left a) = mkVT a

  func = FunD (mkName name) [Clause binds (NormalB body) []]

  binds = map mkVP ["f1", "f2"] ++ map mkBind directives
  mkBind (0, _) = WildP
  mkBind (_, Left a) = mkVP a
  mkBind (_, Right (a, b)) = TupP [mkVP a, mkVP b]

  body = plumberOpE spec (mkF "f1" args1) (mkF "f2" args2)
  mkF n = foldl1 AppE . (mkVE n:) . map mkVE

-- * Template Haskell Utilities

-- TODO: consider whether tricks like http://hpaste.org/54367 could aid this

-- TODO: domain-generic construction methods for TH. E.g. have a "var" function
-- that is polymorphic on return type.

appsT, arrowsT, tuplesT :: [Type] -> Type
appsT = foldl1 AppT
arrowsT = foldr1 (\x y -> appsT [ArrowT, x, y])
tuplesT xs = appsT $ [TupleT $ length xs] ++ xs

mkVE :: String -> Exp
mkVE = VarE . mkName
mkVP :: String -> Pat
mkVP = VarP . mkName
mkVT :: String -> Type
mkVT = VarT . mkName
mkVB :: String -> TyVarBndr
mkVB = PlainTV . mkName

addForalls :: Type -> Type -> Type
addForalls (ForallT b c _) (ForallT b' c' t) = ForallT (b ++ b') (c ++ c') t
addForalls (ForallT b c _) x = ForallT b c x
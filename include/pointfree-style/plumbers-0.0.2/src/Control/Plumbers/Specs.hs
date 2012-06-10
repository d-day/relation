-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Plumbers.Specs
-- Copyright   :  (c) 2012 Michael Sloan 
-- License     :  BSD-style (see the LICENSE file)
-- Maintainer  :  Michael Sloan <mgsloan@gmail.com>
-- Stability   :  experimental
-- Portability :  GHC only
--
-- This module defines the specifications used by "Control.Plumbers" and
-- "Control.Plumbers.Monad".  These need to be defined in a separate module 
-- in order to handle GHC Template Haskell staging restrictions.
--
-----------------------------------------------------------------------------
module Control.Plumbers.Specs where

import Control.Plumbers.TH

import Language.Haskell.TH
  (Exp(TupE), Type(AppT, ForallT), Pred(ClassP), mkName)

productSpec :: PlumberSpec
productSpec     = (baseSpec "*" "_") { plumberTypes = Just productTypes
                                     , plumberOpE   = (\l r -> TupE [l, r]) }

compositionSpec :: PlumberSpec
compositionSpec = (baseSpec "$" "$") { plumberTypes = Just compositionTypes }

lbindSpec  :: PlumberSpec
lbindSpec  = (baseSpec "<=" "=<<")   { plumberTypes = Just lbindTypes }

rbindSpec  :: PlumberSpec
rbindSpec  = (baseSpec ">=" ">>=")   { plumberTypes = Just rbindTypes }

frbindSpec :: PlumberSpec
frbindSpec = (baseSpec ">>" ">>")    { plumberTypes = Just $ fbindTypes False }

flbindSpec :: PlumberSpec
flbindSpec = (baseSpec "<<" "<<")    { plumberTypes = Just $ fbindTypes True  }

productTypes :: PlumberTypes
productTypes = addBaseContext $ baseTypes 
  { resultType = tuplesT [leftType baseTypes, rightType baseTypes] }

compositionTypes :: PlumberTypes
compositionTypes = addBaseContext $ baseTypes 
  { leftType   = arrowsT [rightType baseTypes, leftType baseTypes]
  , resultType = leftType baseTypes
  }

lbindTypes :: PlumberTypes
lbindTypes = addBaseContext . addMonadContext $ baseTypes
  { leftType   = arrowsT [rightType baseTypes, result]
  , rightType  = AppT m $ rightType baseTypes
  , resultType = result
  }
 where
  m = mkVT "m"
  result = AppT m $ leftType baseTypes

rbindTypes :: PlumberTypes
rbindTypes = baseTypes
  { leftType   = rightType  lbindTypes
  , rightType  = leftType   lbindTypes
  , resultType = resultType lbindTypes
  }

fbindTypes :: Bool -> PlumberTypes
fbindTypes b = addMonadContext . addBaseContext $ baseTypes
  { leftType   = AppT m $ leftType   baseTypes
  , rightType  = AppT m $ rightType  baseTypes
  , resultType = AppT m $ (if b then leftType else rightType) baseTypes
  }
 where
  m = mkVT "m"

addMonadContext x = x { resultType = addForalls mforall               $ resultType x }
 where
  m = mkVT "m"
  mforall = (ForallT [mkVB "m"] [ClassP (mkName "Monad") [m]] undefined)

addBaseContext x = x { resultType = addForalls (resultType baseTypes) $ resultType x }
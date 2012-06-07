------------------------------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Copyright   :  (c) Drew Day 2012
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Drew Day <drewday@gmail.com>
-- Stability   :  stable
-- Portability :  portable
--
------------------------------------------------------------------------------------------------
module Main where

import Test.DocTest

main :: IO ()
main = doctest [
                 "--optghc=-packageghc"
               , "--optghc=-isrc"
               , "--optghc=-idist/build/autogen/"
               , "--optghc=-optP-include"
               , "--optghc=-optPdist/build/autogen/cabal_macros.h"
               , "src/Data/Relation.hs"
--             , "src/Data/Relation/Examples/E01.hs"
               , "src/Data/Relation/Examples/E02.hs"
               ]


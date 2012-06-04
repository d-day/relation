-- | Leonel Fonseca. 2010/nov/14.
--   Dull test module.

module T01_Relacion 

where

import qualified Data.Relacion as R
import qualified Data.Set      as S
import qualified Data.Map      as M
import           Data.Maybe (fromMaybe)

x1 ::  [(Int, String)]
x1 =   [ (1, "a"), (1, "b"), (1, "c"), (2, "c")
       , (2, "f"), (2, "g"), (1, "d") 
       ]


r01 = R.fromList x1      -- construye a partir de una lista.
r02 = R.empty            -- construye una relación vacía.
r03 = R.singleton 2 "c"  -- construye una relación unitaria.
r04 = R.singleton 3 "i"
r05 = R.insert 3 "i" r03

t01 r = putStrLn $
           "size = " ++ (show $ R.size r)
        ++ (if  x1 == R.toList r01
                then  "\ntoList funciona como identidad "
                else  "\ntoList no converge ")
        ++ (if  (r02 `R.union` r01 == r01 `R.union` r02)
                then  "\nunion tiene elemento neutro"
                else  "\nunion no converge")
        

r06 = R.unions [r01, r02, r03, r04]
r07 = r01 `R.union` r04
                         -- Concatena una lista de relaciones
t02 = if  r06 == r07 
          then  "unions ok"
          else  "unions falla"

t03 = if  R.null r02 &&  (not . R.null) r01
          then "null ok"
          else "null incorrecto"


-- genera un producto cartesiano entre 
-- el dominio a asociado al N 
-- y el rango asociado a C.
-- Luego para cada elemento del producto cartesiano,
-- indica si ese par existe en la relación r01.

t04 n c =  map mem drive
          
    where
 
    mem = \(x,y) ->  (x, y, R.member x y r01)

    -- proyecta y de (1,y)        
    dom = S.toList . fromMaybe S.empty $ R.lookupDom n r01

    -- proyecta x de (x,"c")
    ran = S.toList . fromMaybe S.empty $ R.lookupRan c r01 

    -- recombinarlos dominios y rangos de parejas
    -- distintas produce pares que antes no existían.
    drive = [ (x,y) | x <- ran, y <- dom ]


    -- otra versión
t04b n c =  map mem drive
          
    where
 
    mem = \(x,y) ->  (x, y, R.member x y r01)

    -- proyecta y de (1,y)        
    dom = S.toList . fromMaybe S.empty $ R.lookupDom n r01

    -- proyecta x de (x,"c")
    ran = S.toList . fromMaybe S.empty $ R.lookupRan c r01 

    -- recombinarlos dominios y rangos de parejas
    -- distintas produce pares que antes no existían.
    drive = [ (x,y) | x <- ran, y <- dom ]

t05 = R.member 2 "c" r01

r08 = R.delete 1 "a" $ 
      R.delete 1 "b" $
      R.delete 1 "d" $
      r01

t06 = (R.dom r01) R.<$| (R.ran r01) $ r01

t07 = (R.dom r01) R.|$> (R.ran r01) $ r01

t09 = (R.dom r01) R.<$| (R.ran r08) $ r01 -- usando r08

t10 = (S.singleton 1) R.|$> (R.ran r01)  $ r01

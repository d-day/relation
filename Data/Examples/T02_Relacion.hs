-- | Leonel Fonseca. 2010/nov/14.
--   Test module showing how to use Data.Relacion.

module T02_Relacion where 

import           Data.Relacion 
import qualified Data.Set      as S

-- | Para estar en la relación lleva
--  - Un estudiante lleva al menos una materia.
--  - Una materia al menos es llevada por un estudiante.

lleva =  fromList 
         [ ("Rebeca" , "Historia"    )
         , ("Rebeca" , "Matemática"  )
         , ("Rolando", "Religión"    )
         , ("Rolando", "Comunicación")
         , ("Teresa" , "Religión"    )
         , ("Teresa" , "Arquitectura")
         , ("Antonio", "Historia"    )
         ]

rebecaLleva = (S.singleton "Rebeca" |$> ran lleva) lleva 

llevanReligión = (dom lleva <$| S.singleton "Religión") lleva

-- otros cursos para aquellos que llevan Religión
otros   =  (llevanReligión |$> ran lleva) lleva

prueba1 =  (llevanReligión <$| ran lleva) lleva == llevanReligión

-- Explorando |> 

llevanReligión2 = lleva |> S.singleton "Religión"

identidad1 s =  ( v1 == v2, v1 )
    where
    v1 =  (dom  lleva |$> s) lleva
    v2 =   ran (lleva |>  s)
   

identidad2 s = ( v1 == v2, v1 )
    where
    v1 =  (dom  lleva <$| s) lleva
    v2 =   dom (lleva |>  s) 


-- Explorando <|

identidad3 s = ( v1 == v2, v1 )
    where
    v1 =  (s       <$| ran lleva) lleva
    v2 =  dom (s <|  lleva)


identidad4 s = ( v1 == v2, v2 )
    where
    v1 =  (s       |$> ran lleva) lleva
    v2 =  ran (s <|  lleva)


religión = S.singleton "Religión"

t11 = identidad1 religión 

t12 = identidad2 religión 

teresa = S.singleton "Teresa"

t13 = identidad3 teresa 

t14 = identidad4 teresa 


identidad1R, identidad2R 
 :: (Ord a, Ord b) => S.Set b -> Relación a b -> Bool

identidad3R , identidad4R
 :: (Ord a, Ord b) => S.Set a -> Relación a b -> Bool

identidad1R s r = (dom r |$> s) r == ran (r |>  s)
identidad2R s r = (dom r <$| s) r == dom (r |>  s) 
identidad3R s r = (s <$| ran r) r == dom (s <| r)
identidad4R s r = (s |$> ran r) r == ran (s <| r)

probarTodas = all id  [ identidad1R religión lleva
                      , identidad2R religión lleva
                      , identidad3R teresa   lleva
                      , identidad4R teresa   lleva
                      ]

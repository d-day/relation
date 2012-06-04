{- | 
    El contenedor Relación modela asociaciones dos elementos.
    Ofrece búsqueda eficiente por cualquiera de los dos elementos. 

    Es similar a Data.Map en que asocia llaves (k) con valores (v).
  
    A diferencia del contenedor Data.Map, un elemento 
    puede estar asociado más de una vez.   
    
    Los dos propósito fundamentales de esta estructura son
    
    1. Asociar elementos.
    2. Ofrecer eficiencia en búsquedas por cualquiera de los 
       dos elementos.
    
    Como no están implementados ni map ni fold, debe convertir
    la estructura en una lista para procesarla secuencialmente.
-}     

{-
    2009/11/09. LFL. Se corrige la definición de delete.

    2009/11/26. LFL. Construcción
-}


module Data.Relacion (

   -- * El tipo @Relación@

   Relación ()  

   -- *  Funcionalidad provista:
 
   -- ** Consultas

 , size         --  Tuplas en la relación.
 , null         --  Esta vacía?

   -- ** Construcción

 , empty        --  Construya una relación vacía.
 , fromList     --  Construya una relación de una lista.
 , singleton    --  Construya una relación unitaria.

   -- ** Operaciones 

 , union        --  Una dos relaciones.
 , unions       --  Concatene una lista de relaciones.
 , insert       --  Inserte una tupla en la relación.
 , delete       --  Elimine una tupla de la relación.
   -- El conjunto con los valores asociados a un valor del dominio.
 , lookupDom     
   -- El conjunto con los valores asociados a un valor del rango.
 , lookupRan    
 , memberDom    --  Pertenece el elemento al dominio?
 , memberRan    --  Pertenece el elemento al rango?
 , member       --  Pertenece la tupla a la relación?
 , notMember    
 
   -- ** Conversión

 , toList       --  Construya una lista de una relación.
   --  Extrae los elementos del dominio a un conjunto. 
 , dom          
   --  Extrae los elementos del rango a un conjunto. 
 , ran

   -- ** Utilitarios

 , compactarSet --  Compacta un conjunto de Maybe's.
   
 , (|$>) -- restringe rango según subconjunto. PICA.
  
 , (<$|) -- restringe dominio según subconjunto. PICA.

 , (<|)  -- restricción de dominio. Z.

 , (|>)  -- restricción de rango. z.

)

where

import           Prelude           hiding (null)
import qualified Data.Map     as M
import qualified Data.Set     as S
import           Data.Maybe        (isJust, fromJust, fromMaybe)


{-
   La implementación no usa S.Set (a,b) porque es necesario
   poder buscar un elemento sin conocer el otro.
   Con Set, la búsqueda es con la función member y hay que
   conocer ambos valores.

   Hay dos mapas que deben ser actualizados de manera coordinada.

   Siempre hay que tener cuidado con el conjunto asociado por
   la llave. Si hay una unión de relaciones, hay que aplicar
   unión al conjunto de valores.
   Si hay una resta hay que manipular en la forma el conjunto 
   de valores.

   Como es multi-mapa una llave k puede tener asociada
   un conjunto de valores v.
   No permitimos la asociación k con un conjunto vacío.
-}
data Relación a b  = Relación { dominio ::  M.Map a (S.Set b)
                              , rango   ::  M.Map b (S.Set a)
                              }

    deriving (Show, Eq, Ord)
    

-- * Funciones sobre relaciones


--  El tamaño es calculado usando el dominio.
-- |  @size r@ devuelve la cantidad de tuplas en la relación.

size    ::  Relación a b -> Int
size r  =   M.fold ((+) . S.size) 0 (dominio r)



-- | Construye una relación sin elementos.

empty   ::  Relación a b 
empty   =   Relación M.empty M.empty


  
-- |
-- La lista debe tener formato [(k1, v1), (k2, v2),..,(kn, vn)].

fromList    ::  (Ord a, Ord b) => [(a, b)] -> Relación a b
fromList xs =
    Relación 
        { dominio =  M.fromListWith S.union $ snd2Set    xs
        , rango   =  M.fromListWith S.union $ flipAndSet xs
        } 
    where  
       snd2Set    = map ( \(x,y) -> (x, S.singleton y) ) 
       flipAndSet = map ( \(x,y) -> (y, S.singleton x) )



toList   ::  Relación a b -> [(a,b)]
toList r =   concatMap
               ( \(x,y) -> zip (repeat x) (S.toList y) )
               ( M.toList . dominio $ r)
  
  

-- | 
-- Construye una relación compuesta por la asociación de @x@ y @y@.

singleton      ::  a -> b -> Relación a b
singleton x y  =   Relación 
                     { dominio = M.singleton x (S.singleton y) 
                     , rango   = M.singleton y (S.singleton x)
                     }



-- | La relación que resulta de unir dos relaciones @r@ y @s@.

union ::  (Ord a, Ord b) 
      =>  Relación a b -> Relación a b -> Relación a b

union r s       =  
    Relación 
      { dominio =  M.unionWith S.union (dominio r) (dominio s)
      , rango   =  M.unionWith S.union (rango   r) (rango   s)
      }


---------------------------------------------------------------
{- Este fragmento proviene de:
    -- Module      :  Data.Map
    -- Copyright   :  (c) Daan Leijen 2002
    --                (c) Andriy Palamarchuk 2008
    -- License     :  BSD-style
    -- Maintainer  :  libraries@haskell.org
    -- Stability   :  provisional
    -- Portability :  portable
 -} 
foldlStrict         ::  (a -> b -> a) -> a -> [b] -> a
foldlStrict f z xs  =   case xs of
      []     -> z
      (x:xx) -> let z' = f z x in seq z' (foldlStrict f z' xx)
---------------------------------------------------------------



-- | Concatena una lista de relaciones en una sola relación.

unions       ::  (Ord a, Ord b) => [Relación a b] -> Relación a b

unions       =   foldlStrict union empty



-- | Inserta la asociación entre @ x @ y @ y @ en la relación @ r @

insert       ::  (Ord a, Ord b) 
             =>  a -> b -> Relación a b -> Relación a b

insert x y r =  -- r { dominio = dominio', rango = rango' } 
                Relación dominio' rango'
  where 
   dominio'  =  M.insertWith S.union x (S.singleton y) (dominio r)
   rango'    =  M.insertWith S.union y (S.singleton x) (rango   r)


{- 
   El borrado no es difícil pero es delicado.
   r = { dominio {  (k1, {v1a, v3})
                 ,  (k2, {v2a})
                 ,  (k3, {v3b, v3})
                 }
       , rango   {  (v1a, {k1}
                 ,  (v2a, {k2{
                 ,  (v3 , {k1, k3}
                 ,  (v3b, {k3}
                 }
      }

   Para borrar (k,v) de la relación haga:
    1. Trabajando sobre el dominio:
       1a. Borre v del conjunto VS asociado con k.
       1b. Si VS es vacío, elimine k del dominio.
    2. Trabajando sobre el rango:
       2a. Borre k del conjunto VS asociado con v
       2b. Si VS es vacío, elimine v del rango. 
         
-}

-- |  Remueve una asociación de la relación.
delete       ::  (Ord a, Ord b) 
             =>  a -> b -> Relación a b -> Relación a b

delete x y r  =  r { dominio = dominio', rango = rango' } 
   where 
   dominio'   =  M.update (borrar y) x (dominio r)
   rango'     =  M.update (borrar x) y (rango   r)
   borrar e s =  if  S.singleton e == s
                     then  Nothing
                     else  Just $ S.delete e s
  
-- | El conjunto de valores asociados a un valor del dominio.

lookupDom     ::  Ord a =>  a -> Relación a b -> Maybe (S.Set b)
lookupDom x r =   M.lookup  x  (dominio r)



-- | El conjunto de valores asociados a un valor del rango.

lookupRan     ::  Ord b =>  b -> Relación a b -> Maybe (S.Set a)
lookupRan y r =   M.lookup  y  (rango   r)



-- | True si el elemento @ x @ pertenece al dominio de @ r @.

memberDom     ::  Ord a =>  a -> Relación a b -> Bool
memberDom x r =   isJust $ lookupDom x r



-- | True si el elemento pertenece al rango.

memberRan     ::  Ord b =>  b -> Relación a b -> Bool
memberRan y r =   isJust $ lookupRan y r



-- | True si la relación está vacía.

-- Before 2010/11/09 null::Ord b =>  Relación a b -> Bool
null    ::  Relación a b -> Bool
null r  =   M.null $ dominio r  



-- | True si la relación contiene la asociación @x@ y @y@

member       ::  (Ord a, Ord b) =>  a -> b -> Relación a b -> Bool
member x y r =   case lookupDom x r of
                      Just s  ->  S.member y s
                      Nothing ->  False
    


-- | True si un par no pertenece a la relación

notMember       ::  (Ord a, Ord b) =>  a -> b -> Relación a b -> Bool
notMember x y r =   not $ member x y r



-- | Devuelve el dominio de la relación como un conjunto.

dom            ::  Relación a b -> S.Set a
dom r          =   M.keysSet (dominio r)



-- | Devuelve el rango de la relación como un conjunto.

ran            ::  Relación a b -> S.Set b
ran r          =   M.keysSet (rango   r)



{- |
    Compacta un conjunto de conjuntos cuyos valores que pueden ser 
    @Just (Set x)@ o @Nothing@.
    
    Los casos @Nothing@ son purgados.

    Es similar a @concat@.
-}
compactarSet ::  Ord a => S.Set (Maybe (S.Set a)) -> S.Set a

compactarSet =   S.fold ( S.union . fromMaybe S.empty ) S.empty



{- |
     Implementación primitiva para el operador de 
     selección a la izquierda o a la derecha. 
     
     PICA provee dos operadores |> y <|,
     respectivamente |$> y <$| en esta biblioteca, que trabajan
     sobre una Relación y OIS's. PICA expone los operadores
     definidos acá, para no romper con la abstracción del
     tipo de datos Relación y porque teniendo acceso a los
     componentes escondidos de Relación, es más eficiente
     la implementación de la operación de restricción.

    (a <$| b) r 

      se lee: por cada elemento @b@ del conjunto @B@,
              seleccione un elemento @a@ del conjunto @A@
              si @a@ está relacionado con @b@ en la relación @r@.

    (a |$> b) r

      se lee: por cada elemento @a@ del conjunto @A@, 
              seleccione un elemento @b@ del conjunto @B@
              si @a@ está relacionado con @b@ en la relación @r@.

    Con respecto a los operadores de restricción de dominio
    y restricción de rango del lenguaje Z que devuelven una relación,
    los descritos son diferentes y devuelven el dominio o el rango.
   

-}


(<$|)          ::  (Ord a, Ord b) 
               =>  S.Set a -> S.Set b -> Relación a b -> S.Set a

(as <$| bs) r  =   as `S.intersection` generarAS bs

    where  generarAS = compactarSet . S.map (`lookupRan` r) 
    
    -- Los sub-conjuntos del dominio (a) asociados con cada b,
    -- tal que b en B y b está en el rango de la relación.
    -- La expresión S.map retorna un conjunto de Either (S.Set a).


-- ( Caso a |> r b )

(|$>)          ::  (Ord a, Ord b) 
               =>  S.Set a -> S.Set b -> Relación a b -> S.Set b

(as |$> bs) r  =   bs `S.intersection`  generarBS as

    where  generarBS = compactarSet . S.map (`lookupDom` r) 



-- | Restricción de dominio para una relación. Modelado como en z.

(<|) :: (Ord a, Ord b) => S.Set a -> Relación a b  -> Relación a b

s <| r  =  fromList $ concatMap
               ( \(x,y) -> zip (repeat x) (S.toList y) )
               ( M.toList dominio' )
    where
    dominio'  =  M.unions . map filtrar . S.toList $ s
    filtrar x =  M.filterWithKey (\k _ -> k == x) dr
    dr        =  dominio r  -- just to memoize the value


-- | Restricción de rango para una relación. Modelado como en z.

(|>) :: (Ord a, Ord b) => Relación a b -> S.Set b -> Relación a b

r |> t =  fromList $ concatMap
               ( \(x,y) -> zip (S.toList y) (repeat x) )
               ( M.toList rango' )
    where
    rango'    =  M.unions . map filtrar . S.toList $ t
    filtrar x =  M.filterWithKey (\k _ -> k == x) rr
    rr        =  rango r   -- just to memoize the value


{- Note:
 
   As you have seen this implementation is expensive in terms
   of storage. Information is registered twice.
   For the operators |> and <| we follow a pattern used in
   the @fromList@ constructor and @toList@ flattener:
   It is enough to know one half of the Relation (the domain or
   the range) to create to other half.
   
-}


{- No implementadas

 
   filter :: (a -> b -> Bool) -> Relación a b -> Relación a b
   map
   difference

-}

--eof

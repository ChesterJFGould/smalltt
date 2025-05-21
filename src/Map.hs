module Map ( 
    Map
  , Map.empty
  , Map.insert
  , Map.lookup
  , LvlMap
  , emptyLvlMap
  , insertLvlMap
  , lookupLvlMap
) where

import Common

import qualified Data.Map as M
import qualified Data.IntMap as IM

newtype LvlMap v = LvlMap { unLvlMap :: IM.IntMap v }

emptyLvlMap :: LvlMap v
emptyLvlMap = LvlMap IM.empty

insertLvlMap :: Lvl -> v -> LvlMap v -> LvlMap v
insertLvlMap l v m = LvlMap (IM.insert (unLvl l) v (unLvlMap m))

lookupLvlMap :: Lvl -> LvlMap v -> v
lookupLvlMap l m = (IM.!) (unLvlMap m) (unLvl l)

type Map v = LvlMap v

empty :: Map v
empty = emptyLvlMap

insert :: Lvl -> v -> Map v -> Map v
insert = insertLvlMap

lookup :: Lvl -> Map v -> v
lookup = lookupLvlMap

module Map ( 
    Map
  , Map.empty
  , Map.insert
  , Map.lookup
) where

type Map k v = k -> v

empty :: v -> Map k v
empty v = \_ -> v

insert :: Eq k => k -> v -> Map k v -> Map k v
insert k v m k'
  | k == k' = v
  | otherwise = m k'

lookup :: Eq k => k -> Map k v -> v
lookup k m = m k

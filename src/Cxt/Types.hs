
module Cxt.Types where

import Common
import CoreTypes
import LvlSet (LvlSet(..))
import SymTable (SymTable(..))
import qualified Map as M

data Cxt = Cxt {
    lvl     :: Lvl           -- ^ Size of local context.
  , env     :: Env           -- ^ Local evaluation environment.
  , mask    :: LvlSet        -- ^ Masks bound vars in local context.
  , tbl     :: SymTable      -- ^ Symbol table for all names (top + local).
  , typ     :: M.Map Lvl GTy -- ^ Holds types for elaborated variables
  , topTyp  :: M.Map Lvl GTy -- ^ Holds types for elaborated top level variables
  , mcxt    :: MetaCxt       -- ^ Metacontext.
  , names   :: Names         -- ^ Compact list of local names, for error printing.
  , frz     :: MetaVar       -- ^ Every metavar smaller than frz is frozen.
  }

instance Show Cxt where
  show _ = "<cxt>"


module MetaCxt where

import qualified Data.Array.Dynamic.L as ADL
import qualified Data.Ref.F           as RF
import GHC.Exts

import LvlSet
import Common
import CoreTypes

--------------------------------------------------------------------------------

size :: MetaCxt -> IO Lvl
size ms = coerce <$> ADL.size ms
{-# inline size #-}

fresh :: MetaCxt -> GTy -> LvlSet -> IO Int
fresh ms ty mask = do
  x <- ADL.size ms
  ADL.push ms (Unsolved mask ty)
  pure x
{-# inlinable fresh #-}

read :: MetaCxt -> MetaVar -> IO MetaEntry
read ms x =  ADL.unsafeRead ms (coerce x)
{-# inline read #-}

solve :: MetaCxt -> MetaVar -> Tm -> Val -> IO ()
solve ms x t ~v =  do
  ADL.unsafeRead ms (coerce x) >>= \case
    Solved{} -> impossible
    Unsolved mask ty -> do
      ref <- RF.new (-1)
      ADL.write ms (coerce x) (Solved ref mask t v ty)
{-# inline solve #-}

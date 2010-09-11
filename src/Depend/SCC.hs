module Depend.SCC (sccs, SCC(..), compDefs) where

import Depend.DFS
import Depend.FVs
-- import Depend.FVs_Data()
-- import Depend.FVs_AST()
-- import Depend.FVs_SIL()

import Data.Array(array)
import Data.List(findIndex)
import Data.Maybe(catMaybes)
import qualified Data.Set as Set


sccs   :: (Ord name, FVs decl name, Defs decl name) => [decl] -> [SCC decl]
sccs ds = map (fmap (ds !!)) (scc graph)
  where
  defines       = map defs ds
  whoDefines x  = findIndex (x `Set.member`) defines
  dependsOn d   = catMaybes (map whoDefines (Set.toList (fvs d)))

  node n d      = (n, dependsOn d)
  graph         = array (0, length ds - 1) (zipWith node [0..] ds)


  



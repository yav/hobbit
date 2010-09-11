module Depend.FVs where

import qualified Data.Set as Set

class Ord name => FVs t name | t -> name where
  fvs  :: t -> Set.Set name

class Ord name => Defs t name | t -> name where
  defs :: t -> Set.Set name

instance FVs t name => FVs [t] name where
  fvs xs  = Set.unions (map fvs xs)

instance FVs t name => FVs (Maybe t) name where
  fvs (Just x)  = fvs x
  fvs Nothing   = Set.empty

instance (FVs s name, FVs t name) => FVs (s,t) name where
  fvs (x,y) = fvs x `Set.union` fvs y

instance (FVs s name, FVs t name) => FVs (Either s t) name where
  fvs (Left x)  = fvs x
  fvs (Right x) = fvs x

instance Defs t name => Defs [t] name where
  defs xs = Set.unions (map defs xs)

instance (Defs s name, Defs t name) => Defs (s,t) name where
  defs (x,y) = defs x `Set.union` defs y


instance (Defs s name, Defs t name) => Defs (Either s t) name where
  defs (Left x)  = defs x
  defs (Right x) = defs x


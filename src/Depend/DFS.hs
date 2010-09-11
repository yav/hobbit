module Depend.DFS(Graph,buildGraph,scc,SCC(..),compDefs) where

-- from "Structuring Depth-First Search Algorithms in Haskell"
-- by David J. King and John Launchbury

import Array
import Data.Array.ST -- hiding (HasBounds(bounds),indices)
import Control.Monad.ST

type Graph vertex           = Array vertex [vertex]

vertices                    :: Ix vertex => Graph vertex -> [vertex]
vertices                    = indices

type Edge vertex            = (vertex,vertex)

edges                       :: Ix vertex => Graph vertex -> [Edge vertex]
edges g                     = [ (v1,v2) | v1 <- vertices g, v2 <- g ! v1 ]

data Tree a                 = Node a (Forest a)
type Forest a               = [Tree a]

flatten                     :: Tree a -> [a]
flatten (Node a ts)         = a : concatMap flatten ts

generate                    :: Ix v => Graph v -> v -> Tree v
generate g v                = Node v (map (generate g) (g!v)) 

type Bounds v               = (v,v)
type Set s v                = STArray s v Bool

empty                       :: Ix v => Bounds v -> ST s (Set s v)
empty b                     = newArray b False

contains                    :: Ix v => Set s v -> v -> ST s Bool
contains                    = readArray 

include                     :: Ix v => Set s v -> v -> ST s ()
include s v                 = writeArray s v True

prune                       :: Ix v => Bounds v -> Forest v -> Forest v
prune b f                   = runST (chop f =<< empty b)

chop                        :: Ix v => Forest v -> Set s v -> ST s (Forest v) 
chop [] _                   = return []
chop (Node v xs : ys) s     = do visited <- contains s v
                                 if visited 
                                   then chop ys s 
                                   else do include s v
                                           as <- chop xs s
                                           bs <- chop ys s
                                           return (Node v as : bs) 

dff                         :: Ix v => Graph v -> Forest v
dff g                       = dfs g (vertices g)      

dfs                         :: Ix v => Graph v -> [v] -> Forest v 
dfs g vs                    = prune (bounds g) (map (generate g) vs)

swap                        :: (a,b) -> (b,a)
swap (x,y)                  = (y,x)

revEdges                    :: Ix v => Graph v -> [Edge v]
revEdges                    = map swap . edges

transpose                   :: Ix v => Graph v -> Graph v
transpose g                 = buildGraph (bounds g) (revEdges g)

buildGraph                  :: Ix v => Bounds v -> [Edge v] -> Graph v
buildGraph b es             = accumArray (flip (:)) [] b es

postorder                   :: Tree a -> [a]
postorder (Node a ts)       = postorderF ts ++ [a]

postorderF                  :: Forest a -> [a] 
postorderF                  = concatMap postorder 

postOrd                     :: Ix v => Graph v -> [v]
postOrd g                   = postorderF (dff g)

scc'                        :: Ix v => Graph v -> Forest v
scc' g                      = dfs g $ reverse $ postOrd $ transpose g


data SCC v                  = NonRec v | Rec [v]
                              deriving Show

scc                         :: Ix v => Graph v -> [SCC v]
scc g                       = map comp (scc' g)
  where
  comp t                    = case flatten t of
                                [v] | not (loop g v) -> NonRec v
                                xs -> Rec xs

loop                        :: Ix v => Graph v -> v -> Bool
loop g v                    = v `elem` (g ! v)

instance Functor SCC where
  fmap f (NonRec x)         = NonRec (f x)
  fmap f (Rec xs)           = Rec (map f xs)

compDefs (NonRec x)         = [x]
compDefs (Rec xs)           = xs



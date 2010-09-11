> module ModSys.Relations where
>
> import qualified Data.Map as Map
> import qualified Data.Set as Set
> import Data.Set(Set)
> import qualified Data.List as List

Relations
=========
\label{sec-relations}

In this section, we present a number of operators for manipulating
relations.  To represent relations we use the #Set# and #Map# libraries provided
with the GHC and Hugs Haskell implementations.
However, the specification in this paper uses only the operators defined here,
so any other representation would do as well.

> type Rel a b = Map.Map a [b]

Next we describe a number of simple operations on relations.  Most of them
require the elements to be in the class #Ord#.  This is due to the
implementation of the #Map# library.  A different representation may
relax or strengthen these requirements.  

The operations #listToRel# and #relToList# allow us to switch between relations
represented as finite maps, and relations represented as association lists.

> listToRel :: (Ord a,Ord b) => [(a,b)] -> Rel a b
> listToRel xs = Map.fromListWith (++) [ (a,[b]) | (a,b) <- xs]

> relToList :: Rel a b -> [(a,b)]
> relToList r = [ (a,b) | (a,bs) <- Map.toList r, b <- bs ]
 
The empty relation is #emptyRel#. It does not relate any elements at all.

> emptyRel :: Rel a b
> emptyRel = Map.empty

The combinators #restrictDom# and #restrictRng# restrict the
domain and range, respectively, of a relation #r#, to the elements satisfying
a predicate #p#. 

> restrictDom :: (Ord a, Ord b) => 
>   (a -> Bool) -> Rel a b -> Rel a b
> restrictDom p r = Map.filterWithKey (\k _ -> p k) r

> restrictRng :: (Ord a, Ord b) => 
>   (b -> Bool) -> Rel a b -> Rel a b
> restrictRng p r = Map.map (filter p) r

To access the domain and range of a relation, we use the functions
 #dom# and #rng#, respectively.

> dom :: Ord a => Rel a b -> Set a
> dom r = Map.keysSet r

> rng :: Ord b => Rel a b -> Set b
> rng r = Set.fromList (concat (Map.elems r))

Sometimes it is useful to apply a function to all elements in the
domain or range of a relation.  This is the task of #mapDom# and
 #mapRng#, respectively.

> mapDom :: (Ord b, Ord x) => 
>   (a -> x) -> Rel a b -> Rel x b
> mapDom f r = Map.mapKeys f r

> mapRng :: (Ord a, Ord x) => 
>   (b -> x) -> Rel a b -> Rel a x
> mapRng f r = Map.map (map f) r

We also need to be able to compute the intersection and union of relations.
Elements are related by the intersection of two relations, if they are
related by _both_ relations.  They are related by the union of two relations,
if they are related by _either_ one of them.

> intersectRel :: (Ord a, Ord b) => 
>   Rel a b -> Rel a b -> Rel a b
> r `intersectRel` s = Map.intersectionWith List.intersect r s

> unionRels :: (Ord a, Ord b) => [Rel a b] -> Rel a b
> unionRels rs = Map.unionsWith (++) rs

The function #minusRel# computes the complement of a relation with
respect to another relation.  The new relation relates all those 
elements that are related by #r#, but not by #s#.

> minusRel :: (Ord a, Ord b) => 
>   Rel a b -> Rel a b -> Rel a b
> r `minusRel` s = Map.differenceWith clash r s
>   where clash a b = case filter (`notElem` b) a of
>                       [] -> Nothing
>                       xs -> Just xs

Given a predicate #p# over the domain of a relation #r#, #partitionDom# 
produces two new relations: the first one is the subset of #r# whose 
first component satisfies #p#, and the second is the rest of #r#.

> partitionDom :: (Ord a, Ord b) =>
>   (a -> Bool) -> Rel a b -> (Rel a b, Rel a b)
> partitionDom p r = Map.partitionWithKey (\k _ -> p k) r 

%\begin{ex}
%If #r = [(1,'a'),(2,'a'),(3,'b')]#, \newline
%then #partitionDom (== 2) r = ([(2,'a')],[(1,'a'),(3,'b')])#.
%\end{ex}

So far we have been thinking of relations as sets of pairs.  An alternative
view is to think of them as functions, which given an element of the
domain, return all related elements in the range.  The function
 #applyRel# converts a relation to a function form.

> applyRel :: (Ord a, Ord b) => Rel a b -> a -> [b]
> applyRel r a = case Map.lookup a r of
>                  Nothing  -> []
>                  Just xs  -> List.nub xs


Finally we define the operation #unionMapSet#, which is the ``bind''
operator of the set monad.  It is not an operation on relations, but 
rather on arbitrary sets.  It is missing from the #Set# library, so we define
it here.

> unionMapSet :: Ord b => (a -> Set b) -> (Set a -> Set b)
> unionMapSet f = Set.unions . map f . Set.toList



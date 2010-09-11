> module AreaLayout (pack, order, Area(..), Region, Addr
>                   , byteBdry, dwordSize) where
>
> import Data.List
> import Data.Bits (complement, (.&.))
> import Monad(guard)

> -- import Random -- for testing
> -- import Debug.Trace

XXX: Convert to using byte boundaries for alignment.

In this section we describe an algorithm for laying out user defined memory
areas.  User areas are contiguous blocks of memory introduced to a program
with the \KWD{area} declaration.  For the purposes of this algorithm 
an area is described by an alignment constraint and a size.  The size specifies
the number of bytes that the area occupies.  The alignment constraint specifies
the number of bits required to describe the starting address for the area.
For example, a memory area with alignment constraint 30 will be aligned
on a 4 byte boundary (assuming a machine that uses 32 bits to address memory).
In general, an area with alignment constraint $a$, will be aligned on
a $2^{max-a}$ byte boundary, where $max$ is the number of bits used to address
memory on a particular machine.  For the sake of concreteness, we assume that
we are working on a 32 bit machine, but the same algorthm will also work on
different architectures.

> type Bits   = Integer
> type Bytes  = Integer
> data Area a = Area { name  :: a
>                    , align :: Bits 
>                    , size  :: Bytes 
>                    , addr  :: Maybe Addr } deriving Show
> 
> byteBdry :: Bits -> Bytes
> byteBdry x = {-trace ("byteBdry: " ++ show x)-} (2^(32 - x))
>
> dwordSize   :: Area a -> Bytes
> dwordSize a  = (size a + 3) .&. complement 3
>
> 

The goal of the algorithm is to choose addresses for the areas in the input,
so that each area gets a distinct, contiguous part of memory.  Furthermore,
all areas should fit within a particular set of regions of memory.  A region is 
a contiguous part of memory specified by the first and last address in the
region.  A region whose last address is smaller then the first address
is empty:

> type Addr   = Integer
> type Region = (Addr,Addr)
>
> isEmpty :: Region -> Bool
> isEmpty (x,y) = y < x

The algorithm is partial, because there is no solution for some imputs.
For example, there are only two valid addresses for an area with an alignment
constraint 1, and therefore if there are 3 such areas in the input there is
no valid solution.  

The main observation we make is that areas with smaller alignment
constraints can be placed at fewer locations in memory.  Thus, when we 
consider a particular address, we eagerly choose the area with the smallest 
alignment constraint that can be placed at the address.  If there are multiple 
such areas, we select larger areas first, because smaller alignment 
constraint correspond to larger alignment boundaries, and so larger areas 
are likely to be a better fit.  For example, consider two areas, 
$A$ of size 256 bytes, and $B$ of size 512 bytes, that need to be aligned 
on a 512 byte boundary.  If we place $A$ before $B$ we need a 256 byte gap 
before we can place $B$, while if we place $B$ before $A$ we need no such gap.
These considerations suggest an ordering on areas:

> prefer :: Area a -> Area a -> Ordering
> prefer (Area { addr = Just _ }) _ = LT  -- or EQ, but not important
> prefer x y
>   | align x < align y   = LT
>   | align x == align y  = compare (size y) (size x)
>   | otherwise           = GT
 
An address satisfies a particular alignment constraint, if its least
signficant bits are all 0:

> aligned :: Addr -> Bits -> Bool
> aligned a n = a `mod` byteBdry n == 0
>
> nextAligned :: Addr -> Bits -> Addr
> nextAligned a n = ((a + bytes - 1) `div` bytes) * bytes
>   where bytes = byteBdry n

When we try to place an area in a region there are two possible outcomes:
either the area cannot be placed in the region, or we can place it
somewhere in the region, which results in splitting the region into smaller
regions (except for areas of size 0):

> fitsIn :: Area a -> Region -> Maybe (Area a, [Region])
> a `fitsIn` (from,to) 
>   = do start <- pickStart
>        let end = start + size a
>        guard (end <= to)
>        Just (a { addr = Just start }, joinRegions (from,start-1) (end+1,to))
>   where
>   pickStart = case addr a of 
>                 Just x  | aligned x (align a) && (x >= from) -> Just x
>                         | otherwise -> Nothing
>                 _ -> Just (from `nextAligned` align a)
>
> joinRegions :: Region -> Region -> [Region]
> joinRegions r1 r2  = if isEmpty r1 then if isEmpty r2 then [] else [r2]
>                                    else if isEmpty r2 then [r1] else 
>                      if snd r1 == fst r2 then [(fst r1, snd r2)] 
>                                          else [r1,r2]

The algorithm to assign addresses to areas keeps track of a list
of regions where we can place areas.  Our stratehy is greedy because 
it places an area into the first region that fits.  However, we first sort
the areas using the preference order that we described above, so that we first
solve the most difficult cases:

> placeArea :: Area a -> [Region] -> Maybe (Area a, [Region])
> placeArea _ []      = Nothing
> placeArea a (r:rs)  = case a `fitsIn` r of
>                         Nothing -> do (a,rs) <- placeArea a rs
>                                       return (a,r:rs)
>                         Just (a,xs) -> Just (a,xs ++ rs)
>
> order :: Region -> [Area a] -> Maybe [Area a]
> order r as  = loop (sortBy prefer as) [r]
>   where
>   loop [] _       = return []
>   loop (a:as) rs  = case placeArea a rs of
>                       Nothing -> Nothing
>                       Just (x,rs') -> do xs <- loop as rs'
>                                          return (x:xs) 



> pack :: [Area a] -> [Area a]
> pack as  = loop (sortBy prefer as)
>   where 
>   loop :: [Area a] -> [Area a]
>   loop []     = []
>   loop [a]    = [a]
>   loop (a : b : cs) 
>     | rest == 0   = a : loop (b : cs)
>     | otherwise   = case fill cs of
>                       Nothing -> a : loop (b : cs)    -- gap
>                       Just (d,ds) -> a : d : loop (b : ds)
>                       
>     where 
>     rest          = dwordSize a `mod` blockSize
>     free          = blockSize - rest
>     blockSize     = byteBdry (align b)
>
>     fill :: [Area a] -> Maybe (Area a, [Area a])
>     fill []       = Nothing
>     fill (c:cs)   
>       | (dwordSize a `mod` byteBdry (align c)) == 0 && 
>         (dwordSize c <= free)     = Just (c,cs)
>       | otherwise = do (d,ds) <- fill cs
>                        return (d,c:ds) 




> {-

The algorithm considers different addresses, and attempts to place an area
at each address.  An attempt may have three outcomes:  the area cannot be
placed at this address because it is not properly aligned, the area cannot
be placed at the address because there is not enough free space, or the are
can be placed at the particular adddress:

> data Result  = Placed | NoSpace | NotAligned
>                   
> try :: Addr -> Addr -> Area a -> Result
> try cur end a
>   | aligned cur (align a) = if free < size a then NoSpace else Placed
>   | otherwise = NotAligned
>   where free = end - cur + 1
 
The rest of the algorithm is a stateful loop that places all areas.
The state has three components: the current address where we want to place
and area, a list of areas that we have already placed, and a list of areas
that we tried to place at the current address, but we could not.

> data S a = S { cur   :: Addr 
>              , done  :: [(Addr,Area a)]
>              , tried :: [Area a]
>              }
>
> order start end as = loop (sortBy prefer as) 
>                         S { cur = start, done = [], tried = [] }   
>   where
>   loop (a:as) s
>     = case try (cur s) end a of
>         Placed      -> loop (reverse (tried s) ++ as)
>                        s { cur    = cur s + size a
>                          , done   = (cur s,a) : done s
>                          , tried  = [] }
>         NotAligned  -> loop as s { tried = a : tried s }
>         NoSpace     -> Nothing
> 
>   loop [] s
>     = case tried s of
>         []  -> Just (reverse (done s))
>         xs  -> loop (reverse (tried s))
>                     s { cur = nextAligned (cur s) (align (head xs))
>                       , tried = [] }

For every candidate address we try to place the areas in order of preference
until we find an area that is correctly aligned.  If we find such area
we continue with the address immediatly after the newly placed area.  If none
of the areas can be placed at a particular address we advance to the next
address that satisfies the alignment constraints for the last area we tried.
Because we ordered the areas by alignment constraint, this would be the
closest address to the current address on which we can place an area.

\subsection{Evaluation}

The algorithm we presented is quadratic in the numnber of areas that need
to be placed.


> -}




> {-
> 
> -- testing ---------------------------------------------------------------------
> 
> validSolution :: [Area Int] -> [(Addr,Area Int)] -> Maybe ()
> validSolution as xs
>   | not (all (`elem` areas) (map name as))  = error "missing area"
>   | length areas /= length (nub areas)      = error "repeated area"
>   | any (\(x,a) -> not (aligned x (align a))) xs  = error "area not aligned"
>   -- | not (nonOverlap 0 xs)                   = error "areas overlap"
>   | otherwise                               = Just ()
>   where
>   areas = map (name . snd) xs
>   nonOverlap s ((x,a) : xs)   = s <= x && nonOverlap (x + size a) xs
>   nonOverlap _ []             = True
>   
>   
> tests :: Int -> IO Double
> tests n = do xs <- sequence $ replicate n $ fmap test (randTest 100)
>              let ys = [ y | Just y <- xs ]
>              putStrLn ("solved: " ++ show (length ys))
>              return ((sum ys / fromIntegral (length ys)))
>   
> test as = fmap wastePercent soln
>   where soln = do soln <- order [(0, 2^32-1)] as
>                   trace (showSoln soln) (Just ())
>                   validSolution as soln
>                   return soln
> 
> -- wastePercent :: [(Addr,Area)] -> Double
> wastePercent soln = trace msg ((waste / used) * 100)
>   where 
>   used  = fromIntegral (totSize soln)
>   opt   = fromIntegral (sum [ size a | (_,a) <- soln ])
>   waste = used - opt
>   msg = "used = " ++ show used ++ ", opt = " ++ show opt ++ ", waste = " ++ show waste
> 
> totSize as = loop 0 as
>   where loop m ((x,a) : xs) = loop (max m (x + size a)) xs
>         loop m [] = m
>  
> showSoln as       = unlines ("--- SOLUTION ------" : loop (fst (head sorted)) sorted)
>   where
>   sorted = sortBy addr as
>   addr (x,_) (y,_) = compare x y
>   loop a ((x,y) : zs)
>     | x > a       = ("*** space: " ++ show (x - a) ++ " ***") 
>                   : loop x ((x,y):zs)
>     | otherwise   = show (x,y) : loop (x + size y) zs
>   loop _ _        = []
> 
> 
> randTest     :: Int -> IO [Area Int]
> randTest n    = mapM randAny [1..n]
>   where
>   randSmall x = do a <- randomRIO (24,32)
>                    s <- randomRIO (4,256)
>                    return (Area x a s)
> 
>   randAny x   = do a <- randomRIO (1,32)
>                    s <- randomRIO (0,2^16)
>                    return (Area x a s)
> 
>   randAlign x = do a <- randomRIO (20,32)
>                    s <- randomRIO (1,1024)
>                    return (Area x a (byteBdry a * s))
> 
> 
> 
> -} 









module BDD where

import Error
import Data.Word

-- Ordered binary decision diagrams --------------------------------------------
type Var            = Word32
data BDD            = F | T | ITE Var BDD BDD
                      deriving (Eq,Show)


simp xs F = F
simp xs T = T
simp xs (ITE x t e) = case lookup x xs of
                        Just True  -> simp xs t
                        Just False -> simp xs e
                        Nothing    -> ITE x (simp ((x,True) : xs) t) 
                                            (simp ((x,False): xs) e)

ite1 T t _ = t
ite1 F _ e = e
ite1 (ITE x p q) t e = ITE x (ite1 p t e) (ite1 q t e)

ite2 p t e = simp [] (ite1 p t e)




ite        :: BDD -> BDD -> BDD -> BDD
ite T t _   = t
ite F _ e   = e
ite p t e   = let x   = maximum [ x | ITE x _ _ <- [p,t,e] ]
                  t'  = ite (with x True  p) (with x True  t) (with x True  e)
                  e'  = ite (with x False p) (with x False t) (with x False e)
              in if t' == e' then t' else ITE x t' e'

with :: Var -> Bool -> BDD -> BDD
with x b (ITE y p q)
  | x == y        = if b then p else q
with _ _ p        = p




-- Bit patterns ----------------------------------------------------------------
type Width          = Word32
data Pat            = Pat { width :: Width, bdd :: BDD }
                      deriving Eq

pWild, pFail       :: Width -> Pat
pWild n             = Pat n T             -- always match
pFail n             = Pat n F             -- never match

pNot               :: Pat -> Pat
pNot (Pat n p)      = Pat n (ite p F T)  -- match if argument does not match

pAnd, pOr          :: Pat {-n-} -> Pat {-n-} -> Pat {-n-}
pAnd (Pat m p) (Pat n q)            
  | m == n          = Pat m (ite p q F)   -- match if both patterns matchs
  | otherwise       = bug "pAnd" "Different widths"
 

pOr (Pat m p) (Pat n q) 
  | m == n          = Pat m (ite p T q)   -- match if one of the pats. matches
  | otherwise       = bug "pOr" "Different widths"

pOrs w ps           = foldr pOr (pFail w) ps
pAnds w ps          = foldr pAnd (pWild w) ps

pPadR, pPadL       :: Pat {-n-} -> {-m::-} Width -> Pat {-m+n-}
pPadR p 0           = p
pPadR (Pat n p) m   = Pat (m+n) (up p)
  where up (ITE x l r)  = ITE (x+m) (up l) (up r)
        up t            = t

pPadL (Pat n p) m   = Pat (m+n) p


-- match if upper bits match p, and lower bits match q
pSplit             :: Pat {-m-} -> Pat {-n-} -> Pat {-m+n-}
pSplit p q          = (p `pPadR` (width q)) `pAnd` (q `pPadL` (width p))

pSplits ps          = foldr pSplit (pWild 0) ps
  
pBool              :: Bool -> Pat {-1-}
pBool False         = Pat 1 (ITE 0 F T)
pBool True          = Pat 1 (ITE 0 T F)

-- match if bits are a particular 2s complement integers
pInt               :: {-n::-} Width -> Integer -> Pat {-n-}
pInt 0 _            = pWild 0
pInt n x            = pInt (n-1) (x `div` 2) `pSplit` pBool (odd x)

-- match if bits are (unsigned) larger than the given number 
pGreater           :: {-n::-} Width -> Integer -> Pat {-n-}
pGreater 0 _        = pFail 0
pGreater n l        = (pGreater n1 l2 `pSplit` pWild 1) `pOr` also
  where
  l2                = l `div` 2
  n1                = n - 1
  also 
    | even l        = pInt n1 l2 `pSplit` pBool True
    | otherwise     = pFail n

pGreaterEq n l      = pGreater n l `pOr` pInt n l
pLess n l           = pNot (pGreaterEq n l)
pLessEq n l         = pNot (pGreater n l)

-- drop some bits from the left (resp. right)

pDropL, pDropR     :: Pat {-n-} -> {-m::-} Width -> Pat {-n-m-}
pDropL (Pat n p) m 
  | m <= n          = Pat w' (trunc p)
  | otherwise       = bug "pDropL" "Dropped too much"
  where
  w'                = n - m
  trunc (ITE x l r) 
    | x >= w'       = trunc (ite l T r)
  trunc t           = t

pDropR (Pat n p) m
  | m <= n          = Pat w' (trunc p)
  | otherwise       = bug "pDropR" "Dropped too much"
  where
  w'                = n - m
  trunc (ITE x l r)
    | x >= m        = let l' = trunc l
                          r' = trunc r
                      in if l' == r' then l' else ITE (x-m) l' r'
    | otherwise     = T
  trunc t           = t

pShiftL, pShiftR   :: Pat {-m-} -> Width -> Pat {-m-}
pShiftL p n         = (p `pSplit` pInt n 0) `pDropL` n
pShiftR p n         = (pInt n 0 `pSplit` p) `pDropR` n


-- | Place a constraint on a field of a pattern.
-- Property: o + m <= n
pField             :: {-o::-} Width -> Pat {-m-} -> Pat {-n-} -> Pat {-m-}
pField o f p        
  | o + m <= n      = p `pAnd` (f `pPadL` (n-m-o) `pPadR` o)
  | otherwise       = bug "pField" "Field too large"
  where
  m                 = width f
  n                 = width p 


instance Show Pat where
  show p  = unlines (showPat p)

showPat            :: Pat -> [String]
showPat (Pat w T)   = [replicate (fromIntegral w) '_']
showPat (Pat _ F)   = []
showPat (Pat w f@(ITE v p q))
  | w' > v          = [ '_' : p | p <- showPat (Pat w' f) ]
  | otherwise       = [ '0' : p | p <- showPat (Pat w' q) ]
                   ++ [ '1' : p | p <- showPat (Pat w' p) ]
    where w'        = w - 1 


-- returns (value, mask)
-- x `matches` (v,m) = v == (x .&. m)
patTests            :: Pat -> [(Integer,Integer)]
patTests (Pat _ T)   = [(0,0)]
patTests (Pat _ F)   = []
patTests (Pat w f@(ITE v p q))
  | w' > v          = patTests (Pat w' f)
  | otherwise       = [ (v, one + m) | (v,m) <- patTests (Pat w' q) ]
                   ++ [ (one + v, one + m) | (v,m) <- patTests (Pat w' p) ]
    where w'        = w - 1
          one       = 2^w'

patMasks           :: Pat -> [Integer]
patMasks (Pat _ T)  = [0]
patMasks (Pat _ F)  = []
patMasks (Pat w f@(ITE v p q))
  | w' > v          = patMasks $ Pat w' f
  | otherwise       = patMasks (Pat w' q)
                   ++ map ((2^w') + ) (patMasks $ Pat w' p)
    where w'        = w - 1 

pr x                = putStrLn $ unlines $ showPat x

willAlwaysMatch (Pat _ T) = True
willAlwaysMatch _         = False

willAlwaysFail (Pat _ F)  = True
willAlwaysFail _          = False

p `willMatchIf` q         = willAlwaysFail (q `pAnd` pNot p)

p `willMatch` n       = p `willMatchIf` pInt (width p) (fromIntegral n)



-- Checks ----------------------------------------------------------------------

goodBDD            :: Width -> BDD -> Bool
goodBDD n (ITE x l r) 
  | x < n           = goodBDD x l && goodBDD x r
  | otherwise       = False
goodBDD _ _         = True

goodPat            :: Pat -> Bool
goodPat (Pat n p)   = goodBDD n p







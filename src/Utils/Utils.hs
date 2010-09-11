module Utils where

import Data.Bits
import Data.List
import Ratio(numerator,denominator)
import Control.Monad

(f `on` g) x y      = f (g x) (g y)

remove             :: (a -> Bool) -> [a] -> Maybe (a,[a])
remove p xs         = case break p xs of
                        (_,[])    -> Nothing
                        (xs,y:ys) -> Just (y, xs ++ ys)

apFst              :: (a -> b) -> (a,c) -> (b,c)
apFst f (x,y)       = (f x, y)

apSnd f (x,y)       = (x,f y)

showBin            :: (Integral a, Bits b) => a -> b -> String
showBin w x         = map sh $ reverse $ map cvt [0 .. fromIntegral w - 1]
  where sh True     = '1'
        sh False    = '0'
          
        cvt n       = testBit x n

uncurry3 :: (a -> b -> c -> d) -> (a,b,c) -> d
uncurry3 f (a,b,c) = f a b c

fst3 (x,_,_) = x
snd3 (_,x,_) = x
trd3 (_,_,x) = x


regroup :: Ord a => [(a,b)] -> [(a,[b])]
regroup xs  = map (\xs -> (fst (head xs), map snd xs))
            $ groupBy ((==) `on` fst)
            $ sortBy (compare `on` fst) xs

zipWith' f (x:xs) ~(y:ys) = f x y : zipWith' f xs ys
zipWith' _ _     _        = []

lg2 x  = let y = toRational (logBase 2 (fromIntegral x))
         in if denominator y == 1 then Just (fromInteger (numerator y))
                                  else Nothing



f # x   = liftM f x
f <# x  = ap f x
f <## x = do f <- f
             f =<< x

class Functor f => ForEach f where
  forEach :: (Monad m) => f a -> (a -> m b) -> m (f b)

  forEach_ :: (Monad m) => f a -> (a -> m b) -> m ()
  forEach_ f m = forEach f m >> return ()

instance ForEach [] where
  forEach = flip mapM
  forEach_ = flip mapM_

instance ForEach Maybe where
  forEach (Just a) f  = liftM Just (f a)
  forEach Nothing _   = return Nothing

forEach2 xs ys f    = zipWithM f xs ys
forEach2_ xs ys f   = zipWithM_ f xs ys

forEach3 (x:xs) (y:ys) (z:zs) f = liftM2 (:) (f x y z) (forEach3 xs ys zs f)
forEach3 _ _ _ _                = return []
                                  
ifM b t e = do x <- b
               if x then t else e

andM m1 m2  = ifM m1 m2 (return False)
orM m1 m2   = ifM m1 (return True) m2
allM xs     = foldr andM (return True) xs
anyM xs     = foldr orM (return False) xs
whenM b m   = ifM b m (return ())







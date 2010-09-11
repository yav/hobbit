module Parsing.Range (module Parsing.Range, module Position) where

import Parsing.Position as Position
import PP


data Range          = Range { from :: Position, to :: Position } deriving Eq

unionRange         :: Range -> Range -> Range
unionRange r1 r2    = Range { from = from r1, to = to r2 }

fromPos            :: Position -> Range
fromPos p           = Range p p

fromString         :: Position -> String -> Range
fromString p s      = Range p (foldl move p s)

endRange           :: Range -> Range
endRange r          = fromPos (to r)

startRange         :: Range -> Range
startRange r        = fromPos (from r)

betweenRange       :: Range -> Range -> Range
betweenRange r1 r2  = Range (to r1) (from r2)

instance Show Range where
  show x            = show (from x) ++ "-" ++ show (to x)

instance Pr Range where
  pr                = text . show








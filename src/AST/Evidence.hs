module AST.Evidence where

import PP
import qualified Data.Map as Map
import Data.Maybe(fromMaybe)
import Data.Word(Word32)


data EvT = ForBit | ForIx | ForPtr deriving Show

newtype EvName      = E Word32 deriving (Eq,Ord)
data OpEvName       = PlusEv | MinusEv | MulEv | Exp2Ev 
                    | ProjEv Int | DummyEv
                    | BitFieldEv | FieldEv | JoinEv | AreaEv
                    | LitEv EvT | EqEv EvT | OrdEv EvT 
                    | NumEv EvT | BitOpsEv EvT | BoundedEv EvT
                    | OrdToEqEv | LeEv | BeEv
                      deriving Show

data Ev             = AsmpEv EvName | IntEv Word32 | OpEv OpEvName [Ev]

projEv n x          = OpEv (ProjEv n) [x]

dummyEv             = OpEv DummyEv []

plusEv x y          = OpEv PlusEv [x,y]
minusEv x y         = OpEv MinusEv [x,y]
mulEv x y           = OpEv MulEv [x,y]
exp2Ev x            = OpEv Exp2Ev [x]

litBitEv x          = OpEv (LitEv ForBit) [x]
litIxEv x           = OpEv (LitEv ForIx) [x]

eqBitEv x           = OpEv (EqEv ForBit) [x]
eqIxEv              = OpEv (EqEv ForIx) []
eqPtrEv             = OpEv (EqEv ForPtr) []

ordBitEv x          = OpEv (OrdEv ForBit) [x]
ordIxEv             = OpEv (OrdEv ForIx) []
ordToEqEv x         = OpEv OrdToEqEv [x]

numBitEv x          = OpEv (NumEv ForBit) [x]
bitOpsBitEv x       = OpEv (BitOpsEv ForBit) [x]

boundedBitEv x      = OpEv (BoundedEv ForBit) [x]
boundedIxEv x       = OpEv (BoundedEv ForIx) [x]

areaEv x y          = OpEv AreaEv [x,y]         -- evidence for Area
joinEv x y          = OpEv JoinEv [x,y]         -- evidence for (_+_=_)
bitFieldEv x y z    = OpEv BitFieldEv [x,y,z]   -- evidence for Has on bitdata
fieldEv x y z       = OpEv FieldEv [x,y,z]      -- evidence for Has on ptrs

leEv x              = OpEv LeEv [x]
beEv x              = OpEv BeEv [x]


simpEv x@(AsmpEv _) = x
simpEv x@(IntEv _)  = x
simpEv (OpEv f es)  = op f (map simpEv es)
  where
  op OrdToEqEv [ OpEv (OrdEv x) xs ] = OpEv (EqEv x) xs 

  op (ProjEv n) [ OpEv _ xs ]     = xs !! n

  op PlusEv [ IntEv x, IntEv y ] = IntEv (x+y) 
  op PlusEv [ x, IntEv 0 ]       = x
  op PlusEv [ IntEv 0, y ]       = y

  op MinusEv [ IntEv x, IntEv y ] = IntEv (x-y) 
  op MinusEv [ x, IntEv 0 ]       = x

  op MulEv [ IntEv x, IntEv y ] = IntEv (x*y) 
  op MulEv [ x, IntEv 1 ]       = x
  op MulEv [ IntEv 1, y ]       = y

  op Exp2Ev [ IntEv x ]         = IntEv (2^x)

  op x es                       = OpEv x es

substEv                :: Map.Map EvName Ev -> Ev -> Ev
substEv s e@(AsmpEv x)  = fromMaybe e (Map.lookup x s)
substEv _ x@(IntEv _)   = x
substEv s (OpEv x es)   = OpEv x (map (substEv s) es)


instance Show EvName where show x = prShow x
instance Pr EvName where pr (E x) = text "ev" <> text (show x)

instance Show Ev where show x = prShow x
instance Pr Ev where
  prn _ (AsmpEv x)          = pr x
  prn _ (IntEv x)           = text (show x)
  prn n (OpEv op es)        
    | n < 1                 = pr op <+> hsep (map (prn 1) es)
  prn _ p                   = parens (pr p)

instance Pr OpEvName where pr x = text (show x)
                      

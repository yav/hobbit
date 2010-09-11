module AST.BitData where

import AST.Type
import AST.Expr
import qualified BDD

import Data.Word


-- Should have at least 1 constructor
data BD             = BD {
                        bd_name :: Name,
                        bd_cons :: [BD_Con],
                        bitData :: Bool
                    }

bd_width           :: BD -> BDD.Width
bd_width x          = bd_con_width (head (bd_cons x))

type FieldBDD       = BDD.Width -> Type -> BDD.Pat

bd_cover           :: (BD_Con -> BDD.Pat) -> BD -> BDD.Pat
bd_cover f x        = BDD.pOrs (bd_width x) (map f (bd_cons x))

junk               :: BD -> BDD.Pat
junk x | bitData x  = BDD.pNot (bd_cover bd_con_bdd_junk x)
junk x              = BDD.pFail (bd_width x)

confusion          :: BD -> [(BD_Con,BD_Con,BDD.Pat)]
confusion x         = con_confusion (bd_cons x)

data BD_Con         = BD_Con {
                        bd_con_name   :: Name,
                        bd_con_rep    :: [BD_Rep],
                        bd_con_guard  :: Maybe Expr
                    }

bd_con_width       :: BD_Con -> BDD.Width
bd_con_width x      = sum (map bd_rep_width (bd_con_rep x))

bd_con_bdd         :: FieldBDD -> BD_Con -> BDD.Pat
bd_con_bdd f x      = BDD.pSplits (map (bd_rep_bdd f) (bd_con_rep x))

bd_con_bdd_junk    :: BD_Con -> BDD.Pat
bd_con_bdd_junk x   = case bd_con_guard x of
                        Nothing -> bd_con_bdd noType x
                        Just _  -> BDD.pFail (bd_con_width x)

bd_con_bdd_conf    :: BD_Con -> BDD.Pat
bd_con_bdd_conf x   = bd_con_bdd noType x

con_confusion        :: [BD_Con] -> [(BD_Con,BD_Con,BDD.Pat)]
con_confusion (x:ys)  = [ (x,y,o) | y <- ys, let o = overlap x y, 
                                             not (BDD.willAlwaysFail o) ] 
                        ++ con_confusion ys
  where overlap x y   = bd_con_bdd_conf x `BDD.pAnd` bd_con_bdd_conf y
con_confusion []      = []

noType             :: FieldBDD
noType w _          = BDD.pWild w

data BD_Rep         = BD_Rep {
                        bd_rep_type  :: BD_Rep_Type,
                        bd_rep_width :: Word32
                    }

bd_rep_bdd         :: FieldBDD -> BD_Rep -> BDD.Pat
bd_rep_bdd f x      = case bd_rep_type x of
                        BD_Field _ t _  -> f w t
                        BD_Wild         -> BDD.pWild w
                        BD_Tag x        -> BDD.pInt w (fromIntegral x)
  where w = bd_rep_width x

data BD_Rep_Type    = BD_Field Name Type (Maybe Expr)
                    | BD_Wild
                    | BD_Tag Word32



module Type.FVS where

import AST
import Type.MonadIO
import Error
import Monad

class FVS t where
  fvs                  :: t -> IO [TyVar]

instance FVS t => FVS [t] where
  fvs xs                = concat `fmap` mapM fvs xs 

instance (FVS a, FVS b) => FVS (a,b) where
  fvs (x,y)             = liftM2 (++) (fvs x) (fvs y)

instance FVS Type where
  fvs t                 = f =<< pruneIO True t
    where
    f (TApp t1 t2)      = fvs [t1,t2]
    f (TFree x)         = return [x]
    f (TCon _)          = return []
    f (TSyn {})         = "Type.FVS.fvs[Type]" `unexpected` "TSyn"
    f (TInfix {})       = "Type.FVS.fvs[Type]" `unexpected` "TInfix"
    f (TParens {})      = "Type.FVS.fvs[Type]" `unexpected` "TParens"


instance FVS Schema where
  fvs (Forall xs ps t)  = do ys <- fvs (ps,t)
                             return [ y | y <- ys, not (y `elem` xs) ] 

instance FVS Pred where
  fvs p                 = concat `fmap` fvsArgs p

instance FVS Goal where
  fvs (Ev _ p)          = fvs p


-- | Compute the free variables in the arguments to a predicate.
fvsArgs                :: Pred -> IO [[TyVar]]
fvsArgs (CIn _ ts)      = mapM fvs ts 







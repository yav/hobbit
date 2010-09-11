module Type.MonadIO where

import AST
import Data.IORef
import Utils
import Error

getVar                       :: TyVar -> IO (Maybe Type)
getVar (TyVar _ r _)          = readIORef r
getVar (TyUser {})            = return Nothing

setVar                       :: TyVar -> Type -> IO ()
setVar (TyVar _ r _) t        = writeIORef r (Just t)
setVar (TyUser {}) _          = "setVar" `unexpected` "TyUser"

class TypeIO t where
  sameIO  :: t -> t -> IO Bool
  pruneIO :: Bool -> t -> IO t        -- Bool: Should we expand ty.syns?

instance TypeIO t => TypeIO [t] where
  sameIO (t:ts) (t':ts')      = do same <- sameIO t t'
                                   if same then sameIO ts ts'
                                           else return False
  sameIO [] []                = return True
  sameIO _ _                  = return False

  pruneIO b ts                = forEach ts (pruneIO b)

instance TypeIO Type where
  sameIO t1 t2 = sameP # pruneIO True t1 <## pruneIO True t2
    where
    sameP (TApp t1 t2) (TApp t1' t2') = do x <- sameIO t1 t1'
                                           if x then sameIO t2 t2' 
                                                else return False
    sameP (TCon x) (TCon y)   = return (x == y) 
    sameP (TFree x) (TFree y) = return (x == y)

    -- XXX:  Cannot happen
    sameP (TSyn _ _ t) (TSyn _ _ t') = sameIO t t'

    sameP _ _ = return False

  
  pruneIO b a@(TFree x) = do t <- getVar x
                             case t of
                               Just t -> do t' <- pruneIO b t
                                            setVar x t' 
                                            return t'
                               Nothing -> return a

  pruneIO True (TSyn _ _ t) = pruneIO True t

  pruneIO _ t               = return t


instance TypeIO Pred where
  sameIO (CIn c ts) (CIn c' ts')
    | c == c'                 = sameIO ts ts'
    | otherwise               = return False

  pruneIO b (CIn c ts)        = CIn c # pruneIO b ts

instance TypeIO Goal where
  sameIO (Ev x p) (Ev y q)
    | x == y                  = sameIO p q
    | otherwise               = return False

  pruneIO b (Ev x p)          = Ev x # pruneIO b p





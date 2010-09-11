module Type.Subst where

import AST 
import Type.Monad
import Error

import Utils
import MonadLib


-- Note: We would like to preserve sharing,
-- as represented by type variables (i.e., if 
-- a type variable is mentioned multiple times
-- in the body of a type, then after the substitution
-- the type it points to will not get duplucated.)


type Substitution   = TyVar -> Maybe Type

listSubst          :: [(TyVar,Type)] -> Substitution
listSubst s x       = lookup x s

subst              :: Subst t => Substitution -> t -> TypeM t
subst s e           = fmap fst $ runStateT [] 
                    $ runReaderT s
                    $ subst' e

-- We use the state to preserve the sharing.
-- (e.g., if we apply { a |-> T } to (a -> a)
-- we get: let a = T in a -> a)
-- the 'let' is implemented with a reference

type SubM           = ReaderT Substitution (StateT [(TyVar,Type)] TypeM)
typeM m             = lift (lift m)

class Subst t where
  subst'           :: t -> SubM t

instance (Subst a, Subst b) => Subst (a,b) where
  subst' (a,b)  = (,) # subst' a <# subst' b

instance Subst a => Subst [a] where
  subst' xs     = forEach xs subst'

instance Subst a => Subst (Maybe a) where
  subst' xs     = forEach xs subst'
  




instance Subst Type where
  subst' t  = case t of
                TApp t1 t2 -> TApp # subst' t1 <# subst' t2
                TCon _  -> return t    -- Note: Assumes no types in names.
                TFree v -> checkSeen v $ checkFree v $ checkBound v t
                TSyn c ts t -> TSyn c # forEach ts subst' <# subst' t
                TInfix {} -> "Type.Subst.subst'[Type]" `unexpected` "TInfix"
                TParens {} -> "Type.Subst.subst'[Type]" `unexpected` "TParens"
                                                          
    where
    save v        = do v' <- typeM (freshTVar v)
                       let t = TFree v'
                       s <- get
                       set ((v,t):s)
                       return (v',t)
 
    checkSeen v k = do seen <- get
                       case lookup v seen of
                         Nothing  -> k
                         Just t   -> return t

    checkFree v k = do sub <- ask
                       case sub v of
                         Nothing -> k
                         Just t' -> do (v',t2) <- save v
                                       inBase (setVar v' t')
                                       return t2

    -- we look at the pointer only if:
    --  - this is a variable we have not already seen, and
    --  - the substitution did not have binding for it
    checkBound v t  = do mt <- inBase (getVar v)
                         case mt of 
                           Just t   -> do (v',t') <- save v
                                          (inBase . setVar v') =<< subst' t
                                          return t'
                           Nothing  -> return t
  

instance Subst Pred where
  subst' (CIn c ts) = CIn c # forEach ts subst' 

instance Subst StructField where
  subst' f@(StField { sfType = t }) = do t <- subst' t
                                         return (f { sfType = t })
  subst' (StPad t)                  = StPad # subst' t



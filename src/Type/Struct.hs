module Type.Struct (structRules) where

import AST
import Type.Monad
import Type.Algs
import Type.Env
import Type.FVS
import Type.Error
import Pass hiding (err)

import Utils
import MonadLib hiding(collect)
import Data.List(nub)
import qualified Data.Map as Map


-- XXX: This may get slow!


-- PRE: structs are in dependecy order,
-- but we don't care about recursive groups.
-- This is OK because recursive structs should only appear
-- under pointers, and we don't need the "BytRep" rules of the target
-- of a pointer.
structRules :: Env -> [Struct TyVar] -> RuleEnv -> Pass [Rule]
structRules ks ss rEnv = run env (loop ss)
  where 
  env = emptyDB { kindingEnv = ks, rules = rEnv }

  loop (s:ss) = do s   <- simpPreds s 
                   r1  <- ruleSizeOf s
                   rs2 <- rulesHas s
                   rs3 <- rulesBytes s
                   withRules (r1 : rs2 ++ rs3) (loop ss)
  loop []     = getRules


simpPreds          :: Struct TyVar -> TypeM (Struct TyVar)
simpPreds s         = do let fs = stFields s 
                         gs <- forEach (polyPreds fs) newGoal
                         (gs,_) <- withSkolems (stParams s) 
                                 $ simplify True [] gs
                         let ps = map goalPred gs
                         ys <- inBase (fvs (map TFree (polyVars fs)))
                         
                         return s { stFields = Forall ys ps (poly fs) } 




-- Computing the size ----------------------------------------------------------

ruleSizeOf         :: Struct TyVar -> TypeM Rule
ruleSizeOf s        = do s <- freshStruct s
                         (t,vs,ps,(e,n)) 
                            <- common s $ do (e,n) <- sizeOfFields (fields s)
                                             case stSize s of
                                               Nothing -> return ()
                                               Just t  -> unify n t
                                             return (e,n)  
                         as <- inBase $ quantify ps (CIn cSizeOf [t, n])
                         let proof vals = substEv (Map.fromList (zip vs vals)) e
                         return (Rule proof as)
                            


-- Conversion to/from bytes ----------------------------------------------------
 
rulesBytes         :: Struct TyVar -> TypeM [Rule]
rulesBytes s        = do s <- freshStruct s
                         ok <- try $ common s 
                             $ forEach (fields s) field
                         case ok of
                           Left _ -> return []
                           Right (t,_,ps,_) -> 
                             do ax <- inBase (quantify ps (CIn cBytes [t]))
                                let proof _ = dummyEv
                                return [Rule proof ax]

  where field (StField { sfType = t })  = newEv (CIn cBytes [t]) >> return ()
        field (StPad {})                = return ()



-- Accessing fields ------------------------------------------------------------

rulesHas           :: Struct TyVar -> TypeM [Rule]
rulesHas s@(Struct _ _ (Forall _ _ fs) _)
  = do rs1 <- forEach (names pre) (ruleHasBefore s) 
       rs2 <- forEach (names post) (ruleHasAfter s)
       return (rs1++rs2) 
  where 
  isDotDot (StPad Nothing) = True
  isDotDot _               = False
  
  (pre,post) = break isDotDot fs 
  
  names fs = [ l | StField { sfName = l } <- fs ]


fieldIs l (StField { sfName = l' }) = l == l'
fieldIs _ _                         = False


-- XXX: duplication

ruleHasBefore s l
  = do s <- freshStruct s
       let (pre,f:_) = break (fieldIs l) (fields s)
       (t,vs,ps,(aS,aF,e)) <- common s
                            $ do aS    <- newTVarAnon kNat
                                 aF    <- newTVarAnon kNat
                                 (e,n) <- sizeOfFields pre
                                 a1    <- newEv (CIn cAlign [aS])
                                 a2    <- newEv (CIn cAlign [aF])
                                 newEv (CIn cGCD [aS,n,aF])
                                 return (aS,aF,fieldEv e a1 a2) 
       let stRef  = tARef aS t
           flRef  = tARef aF (sfType f)
       -- ax <- inBase $ quantify ps (CIn cHas [tLab l, flRef, stRef])
       ax <- inBase $ quantify ps (CIn cField [tLab l, stRef, flRef])
       let proof vals = substEv (Map.fromList (zip vs vals)) e
       return (Rule proof ax)
                            
    
ruleHasAfter s l
  = do s <- freshStruct s
       let f:post  = dropWhile (not . fieldIs l) (fields s)
       (t,vs,ps,(aS,aF,e)) 
          <- common s $ do aS <- newTVarAnon kNat
                           aF <- newTVarAnon kNat
                           n  <- newTVarAnon kNat
                           (e',n') <- sizeOfFields post
                           s <- case stSize s of
                                  Nothing -> err (MiscError "`..` with no size")
                                  Just size -> do newEv (CIn cAdd [n',n,size])
                                                  newEv (CIn cDNat [size])
                           a1    <- newEv (CIn cAlign [aS])
                           a2    <- newEv (CIn cAlign [aF])
                           newEv (CIn cGCD [aS,n,aF])
                           return (aS,aF,fieldEv (minusEv s e') a1 a2)
       let stRef  = tARef aS t
           flRef  = tARef aF (sfType f)
       -- ax <- inBase $ quantify ps (CIn cHas [tLab l, flRef, stRef])
       ax <- inBase $ quantify ps (CIn cField [tLab l, stRef, flRef])
       let proof vals = substEv (Map.fromList (zip vs vals)) e
       return (Rule proof ax)



--------------------------------------------------------------------------------

fields s = poly (stFields s)


assume         :: Goal -> TypeM (EvName,Pred)
assume (Ev x p) = do addEvDef x (AsmpEv x)
                     return (x,p)

sizeOfType         :: Type -> TypeM (Ev,Type)
sizeOfType t        = do n <- newTVarAnon kNat
                         e <- newEv (CIn cSizeOf [t,n])
                         return (e,n)

sizeOfField        :: StructField -> TypeM (Ev,Type)
sizeOfField (StField { sfType = t })  = sizeOfType t
sizeOfField (StPad (Just t))          = sizeOfType t
sizeOfField (StPad Nothing)           = do n <- newTVarAnon kNat
                                           e <- newEv (CIn cDNat [n])
                                           return (e,n)

sizeOfFields       :: [StructField] -> TypeM (Ev,Type)
sizeOfFields fs     = do (es,ts) <- unzip # forEach fs sizeOfField  
                         n       <- tSum ts
                         return (evSum es, n)

-- XXX (see Bitdata?)
tSum               :: [Type] -> TypeM Type
tSum []             = return (tNat 0)
tSum (x:xs)         = do n <- tSum xs
                         a <- newTVarAnon kNat
                         _ <- newEv (CIn cAdd [x,n,a])
                         return a 

evSum              :: [Ev] -> Ev
evSum []            = IntEv 0
evSum xs            = foldr1 plusEv xs


quantify           :: [Pred] -> Pred -> IO (Poly Pred)
quantify ps q       = do xs <- fvs (ps,q)
                         return (Forall (nub xs) ps q)


common :: Struct TyVar -> TypeM a -> TypeM (Type, [EvName], [Pred], a)
common s@(Struct _ xs (Forall _ ps _) _) m
  = do gs      <- forEach ps newGoal
       (us,ps) <- unzip # forEach gs assume
       let env  = map AsmpEv us `zip` ps

       (r,as)  <- collect m

       (as,_)  <- withSkolems xs $ simplify True env as  
       (vs,qs) <- unzip # forEach as assume
       return (stAsType s, us ++ vs, ps ++ qs, r)


freshStruct (Struct s xs (Forall ys ps fs) m) 
  = do (ys,ps,(fs,m)) <- instantiate' (Forall ys ps (fs,m)) 
       return (Struct s xs (Forall ys ps fs) m)







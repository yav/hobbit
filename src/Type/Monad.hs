module Type.Monad (module Type.Monad, module Type.MonadIO) where
                  

import AST
import Error
import Type.MonadIO
import Type.FVS
import Type.Error
import qualified Type.Env; import Type.Env(Env)
import qualified Pass

import Data.List(find)
import qualified Data.Map as Map
import qualified Data.Map as IntMap

import MonadLib hiding (collect)
import qualified MonadLib as M (collect)
import Utils

import Control.Monad.Fix(mfix)

import Data.IORef
import Data.Word




type TypeM          = WriterT [Goal]      -- Collecting contraints
                    ( WriterT [DGoal]     -- Delayed (top-level) constraints
                    ( ReaderT DB        -- Useful info
                    ( ExceptionT Error  -- To report fatal errors
                    ( StateT S          -- (see bellow)
                      IO ))))           -- For references

data DB             = DB { typingEnv  :: Env
                           -- ^ The schemas for variables.

                         , kindingEnv :: Env
                           -- ^ Kinds for type constructors.

                         , recVars    :: Map.Map Name Expr
                           -- ^ Replacements for recurisve variables.
                           --   (see 'implicit' in "Type.Infer")

                         , evMap      :: Map.Map EvName Ev
                           -- ^ Evidence

                         , rules      :: RuleEnv 
                           -- ^ Instances that we can use to solve predicates.

                         , bdts       :: [BDT]
                           -- ^ Bitdata types, used to check bitdata ctrs.

                         , curDefs    :: [Name]
                           -- ^ (nested) definitions we are currently checking.
                           -- This is for error reporting.
                         }

emptyDB            :: DB
emptyDB             = DB { typingEnv  = Type.Env.empty
                         , kindingEnv = Type.Env.empty
                         , recVars    = Map.empty
                         , evMap      = IntMap.empty
                         , rules      = RuleEnv [] []
                         , bdts       = []
                         , curDefs    = []
                         }


data S              = S { evNameSeed   :: !Word32
                          -- ^ Evidence names grow from here.

                        , evMapS       :: !(Map.Map EvName Ev)
                          -- ^ Definitions for evidence.
                          -- This should be in a Writer component,
                          -- but the monoid instance for IntMap is buggy.
                        } 

emptyS              = S { evNameSeed  = 0
                        , evMapS      = IntMap.empty } 

run                :: DB -> TypeM a -> Pass.Pass a
run db m            = do x <- Pass.io (run' emptyS db m)
                         case x of
                           Left e  -> do d <- Pass.io (printError e)
                                         Pass.err [show d]
                           Right a -> return a
          
-- | Go!
run'               :: S -> DB -> TypeM a -> IO (Either Error a)
run' s db m         = fmap fst $ runStateT s
                    $ runExceptionT
                    $ runReaderT db
                    $ fmap fst $ runWriterT 
                    $ fmap fst $ runWriterT 
                    $ (fst # mfix (\ ~(_,ev) -> 
                               do r  <- ask >>= \e -> local (e { evMap = ev }) m
                                  ev <- evMapS # get
                                  return (r,ev)))



-- Errors and warnings ---------------------------------------------------------
err              :: ErrorT -> TypeM a
err e             = errs [e]

errs             :: [ErrorT] -> TypeM a
errs es           = do ds <- curDefs # ask
                       raise (Err ds es)

inDefn           :: Name -> TypeM a -> TypeM a
inDefn x m        -- = trace ("<" ++ show x ++ ">")
                  = ask >>= \d -> local (d { curDefs = x : curDefs d }) m



-- New names and variables -----------------------------------------------------

evFor            :: EvName -> TypeM Ev
evFor x           = do m <- evMap # ask
                       let Just e = IntMap.lookup x m
                       return e

newGoal          :: Pred -> TypeM Goal
newGoal p         = do s <- get
                       set (s { evNameSeed = 1 + evNameSeed s })
                       let n = E (evNameSeed s)
                       return (Ev n p)

newEv            :: Pred -> TypeM Ev
newEv p           = do g <- newGoal p
                       delay g
                       evFor (goalName g)
                       

newTVar          :: Name -> Kind -> TypeM Type
newTVar x k       = do r <- inBase (newIORef Nothing)
                       return (TFree (TyVar x r k))

newTVarAnon      :: Kind -> TypeM Type
newTVarAnon k     = newTVar (VarName "") k

freshTVar        :: TyVar -> TypeM TyVar
freshTVar t       = do r <- inBase (newIORef Nothing)
                       return (t { tyVarPtr = r })




-- Typing environment ----------------------------------------------------------
recVar           :: Name -> TypeM (Maybe Expr)
recVar x          = (Map.lookup x . recVars) # ask

withRecVars      :: [(Name,Expr)] -> TypeM a -> TypeM a
withRecVars xs m  = do e <- ask
                       let e' = e { recVars = Map.fromList xs
                                                `Map.union` recVars e }
                       local e' m

getEnv           :: TypeM Env
getEnv            = typingEnv # ask

freeInEnv        :: TypeM [TyVar]
freeInEnv         = (inBase . fvs) =<< getEnv

inEnv            :: Env -> TypeM a -> TypeM a
inEnv e m         = ask >>= \r -> local (r { typingEnv = e }) m

inExtEnvL        :: [(Name,Schema)] -> TypeM a -> TypeM a
inExtEnvL env m   = do e <- ask
                       let e' = e { typingEnv = foldr Type.Env.ext 
                                                      (typingEnv e) env }
                       local e' m

lkpTCon          :: Name -> TypeM Schema
lkpTCon x         = do env <- kindingEnv # ask
                       case Type.Env.lookup x env of
                         Just s   -> return s
                         Nothing  -> err (UndefinedTypeConstructor x)

lkp              :: Name -> TypeM Schema
lkp x             = do env <- typingEnv # ask
                       case Type.Env.lookup x env of
                         Just s   -> return s
                         Nothing  -> err (UndefinedVariable x)



-- Classes ---------------------------------------------------------------------
withRules        :: [Rule] -> TypeM a -> TypeM a
withRules rs m    = do e <- ask
                       let env = rules e
                           env' = env { instRules = rs ++ instRules env } 
                       local (e { rules = env' }) m

getRules         :: TypeM [Rule]
getRules          = (instRules . rules) # ask

getInstances     :: Name -> TypeM [Rule]
getInstances c    = filter ok # getRules
  where ok r      = case ruleHead r of
                      CIn c' _ | c == c' -> True
                      _                  -> False

getSuperRules    :: Name -> TypeM [Rule]
getSuperRules c   = (filter ok . superRules . rules) # ask
  where ok r      = case polyPreds (rulePred r) of
                      [ CIn c' _ ] | c == c'  -> True
                      _                       -> False
                        
                  

-- XXX: Should compute closures of the FDs once and for all...
-- although we don't need to do that for this particular set of FDs.
-- XXX: Should carry FDs in TypeM (i.e. make them user specified)
getFDs           :: Name -> TypeM [FunDep']
getFDs c 
  | c == cBitRep || c == cBitData || c == cSizeOf || c == cValIn 
                  = return [ ([0],[1]) ]
  | c == cExp2    = return [ ([0],[1]), ([1],[0]) ]
  -- | c == cHas     = return [ ([0,2],[1]) ]
  | c == cAdd || c == cJoin
                  = return [ ([0,1],[2]), ([0,2],[1]), ([1,2], [0]) ]
  | c == cGCD || c == cTimes || c == cField || c == cUpdField
                  = return [ ([0,1],[2]) ]

  | otherwise     = return []




-- Collecting goals ------------------------------------------------------------

-- data Constraint   = Delayed DGoal | Collected Goal


collect          :: TypeM a -> TypeM (a,[Goal])
collect m         = M.collect m

collect'         :: TypeM a -> TypeM (a,[Goal],[DGoal])
collect' m        = do ((a,gs),dgs) <- lift $ M.collect (runWriterT m)
                       return (a,gs,dgs)

delayL           :: [Goal] -> TypeM ()
delayL gs         = mapM_ delay gs

delay            :: Goal -> TypeM ()
delay g           = put [g]

delay'           :: [DGoal] -> TypeM ()
delay' gs         = lift (put gs)

addEvDef         :: EvName -> Ev -> TypeM ()
addEvDef d e      = do s <- get
                       set (s { evMapS = IntMap.insert d e (evMapS s) })


-- Bitdata ---------------------------------------------------------------------

-- XXX: Move to Type.Bitdata

findBDT          :: Name -> TypeM (Maybe BDT)
findBDT x         = find ((x ==) . bdtName) # getBDTs

getBDTCtr        :: Name -> TypeM (BDT,BDTCtr)
getBDTCtr x       = (try . findBDTCtr x) =<< getBDTs 
  where
  try (Just x)    = return x
  try Nothing     = err (UndefinedConstructor x)
                      
getBDTs          :: TypeM [BDT]
getBDTs           = bdts # ask

withBDT          :: BDT -> TypeM a -> TypeM a
withBDT b m       = ask >>= \e -> local (e { bdts = b : bdts e }) m

withBDTs         :: [BDT] -> TypeM a -> TypeM a
withBDTs bs m     = ask >>= \e -> local (e { bdts = bs }) m



-- Misc ------------------------------------------------------------------------

-- | Convert a Nat type to the corresponding number.
staticTNat         :: Type -> TypeM Word32
staticTNat t        = do t <- inBase (pruneIO True t)
                         case t of
                           TCon (TNat n) -> return n
                           _ -> bug "staticTNat" 
                                    ("Not a static Nat type. " ++ show t)





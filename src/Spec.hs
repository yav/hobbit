-- XXX: This needs some re-working...

-- | This module specializes a program to a monomorphic version.  
-- Polymorphic defintions are replaced with multiple versions, 
-- one for each type at which the definition is instantiated.   
-- In addition we also erase all dictionaries from the program.
-- Notes:
--  * Types change, after this pass we only deal with type constants (no apps)
--  * We only suport (statically) bounded polymorphic recursion.
--  * The transformation is only valid for pure expressions,
--    as otherwise it may omit or duplicate effects.

module Spec(specialize, Use(..)) where

import AST
import AST.SIL(tFunSimple)
import Error
import Depend.FVs(defs)
import Depend.FVs_AST()
import Type.MonadIO 
import PP

import Data.List(find,partition,groupBy,nubBy,nub)
import qualified Data.Set as Set
import qualified Data.Map as Map

import MonadLib
import Utils


-- XXX: Perhaps we should try to preserve some sharing between local
-- definitions that are identically instantiated.  We need to watch out
-- for differently instantiated local veriables though.

-- XXX: Should we generate definitions for ADTs,
-- whose constructors are not used, but they appear in
-- type signatures never the less?
-- (We could generate definitions without any constructors)




-- A 'Use' is a particular instantiation of a polymorphic value.
--  * 'uName' is the name of the variable that is being instantiated.
--  * 'uTypes' are the type parameters.
--  * 'uEv' are the evidence paramaters.
data Use            = Use { uName :: Name, uTypes :: [Type], uEv :: [Ev] }

instance Eq Use where
  x == y            = (uName x, uTypes x) == (uName y, uTypes y)

instance Show Use where show x = prShow x
instance Pr Use where
  pr u              = foldl app e (uEv u)
    where e         = pr (uName u) <> tris (commaSep (map pr (uTypes u)))
          app x y   = x <> cdot <> prn 1 y
                                  



type SpecM          = WriterT [Use]         -- Instantiations of values.
                    ( WriterT [(Name, [Type])] -- Inst. of a type. (used?)
                    ( ReaderT Env
                      IO ))

data Env            = Env
                    { tySubst :: [(TyVar,Type)]
                    , evSubst :: Map.Map EvName Ev }

emptyEnv            = Env [] Map.empty


-- The expressions in bitdata are:
--    * 'if' clauses
--    * default values

specialize :: ([ADT], BindBlock, [Use]) -> IO ([ADT], BindBlock)
specialize (adts,ds,uses)
  = runReaderT emptyEnv $ fmap fst $ runWriterT $ fmap fst $ runWriterT
  $ do (ds,us) <- usesOf (specBinds ds uses)
       let (ds',us') = selectors us
       as <- dataForCtrs (nub us') adts
       return (as,ds { prims = ds' ++ prims ds })

selectors :: [Use] -> ([PrimDecl], [Use])
selectors uses = (map selSig sels ++ map updSig upds, other1)
  where 
  (sels,other)  = partition (isSelect . uName) uses
  (upds,other1) = partition (isUpdate . uName) other

  isSelect (Select _) = True
  isSelect _          = False

  isUpdate (Update _) = True
  isUpdate _          = False

  -- r -> a
  selSig u = PrimDecl (nameFor u) (Just $ uEv u) 
                                  $ mono $ TCon $ tFunSimple t2 t1
    where [TCon t1, TCon t2] = uTypes u

  -- r -> a -> a
  updSig u = PrimDecl (nameFor u) (Just $ uEv u) $ mono $ TCon $ 
                                              tFunSimple t1 (tFunSimple t2 t2)
    where [TCon t1, TCon t2] = uTypes u


  


-- Abstract data types ---------------------------------------------------------

-- | Given the uses for some constructors we generate specialized datatypes.
dataForCtrs :: [Use] -> [ADT] -> SpecM [ADT]
dataForCtrs uses adts = do cs <- forEach allCtrs specADTCtr
                           return $ map toData $ groupBy inSameType cs
  where
  allCtrs    :: [(ADT,Poly ADTCtr,[Type])]
  allCtrs     = do use <- uses
                   case findADTCtr (uName use) adts of
                     Just (adt,ctr) -> [(adt,ctr,uTypes use)]
                     Nothing        -> [] -- must be bitdata...

  inSameType :: (ADT,[Type],ADTCtr) -> (ADT,[Type],ADTCtr) -> Bool
  inSameType (x,ts,_) (y,ss,_) = adtName x == adtName y && ts == ss

  isSameCon  :: (ADT,[Type],ADTCtr) -> (ADT,[Type],ADTCtr) -> Bool
  isSameCon (_,ts,c) (_,ss,d) = acName c == acName d && ts == ss

  toData     :: [(ADT,[Type],ADTCtr)] -> ADT
  toData cs   = ADT { adtName   = nameFor $ Use (adtName a) ts []
                    , adtParams = []
                    , adtCtrs   = map mono ctrs }
    where
    (a,ts,_) : _  = cs
    ctrs          = [ c | (_,_,c) <- nubBy isSameCon cs ]


-- | Given a constructor (with its polymorphic ADT), we return
-- an instantiation for the ADT, and a specialized constructor.

-- NOTE: this assumes that parameters to the type come last in the 
-- constructor schame (see `acSchema` in `AST.Data`)

specADTCtr         :: (ADT, Poly ADTCtr, [Type]) -> SpecM (ADT,[Type],ADTCtr)
specADTCtr (a,c,ts) = letTyVars (zip (polyVars c ++ adtParams a) ts)
                    $ do let con = poly c
                         fs <- forEach (acFields con) normT  
                         return ( a
                                , drop (length (polyVars c)) ts
                                , ADTCtr { acName  = nameFor 
                                                   $ Use (acName con) ts []
                                         , acFields = fs }
                                ) 


-- Expressions -----------------------------------------------------------------

-- | Specialize an expression.
-- We collect instantiations for definitions, and rename variables 
-- to refer to the correct instance of a definition.
specE              :: Expr -> SpecM Expr
specE e@(AppEv _ _) = specAppEv e []
specE e@(AppT _ _)  = specAppT e [] []
specE e             = specAppT e [] []

-- | Collect evidence paramaters.
specAppEv                  :: Expr -> [Ev] -> SpecM Expr
specAppEv (AppEv e e') es   = do e' <- normEv e'  
                                 specAppEv e (e':es)
specAppEv e es              = specAppT e [] es

-- | Collect type parameters, and instantiate.
-- Only variables may be instantiated --- they refer to definitions.
specAppT                   :: Expr -> [Type] -> [Ev] -> SpecM Expr
specAppT (AppT e t) ts es   = do t <- normT t
                                 specAppT e (t:ts) es
specAppT (Var x) ts es      = do ts <- forEach ts normT 
                                 let use = Use x ts es
                                 addUses [use] >> return (Var (nameFor use))
specAppT (Match m) [] []    = Match # specM m
specAppT (Lit l) [] []      = return (Lit l)
-- Note: if we had polymorphic 'bitdata',
-- we would have to use the instantiated version of the constructor
specAppT (Con c fs) [] []   = Con c # forEach fs specFV  
specAppT (App e1 e2) [] []  = App # specE e1 <# specE e2
specAppT (Upd e fs) [] []   = Upd # specE e <# forEach fs specFV
specAppT (Do p e1 e2) [] [] = do (e2,uses) <- usesOf (specE e2)
                                 addUses (killUses uses (defs p))
                                 p  <- specP uses p
                                 e1 <- specE e1
                                 return (Do p e1 e2)
specAppT e _ _              = "specAppT" `unexpected` show e


-- | Specialize a field value.
specFV             :: FieldV -> SpecM FieldV
specFV (FieldV l _ e) = FieldV l Nothing # specE e



-- | Instantiate a match.
specMatch          :: Match -> Use -> SpecM Match
specMatch m u       = appT m (uTypes u) 
  where
  appT                       :: Match -> [Type] -> SpecM Match
  appT (MAbsT a m) (t:ts)     = letTyVars [(a,t)] (appT m ts)
  appT (MAbsT _ _) []         = err "Not enough type parameters:"
  appT m []                   = appEv m (uEv u)
  appT _ _                    = err "Too many type parameters:"

  appEv                      :: Match -> [Ev] -> SpecM Match
  appEv (MAbsEv x _ m) (e:es) = letEvVar x e (appEv m es)
  appEv (MAbsEv _ _ _) []     = err "Not enough evidence parameters:"
  appEv m []                  = specM m
  appEv _ _                   = err "Too many evidence parameters:"

  err msg = bug "specMatch" $ unlines [ msg, show m, show u ]
  


-- | Specialize a match, after it has been applied to types and evidence.
specM              :: Match -> SpecM Match
specM (MIs e)       = MIs # specE e
specM (MOr m1 m2)   = MOr # specM m1 <# specM m2
specM (MPat p m)    = do (m,uses) <- usesOf (specM m)
                         addUses (killUses uses (defs p))
                         p <- specP uses p 
                         return (MPat p m)
specM (MGrd q m)    = do (m,uses) <- usesOf (specM m)
                         addUses (killUses uses (defs q))
                         q        <- specQ uses q
                         return (MGrd q m)

specM (MAbsEv {})   = "specM" `unexpected` "Unexpected MAbsEv."
specM (MAbsT {})    = "specM" `unexpected` "Unexpected MAbsT."






-- Patterns --------------------------------------------------------------------
-- | Specialize a qualifier given a set of uses.                             
specQ              :: [Use] -> Qual -> SpecM Qual
specQ uses q        = case q of
                        QGrd e        -> QGrd # specE e
                        QLet d        -> QLet # specBinds d uses
                        QPat p e      -> QPat # specP uses p <# specE e

                        QLocal q1 q2  -> 
                          do (q2,q2Uses) <- usesOf (specQ uses q2)
                             addUses (killUses q2Uses (defs q1))
                             q1 <- specQ q2Uses q1
                             return (QLocal q1 q2)

                        QThen q1 q2 -> 
                          do (q2',q2uses)<- usesOf (specQ uses q2)
                             addUses (killUses q2uses (defs q1))
                             q1 <- specQ (q2uses ++ killUses uses (defs q2)) q1
                             return (QThen q1 q2') 



-- | Specialize a pattern given a set of uses.
specP              :: [Use] -> Pat -> SpecM Pat
specP uses p        = case p of
                        PVar x      -> return (PVar x)
                        PWild       -> return PWild
                        p `PSig` t  -> PSig # specP uses p <# normT t

                        PAbs p q -> 
                          do (q',qUses) <- usesOf (specQ uses q)
                             addUses (killUses qUses (defs p))
                             p' <- specP (qUses ++ killUses uses (defs q)) p
                             return (PAbs p' q')

                        PApp p ts es ps ->  
                          do ts <- mapM normT ts
                             es <- mapM normEv es
                             -- Note: assumes that the 'ps'
                             -- do not shadow each other.
                             ps <- mapM (specP uses) ps
                             p  <- specBP p ts es 
                             -- XXX: we should be consistents as to where
                             -- we store the evidence.
                             return (PApp p [] es ps)
    
{-
                        PInc x k e  -> PInc x k # specE e
                        PDec x k e  -> PDec x k # specE e 
      
                        -- Note: assumes that bindings in one of the 
                        -- 'p's are not visible in the others.
                        
                        PCon c ts ps -> 
                          do ts <- forEach ts normT
                             let use  = Use c ts [] 
                                 c'   = nameFor use
                             addUses [use]
                             PCon c' [] # forEach ps (specP uses)
      
                        PSplit p1 p2  -> PSplit # specP uses p1 <# specP uses p2

                        p `PEv` e   -> PEv # specP uses p <# normEv e
-}

                        PParens {}  -> bug "specP" "PParens"
                        PInfix {}   -> bug "specP" "PInfix"

-- Note: Split and inc/dec are implemented directly
-- with primitives so we do not generate uses
-- for them.
specBP p ts es
  = case p of
      BPSplit  -> return p 
      BPCon c -> do let use = Use c ts es
                        c'  = nameFor use
                    addUses [use]
                    return (BPCon c')
      BPUpd d e1 e2 -> BPUpd d # specE e1 <# specE e2



-- Declarations ----------------------------------------------------------------

-- | Replace a list of plymorphic bindings, 
-- with a list of monomorphic ones, based on a set of uses.
-- Uses not defined by this group of bindings are propagated,
-- using the output component of the monad.
-- Bindings that are not used disappear, while bindings that
-- are used at different types are replaced with multiple
-- definitions, one for each instantiation.

-- For the moment we always keep areas, even if they are not used
-- bit perhaps we should treat them like other definitions.

specBinds          :: BindBlock -> [Use] -> SpecM BindBlock
specBinds b todo   = do as <- mapM specArea (areas b)
                        loop b (emptyBindBlock { areas = as }) todo []
  where
  loop _ b [] _      = return b

  -- We generate at most one definition for poly bindings.
  loop ob b (use:todo) done
    | use `elem` done   = loop ob b todo done

  loop ob b (use:todo) done = 
    case find (isThis . biName . impBind) (expBinds ob) of
      Just e  -> do (e',u') <- usesOf (specExpBind use e)
                    let b' = b { expBinds = e' : expBinds b }
                    loop ob b' (u'++todo) (use:done)
      Nothing -> 
        case find (isThis . primName) (prims ob) of
          Nothing -> addUses [use] >> loop ob b todo done
          Just p  -> do (p',u') <- usesOf (specPrim use p)
                        let b' = b { prims = p' : prims b }
                        loop ob b' (u'++todo) (use:done)
    where isThis y = uName use == y


-- | Generate a specialized version of a binding, 
-- for a particular instantiation.
specExpBind u (ExpBind (ImpBind _ m) sc) 
  = do let Forall xs _ t = sc 
       m  <- specMatch m u
       t  <- letTyVars (zip xs (uTypes u)) (normT t)
       return (ExpBind (ImpBind (nameFor u)  m) (mono t))

specArea a
  = do t <- normT (arType a)
       let e = simpEv # arEv a
       return (a { arType = t, arEv = e })

specPrim u p
  = do let Forall xs _ t = primType p
       t <- letTyVars (zip xs (uTypes u)) (normT t)
       return (PrimDecl (nameFor u) (Just (uEv u)) (mono t))


-- Monadic operations & other utility functions --------------------------------

-- | Pick a name for a particular instantiation of a variable.
nameFor            :: Use -> Name
nameFor u           = case uTypes u of
                        [] -> uName u
                        ts -> Inst (uName u) (map unType ts) 
  where
  unType (TCon x) = x
  unType _        = bug "Spec.nameFor.unType" "not a TCon"
  



-- | Remove names from a collection of uses.
-- This is used to remove "uses" at the point where they are defined.
killUses           :: [Use] -> Set.Set Name -> [Use]
killUses uses xs    = [ u | u <- uses, not (uName u `Set.member` xs) ]

-- | Add a list of uses.
addUses            :: [Use] -> SpecM ()
addUses us          = put us 

-- | Execites a computation, collecting the variables that were
-- used in the process.  For each used name we record the types
-- at which it was used.  Monomorphic values simply have an empty
-- list of types.
usesOf             :: SpecM a -> SpecM (a,[Use])
usesOf m            = collect m


-- | Normalize a type:
--  * Replaces type variables with concrete types
--  * Replaces free type variables with a default type 
--  * Type applications are replaced by appropriately named type constructors.
--    (Example: "List Int" becomes List@Int)
-- Note: We assume that the type has been pruned, 
-- so the only type variables are the ones that are truly free.

normT              :: Type -> SpecM Type
normT t             = norm =<< inBase (pruneIO True t)
  where
  norm (TApp t1 t2) = tapps t1 [t2]
    where
    tapps (TApp t1 t2) ts = tapps t1 (t2:ts)
    tapps t ts            = do TCon c <- normT t
                               ts     <- forEach ts normT
                               newType c ts
  norm (TFree x)    = do s <- tySubst # ask
                         case lookup x s of
                           Just t  -> return t
                           Nothing -> flip newType [] =<< defType 
    where
    -- XXX: This will insert kinds as type constructors...
    defType         = return TSome -- do k <- normT (tyVarKind x)

  norm (TCon c)     = newType c []
  norm (TSyn {})    = "Spec.normT" `unexpected` "TSyn"
  norm (TInfix {})  = "Spec.normT" `unexpected` "TInfix"
  norm (TParens {}) = "Spec.normT" `unexpected` "TParens"


-- | Bind type variables for the duration of a compuation.
letTyVars          :: [(TyVar,Type)] -> SpecM a -> SpecM a
letTyVars ts m      = ask >>= \e -> local (e { tySubst = newSubst e }) m
  where newSubst e  = ts ++ tySubst e 

letEvVar        :: EvName -> Ev -> SpecM a -> SpecM a
letEvVar x e m    = do r <- ask 
                       let r' = r { evSubst = Map.insert x e (evSubst r) }
                       local r' m

normEv             :: Ev -> SpecM Ev
normEv e            = (simpEv . (`substEv` e) . evSubst) # ask
                            


-- | NOTE: The 'ts' are normalized.
newType            :: Name -> [Type] -> SpecM Type
newType c ts        = do lift $ put [(c,ts)]
                         return (TCon (nameFor (Use c ts [])))


{- Example:  This is how we can get free variables that have a higher kind.
Consider a version of the resumption monad transformer like this:

data Res m a  = Return a | Yield (m (Res m a))

isDone       :: Res m a -> Bool
isDone (Return _) = True
isDone _          = False

x            :: Bool
x             = isDone (Return 'a')

With explicit instantiations:

x             = isDone@m@Char (Return@m@Char 'a')

The variable 'm' is free, and is of kind '* -> *'.
-}




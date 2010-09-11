-- | This module performs kind checking and normalization of
-- types written by the programmer.

-- We check that types written by the user are valid,
-- and transform them into the intetrnal representation of the compiler.

-- User type signature can mention user defined types, so we need
-- to process user defined datatypes, before we examine the type signatures
-- in ordinary declarations and expressions.  Howevere, user defined datatypes
-- also contain expressions, which is why we process data definitions twice.

module Type.Kind (KMod(..), checkModule) where

import AST
import Error
import qualified Pass
import Depend.SCC
import Type.FVS
import Depend.FVs_Data()
import Type.Monad
import Type.Error
import Type.Algs
import qualified Type.Env

import Utils
import MonadLib as M
import Data.List(find)
import qualified Data.Map as Map

-- XXX: This module could probably be cleaned up.


data CollOut        = APrim Name Schema | APred Pred
type CollM          = WriterT [CollOut] TypeM

-- We carry around the definitions of type synonyms.
type KindM          = ReaderT (Map.Map Name TS) CollM

-- For processing types written by the user:
type SigM           = ReaderT Bool    -- Allow implicitly quantified
                    ( WriterT [Pred]    -- Abbrev. predicates
                    ( StateT [TyVar]  -- Known type vars
                      KindM ))



-- Next follow some conversions between the different monads.



runCollM           :: CollM a -> TypeM (a, [CollOut])
runCollM m          = runWriterT m


splitCo :: [CollOut] -> ([(Name,Schema)],[Pred])
splitCo []                  = ([],[])
splitCo (APrim x s : os)    = let (as,bs) = splitCo os
                              in ((x,s) : as,bs)
splitCo (APred p : os)      = let (as,bs) = splitCo os
                              in (as,p:bs)

runKindM           :: Map.Map Name TS -> KindM a -> CollM a
runKindM m          = runReaderT m

runSigM            :: Bool -> [TyVar] -> SigM a -> KindM (a,[TyVar],[Pred])
runSigM b s m       = do ((x,y),z) <- runStateT s $ runWriterT $ runReaderT b m
                         return (x,z,y)

runSigM'           :: Bool -> [TyVar] -> SigM a -> KindM (a,[TyVar],[Pred])
runSigM' b s m       = runSigM b s m

inTypeC            :: TypeM a -> CollM a
inTypeC m           = lift m

inTypeK            :: TypeM a -> KindM a
inTypeK m           = lift $ inTypeC m

inTypeS            :: TypeM a -> SigM a
inTypeS m           = lift $ lift $ lift $ inTypeK m

inKind             :: KindM a -> SigM a
inKind m            = lift $ lift $ lift m



-- The `inDefnX` functions are liftings of `inDefn` from `TypeM`.
-- We use them to record what we are working on,
-- so that we can report better errors.

inDefnC            :: Name -> CollM a -> CollM a 
inDefnC x m         = do (a,w) <- inTypeC $ inDefn x $ runCollM m
                         put w
                         return a

inDefnK            :: Name -> KindM a -> KindM a 
inDefnK x m         = do r <- ask
                         lift $ inDefnC x (runKindM r m)

inDefnS            :: Name -> SigM a -> SigM a 
inDefnS x m         = do xs <- get
                         b  <- ask
                         (a,ys,ps) <- inKind $ inDefnK x $ runSigM b xs m
                         put ps
                         set ys
                         return a


-- Environments for families of types/kinds

initTEnv :: TypeM Type.Env.Env
initTEnv = do t1@(TFree a) <- newTVarAnon kType
              t2@(TFree b) <- newTVarAnon kType
              let fam (Select l) = Just 
                                 $ Forall [a,b] 
                                          [CIn cField [tLab l,t2,t1]] 
                                 $ tFun t2 t1
                  fam (Update l)  = Just 
                                  $ Forall [a,b]
                                           [CIn cUpdField [tLab l,t2,t1]]
                                  $ tFun t1 (tFun t2 t2)
                  fam _ = Nothing
              return $ Type.Env.fromFun fam

initKEnv :: Type.Env.Env
initKEnv = Type.Env.fromFun fam
  where
  fam (TNat _)  = Just $ mono kNat
  fam (TLab _)  = Just $ mono kLab
  fam _         = Nothing

data KMod = KMod { adts     :: [ADT],
                   bdts     :: [BitData],
                   structs  :: [Struct TyVar],
                   rules    :: RuleEnv,
                   binds    :: BindBlock }

-- XXX: what are the preds? qualified kinds?
-- XXX: Shouldn't the type for constructors be stored in the ADT/BDT?
checkModule :: ([DataDecl],BindBlock,RuleEnv) 
            -> Pass.Pass (KMod, Type.Env.Env, Type.Env.Env, [Pred])


checkModule (tys,binds,rules)
  = Type.Monad.run (emptyDB { typingEnv = initKEnv, kindingEnv = sortEnv })
  
  -- This happens in `TypeM`
  $ do (((as,bs,ss,ts),kenv),out1) <- runCollM (checkUserTypes tys)
       let (ctrs,ps1) = splitCo out1
       (r,out2) <- inEnv kenv 
                  $ runCollM 
                  $ runKindM ts      
                  $ do bs  <- forEach bs checkBitData2
                       ds  <- checkBindBlock binds
                       rs1 <- forEach (superRules rules) checkRule
                       rs2 <- forEach (instRules rules) checkRule
                       return $ KMod as (reverse bs) (reverse ss) 
                                        (RuleEnv rs1 rs2) ds
       let (prims,ps2) = splitCo out2
       tenv1 <- initTEnv 
       let tenv = foldr Type.Env.ext tenv1 (ctrs ++ prims)
       return (r, kenv,tenv, ps1++ps2)





-- | Sorts for kinds.
sortEnv            :: Type.Env.Env 
sortEnv             = Type.Env.fromFun sort
  where 
  sort (ConName "->") = Just $ mono (sSort `sFun` sSort `sFun` sSort)
  sort _              = Just $ mono sSort




-- Note: Bitdata is in reversed dependency order.
checkUserTypes :: [DataDecl] 
               -> CollM ( ([ADT], [BitData], [Struct TyVar], Map.Map Name TS)
                        , Type.Env.Env )
checkUserTypes ds   = check (sccs ds) ([],[],[],Map.empty)
  where
  -- the state is the tuple: (ADTs, BDTs, structs, type syns)
  check [] st       = do xs <- inTypeC getEnv
                         return (st,xs)

  check (NonRec (DataDecl d) : ds) (as,bs,ss,ts)
    = do a <- checkAlgData ts d
         inTypeC $ monomorph [adtKind a]
         withKinds [aEnv a] (check ds (a:as,bs,ss,ts))

  check (NonRec (BitdataDecl d) : ds) (as,bs,ss,ts)
    = do b <- checkBitData1 ts d
         withKinds (bEnv b) (check ds (as,b:bs,ss,ts))

  check (NonRec (StructDecl s) : ds) (as,bs,ss,ts)
    = do s <- checkStruct ts s
         inTypeC $ monomorph [stKind s]
         withKinds [sEnv s] (check ds (as,bs,s:ss,ts))

  check (NonRec (TypeDecl t) : ds) (as,bs,ss,ts)
    = do t <- checkTypeSyn ts t
         inTypeC $ monomorph [tsKind t]
         withKinds [tEnv t] (check ds (as,bs,ss,Map.insert (tsName t) t ts))

  check (NonRec (KSigDecl k) : ds) (as,bs,ss,ts)
    = withKinds [kEnv k] (check ds (as,bs,ss,ts))

  -- XXX: The results of the functions here are a bit awkward.
  check (Rec d : ds) (as,bs,ss,ts)
    = do (adts,tysyns,structs) <- inTypeC $ checkRecs d
         (as',ts',ss',ts2) <- checkRecData ts adts tysyns structs
         withKinds (map aEnv as' ++ map tEnv ts' ++ map sEnv ss') 
           $ check ds (as'++as,bs,ss'++ss,ts2)

  checkRecs ds = case splitDecls ds of
                   (as,[],ts,ss)  -> return (as,ts,ss)
                   (_,fs,_,_)     -> err (RecursiveBitdata fs)

  splitDecls []     = ([],[],[],[])
  splitDecls (d:ds) = case d of
                        DataDecl a                  -> (a:as,bs,ts,ss)
                        BitdataDecl (BitData x _ _) -> (as,x:bs,ts,ss)
                        TypeDecl t                  -> (as,bs,t:ts,ss)
                        StructDecl s                -> (as,bs,ts,s:ss)
                        KSigDecl _                  -> (as,bs,ts,ss)
    where (as,bs,ts,ss) = splitDecls ds


aEnv a              = (adtName a, mono (adtKind a))
bEnv b              = [(bdName b, mono (bdKind b))] ++ map sub (bdCtrs b)
  where sub f       = (subName (bdName b) (fcName f), mono kType)
tEnv t              = (tsName t, mono (tsKind t))
sEnv s              = (stName s, mono (stKind s))
kEnv (KSig x k)     = (x, mono k)






-- | Check a strongly connected component of recursive data types.
checkRecData       :: Map.Map Name TS 
                   -> [AlgData] -> [TypeSyn] -> [Struct TParam]
                   -> CollM ([ADT],[TS],[Struct TyVar],Map.Map Name TS)
checkRecData ts ads tds sds
  = do let tds' = sccs tds
       aenv <- inTypeC $ forEach [ x | AlgData x _ _ <- ads ] guessKind
       senv <- inTypeC $ forEach (map stName sds) guessKind
       let env1 = aenv ++ senv

       -- check the type synonyms
       (tds, ts) <- withKinds env1 (foldM aTypeSyn ([],ts) tds')
       let env2 = [ (tsName t, mono (tsKind t)) | t <- tds ]

       (ads,sds) <- withKinds (env2++env1)
                  $ do ads <- forEach ads (checkAlgData ts)
                       sds <- forEach sds (checkStruct ts)
                       return (ads,sds)

       let aks = [ k | (_,Forall _ _ k) <- aenv ]
           sks = [ k | (_,Forall _ _ k) <- senv ]
           tks = [ k | (_,Forall _ _ k) <- env2 ]
       inTypeC $ do forEach2_ aks (map adtKind ads) 
                              (\x y -> unify x y >> return ())
                    forEach2_ sks (map stKind sds) 
                              (\x y -> unify x y >> return ())
                    monomorph aks
                    monomorph sks
                    monomorph tks
                    return (ads,tds,sds,ts)
  where
  guessKind x = do k <- newTVarAnon sSort
                   return (x,mono k)

  aTypeSyn _ (Rec ts) 
    = inTypeC $ err (RecursiveTypeSynonyms [ x | TypeSyn x _ _ <- ts])

  aTypeSyn (tds,ts) (NonRec td)  
    = do td <- checkTypeSyn ts td
         return (td : tds, Map.insert (tsName td) td ts)



-- Algebraic data --------------------------------------------------------------

checkAlgData       :: Map.Map Name TS -> AlgData -> CollM ADT
checkAlgData ts (AlgData x as cs)
  = do xs <- inTypeC $ argEnv as
       cs <- runKindM ts $ forEach cs $ checkADataCon xs
       let adt =  ADT { adtName = x, adtParams = xs, adtCtrs = cs }
       -- adding constants for the constructors:
       put [ APrim (acName (poly c)) (acSchema adt c) | c <- cs ]
       return adt


-- | Fields should be of kind 'Type'                        
checkADataCon      :: [TyVar] -> DataCon -> KindM (Poly ADTCtr)
checkADataCon xs (DataCon c ts) 
  = inDefnK c
  $ withTParams'' xs
  $ do (ts,ks) <- unzip # forEach ts infer
       inTypeS $ forEach_ ks $ unify kType
       return (ADTCtr c ts)



-- Bitdata ---------------------------------------------------------------------

checkBitData1      :: Map.Map Name TS -> BitData -> CollM BitData
checkBitData1 ts b  
  = do (fs,_) <- inDefnC (bdName b) 
               $ runKindM ts $ withTParams [] 
                             $ forEach (bdCtrs b) checkBDataCon1
       let bdt = b { bdCtrs = fs }
       -- adding constants for constructors:
       put [ APrim (fcName b) (bdcSchema bdt b) | b <- fs ]
       return bdt

-- Note that we check the 'if' clause later.
checkBDataCon1     :: FlatCon -> SigM FlatCon
checkBDataCon1 (FlatCon c fs a i) 
                    = inDefnS c
                    $ FlatCon c # forEach fs checkBField1
                               <# forEach a (\ls -> forEach ls checkLay)
                               <# return i 
checkBDataCon1 (FlatCon2 c fs i)
                    = inDefnS c
                    $ FlatCon2 c # checkBField2_1 fs <# return i
                                

-- | The fields should be of kind 'Type'
-- Note that we check default values later.
checkBField1       :: Field -> SigM Field
checkBField1 f      = inDefnS (fieldName f)
                    $ do (t,k) <- infer (fieldType f)
                         inTypeS $ unify k kType
                         return (f { fieldType = t })

 -- | The type sigs in layout should be of kind 'Type'
checkLay           :: Layout -> SigM Layout
checkLay (LaySig ls t)  
                    = do (t,k) <- infer t
                         inTypeS $ unify k kType
                         ls    <- forEach ls checkLay
                         return (LaySig ls t)
checkLay l          = return l

checkBField2_1     :: Layout2 -> SigM Layout2
checkBField2_1 f    = case f of
                        BF_Named f  -> BF_Named # checkBField1 f
                        BF_Cat l r  -> BF_Cat # checkBField2_1 l 
                                             <# checkBField2_1 r 
                        BF_Sig l t  -> BF_Sig # checkBField2_1 l
                                             <# do (t,k) <- infer t
                                                   inTypeS $ unify k kType
                                                   return t
                        _ -> return f

-- Type synonyms ---------------------------------------------------------------

checkTypeSyn       :: Map.Map Name TS -> TypeSyn -> CollM TS
checkTypeSyn ts (TypeSyn x as t) 
  = inDefnC x
  $ do xs <- inTypeC $ argEnv as
       Forall ys ps (t,k) <- runKindM ts $ withTParams'' xs $ infer t
       return $ TS { tsName   = x
                   , tsParams = xs
                   , tsBody   = Forall ys ps t
                   , tsBodyK  = k }


-- Structs ---------------------------------------------------------------------

-- XXX: We ignore the schema in `fs` for the moment
checkStruct :: Map.Map Name TS -> Struct TParam -> CollM (Struct TyVar)
checkStruct ts (Struct t as fs s)
  = inDefnC t
  $ do xs <- inTypeC $ argEnv as
       Forall ys ps (fs,s) <- runKindM ts $ withTParams'' xs
                            $ do fs <- forEach (poly fs) checkStructField
                                 s  <- isNat s
                                 return (fs,s)
       return (Struct t xs (Forall ys ps fs) s) 

-- | Constraints should be of kind 'Nat'
isNat :: Maybe Type -> SigM (Maybe Type)
isNat Nothing     = return Nothing
isNat (Just t)    = do (t,k) <- infer t
                       inTypeS $ unify k kNat
                       return (Just t)

-- | Fields should be of kind 'Area'
checkStructField :: StructField -> SigM StructField
checkStructField (StField l t p)  = do (t,k) <- infer t
                                       inTypeS $ unify k kArea
                                       return (StField l t p)
checkStructField (StPad Nothing)  = return (StPad Nothing)
checkStructField (StPad (Just t)) = do (t,k) <- infer t
                                       inTypeS $ unify k kArea
                                       return (StPad (Just t))



-- Utils -----------------------------------------------------------------------


implicitOK         :: SigM Bool
implicitOK          = ask

withKinds          :: [(Name,Schema)] -> CollM a -> CollM a
withKinds xs m      = do (a,ys) <- inTypeC $ inExtEnvL xs (runCollM m)
                         put ys
                         return a


withTParams'' :: [TyVar] -> SigM a -> KindM (Poly a)
withTParams'' env m  
  = do (a,vs,ps) <- runSigM' False env m
       let n = length vs - length env
       return (Forall (take n vs) ps a)

withTParams :: [TParam] -> SigM a -> KindM (a,[TyVar])
withTParams as m  
  = do env <- inTypeK $ argEnv as
       (a,vs,ps) <- runSigM' False env m
       when (not (null ps)) $ inTypeK 
                            $ err $ MiscError "Predicates not allowed here."
       return (a,vs)




argEnv             :: [TParam] -> TypeM [TyVar]
argEnv as           = forEach as param 
  where 
  param (TP a k)    = do k <- case k of 
                                Nothing -> newTVarAnon sSort
                                Just k  -> return k
                         TFree a <- newTVar a k
                         return a
  


monomorph          :: [Kind] -> TypeM ()
monomorph ks        = do vs <- inBase (concat # forEach ks fvs)
                         forEach_ vs (unify kType . TFree)

-- Returns (arity, type syn)
tySyn              :: Name -> KindM (Maybe (Int,Schema))
tySyn x             = do t <- Map.lookup x # ask
                         return (toSchema # t)
  where
  toSchema ty       = let xs             = tsParams ty
                          Forall ys ps t = tsBody ty
                      -- NOTE: params are the first arguments
                      in (length xs, Forall (xs ++ ys) ps t)





-- Kind inference --------------------------------------------------------------


infer :: Type -> SigM (Type,Kind)
infer (TApp t1 t2)  = inferTApp (splitTApp t1 [t2])
infer c@(TCon _)    = inferTApp (c,[])
infer (TFree v)     
  = do seen <- get
       let x = tyVarName v
       case find ((x ==) . tyVarName) seen of
         Just v  -> return (TFree v, tyVarKind v)
         Nothing -> -- New user variable:
           do whenM (not # implicitOK)
                $ inTypeS ((err . UndefinedTypeVariable) =<< freshTVar v)
              a <- inTypeS $ do k <- newTVarAnon sSort
                                TFree v' <- newTVar x k
                                return v'
              set (a : seen)
              return (TFree a, tyVarKind a)
infer (TSyn {})     = "Kind.infer" `unexpected` "TSyn"
infer (TInfix {})   = "Kind.infer" `unexpected` "TInfix"
infer (TParens {})  = "Kind.infer" `unexpected` "TParens"

-- `normalizes' type synonyms
inferTApp :: (Type, [Type]) -> SigM (Type,Kind)
inferTApp (t,ts) =
  case t of
    TCon c -> 
      do tc <- inKind (tySyn c)
         case tc of
           Nothing -> do k <- inTypeS $ kindFor c
                         tApp t k ts
           Just (n,s) -> do (as,ps,t) <- inTypeS $ instantiate' s
                            let ts1 = take n ts
                                ts2 = drop n ts
                                missingArgs = n - length ts1

                            -- XXX: allow abbreviations for type synonyms
                            -- when they are predicate synonyms?
                            when (missingArgs > 0) $ inTypeS $
                              err (TypeSynonymNotFullyApplied c missingArgs)
      
                            (ts1,ks) <- unzip # forEach ts1 infer
                            -- NOTE: here we assume that the params 
                            -- come first in the schema (see `tySyn`)
                            inBase (forEach2_ as ts1 setVar) -- no sort errors
                            forEach ps addPred
                            forEach (drop n as) addVar

                            k <- inTypeS $
                              do k <- kindFor c
                                 a <- newTVarAnon sSort
                                 unify k (foldr kFun a ks)
                                 return a
                            -- NOTE: ditto
                            tApp (TSyn c (map TFree (take n as)) t) k ts2
    _ -> tApp' t ts -- must be a type variable
  
  where
  tApp'        :: Type -> [Type] -> SigM (Type,Kind)
  tApp' t ts    = do (t,k) <- infer t
                     tApp t k ts

  -- the 't' is processed, the 'ts' are not.
  -- eliminates abbreviation notation
  tApp         :: Type -> Kind -> [Type] -> SigM (Type,Kind)
  tApp t k ts   = do (ts,ks) <- unzip # forEach ts infer
                     (sub,a,b) <- inTypeS $ do a   <- newTVarAnon sSort
                                               unify k (foldr kFun a ks)
                                               b   <- newTVarAnon sSort
                                               sub <- match (kFun b kPred) a
                                               return (sub,a,b)
                     let ty = foldl TApp t ts 
                     if sub then 
                        do v <- inTypeS $ newTVarAnon b
                           let pred = TApp ty v
                           case typeToPred pred of
                             Just p -> do addVarPred v p
                                          return (v,b)
                             Nothing -> inTypeS $ err $ InvalidPredicate pred
                        else return (ty,a)

-- Check the fun-dep to avoid ambig.
addVarPred         :: Type -> Pred -> SigM ()
addVarPred (TFree v) p = do addVar v
                            addPred p 
addVarPred t _         = "addPred" `unexpected` show t

addVar             :: TyVar -> SigM()
addVar x            = do s <- get; set (x:s)

addPred            :: Pred -> SigM ()
addPred p           = put [p]

kindFor c = do Forall [] [] k <- lkp c
               return k

 
-- | Find the free variables in a schema and quantify over them
polyToPoly         :: Poly t -> (t -> SigM t) -> KindM (Poly t)
polyToPoly (Forall [] ps t) how
                    = do ((ps,t),xs,qs) <- runSigM' True [] 
                                         $ do ps <- forEach ps checkPred
                                              t  <- how t
                                              return (ps,t)
                         return (Forall xs (ps++qs) t)
polyToPoly _ _      = bug "polyToPoly" ("explicit quantifiers")


-- | Find the free variables in a schema and quantify over them
schemaToSchema     :: Schema -> KindM Schema
schemaToSchema s    = polyToPoly s (\t -> do (t,k) <- infer t
                                             inTypeS $ unify k kType
                                             return t)


-- | Check that a type written by the user is valid and monomorphic. 
typeToType         :: Type -> KindM Type
typeToType t        = do ((t,k),_,ps) <- runSigM False [] (infer t)
                         inTypeK (unify k kType)
                         put (map APred ps)
                         return t
                         
-- | Kind check expressions | --------------------------------------------------
-- After we compute the kinds of user defined data types,
-- we check and convert all types written by the user to our 
-- internal representation.



checkBitData2      :: BitData -> KindM BitData
checkBitData2 b     = do cs <- forEach (bdCtrs b) checkBDataCon2 
                         return (b { bdCtrs = cs })


-- | The second phase of kind checking a 'bitdata' constructor.
checkBDataCon2     :: FlatCon -> KindM FlatCon
checkBDataCon2 b@(FlatCon2 {})
  = inDefnK (fcName b) 
  $ do fs <- checkBField2_2 (fcFields2 b) 
       e  <- forEach (fcIf b) checkE
       return (b { fcFields2 = fs, fcIf = e })
  
checkBDataCon2 b@(FlatCon {})
  = inDefnK (fcName b) 
  $ do fs <- forEach (fcFields b) checkBField2 
       e  <- forEach (fcIf b) checkE
       return (b { fcFields = fs, fcIf = e })
  

-- | The second phase of kind checking a 'bitdata' field.
checkBField2       :: Field -> KindM Field
checkBField2 f      = inDefnK (fieldName f)
                    $ do e <- forEach (fieldDefault f) checkE
                         return (f { fieldDefault = e })

checkBField2_2      :: Layout2 -> KindM Layout2
checkBField2_2 (BF_Named f) = BF_Named # checkBField2 f
checkBField2_2 (BF_Sig l t) = BF_Sig # checkBField2_2 l <# return t
checkBField2_2 (BF_Cat l r) = BF_Cat # checkBField2_2 l <# checkBField2_2 r
checkBField2_2 f            = return f                        


checkRule          :: Rule -> KindM Rule
checkRule (Rule how p)  = do p <- polyToPoly p checkPred
                             return (Rule how p)

checkPred          :: Pred -> SigM Pred
checkPred p         = do (t,k) <- infer (predToType p)
                         inTypeS $ unify k kPred
                         case typeToPred t of
                           Just t  -> return t
                           Nothing -> bug "checkPred" ("Not a pred: " ++ show t)


checkBindBlock b            = BindBlock # mapM checkPrim  (prims b)
                                       <# mapM checkArea  (areas b)
                                       <# mapM checkExp   (expBinds b)
                                       <# mapM checkImp   (impBinds b)
                                 

checkPrim (PrimDecl x e s)  = inDefnK x
                            $ do s <- schemaToSchema s
                                 put [APrim x s]    -- XXX: silly...
                                 return (PrimDecl x e s)

checkArea a@(AreaDecl {})   = inDefnK (arName a)
                            $ do t <- typeToType (arType a)
                                 return (a { arType = t }) 

checkExp                   :: ExpBind -> KindM ExpBind
checkExp (ExpBind b t)      = inDefnK (biName b)
                            ( ExpBind # checkImp b <# schemaToSchema t )

checkImp                   :: ImpBind -> KindM ImpBind
checkImp (ImpBind x m)      = inDefnK x ( ImpBind x # checkM m )


-- | The check functions bellow traverse the AST and check the types:
--  * User written schemas get explicitly quantified
--  * We check that simple types do not contain type variables
{-
-- a primitive:
-}

checkM                     :: Match -> KindM Match
checkM (MOr m1 m2)          = MOr # checkM m1 <# checkM m2
checkM (MIs e)              = MIs # checkE e
checkM (MPat p m)           = MPat # checkP p <# checkM m
checkM (MGrd q m)           = MGrd # checkQ q <# checkM m
checkM (MAbsT _ _)          = "checkM" `unexpected` "MAbsT"
checkM (MAbsEv _ _ _)       = "checkM" `unexpected` "MAbsEv"

checkQ                     :: Qual -> KindM Qual
checkQ (QPat p e)           = QPat # checkP p <# checkE e
checkQ (QLet ds)            = QLet # checkBindBlock ds
checkQ (QGrd e)             = QGrd # checkE e
checkQ (QLocal q1 q2)       = QLocal # checkQ q1 <# checkQ q2
checkQ (QThen q1 q2)        = QThen # checkQ q1 <# checkQ q2

checkE e  = case e of
              App e1 e2    -> App # checkE e1 <# checkE e2
              Var x        -> return (Var x)
              Lit l        -> return (Lit l)
              Match m      -> Match # checkM m

              Sig e t      -> Sig # checkE e <# typeToType t
              Con c fs     -> Con c # forEach fs checkF 
              Upd e fs     -> Upd # checkE e <# forEach fs checkF 

              Do p e1 e2   -> Do # checkP p <# checkE e1 <# checkE e2
    
              AppT _ _     -> "checkE" `unexpected` "AppT"
              AppEv _ _    -> "checkE" `unexpected` "AppEv"
              Parens _     -> "checkE" `unexpected` "Parens"
              Infix _ _ _  -> "checkE" `unexpected` "Infix"

checkP p  = case p of
             PVar x        -> return (PVar x)
             PWild         -> return PWild
             PSig p t      -> PSig # checkP p <# typeToType t
             PAbs p q      -> PAbs # checkP p <# checkQ q
             PApp p ts es ps -> PApp # checkBP p <# mapM typeToType ts 
                                        <# return es <# mapM checkP ps
{-
             PCon c _ ps   -> PCon c [] # forEach ps checkP
             PSplit p1 p2  -> PSplit # checkP p1 <# checkP p2
             PInc x k e    -> PInc x k # checkE e
             PDec x k e    -> PDec x k # checkE e
             PEv {}        -> "checkP" `unexpected` "PEv"
-}

             PParens {}    -> "checkP" `unexpected` "PParens"
             PInfix {}     -> "checkP" `unexpected` "PInfix"

checkBP p = case p of
              BPSplit       -> return p
              BPCon _       -> return p
              BPUpd d e1 e2 -> BPUpd d # checkE e1 <# checkE e2
             
checkF (FieldV l x e)       = FieldV l x # checkE e


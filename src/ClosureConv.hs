-- XXX: this has bugs, use the other algortihm i implemented
-- based on thomas johannson's paper.


-- | After closure conversion the type 'a -> b' gets a concrete definition:
-- it is an algebraic datatype that has a constructor for each function 
-- of that type in the program.  The values stored in the constructors are 
-- the free variables for the corresponding function.
-- ...

-- Note that even though we are generating new ADTs for the function
-- closures we never need to generate constructor functions,
-- as the constructors are always fully applied.

module ClosureConv (closureConv, showCC) where

import AST (ADT'(..), ADTCtr'(..), Type(TCon), mono)
import qualified AST as A 
import AST.SIL
import Error
import PP

import Utils
import MonadLib
import Monad(when)
import Control.Monad.Fix(mfix)

import qualified Data.Set as Set ; import Data.Set(Set)
import qualified Data.Map as Map
import qualified Data.Map as IMap
import Data.Maybe(isJust)
import Data.Word


type CM             = ReaderT In    -- Environment
                    ( WriterT [Out] -- Generated top level definitions
                    ( StateT S      -- State
                      Id
                    ))

data In             = In
                    { types     :: Map.Map Name SimpleType     
                      -- ^ Types for values that are in scope.

                    , topLevel  :: Set Name
                      -- ^ Definitions defined at the top level
                      -- are not stored in closures.
 
                    , known     :: Map.Map Name KnownFun 
                      -- ^ Known functions. 
                    }

initIn              = In { types = Map.empty
                         , topLevel = Set.empty
                         , known = Map.empty }


data Out            = PutFun (FunDecl Expr)
                    | PutProc (FunDecl Stmt)
                    | PutArea Decl


data S              = S 
                    { workNames :: Map.Map Name Word32
                      -- ^ How many top-level things we have with this name.
                      -- We use this to generate readable top-level names.
  
                    , todo      :: [WhatsNew]
                      -- ^ Things that we need to generate code for.
                      -- (new function constructors or application operators)
                    } 


initS               = S
                    { workNames = Map.empty
                    , todo      = []
                    }
      

data WhatsNew       = None | NewCon ConName | NewOp OpName


type Result         = ([FunADT], [FunDecl Expr], [FunDecl Stmt], [Decl])

closureConv :: [Decl] -> Result
closureConv ds   
  = let ((ds',fs),s)  = runId
                      $ runStateT initS
                      $ runWriterT
                      $ runReaderT initIn
                      $ loop [] ds
        (fdts,apps,runs)   = appDefns (todo s)   -- XXX
        (topAs,topFs,topPs) = groupOut [] [] [] fs
    in (fdts, apps ++ topFs, runs ++ topPs, topAs ++ ds')
  where
  groupOut as fs ps (PutArea a : xs)  = groupOut (a:as) fs ps xs 
  groupOut as fs ps (PutFun f : xs)   = groupOut as (f:fs) ps xs
  groupOut as fs ps (PutProc p : xs)  = groupOut as fs (p:ps) xs
  groupOut as fs ps []                = (as,fs,ps)

  loop xs (d:ds)      = do (d,bs,ks,_) <- decl d
                           addTypes bs $ addTop bs $ addKnown ks 
                                                   $ loop (d:xs) ds
  loop xs []          = return (reverse xs)



showCC :: Result -> Doc
showCC (ccADTs,ccFuns,ccProcs,ccDecls) = vpr [vals,funs,procs,datas]
  where vals  = vpr (text "-- Values --" : map pr ccDecls)
        funs  = vpr (text "-- Functions -- " : map pr ccFuns)
        procs = vpr (text "-- Procedures -- " : map pr ccProcs)
        datas = vpr (text "-- Data types -- " : map pr ccADTs)



         
-- | Select the variables from a list of atoms.
atomVars           :: [Atom] -> CM (Set Binder)
atomVars xs         = do ds <- topLevel # ask
                         let vs = [ x | Var x <- xs, not (x `Set.member` ds) ]
                         Set.fromList # forEach vs (\x -> 
                                          do t <- typeOf x
                                             return (Bind x t))


-- | Expressions in a pure form
expr               :: Expr -> CM (Expr, Set Binder)
expr e@(Atom a)     = (,) e # atomVars [a]
expr e@(Con _ as)   = (,) e # atomVars as
expr e@(Prim _ as)  = (,) e # atomVars as
expr (App f xs)     = apply appP f xs
expr (CommE e)      = do (e,vs) <- comm expr e
                         return (CommE e, vs)
expr (Do _)         = "CC.expr" `unexpected` "Do"
                 
-- | Expressions in a side effecting form.
atomM            :: Atom -> CM (Stmt, Set Binder)
atomM (Var x)     = apply appM x []
atomM (Lit _)     = bug "atomM" "Literal"

exprM            :: Expr -> CM (Stmt, Set Binder)
exprM (Atom a)    = atomM a
exprM (App f xs)  = apply appM f xs
exprM (CommE e)   = do (s,vs) <- comm exprM e
                       return (CommS s, vs)
exprM (Prim c xs) = do vs <- atomVars xs
                       return (PrimS c xs, vs)
exprM (Do s)      = stmt s
exprM e           = "exprM" `unexpected` show e


stmt (Call f xs)    = apply appM f xs
stmt (LetM b s1 s2) = do (s1,vs1) <- stmt s1
                         (s2,vs2) <- addTypes [b] (stmt s2)
                         return (LetM b s1 s2, vs1 `Set.union` Set.delete b vs2)
stmt (PrimS c xs)   = do vs <- atomVars xs
                         return (PrimS c xs, vs)
stmt (CommS s)      = do (s,vs) <- comm stmt s
                         return (CommS s, vs)
                         

-- Application -----------------------------------------------------------------

appM = (runKnown, Call, RunOp)
appP = (appKnown, App, AppOp)

apply (ifKnown, mkApp, mkOp) f xs
  = do a <- isKnown f
       (e,vs1) <- doApp a
       vs2 <- atomVars xs
       return (e, vs1 `Set.union` vs2)
  where
  doApp (Just i)
    = do bs <- forEach xs (\x -> (,) x # typeOf x)
         let (s,w) = ifKnown i ([ (b2a b, varType b) | b <- kFreeArgs i] ++ bs)
         addWhatsNew w
         return (s,kFreeVars i)
         -- return (s, Set.fromList (kFreeArgs i))

  doApp Nothing
    = do t <- typeOf f   
         let op = mkOp t (fromIntegral (length xs))
         addWhatsNew (NewOp op)
         ds <- topLevel # ask
         return ( (mkApp (OpName op) (Var f:xs))
                , if f `Set.member` ds then Set.empty 
                                       else Set.singleton (Bind f t))




-- XXX: Similarities between runKnown and appKnown

runKnown f xs
  | a == argNum   = case kWorkerM f of
                      Just w  -> (Call w allArgs, None)
                      Nothing -> indirect
  | a < argNum    = indirect
  | otherwise     = bug "runKnown" "Under-application"
  where
  -- when we use a 'run' operator
  indirect = (CommS $ Let (AVal b e1) s2, NewOp run)
    where
    b   = Bind TmpRes r 
    as  = take (fromIntegral a) allArgs 
    bs  = drop (fromIntegral a) allArgs
    e1  = App (kWorker f) as 
    run = RunOp r (fromIntegral (length bs))
    s2  = Call (OpName run) (Var TmpRes : bs) 


  -- known function
  a               = fromIntegral (length rs) :: Word32
  FunT rs r       = kType f                 

  -- arguments
  allArgs      = map fst xs
  argNum       = fromIntegral (length xs - length (kFreeArgs f)) :: Word32



-- | Apply a known function to some arguments.
-- As a result we return:
--  * The expression for the application.
--  * Function constructors or application operators that we used.

appKnown           :: KnownFun -> [(Atom,SimpleType)] -> (Expr, WhatsNew)
appKnown f xs
  --  * Exact application: call function
  | a == argNum   = (App (kWorker f) allArgs, None)


  --  * Not enough argumnets: create a closure (NewCon)
  | a > argNum    = let ts  = map snd xs
                        t   = foldr tFunSimple r (drop (fromIntegral argNum) rs)
                        c   = ConOp
                              { conWorker  = f
                              , conType    = FunT ts t
                              , conHave    = argNum
                              }
                    in (Con (ConName c) allArgs, NewCon c)

  --  * Too many argument: call the function, then apply the result (NewApp)
  | otherwise     = let b   = Bind TmpRes r 
                        as  = take (fromIntegral a) allArgs 
                        bs  = drop (fromIntegral a) allArgs
                        e1  = App (kWorker f) as 
                        ap  = AppOp r (fromIntegral (length bs))
                        e2  = App (OpName ap) (Var TmpRes : bs) 
                    in (CommE $ Let (AVal b e1) e2, NewOp ap)
  where
  -- known function
  a                 = kArity f
  FunT rs r         = kType f                 

  -- arguments
  allArgs      = map fst xs
  argNum       = fromIntegral (length xs - length (kFreeArgs f)) :: Word32



-- Constructs that are common to expressions and staments ----------------------

comm :: (a -> CM (b, Set Binder)) -> Comm a -> CM (Comm b, Set Binder)
comm how (Switch x as)  
  = do t' <- typeOf x   
       let vs1 = Set.singleton (Bind x t')
       (as,vs2) <- unzip # forEach as (alt how)
       return (Switch x as, vs1 `Set.union` Set.unions vs2)
comm how (BSwitch x as) 
  = do vs1 <- atomVars [x]
       (as,vs2) <- unzip # forEach as (bAlt how)
       return (BSwitch x as, vs1 `Set.union` Set.unions vs2)

comm how (Let d e)        = localDecl how d e
comm _   (Raise t)        = return (Raise t, Set.empty)
comm how (Handle m1 m2)   
  = do (m1,vs1) <- how m1
       (m2,vs2) <- how m2
       return (Handle m1 m2, vs1 `Set.union` vs2)


-- | Closure convert an alternative.
alt                :: (a -> CM (b,Set Binder)) -> Alt a 
                   -> CM (Alt b , Set Binder) 
alt how (Case c e)  = do (e,vs) <- how e 
                         return (Case c e, vs)

bAlt               :: (a -> CM (b, Set Binder)) -> BAlt a 
                   -> CM (BAlt b, Set Binder)
bAlt how (BCase p e)= do (e,vs) <- how e
                         return (BCase p e, vs)




-- Declarations ----------------------------------------------------------------

-- Returns: 
--  * A closure converted declaration
--  * Names and type of values introduced by this declaration
--  * Any known functions introduced by the declaration
--  * Free variables in this declaration.

decl :: Decl -> CM (Decl, [Binder], [(Name,KnownFun)], Set Binder)

decl (Area x r v e) = return (Area x r v e, [x], [], Set.empty)

decl (AVal x e) = case isM (varType x) of
                   Just _ -> let f = Fun { funName   = varName x
                                         , funArgs   = []
                                         , funResT   = varType x
                                         , funDef    = e
                                         }
                             in decl (AFun f)
                   Nothing -> do (e,vs)  <- expr e
                                 return (AVal x e, [x], [], vs)
decl (AFun f)
  = do (i,vs) <- mfix $ \ ~(_,vs) -> do i0 <- knownFun0 f (Set.toList vs)
                                        let i = i0 { kFreeVars = vs }
                                        vs <- funDecl f i
                                        return (i,vs)
       let b = funBinderV f
       d <- addClo b i
       return (d, [b], [(funName f,i)], vs)

-- | The recursive case is intricate...
-- We use 'mfix' because when we generate a call to a 
-- knwon function we need to supply its free variables.  
-- If we are calling a known function that is currently being defined
-- we don't know its free variables yet.
decl (Rec fs) 
  = do let xs = map funName fs
           bs = map funBinderV fs

       (is,vss) <- mfix $ \ ~(_,vss) -> 
          do let argss = map Set.toList vss       
             is0 <- forEach2' fs argss knownFun0
             let is = [ i { kFreeArgs = as, kFreeVars = vs }
                         | i <- is0 | as <- argss | vs <- vss ]
             vss <- addTypes bs $ addKnown (zip xs is0) 
                                $ forEach2' fs is funDecl 
             return (is,vss)

       ds <- forEach2 bs is addClo  -- These closure values may be recursive 
       return ( Cyc [ (b,c,as) | AVal b (Con c as) <- ds]
              , bs
              , zip xs is
              , Set.unions vss Set.\\ Set.fromList bs)
decl (Cyc _) = "decl" `unexpected` "Cyc"

 

localDecl :: (a -> CM (b, Set Binder)) -> Decl -> a -> CM (Comm b, Set Binder)

-- XXX: It would be nice to avoid storing the pointers to areas in closures
-- as they are global, but for the moment this is the simplest...
-- The problem is that moving a local 'area' declaration to the top level
-- may require us to rename it to avoid name clashes, and so we would have
-- to use the new name in the expression 'e', but the monad does not support
-- such renaming map at the moment.  Instead we turn the local declaration
-- into: let x = x' in e    where x' is the name of the top-lelve area decl.

localDecl how (Area b@(Bind x t) r v ev) e  
  = do x' <- areaName x
       let area = Area (Bind x' t) r v ev
       put [PutArea area]
       (e, vs) <- addTypes [b] (how e)
       let aDecl = AVal (Bind x t) (Atom (Var x'))
       return (Let aDecl e, Set.delete b vs)
                                            
localDecl how d e 
  = do (d, bs, ks, vs1) <- decl d
       (e, vs2) <- addTypes bs $ addKnown ks $ how e
       return (Let d e, vs1 `Set.union` (vs2 Set.\\ Set.fromList bs))



-- Adds top level definitions, but not the closures for the pure functions.
funDecl      :: FunDecl Expr -> KnownFun -> CM (Set Binder)
funDecl f i   = do let xs = funArgs f
                   case isM (funResT f) of
                     Just t -> let Just fM = kWorkerM i in eff fM t xs 
                     Nothing -> pure xs
  where 
  pure xs   = do (e,vs) <- addTypes xs (expr (funDef f))
                 let xs'  = kFreeArgs i ++ xs
                     fun  = f { funName = kWorker i, funArgs = xs' 
                              , funDef = e }
                 put [PutFun fun]
                 return (vs Set.\\ Set.fromList xs)

  eff fM t xs 
    = do (s,vs) <- addTypes xs (exprM (funDef f))
         let xs'  = kFreeArgs i ++ xs
             proc = f { funName = fM, funArgs = xs', funResT = t, funDef = s }
             cC   = ConOp { conWorker = i
                          , conType   = FunT (map varType xs') (funResT f)
                          , conHave   = fromIntegral (length xs) }
         put [PutProc proc]
         when (not (null xs)) $ put [ PutFun $
           f { funName = kWorker i, funArgs = xs'
                                  , funDef = Con (ConName cC) (map b2a xs') } ]
         addWhatsNew (NewCon cC)
         return (vs Set.\\ Set.fromList xs)
  
                     




                     



isEff :: FunDecl a -> Bool
isEff f = isJust (isM (funResT f))


knownFun0          :: FunDecl Expr -> [Binder]  -> CM KnownFun
knownFun0 f as      = do w@(FunFor x) <- wFunName (funName f)
                         let wM = if isEff f then Just (ProcFor x)
                                             else Nothing
                         return (Info
                                   { kWorker    = w
                                   , kWorkerM   = wM
                                   , kFreeArgs  = as
                                   , kFreeVars  = Set.empty 
                                   , kType      = funTypeF f
                                   })




addClo :: Binder -> KnownFun -> CM Decl
addClo b i  = do addWhatsNew (NewCon c)
                 return (AVal b (Con (ConName c) (map b2a as)))
  where 
  as = kFreeArgs i
  c  = ConOp
     { conWorker = i
     , conType   = FunT (map varType as) (varType b)
     , conHave   = 0
     }








b2a                :: Binder -> Atom
b2a b               = Var (varName b)


------------------------------ Part 2 ------------------------------------------
--------------- Generate code for application operators ------------------------

type Ops a          = Map.Map SimpleType (Map.Map Word32 [Alt a])
data AppState       = AS { asCtrs  :: Map.Map SimpleType (Set ConName)
                           -- ^ The set of constructors for a given type.

                         , asApps  :: Ops Expr
                           -- ^ Application operators for a given type.
                           -- The inner map keeps the alternatives for
                           -- the different application operators of a type.

                         , asRuns  :: Ops Stmt

                         } deriving Show

setApps s x         = s { asApps = x }
setRuns s x         = s { asRuns = x }

-- | Add a new alternative to a particular application/run operator.
newAlt :: (AppState -> Ops a) -> (AppState -> Ops a -> AppState) 
       -> OpName -> Alt a -> AppState -> AppState
newAlt get set a alt s = set s newMap
  where
  upd m1 m2         = IMap.unionWith (++) m2 m1
  theAlt            = IMap.singleton (opArgs a) [alt]
  newMap            = Map.insertWith upd (opType a) theAlt (get s)




-- A goal identifies a particular constructor case in a particular
-- application/run operator.
type Goal           = (OpName, ConName) 


-- | Generate definitions for application operators and function datatypes,
-- based on the information collected during closure conversion.
appDefns           :: [WhatsNew] -> ([FunADT], [FunDecl Expr], [FunDecl Stmt])
appDefns todo 
  = ( map toADT (Map.toList (asCtrs s))
    , concat $ Map.elems (Map.mapWithKey (gen appOp) (asApps s))
    , concat $ Map.elems (Map.mapWithKey (gen runOp) (asRuns s))
    )
  where
  s                 = genApps (initApp todo)

  appOp             = (CommE, AppOp)
  runOp             = (CommS, RunOp)

  gen (comm,op) t m = IMap.elems (IMap.mapWithKey g m)
    where g n as    = opDefn comm (op t n) as

  toADT (t,s)       = ADT 
                    { adtName   = t
                    , adtParams = []
                    , adtCtrs   = map toCtr (Set.toList s)
                    }

  toCtr c           = mono $ ADTCtr 
                    { acName    = c       
                    , acFields  = map TCon (args (conType c))
                    }


-- | The defintion of an application/run operator.
opDefn             :: (Comm a -> a) -> OpName -> [Alt a] -> FunDecl a
opDefn comm a as    = Fun opName args y def 
  where
  args              = [ Bind a x | a <- map (Arg opName) [0..] | x <- xs ]
  def               = comm $ Switch (Arg opName 0) as
  opName            = OpName a
  FunT xs y         = opSig a


-- | Compute the initial state, based on what we collected during
-- the closure conversion process.
initApp            :: [WhatsNew] -> ([Goal],AppState)
initApp ws          = foldl upd ([],s) ws
  where
  upd (gs,s) w      = let (gs',s') = whatsNew w s
                      in (gs'++gs,s')
  s                 = AS
                        { asCtrs = Map.empty
                        , asApps = Map.empty
                        , asRuns = Map.empty
                        } 

-- | Generate application operators.
genApps            :: ([Goal],AppState) -> AppState
genApps ([],s)          = s
genApps ((a,c):todo,s)  = let (w,s1)  = conAlt (a,c) s
                              (gs,s2) = whatsNew w s1
                          in genApps (gs++todo,s2)

-- | How the state is affected by a 'WhatsNew' action.
whatsNew           :: WhatsNew -> AppState -> ([Goal],AppState)
whatsNew None s       = ([],s)
whatsNew (NewCon c) s = newCon c s
whatsNew (NewOp a) s  = newOp a s


-- | Add a new constructor to the list of things to do.
-- This may result in mutiple new goals, one for each application/run
-- operator that mentions the new constructor.
newCon             :: ConName -> AppState -> ([Goal], AppState)
newCon c s = 
  case Map.lookup ty (asCtrs s) of
    Just cs | Set.member c cs -> ([], s)
    _ -> let aps  = case Map.lookup ty (asApps s) of
                      Nothing -> []
                      Just as -> [ (AppOp ty n, c) | n <- IMap.keys as ]
             runs = case Map.lookup ty (asRuns s) of
                      Nothing -> []
                      Just as -> [ (RunOp ty n, c) | n <- IMap.keys as ]
         in (aps ++ runs, s')

  where 
  ty  = result (conType c)
  s'  = s { asCtrs = Map.insertWith Set.union ty (Set.singleton c) (asCtrs s) }



-- | Add a new application/run operator to the list of things to do.
-- This may result in multiple new goals, one for each constructor
-- in the new application operator.
newOp    :: OpName -> AppState -> ([Goal], AppState)
newOp a s 
  | done      = ([],s)
  | otherwise = case Map.lookup (opType a) (asCtrs s) of
                  Just cs -> ([ (a,c) | c <- Set.toList cs ], s')
                  Nothing -> ([], s')

  where 
  (s',done)   = case a of 
                  AppOp {} -> (newState asApps setApps, findOp (asApps s))
                  RunOp {} -> (newState asRuns setRuns, findOp (asRuns s))

  newState get set  = set s 
                    $ Map.insertWith (flip IMap.union) (opType a) theMap 
                    $ get s
  theMap            = IMap.singleton (opArgs a) [] 

  findOp m          = case Map.lookup (opType a) m of
                        Nothing -> False
                        Just as -> IMap.member (opArgs a) as

conAlt :: Goal -> AppState -> (WhatsNew, AppState)
conAlt (a,c) s 
  = let (ds, as)    = unzip (zipWith conArg [0..] (args (conType c)))
        funArgs     = zipWith funArg [1..] (tail $ args $ opSig a)
    in case a of
         AppOp {} -> let (e,w) = appKnown (conWorker c) (as ++ funArgs)
                     in (w, newAlt asApps setApps a (theAlt CommE e ds) s)
         RunOp {} -> let (e,w) = runKnown (conWorker c) (as ++ funArgs)
                     in (w, newAlt asRuns setRuns a (theAlt CommS e ds) s)
  where
  theAlt comm e ds  = Case (ConName c) (foldr (\d -> comm . Let d) e ds)

  opName            = OpName a
  cloName           = Arg opName 0
  cName             = ConName c

  conArg n t        = (AVal (Bind x t) e, (Var x, t))
    where x         = Fld cloName cName n 
          e         = primGetFieldA cName n (Var cloName)

  funArg n t        = (Var (Arg opName n), t)




-- Monadic operations ----------------------------------------------------------

forEach2' (x:xs) ~(y:ys) f  = (:) # f x y <# forEach2' xs ys f
forEach2' _ _ _             = return []
                                

-- | Pick unqiue top level names.
-- Assumption: top level names are qualified, local names are not qualified.
isGlobal :: Name -> Bool
isGlobal (UName (A.Qual _ _))             = True
isGlobal (UName (A.Inst (A.Qual _ _) _))  = True
isGlobal _                                = False


areaName, wFunName :: Name -> CM Name

areaName x | isGlobal x = return x
areaName x              = topName x

wFunName x | isGlobal x = return (FunFor x)
wFunName x              = FunFor # topName x



-- | Pick a name for the worker function of a particular function. 
topName            :: Name -> CM Name
topName x'          = do s <- get
                         let x      = GlobFor x'
                             m1     = workNames s 
                             f _    = (+) 
                             (n,m2) = Map.insertLookupWithKey f x 1 m1
                         set (s { workNames = m2 })

                         return $ case n of
                                    Nothing -> x
                                    Just n  -> Ren x n

addWhatsNew        :: WhatsNew -> CM ()
addWhatsNew w       = do s <- get
                         set s { todo = w : todo s }

isKnown            :: Name -> CM (Maybe KnownFun)
isKnown f           = (Map.lookup f . known) # ask

class TypeOf t where
  typeOf           :: t -> CM SimpleType

instance TypeOf Name where
  typeOf x          = do e <- types # ask
                         case Map.lookup x e of
                           Just t   -> return t
                           Nothing  -> bug "typeOf" 
                                           ("Undefined name: " ++ show x)

instance TypeOf Atom where
  typeOf (Var x)    = typeOf x
  typeOf (Lit l)    = typeOf l

instance TypeOf Literal where
  typeOf (Int _)    = return tIntSimple



addTypes           :: [Binder] -> CM a -> CM a
addTypes bs m       = do e <- ask
                         local (e { types = newMap (types e) }) m
  where
  newMap m          = foldr add1 m bs
  add1 (Bind x t) m = Map.insert x t m


addKnown           :: [(Name,KnownFun)] -> CM a -> CM a
addKnown xs  m      = do e <- ask
                         local (e { known = newMap (known e) }) m
  where
  newMap m          = foldr (uncurry Map.insert) m xs

addTop             :: [Binder] -> CM a -> CM a
addTop bs m         = do e <- ask 
                         let e'  = e { topLevel = Set.fromList (map varName bs) 
                                            `Set.union` topLevel e }
                         local e' m


> module ModuleSystem (resolve) where

We are using the following modules:

> import AST as A
> import Pass
> import Error
> -- import PP
> 
> import ModSys.AST as M
> import ModSys.Sem
> import ModSys.Ents 
> import ModSys.Relations
> import Depend.FVs
> import Depend.FVs_AST()

> import Data.Set (Set)
> import qualified Data.Set as Set
> import Data.List(sort,group)
> import MonadLib
> import Utils


Entry Point
~~~~~~~~~~~

XXX: The rules are very ad-hok.  Could we at least fake something
so that we pass them in as if they were in their own module?

> resolve :: [A.Module] -> RuleEnv -> Pass ([DataDecl],BindBlock,RuleEnv)
> resolve ms rules =
>   do ms1 <- mapM modSysModule ms
>      let modNames = map A.modName ms
>      case mProgram ms1 of
>        Left es -> let toErr m xs = ("In module: " ++ show m) : map show xs
>                       allErrs = concat (zipWith toErr modNames es)
>                   in err allErrs
>                        
>        Right results ->
>          do let globs   = map (applyRel . fst) results
>             (mPrim,gPrim) <- findPrimMod (zip modNames globs)
>             rs' <- resolveRules mPrim gPrim rules
>             (tss,bs) <- unzip # zipWithM aModule globs ms
>             let block = BindBlock (concat (map prims bs))
>                                   (concat (map areas bs))
>                                   (entry : concat (map expBinds bs))
>                                   (concat (map impBinds bs))
>             return (concat tss, block, rs')

> findPrimMod xs  = case lookup "Prims" xs of
>                     Just g   -> return ("Prims", g)
>                     Nothing  -> err ["Cannot find the module 'Prims'"]


XXX: This is a hack.  We resolve rules as if they are in
the module "Prims".

> resolveRules :: A.ModName -> (QName -> [Entity]) -> RuleEnv -> Pass RuleEnv
> resolveRules m g e = 
>   do sRs <- run m g (mapM aRule (superRules e))
>      iRs <- run m g (mapM aRule (instRules e))
>      return (RuleEnv sRs iRs)

XXX: Not good if we are not compiling a whole program.

> entry = ExpBind (ImpBind entryName  (MIs (Var mainName))) (mono mainType)


> modErrs m es  = err (("In module: " ++ show m) : es)



       
What does a module define?
~~~~~~~~~~~~~~~~~~~~~~~~~~

The functions in this section compute the entities
defined in a module.  This is part of the input to
the module system proper.

> modSysModule   :: A.Module -> Pass M.Module
> modSysModule m  = case duplicates of 
>                     [] -> return $
>                           M.Module { M.modName    = mName,
>                                      M.modExpList = A.modExpList m,
>                                      M.modImports = A.modImports m,
>                                      M.modDefines = defs }
>                     -- report where
>                     _ -> modErrs m [ "Multiple definitions for " ++ show x
>                                                       | x <- duplicates ]
>   where
>   mName         = A.modName m
>   vs            = defBindBlock mName (modBinds m) 
>   ess           = concat (vs : map (defDataDecl mName) (modTypes m))
>   defs          = listToRel [ (name e, e) | e <- ess ]
>   duplicates    = [ name x | x : _ : _ <- group (sort ess) ]


These functions compute value entities introduced by a binding block.

> defPrim m p       = [ Entity m (primName p) Value ]
> defArea m a       = [ Entity m (arName a) Value ]
> defExpBind m b    = defImpBind m (impBind b)
> defImpBind m b    = [ Entity m (biName b) Value ]
> defBindBlock m b  = concatMap (defPrim m)    (prims b) ++
>                     concatMap (defArea m)    (areas b) ++
>                     concatMap (defExpBind m) (expBinds b) ++
>                     concatMap (defImpBind m) (impBinds b)


These functions compute the entities introduced by various type declarations.  

> defAlgData m (AlgData x _ cs) = tys ++ cons
>   where tys               = [ Entity m x (Type (Set.fromList cons)) ]
>         cons              = map con cs
>         con (DataCon x _) = Entity m x Constr 
>
> defBitData m (BitData x cs _) = tys ++ cons
>   where tys     = Entity m x (Type (Set.fromList (cons ++ conTs))) : conTs
>         conTs   = map conT cs
>         cons    = map con cs
>         con c   = Entity m (fcName c) Constr
>         conT c  = Entity m (TSub x (fcName c)) (Type Set.empty)
>
> defStruct m s = [Entity m (stName s) (Type Set.empty)]
>
> defTypeSyn m (TypeSyn x _ _) = [ Entity m x (Type Set.empty) ]
>
> -- XXX: At the moment there is no way to specify ownership in ifaces.
> defKSig m (KSig x _) = [ Entity m x (Type Set.empty) ]
>
> defDataDecl m d = case d of
>                     DataDecl d    -> defAlgData m d
>                     BitdataDecl d -> defBitData m d
>                     StructDecl d  -> defStruct m d
>                     TypeDecl d    -> defTypeSyn m d
>                     KSigDecl d    -> defKSig m d



Rewriting
~~~~~~~~~

Here we replace top-level names with their "original names".


The Monad
~~~~~~~~~

> type M      = ReaderT Env (WriterT [(Name,[Entity])] Id) -- Env/Errors
> 
> data Env  = Env { theMod  :: ModName,
>                   globals :: QName -> [Entity],
>                   locals  :: Set Name }

The writer component of this monad is used to report errors.
It is easy to compute many errors, so instead of using an exception
monad we use a writer monad to collect all errors.

In the environment we carry the name of the module that we are processing,
a global function that maps qualified names to entities (from the result
of the module system proper) and a bunch of local names, so that we
can handle local names that shadow global names.

> withLocals :: Set.Set Name -> M a -> M a
> withLocals xs m = do e <- ask
>                      let e' = e { locals = Set.union xs (locals e) }
>                      local e' m


A generic lookup function that "rewrites" a global name (as long as a given
predicate is satisified).  It checks if the name is shadowed, and if it
isn't it looks it up in the map.  If there is only one possible interpretation,
then everything is OK but, otherwise, we report an error.

> lkp      :: (Entity -> Bool) -> Name -> M Name
> lkp _ x@(TNat _)    = return x
> lkp _ x@(TLab _)    = return x
> lkp _ x@(Select _)  = return x
> lkp _ x@(Update _)  = return x
> lkp p x   = do e <- ask
>                if x `Set.member` locals e then return x
>                  else case [ e | e <- globals e (Q x), p e ] of
>                         [ e ]  -> return (origName e)
>                         es     -> put [(x,es)] >> return x

The following are various specializations of 'lkp'.  The first
two are used to replaces uses of names for values and types repectively.
We have two functions, corresponding to the two namespaces (i.e.,
we may have a value and a type with the same name).

> lkpVal x      = lkp (not . isType) x
> lkpTy x       = lkp isType x

The next two functions are used when we replace top level
definitions with their original names (I guess this is not
strictly neccessary but it makes things easier).  They we only
consider the entities that are defined in this function.

XXX: It seems that this will already catch multiple definitions
for something, so we do not need to perform the check in 'modSysModule'.

> lkpValDef x   = do m <- theMod # ask
>                    lkp (\e -> not (isType e) && definedIn e == m) x
>
>
> lkpTyDef x    = do m <- theMod # ask
>                    lkp (\e -> isType e && definedIn e == m) x 


> run :: ModName -> (QName -> [Entity]) -> M a -> Pass a
> run x gs m = let (a,errs) = runId $ runWriterT 
>                           $ runReaderT (Env x gs Set.empty) m
>              in case errs of
>                   []    -> return a
>                   errs  -> modErrs x (map report errs)
>   where report (x,[]) = "Undefined name " ++ show x
>         report (x,xs) = "Ambiguous name, " ++ show x ++ " |-> " ++ show xs




Rewriting a whole module
~~~~~~~~~~~~~~~~~~~~~~~~

> aModule :: (QName -> [Entity]) -> A.Module -> Pass ([DataDecl], BindBlock)
> aModule gs m 
>   = run (A.modName m) gs 
>   $ do b  <- topBindBlock (modBinds m)
>        ts <- mapM topType (modTypes m) 
>        return (ts,b)


Rewriteing Types
~~~~~~~~~~~~~~~~

> topType :: DataDecl -> M DataDecl
> topType (BitdataDecl b)   = BitdataDecl # bitData b 
> topType (DataDecl d)      = DataDecl # algData d
> topType (TypeDecl d)      = TypeDecl # typeDecl d
> topType (KSigDecl d)      = KSigDecl # ksigDecl d
> topType (StructDecl d)    = StructDecl # structDecl d

> structDecl (Struct t as fs s)
>   = Struct # lkpTyDef t <# return as
>           <# (mono # forEach (poly fs) structField) <# forEach s aType

> structField (StField l t p) = StField l # aType t <# return p
> structField (StPad p)       = StPad # forEach p aType

> -- we do not resolve kinds...
> ksigDecl (KSig x k) = KSig # lkpTyDef x <# return k    

> typeDecl (TypeSyn c as t) = TypeSyn # lkpTyDef c <# return as <# aType t
> 
> bitData (BitData t cs ds) = BitData # lkpTyDef t <# forEach cs flatCon
>                                                  <# forEach ds lkpTy 

> flatCon f@(FlatCon2 {})
>   = FlatCon2 # lkpValDef (fcName f) 
>             <# field2 (fcFields2 f) 
>             <# withLocals fs (forEach (fcIf f) expr)
>   where fs = Set.fromList $ map fieldName $ l2Fields $ fcFields2 f

> flatCon f@(FlatCon {})
>   = FlatCon # lkpValDef (fcName f)
>            <# forEach (fcFields f) field
>            <# forEach (fcAs f) asClause 
>            <# withLocals fs (forEach (fcIf f) expr)
>   where fs = Set.fromList $ map fieldName $ fcFields f

> asClause as = forEach as layout
> layout (LaySig ls t)  = LaySig # forEach ls layout <# aType t
> layout l              = return l
> field f = Field (fieldName f) # aType (fieldType f) 
>                              <# forEach (fieldDefault f) expr
>
> field2 (BF_Named f)   = BF_Named # field f
> field2 (BF_Cat l r)   = BF_Cat # field2 l <# field2 r
> field2 (BF_Sig l t)   = BF_Sig # field2 l <# aType t
> field2 (BF_Tag n)     = return (BF_Tag n)
> field2 BF_Wild        = return BF_Wild  
> field2 BF_Unit        = return BF_Unit


> algData (AlgData t as cs) = (`AlgData` as) # lkpTyDef t <# forEach cs algCon
> algCon (DataCon c ts) = DataCon # lkpValDef c <# forEach ts aType
>
> aType    :: Type -> M Type
> aType t   = case t of
>               TApp t1 t2  -> TApp # aType t1 <# aType t2
>               TCon c      -> TCon # lkpTy c 
>               TFree _     -> return t
>               TSyn {}     -> "aType" `unexpected` "TSyn"
>               TInfix {}   -> "aType" `unexpected` "TInfix"
>               TParens {}  -> "aType" `unexpected` "TParens"

> aPoly     :: (t -> M t) -> Poly t -> M (Poly t)
> aPoly f s  = do ps <- forEach (polyPreds s) aPred
>                 t  <- f (poly s)
>                 return (s { polyPreds = ps, poly = t }) 
> 
> aSchema  :: Schema -> M Schema
> aSchema s = aPoly aType s
>             
> aPred    :: Pred -> M Pred
> aPred (CIn c ts) = CIn # lkpTy c <# forEach ts aType 
>
> aRule    :: Rule -> M Rule
> aRule (Rule how p)  = Rule how # aPoly aPred p

              
Rewriting of Value Bindings
~~~~~~~~~~~~~~~~~~~~~~~~~~~

> topPrim (PrimDecl x e t) = PrimDecl # lkpValDef x <# return e <# aSchema t
> topArea a = do x <- lkpValDef (arName a)
>                t <- aType (arType a)
>                return (a { arName = x, arType = t })
> topExpBind (ExpBind i s)  = ExpBind # topImpBind i <# aSchema s
> topImpBind (ImpBind x m)  = ImpBind # lkpValDef x <# match m
> topBindBlock (BindBlock ps as es is)
>   = BindBlock  # mapM topPrim ps <# mapM topArea as 
>               <# mapM topExpBind es <# mapM topImpBind is


> locPrim (PrimDecl x e t)  = PrimDecl x e # aSchema t
> locArea a                 = do t <- aType (arType a)
>                                return (a { arType = t })
> locExpBind (ExpBind i s)  = ExpBind # locImpBind i <# aSchema s
> locImpBind (ImpBind x m)  = ImpBind x # match m
> locBindBlock (BindBlock ps as es is)
>   = BindBlock  # mapM locPrim ps <# mapM locArea as 
>               <# mapM locExpBind es <# mapM locImpBind is


> match  :: Match -> M Match
> match m = case m of
>             MOr m1 m2 -> MOr # match m1 <# match m2
>             MIs e     -> MIs # expr e
>             MPat p m  -> do p' <- pat p
>                             m' <- withLocals (defs p) (match m)
>                             return (MPat p' m')
>             MGrd q m  -> do q' <- qual q
>                             m' <- withLocals (defs q) (match m)
>                             return (MGrd q' m')
>
>             MAbsT {}  -> "match" `unexpected` "MAbsT"
>             MAbsEv {} -> "match" `unexpected` "MAbsEv"
> 
> 
> expr   :: Expr -> M Expr
> expr e  = case e of
>             App e1 e2 -> App # expr e1 <# expr e2
>             Match m   -> Match # match m
>             Var x     -> Var # lkpVal x 
>             Lit _     -> return e
>             
>             Sig e t   -> Sig # expr e <# aType t
>             Con c fs  -> Con # lkpVal c <# forEach fs fieldV   
>             Upd e fs  -> Upd # expr e <# forEach fs fieldV 
>
>             Do p e1 e2 -> do e1 <- expr e1
>                              p' <- pat p
>                              e2 <- withLocals (defs p') (expr e2)
>                              return (Do p' e1 e2)
>
>             AppT {}   -> "expr" `unexpected` "AppT"
>             AppEv {}  -> "expr" `unexpected` "AppEv"
>             Parens {} -> "expr" `unexpected` "Parens"
>             Infix {}  -> "expr" `unexpected` "Infix"
> 
> 
> fieldV :: FieldV -> M FieldV 
> fieldV (FieldV l _ e) = FieldV l Nothing # expr e
> 
> 
> qual   :: Qual -> M Qual
> qual q  = case q of
>             QPat p e      -> QPat # pat p <# withLocals (defs p) (expr e)
>             QLet bs       -> QLet # withLocals (defs bs) (locBindBlock bs)
>             QGrd e        -> QGrd # expr e
>             QLocal q1 q2  -> QLocal # qual q1 <# withLocals (defs q1) (qual q2)
>             QThen q1 q2   -> QThen # qual q1 <# withLocals (defs q1) (qual q2)
>
> pat    :: Pat -> M Pat
> pat p   = case p of
>             PVar _          -> return p   
>             PWild           -> return p
>             PSig p t        -> PSig # pat p <# aType t
>             PAbs p q        -> PAbs # pat p <# withLocals (defs p) (qual q) 
>             PApp p ts es ps -> PApp # bpat p <# mapM aType ts <# return es <# mapM pat ps
> {-
>             PCon c _ ps   -> do c <- lkpVal c
>                                 PCon c [] # forEach ps pat
>             PSplit p1 p2  -> PSplit # pat p1 <# pat p2
>             PInc x k e  -> PInc x k # expr e
>             PDec x k e  -> PDec x k # expr e
>             PEv {}      -> "pat" `unexpected` "PEv"
> -}
>
>             PParens {}  -> "pat" `unexpected` "PParens"
>             PInfix {}   -> "pat" `unexpected` "PInfix"
>
> bpat p = case p of
>            BPSplit        -> return p
>            BPCon c        -> BPCon # lkpVal c
>            BPUpd d e1 e2  -> BPUpd d # expr e1 <# expr e2




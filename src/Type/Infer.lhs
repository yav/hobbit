> module Type.Infer (inferModule,DB(..)) where
> 
> import AST
> import Error
> import Type.Monad
> import Type.Error
> import Type.Algs
> import Type.FVS
> import Type.Env
> import Depend.SCC
> import Depend.FVs_AST()
> import Utils
> import MonadLib hiding (collect)
> import qualified Pass
> 
> import Control.Monad.Fix(MonadFix(mfix))
> import Data.Maybe(fromMaybe)

 
The types for built-in families of constants:

> famTEnv :: TypeM Type.Env.Env
> famTEnv = do t1@(TFree a) <- newTVarAnon kType
>              t2@(TFree b) <- newTVarAnon kType
>              let fam (Select l) = Just $ Forall [a,b] 
>                                          [CIn cField [tLab l,t2,t1]]
>                                        $ tFun t2 t1
>                  fam (Update l) = Just $ Forall [a,b]
>                                          [CIn cUpdField [tLab l,t2,t1]]
>                                        $ tFun t1 (tFun t2 t2)
>                  fam _ = Nothing
>              return $ Type.Env.fromFun fam

The types of adts constructors:







                  = Top Level Bindings =
```

> inferModule  :: DB -> [Pred] -> BindBlock -> Pass.Pass ([BDT],BindBlock)
> inferModule db ps bs  = run db 
>                       $ do (r,gs,dgs) <- collect' check
>                            solveGoals gs dgs
>                            return r
>   where check = do forEach ps newEv
>                    (bs,env) <- tcBinds bs
>                    tys <- inExtEnvL env $ forEach (bdts db) checkBDT 
>                    return (tys,bs)
 
```                         
                          

Check the expressions in bitdata declarations.
The rewriting of expressions does not expand defaults
and ``if`` clauses so it is safe to do this in a context
where the expressions in other BDTS are not yet processed.
```

> checkBDT b          = do cs <- forEach (bdtCtrs b) checkBDTCtr
>                          return (b { bdtCtrs = cs })
> checkBDTCtr c       = do fs <- forEach (bcFields c) checkField
>                          i  <- forEach (bcIf c) checkIf
>                          return (c { bcFields = fs, bcIf = i })
> checkField f        = do e <- forEach (fieldDefault f) (\e -> 
>                                 do (e,t) <- infer e
>                                    unify t (fieldType f)
>                                    return e)
>                          return (f { fieldDefault = e })

> -- XXX: do we need to check anything here?
> -- Remeber that in Types.Bitdata we generated a definition for the 'if'...
> checkIf e           = do -- (e,t) <- infer e
>                          -- unify t tBool
>                          return e

                          
```


```

> class Infer a b where
>   infer :: a -> b
> 

```
                == Literals ==
```

> instance Infer Literal (TypeM (Expr,Type)) where
>   infer l = case l of
>               Int _ -> do let fromNat = Qual "Prims" (VarName "fromNat")
>                           s <- lkp fromNat
>                           (as,xs,t) <- instantiate s
>                           let e2 = tapps (Var fromNat) (map TFree as)
>                               e3 = App (eapps e2 xs) (Lit l)
>                           return (e3,tCod t)
>               Chr _ -> return (Lit l, tChar)
>               Str _ -> return (Lit l, tString)

```

              == Expressions ==
```

> instance Infer Expr (TypeM (Expr,Type)) where
> 
>   infer e = case e of
>         
>               App e1 e2   -> do (e1,t1) <- infer e1
>                                 (e2,t2) <- infer e2
>                                 a <- newTVarAnon kType
>                                 unify t1 (tFun t2 a) 
>                                 return (App e1 e2, a)
>
>               Var x       -> 
>                 do s <- lkp x
>                    (as,xs,t) <- instantiate s
>                    me <- recVar x
>                    let e1 = fromMaybe (Var x) me
>                        e2 = tapps e1 (map TFree as)
>                        e3 = eapps e2 xs
>                    return (e3,t)
> 
>               Lit l       -> infer l
> 
>               -- XXX: Should allow schemas in sigs (handle early by rewrite)
>               Sig e s     -> do (e,t) <- infer e
>                                 unify t s
>                                 return (e,s)
>
>               Match m -> do (m,t) <- infer m
>                             return (Match m, t)
>
> 
>               Con c fs    -> checkCon c fs
> 
>               Upd e fs    -> 
>                 do (e,t) <- infer e
>                    fs    <- forEach fs $ \(FieldV l _ e') -> 
>                               do (e',t') <- infer e'
>                                  -- d <- newEv (CIn cHas [tLab l,t',t])
>                                  d <- newEv (CIn cUpdField [tLab l,t,t'])
>                                  return (FieldV l (Just d) e')
>                    return (Upd e fs, t)
>
>               Do p e1 e2  -> do (e1,t1) <- infer e1
>                                 (p,a,env) <- infer p
>                                 unify (tM a) t1
>                                 (e2,t2) <- inExtEnvL env (infer e2)
>                                 b <- newTVarAnon kType
>                                 unify (tM b) t2
>                                 return (Do p e1 e2,t2)
>
>               AppT {}     -> "infer@Expr" `unexpected` "AppT"
>               AppEv {}    -> "infer@Expr" `unexpected` "AppEv"
>               Parens {}   -> "infer@Expr" `unexpected` "Parens"
>               Infix {}    -> "infer@Expr" `unexpected` "Infix"
> 
> 
> checkCon c fs = do (bdt,ctr) <- getBDTCtr c 
>                    fs        <- checkField fs [] (bcFields ctr)
>                    return (Con c fs, bdtAsType bdt)
>   where 
>   fieldName (FieldV x _ _)  = x
> 
>   checkField [] done []   = return done
>   checkField fs done []   = errs (map toErr fs)
>     where toErr f | x `elem` doneNames  = x `MultipleInitializers` c
>                   | otherwise           = x `UndefinedFieldOf` c
>                     where x = fieldName f
>           doneNames  = map fieldName done
>     
>   checkField fs done (AST.Field l s e : rest) = 
>     case remove ((l ==) . fieldName) fs of
>       Just (FieldV l x e,fs) -> 
>         do (e,t) <- infer e
>            unify t s
>            checkField fs (FieldV l x e : done) rest
>       Nothing -> 
>         case e of
>           Nothing -> err (l `UninitializedFieldOf` c)
>           Just _  -> let def = defName c l
>                      in checkField fs (FieldV l Nothing (Var def) : done) rest

```

                    == Matches ==                              
```
              
> instance Infer Match (TypeM (Match,Type)) where
> 
>   infer m = case m of
> 
>               MOr m1 m2     -> do (m1,t1) <- infer m1
>                                   (m2,t2) <- infer m2
>                                   unify t1 t2
>                                   return (MOr m1 m2, t1)
> 
>               MIs e         -> do (e,t) <- infer e
>                                   return (MIs e,t)
>
>               MPat p m      -> do (p,t1,env) <- infer p
>                                   (m,t2) <- inExtEnvL env (infer m)
>                                   return (MPat p m, tFun t1 t2)
>
>               MGrd q m      -> do (q,env) <- infer q
>                                   (m,t) <- inExtEnvL env (infer m) 
>                                   return (MGrd q m, t)
> 
>               MAbsT _ _     -> "infer(match)" `unexpected` "MAbsT"
>               MAbsEv _ _ _  -> "infer(match)" `unexpected` "MAbsEv"

```

                  == Qualifiers ==
```

> instance Infer Qual (TypeM (Qual,[(Name,Schema)])) where
> 
>   infer q = case q of
>     
>     QGrd e -> do (e,t) <- infer e
>                  unify t tBool
>                  return (QGrd e, [])
> 
>     QLet bs -> do (bs,env) <- tcBinds bs
>                   return (QLet bs,env)
> 
>     QPat p e -> do (p,s,env) <- infer p
>                    (e,t) <- infer e
>                    unify t s
>                    return (QPat p e, env) 
> 
>     QLocal q1 q2  -> do (q1,env1) <- infer q1
>                         (q2,env2) <- inExtEnvL env1 (infer q2)
>                         return (QLocal q1 q2, env2)
> 
>     QThen q1 q2 -> do (q1,env1) <- infer q1
>                       (q2,env2) <- inExtEnvL env1 (infer q2)
>                       return (QThen q1 q2, env2 ++ env1)
 
```


Patterns
~~~~~~~~
  
> instance Infer FieldP (Type -> TypeM (FieldP,[(Name,Schema)])) where
>   infer (FieldP l _ p) ty   =  do (p,t,env) <- infer p
>                                   d <- newEv (CIn cField [tLab l,ty,t])
>                                   return (FieldP l (Just d) p,env)  
> 
> 
> instance Infer Pat (TypeM (Pat,Type,[(Name,Schema)])) where
>   
>   infer p = case p of
>   
>               PVar x -> 
>                 do a <- newTVarAnon kType
>                    return (PVar x `PSig` a, a, [(x,mono a)])
> 
>               PWild -> 
>                 do a <- newTVarAnon kType
>                    return (PWild `PSig` a, a, [])
>
>               PSig p s -> 
>                 do (p,t,env) <- infer p
>                    unify t s
>                    return (p,s,env)
> 
>               PAbs p q -> 
>                 do (p',t,env1) <- infer p
>                    (q',env2) <- inExtEnvL env1 (infer q)
>                    return (PAbs p' q', t, env2 ++ env1)
>
>               -- Note: we ignore incoming types and evidence
>               -- because they should be empty.  In the future
>               -- we might want to change this to provide control
>               -- over how pattrens are instantiated.
>               -- Note: could remove PSig here but it is convinient to keep
>               PApp p _ _ ps ->
>                 do (ps,ts,envss) <- unzip3 # forEach ps infer
>                    (p',s) <- infer p
>                    (as,ev,t) <- instantiate s
>                    a <- newTVarAnon kType
>                    unify (foldr tFun a ts) t
>                    return ( PApp p' (map TFree as) ev ps `PSig` a
>                           , a
>                           , concat (reverse envss)
>                           )
>
> {-
>               -- Note: we do not make 'if' clauses explicit here.
>               -- Note: We adopt the Haskell approach to qualified ctrs
>               -- (i.e., evidence is an extra argument)
>               PCon c _ ps -> 
>                 do (ps,ts,envss) <- unzip3 # forEach ps infer
>                    (as,_,t) <- instantiate =<< lkp c  
>                    -- NOTE: we ignore the evidence here
>                    -- but the goals are still added.
>                    a <- newTVarAnon kType
>                    unify (foldr tFun a ts) t
>                    return ( PCon c (map TFree as) ps `PSig` a
>                           , a
>                           , concat (reverse envss)
>                           )
>               
>               PSplit p1 p2  -> 
>                 do (p1,t1,env1) <- infer p1
>                    (p2,t2,env2) <- infer p2
>                    a <- newTVarAnon kNat
>                    b <- newTVarAnon kNat
>                    c <- newTVarAnon kNat
>                    d <- newEv (CIn cJoin [a, b, c]) 
>                    unify t1 (tBit a)
>                    unify t2 (tBit b)
>                    let t = tBit c
> 
>                    return ( (PSplit p1 p2 `PEv` d) `PSig` t
>                           , t
>                           , env2 ++ env1
>                           )
> 
>               PInc x k e ->
>                 do (e,t) <- infer e
>                    n <- newTVarAnon kNat
>                    unify t (tIx n) 
>                    return (PInc x k e `PSig` t, t, [(x,mono t)])
>
>               PDec x k e ->
>                 do (e,t) <- infer e
>                    n <- newTVarAnon kNat
>                    unify t (tIx n)
>                    return (PDec x k e `PSig` t, t, [(x,mono t)])
>                    
>                    
> 
>               PEv {} -> bug "infer.Pat" "PEv"
> -}
>               PParens {} -> bug "infer.Pat" "PParens"
>               PInfix {} -> bug "infer.Pat" "PInfix"


> instance Infer BPat (TypeM (BPat,Schema)) where
>   infer p = case p of
>
>               BPSplit -> (,) p `fmap` lkp (qPrim (VarName "#"))
>               BPCon c -> (,) p `fmap` lkp c
>               -- XXX: no evidence?
>               BPUpd d e1 e2 -> do (e1,t1) <- infer e1
>                                   (e2,t2) <- infer e2
>                                   t <- tIx `fmap` newTVarAnon kNat
>                                   unify t1 t
>                                   unify t2 t
>                                   return (BPUpd d e1 e2, mono (tFun t t))



                                   


Checking Bindings
~~~~~~~~~~~~~~~~~


> tcBinds      :: BindBlock -> TypeM (BindBlock, [(Name,Schema)])
> tcBinds b     = do b <- improveExps b
>                    let env1 = expEnv b
>                    (iBs,env2) <- inExtEnvL env1 (infs (sccs (impBinds b)))
>                    let env = env2 ++ env1
>                    inExtEnvL env $
>                      do as <- mapM checkArea (areas b)
>                         es <- mapM checkExpl (expBinds b)
>                         return (b { areas    = as,
>                                     expBinds = es ++ iBs,
>                                     impBinds = [] }, env)
>   where
>   infs (bs:bss) = do (bs,env) <- implicit (compDefs bs)
>                      (bss,envs) <- inExtEnvL env (infs bss)
>                      return (bs++bss, env ++ envs)
>   infs []       = return ([],[])


> improveExps  :: BindBlock -> TypeM BindBlock
> improveExps b = do es <- mapM impExp (expBinds b)
>                    return (b { expBinds = es }) 
>   where 
>   impExp (ExpBind x s)  = do s <- nicerPoly s
>                              return (ExpBind x s)

> expEnv       :: BindBlock -> [(Name,Schema)]
> expEnv b      = map primT (prims b) ++
>                 map areaT (areas b) ++
>                 map expT (expBinds b)
>   where
>   primT p             = (primName p, primType p)
>   areaT a             = (arName a, mono (arType a))
>   expT (ExpBind i s)  = (biName i, s)


> checkExpl    :: ExpBind -> TypeM ExpBind
> checkExpl (ExpBind (ImpBind x m) sc) = inDefn x $
>   do sc <- nicerPoly sc
>      ((as,ev,s),ds) <- collect (instantiate sc)
>      as' <- inBase $ fvs $ map TFree as
>      ((m,t),gs,gsD) <- collect' $ infer m
>      unifyWith as' t s
>      (gs,[Forall bs _ _]) <- generalize' as' gs [s]  
>      let preds = map goalPred ds
>          old (DGoal        es  (Forall      xs            ps  gs)) 
>               = DGoal (ev ++ es) (Forall (as'++xs) (preds ++ ps) gs)
>      delay' (DGoal ev (Forall as' preds gs) : map old gsD)
>      newDefn ds (Forall as' preds s) (ImpBind x m)

> -- | Abstract over types, evidence, and provide definitions for evidence.
> newDefn            :: [Goal]      -- ^ Abstracted evidence
>                    -> Schema      -- ^ Schema for the bindings
>                    -> ImpBind     -- ^ Binding from which we are abstracting
>                    -> TypeM ExpBind
> newDefn ds s (ImpBind x m) = do forEach_ ds $ \ (Ev x _) -> 
>                                     addEvDef x (AsmpEv x)
>                                 return (ExpBind (ImpBind x withTy) s)
>   where 
>   withTy            = foldr MAbsT (foldr mAbsEv m ds) (polyVars s)
>   mAbsEv (Ev x p) m = MAbsEv x p m


> -- | Compute replacement for recursive occurences to variables.
> -- While infering types for a group of recursive bindings we assume
> -- monomorphic types for the bindings.  Eventually, however,
> -- the bindings may become polymorphic and overloaded.  Therefore in
> -- the code we need to replace the recursive calls with ones that
> -- are instantiated appropriately, and given the neccessary evidence.
> newCallSite        :: [EvName]    -- ^ Name for the evidence
>                    -> Name      -- ^ Name of the binding
>                    -> [TyVar]   -- ^ Type variables
>                    -> (Name, Expr)
> newCallSite ds x xs 
>   = (x, eapps (Var x `tapps` map TFree xs) (map AsmpEv ds))

> -- | Type-check a SCC of implicitly typed bindings
> implicit     :: [ImpBind] -> TypeM ([ExpBind], [(Name,Schema)])
> implicit bs   
>   = do (_,_,x,y) <- mfix $ \ ~(schemas,dicts,_,_) -> 
> 
>          do let xs      = map biName bs
>             ts         <- forEach xs (\_ -> newTVarAnon kType)
>             let tyVarss = map polyVars schemas
>                 recVars = zipWith' (newCallSite (map goalName dicts)) 
>                                                                 xs tyVarss
>   
>             (bs1,ps) <- collect                         
>                       $ inExtEnvL (zip xs (map mono ts)) 
>                       $ withRecVars recVars
>                       $ zipWithM infer1 bs ts
>   
>             (dicts,schemas) <- generalize ps ts
>             bs2 <- forEach2 schemas bs1 (newDefn dicts) 
>             return (schemas,dicts,bs2, xs `zip` schemas)
>                     
>        return (x,y)
>   where
>   infer1 (ImpBind x m) s  = do (m,t) <- inDefn x $ infer m
>                                unify t s
>                                return (ImpBind x m)

> checkArea :: AreaDecl -> TypeM AreaDecl
> checkArea a = do d <- newEv (CIn cAreaDecl [arType a])
>                  return (a { arEv = Just d })






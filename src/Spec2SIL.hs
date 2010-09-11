-- | Goals:
--  * Sequentialize expression evaluation
--  * Simplify patterns
--  * Rename expressions to avoid variable shadowing.
--  * Provide definitions for primitives and constructor functions
--    so that they can be treated uniformly in closure conversion.
--    Later these should be inlined. (XXX: this should be equivalent
--      to making constructors and prims fully applied)
--  * Translate away bitdata.  This also looses some type information:
--    bitdata types are translated into their underlying bit vector reps.


-- Preserving argument and fields names is hard
-- (given that we want to avoid shadowing).
-- Instead we try to preserve the names for definitions,
-- but argumenst and fields get generic derived names.
-- The n-th argument of function 'f' is Arg f n.
-- The n-the field (in a pattern) of a construcotr 'c' of value 'x'
-- is Field x c n.
-- For fields it is important that we also have the constructor name,
-- as otherwise we might get (bad) shadowing:
-- case x of
--   C a b -> let f y = a + y in
--            case x of
--              D c d -> f 2
-- if we don't use constructr names becomes:
-- case x of
--   C x$1 x$2 -> let f f$1 = x$1 + f$1 in
--                case x of
--                  D x$1 x$2 -> f 2
-- Now if we do closure conversion we pass the wrong value for the
-- free variable for 'f', and the program is not type correct any more.
--
-- Technically shadowing still occurs with the other schema, but it is harmless
-- because it is the exact same value that gets the same name.



module Spec2SIL (seqProg) where

import qualified AST as I
import qualified AST.SIL as O
import qualified BDD
import Depend.SCC
import Depend.FVs_AST()
import Error

import Utils
import MonadLib
import qualified Data.Map as Map
import Data.List(find,partition)
import Data.Bits
import Data.Word




-- XXX: In pattern translation:
--    * Name temporaries for subfields, using the Arg/Field convention
--      so that later when we check patterns we can report better errors.

--    * Make sure that there is no shadowing (required by CC) (this is ok now?)



seqProg            :: [I.ADT]                 -- ^ ADT types
                   -> [I.BDT]                 -- ^ Bitdata types
                   -> I.BindBlock             -- ^ Top level bindings
                   -> [O.Decl]  

seqProg adts bdts bs 
  = map (wrapper O.Con) aCtrs ++ map bWrap bCtrs 
 ++ fst (run bdts initSubst (topDecls bs))
  where
  toSub (x,t) = (x, (O.Var (O.UName x),t))
  initSubst   = Map.fromList (map toSub aCtrs ++ map (toSub . fst) bCtrs)
  aCtrs     = [ anADT a c  | a <- adts, c <- I.adtCtrs a ]
  bCtrs     = [ aBDT b c   | b <- bdts, c <- I.bdtCtrs b ]

  anADT a c = let c' = I.poly c in (I.acName c', aType a c')
  aBDT  b c = ((I.bcName c, transTName bdts (bType b c)), c)

  aType a c = foldr O.tFunSimple (I.adtName a) 
                                        (map (tType' bdts) (I.acFields c))
  bType b c = case I.bcFields c of
                [] -> I.bdtName b
                _  -> I.TSub (I.bdtName b) (I.bcName c) 
                                                `O.tFunSimple` I.bdtName b 

  -- aWrap (,) = 

  bWrap (xt,c) = wrapper mk xt
    where mk _ []   = conBase c
          mk _ [x]  = O.Atom x
          mk c _    = "bWrap" `bug` ("Too many arguments to: " ++ show c)

-- XXX: to really decide if we have a function or a value, look at 
-- result as well?  (if monadic computations are 0 arity functions)
  wrapper :: (O.Name -> [O.Atom] -> O.Expr) -> (I.Name, O.SimpleType) -> O.Decl
  wrapper body (x,t)
    = case O.args t2 of
        [] -> O.AVal (O.Bind x' t) (body x' [])
        ts -> let as = [ O.Bind a t | a <- map (O.Arg x') [0..] | t <- ts ]
              in O.AFun $ O.Fun 
                   { O.funName = x'
                   , O.funArgs = as
                   , O.funResT = O.result t2
                   , O.funDef  = body x' (map (O.Var . O.varName) as) }
    where x' = O.UName x
          t2 = O.fun2funT t
               



-- Expressions -----------------------------------------------------------------

expr               :: I.Expr -> M (O.Expr, O.SimpleType)
expr (I.Var x)      = do (a,t) <- apSubst x
                         return (O.Atom a, t)
expr e@(I.App _ _)  = apps O.CommE O.App e []
expr (I.Match m)    = do x <- newTmp 
                         (d,t) <- funMatch x m
                         return (O.CommE $ O.Let d (O.Atom (O.Var x)), t)
expr (I.Lit l)      = do (l,t) <- literal l
                         return (O.Atom (O.Lit l), t)

-- | Translate away bitdata constructors.
expr (I.Con c fs)   
  = do (bdt,con) <- getBDTCtr c
       t <- tType (I.bdtAsType bdt)
       updFields con fs (conBase con, t)

expr (I.Upd e []) = expr e
expr (I.Upd e fs)     
  = do et <- expr e
       con <- case snd et of
                I.Qual q (I.TSub _ c) -> snd # getBDTCtr (I.Qual q c)
                t                     -> "expr" `unexpected` show t
       updFields con fs et

expr e@(I.Do _ _ _) = do (s,t) <- toStmt e
                         return (O.Do s,t)
                         
expr (I.AppT {})    = "expr" `unexpected` "AppT"
expr (I.AppEv {})   = "expr" `unexpected` "AppEv"
expr (I.Sig {})     = "expr" `unexpected` "Sig"
expr (I.Parens {})  = "expr" `unexpected` "Parens"
expr (I.Infix {})   = "expr" `unexpected` "Infix"


literal            :: I.Literal -> M (O.Literal, O.SimpleType)
literal (I.Int n)   = return (O.Int n, O.tIntSimple)


toStmt :: I.Expr -> M (O.Stmt, O.SimpleType)
toStmt e@(I.Var _)    = apps O.CommS O.Call e []
toStmt e@(I.App _ _)  = apps O.CommS O.Call e []
toStmt (I.Match m)    = match O.CommS toStmt [] m
toStmt (I.Do p e1 e2) = do (s1,t1) <- toStmt e1
                           x       <- newTmp
                           let e    = O.Atom (O.Var x)
                               Just t1' = O.isM t1
                           (s2,t2) <- pat O.CommS p e t1' (toStmt e2)
                           return (O.LetM (O.Bind x t1') s1 s2, t2)
toStmt e              = "toStmt" `unexpected` show e 



apps :: HasComm a -> (O.Name -> [O.Atom] -> a) 
     -> I.Expr -> [O.Atom] -> M (a, O.SimpleType)
apps mk how (I.App e1 e2) xs = do r <- expr e2
                                  nameExpr mk r (\x -> apps mk how e1 (x:xs)) 
apps mk how e xs             = do (e,t) <- expr e
                                  nameExpr mk (e,t) $ \(O.Var f) -> 
                                    return (how f xs, 
                                            iterate O.tCodSimple t !! length xs)




conBase :: I.BDTCtr -> O.Expr
conBase con = O.primFromLitBit (I.bcWidth con) (O.Lit (O.Int base))
  where
  base = foldr (.|.) 0 (map lay (I.bcLayout con))
  lay :: I.FreeLayout -> Integer
  lay (I.LayInt n _ I.:@: b)  = (n .&. (2 ^ I.bfWidth b - 1))
                                       `shiftL` fromIntegral (I.bfOffset b)
  lay _                       = 0


updFields :: I.BDTCtr -> [I.FieldV] 
          -> (O.Expr, O.SimpleType) -> M (O.Expr, O.SimpleType)
updFields con fs et = loop [] [] fs 
  where
  fields      = [ (l,b) | I.LayField l I.:@: b <- I.bcLayout con ]
  fieldLoc l  = case lookup l fields of
                  Just b  -> b
                  Nothing -> "fieldLoc" `bug` ("Missing field: " ++ show l)

  loop :: [I.BitField] -> [O.Atom] -> [I.FieldV] -> M (O.Expr, O.SimpleType)
  loop bs as (I.FieldV l _ e2 : fs) 
    = do et <- expr e2
         nameExpr O.CommE et $ \a -> loop (fieldLoc l : bs) (a : as) fs
  loop bs as [] = nameExpr O.CommE et $ \a -> 
                  return (O.primUpdFields (I.bcWidth con) bs (a:as), snd et)
  





-- Pattern matching ------------------------------------------------------------


-- For when we don't know the type (see `pat`)
pat' :: HasComm a -> I.Pat -> O.Expr 
     -> M (a, O.SimpleType) -> M (a, O.SimpleType)
pat' mk (I.PSig p t) e k = do t <- tType t
                              pat mk p e t k
pat' _ p _ _  = "Spec2SIL" `unexpected` show p
 

pat :: HasComm a -> I.Pat -> O.Expr -> O.SimpleType 
    -> M (a, O.SimpleType) -> M (a, O.SimpleType)

pat mk (I.PSig p _) e t k = pat mk p e t k

-- x <- e; k
-- let x = e; k
pat mk (I.PVar x) e t k 
  = do x' <- tName x
       nameExpr' mk (Just x') (e,t) $ \a -> addSubst [(x,(a,t))] k

-- _ <- e; k
-- let _ = e; k
-- OR: just k   (ignoring nontermination)
pat _ I.PWild _ _ k = k
                                 
-- (p | q) <- e; k
-- (p <- e); q; k
pat mk (I.PAbs p q) e t k = pat mk p e t (qual mk q k)

-- see bpat
pat mk (I.PApp p ts es ps) e t k = bpat mk p ts es ps e t k


{-
-- p1 # p2 ev@(x,y) <- e; k
-- let v = e; p1 <- v(y,x); p2 <- v(0,y); k
pat mk (I.PSplit p1 p2 `I.PEv` ev) e t k
  = nameExpr mk (e,t) $ \x -> pat' mk p1 (upper x) $ pat' mk p2 (lower x) k
  where 
  -- XXX: Should we really be matching on the evidence like this?
  I.OpEv I.JoinEv [I.IntEv x, I.IntEv y] = ev
  upper a = O.primGetFieldB (x+y) (I.BitField y x) a
  lower a = O.primGetFieldB (x+y) (I.BitField 0 y) a

-- (x + n | x >= b) <- e; k
-- let u = e; let v = b; let x = u - n; if x >= v; k
pat mk (I.PDec x n b) e t k
  = nameExpr mk (e,t) $ \u -> 
    do b <- expr b
       nameExpr mk b $ \v -> 
         do let n' = fromIntegral n
            x' <- tName x
            nameExpr' mk (Just x') (O.Prim O.PDecBy [O.Lit (O.Int n'), u], t) 
              $ \a -> addSubst [(x,(a,t))] $
                      pat' mk pTrue (O.Prim O.PGEQ [a,v]) k
  

-- (x - n | x <= b) <- e; k
-- let u = e; let v = b; let x = u + n; if x <= v; k
pat mk (I.PInc x n b) e t k
  = nameExpr mk (e,t) $ \u -> 
    do b <- expr b
       nameExpr mk b $ \v -> 
         do let n' = fromIntegral n
            x' <- tName x
            nameExpr' mk (Just x') (O.Prim O.PIncBy [O.Lit (O.Int n'), u], t) 
              $ \a -> addSubst [(x,(a,t))] $
                      pat' mk pTrue (O.Prim O.PLEQ [a,v]) k

pat mk (I.PCon c _ ps) e t k
  = do c <- getBDTCtr' c 
       case c of 
         Nothing    -> adtCtr 
         Just (_,c) -> bdtCtr c 
  where
  -- C p1 p2 <- e; k   
  -- let x = e; case x of C -> p1 <- x.C.0; p2 <- x.C.1; k
  adtCtr    = nameExpr mk (e,t) $ \x -> 
              do -- c <- tName c
                 let c' = O.UName c  -- Use, not a definition
                 let subPat (n,p) k = pat' mk p (O.primGetFieldA c' n x) k 
                 case x of
                   O.Var x -> do (e,t) <- foldr subPat k $ zip [0..] ps
                                 return (mk $ O.Switch x [O.Case c' e], t)
                   O.Lit _ -> bug "pat" "Literal"
 
  -- C p <- e; k
  -- let x = e; bcase x of C.as -> ...check if...; p <- e; k
  -- XXX: check the IF clause as well
  bdtCtr c = nameExpr mk (e,t) $ \x -> 
             do let subPat p k = pat' mk p (O.Atom x) k
                (e,t) <- foldr subPat k ps
                return (mk $ O.BSwitch x [ O.BCase cAS e ], t)
    where
    cAS = foldr field (BDD.pWild (I.bcWidth c)) (I.bcLayout c)

    field (I.LayInt n _ I.:@: I.BitField o w) b = BDD.pField o (BDD.pInt w n) b
    field _ b                                   = b
-}

pat _ p _ _ _  = "pat" `unexpected` show p



-- p1 # p2 ev@(x,y) <- e; k
-- let v = e; p1 <- v(y,x); p2 <- v(0,y); k
bpat mk I.BPSplit _ [ev] [p1,p2] e t k
  = nameExpr mk (e,t) $ \x -> pat' mk p1 (upper x) $ pat' mk p2 (lower x) k
  where 
  -- XXX: Should we really be matching on the evidence like this?
  I.OpEv I.JoinEv [I.IntEv x, I.IntEv y] = ev
  upper a = O.primGetFieldB (x+y) (I.BitField y x) a
  lower a = O.primGetFieldB (x+y) (I.BitField 0 y) a

bpat mk (I.BPCon c) _ _ ps e t k
  = do c <- getBDTCtr' c 
       case c of 
         Nothing    -> adtCtr 
         Just (_,c) -> bdtCtr c 
  where
  -- C p1 p2 <- e; k   
  -- let x = e; case x of C -> p1 <- x.C.0; p2 <- x.C.1; k
  adtCtr    = nameExpr mk (e,t) $ \x -> 
              do -- c <- tName c
                 let c' = O.UName c  -- Use, not a definition
                 let subPat (n,p) k = pat' mk p (O.primGetFieldA c' n x) k 
                 case x of
                   O.Var x -> do (e,t) <- foldr subPat k $ zip [0..] ps
                                 return (mk $ O.Switch x [O.Case c' e], t)
                   O.Lit _ -> bug "pat" "Literal"
 
  -- C p <- e; k
  -- let x = e; bcase x of C.as -> ...check if...; p <- e; k
  -- XXX: check the IF clause as well
  bdtCtr c = nameExpr mk (e,t) $ \x -> 
             do let subPat p k = pat' mk p (O.Atom x) k
                (e,t) <- foldr subPat k ps
                return (mk $ O.BSwitch x [ O.BCase cAS e ], t)
    where
    cAS = foldr field (BDD.pWild (I.bcWidth c)) (I.bcLayout c)

    field (I.LayInt n _ I.:@: I.BitField o w) b = BDD.pField o (BDD.pInt w n) b
    field _ b                                   = b

-- (p + e1 | x >= e2) <- e; k
-- let u = e; let v = e1; let w = e2; let x = u - v; if x >= w; p <- x; k
bpat mk (I.BPUpd d e1 e2) _ _ [p] e t k
  = expr e1 >>= \e1 ->
    expr e2 >>= \e2 ->
    nameExpr mk (e,t) $ \u ->
    nameExpr mk e1    $ \v ->
    nameExpr mk e2    $ \w ->
    let (op,test) = case d of
                      I.Inc -> (O.PIncBy, O.PLEQ)
                      I.Dec -> (O.PDecBy, O.PGEQ)
    in nameExpr mk (O.Prim op [v,u],t) $ \x ->
       pat' mk pTrue (O.Prim test [x,w]) (pat mk p (O.Atom x) t k)

bpat _ bp ts evs _ _ _ _ = "bpat" `unexpected` show (bp,ts,evs)
    

         
pTrue = I.PApp (I.BPCon (I.qPrel (I.ConName "True"))) [] [] [] `I.PSig` tBool
tBool = I.TCon (I.qPrel (I.ConName "Bool"))


qual :: HasComm a -> I.Qual -> M (a, O.SimpleType) -> M (a, O.SimpleType)
qual mk (I.QPat p e) m      = do (e,t) <- expr e
                                 pat mk p e t m
qual mk (I.QLet d) m        = localDecl mk d m
qual mk (I.QGrd e) m        = qual mk (I.QPat pTrue e) m
qual mk (I.QLocal q1 q2) m  = do cur <- getCtxt 
                                 qual mk q1 $ qual mk q2 $ inCtxt cur m
qual mk (I.QThen q1 q2) m   = qual mk q1 $ qual mk q2 m




-- Declarations ----------------------------------------------------------------

funMatch           :: O.Name -> I.Match -> M (O.Decl, O.SimpleType)
funMatch f m        = do let (as,ts) = unzip (args f m)
                         ts    <- forEach ts tType 
                         (e,t) <- match O.CommE expr (zip as ts) m
                         let ty = foldr O.tFunSimple t ts
                             xs = zipWith O.Bind as ts
                             d  = case as of
                                    [] -> O.AVal (O.Bind f t) e
                                    _  -> O.AFun (O.Fun f xs t e)
                         return (d,ty)
  

args :: O.Name -> I.Match -> [(O.Name, I.Type)]
args f m = [ (O.Arg f x, t) | (x,t) <- zip [0..] (reverse (loop [] m)) ]
  where
  loop x (I.MOr m _)  = loop x m
  loop x (I.MIs _)    = x
  loop x (I.MPat p m) = loop (typeOf p:x) m
  loop x (I.MGrd _ m) = loop x m
  loop _ m            = "args" `unexpected` show m

  typeOf (_ `I.PSig` t) = t
  typeOf (I.PAbs p _)   = typeOf p
  typeOf x              = "args.type Of" `unexpected` show x


match :: HasComm a -> (I.Expr -> M (a,O.SimpleType)) 
      -> [(O.Name,O.SimpleType)] -> I.Match -> M (a, O.SimpleType)
match mk how a (I.MOr m1 m2)      = do (e1,t) <- match mk how a m1
                                       (e2,_) <- match mk how a m2
                                       return (mk $ O.Handle e1 e2, t)
match _ how _ (I.MIs e)           = how e
match mk how ((a,t):as) (I.MPat p m)  = pat mk p (O.Atom (O.Var a)) t 
                                      $ match mk how as m
match mk how a (I.MGrd q m)       = qual mk q 
                                  $ match mk how a m
match _ _ _ m                     = "match" `unexpected` show m


-- XXX: not pretty
topDecls     :: I.BindBlock -> M ([O.Decl], Ctxt)
topDecls ds   = do (ps,xs) <- fmap unzip $ mapM prim (I.prims ds)
                   (as,ys) <- fmap unzip $ mapM area (I.areas ds)
                   addSubst (concat (xs ++ ys)) $ 
                     do (es,zs) <- loop [] (sccs (I.expBinds ds))
                        return (ps ++ as ++ es, zs)
  where
  loop ds (b:bs)  = do (d,sub) <- case b of
                                    NonRec b -> nonRecBind b
                                    Rec bs   -> recBinds bs
                       addSubst sub (loop (d:ds) bs)
  loop ds []      = do ctxt <- getCtxt
                       return (reverse ds, ctxt)

                  
                             
localDecl :: HasComm a -> I.BindBlock -> M (a,O.SimpleType) 
          -> M (a, O.SimpleType)
localDecl mk d m = do (ds, ctxt) <- topDecls d
                      (e,t) <- inCtxt ctxt m
                      return (foldr (\d -> mk . O.Let d) e ds, t)


                  
-- XXX: Maybe we don't need to return the types... we can rebuild them?
nonRecBind :: I.ExpBind -> M (O.Decl, [(I.Name,(O.Atom,O.SimpleType))])
nonRecBind (I.ExpBind (I.ImpBind f m) s) =
  do f'     <- tName f
     t'     <- tType (scType s) 
     (d,_)  <- funMatch f' m
     return (d, [(f,(O.Var f',t'))])


recBinds :: [I.ExpBind] -> M (O.Decl, [(I.Name,(O.Atom, O.SimpleType))])
recBinds exps
  = do let defs   = map I.impBind exps
           nameTs = zip (map I.biName defs) (map (scType . I.biSchema) exps)
           names  = map fst nameTs
           types  = map snd nameTs
       names'    <- forEach names tName
       types'    <- forEach types tType
       let subst = zip names (zip (map O.Var names') types')
       decls     <- addSubst subst
                  $ forEach2 names' (map I.biDef defs) funMatch
       let (vals,funs) = partition isVal (map fst decls)
       case vals of
         [] -> return (O.Rec [ f | O.AFun f <- funs], subst)
         bs -> error ("Values cannot be recursive: " ++ show bs)  
         -- XXX: report properly
  where
  isVal (O.AVal _ _)  = True
  isVal _             = False
 




area (I.AreaDecl x r v (Just e) t) =
  do x' <- tName x
     t' <- tType t
     return (O.Area (O.Bind x' t') r v e, [(x,(O.Var x',t'))]) 
area a@(I.AreaDecl {}) 
  = bug "Spec2Sil.area" ("No evidence for: " ++ show (I.arName a))

prim (I.PrimDecl x (Just ev) s)
  = do f  <- tName x
       t' <- tType (scType s)
       let ft   = O.fun2funT t'
           args = [ O.Bind a t | a <- map (O.Arg f) [0..] | t <-  O.args ft ]
           prim = O.UserPrim x ev
           decl = case args of
                    [] -> O.AVal (O.Bind f (O.result ft)) (O.Prim prim [])
                    _  -> O.AFun $ O.Fun
                            { O.funName = f
                            , O.funArgs = args
                            , O.funResT = O.result ft
                            , O.funDef  = O.Prim prim 
                                          (map (O.Var . O.varName) args) }
       return (decl, [(x,(O.Var f,t'))])
prim b = "Spec2SIL.prim" `unexpected` show b
                  
                    



--------------------------------------------------------------------------------

tName              :: I.Name -> M O.Name
tName x             = do s <- getSubst
                         return $ 
                           case Map.lookup x s of
                             Nothing                    -> O.UName x
                             Just (O.Lit _,_)           -> O.UName x
                             Just (O.Var (O.Ren x n),_) -> O.Ren x (n+1)
                             Just (O.Var x,_)           -> O.Ren x 0

-- | Replaces bitdata types with bit-vector types.
tType              :: I.Type -> M O.SimpleType
tType t             = (`tType'` t) # getBDTs

tType'             :: [I.BDT] -> I.Type -> O.SimpleType
tType' bdts (I.TCon x)  = transTName bdts x
tType' _ t             = "trans" `unexpected` show t


-- Note: assumes no poly bitdata
transTName bdts (I.TSub t _)  = transTName bdts t
transTName bdts (I.Inst c xs) = I.Inst c (map (transTName bdts) xs) 
transTName bdts b             = case find ((b==) . I.bdtName) bdts of
                                  Nothing -> b
                                  Just b  -> O.tBitSimple (I.bdtWidth b)

scType :: I.Schema -> I.Type
scType (I.Forall [] [] t) = t
scType t = "scType" `unexpected` show t




-- Monad and support -----------------------------------------------------------

newtype M a = M { unM :: ReaderT Env (StateT Word32 Id) a }
type Subst  = Map.Map I.Name (O.Atom, O.SimpleType)
data Env    = Env {
  subst :: Subst,   -- ^ How to translate variables (and their types).
  bdts  :: [I.BDT]  -- ^ Bitdata declarations
  }


instance Functor M where
  fmap f (M m)      = M (fmap f m)

instance Monad M where
  return x          = M (return x)
  M m >>= f         = M (m >>= (unM . f))

run                :: [I.BDT] -> Ctxt -> M a -> a
run bdts s (M m)    = fst $ runId $ runStateT 0 $ runReaderT env m
  where env         = Env { subst = s, bdts  = bdts }

-- This really should be a class, but that leads to 
-- the 'different contexts' bug in the Haskell report/GHC.
type HasComm t      = O.Comm t -> t


getBDTs            :: M [I.BDT]
getBDTs             = M (bdts # ask)

getBDTCtr'         :: I.Name -> M (Maybe (I.BDT, I.BDTCtr))
getBDTCtr' c        = I.findBDTCtr c # getBDTs

getBDTCtr          :: I.Name -> M (I.BDT, I.BDTCtr)
getBDTCtr c         = do m <- getBDTCtr' c
                         case m of
                           Just x  -> return x
                           Nothing -> "getBDTCtr" `bug` 
                                            ("Missing constructor: " ++ show c) 

getSubst           :: M Subst
getSubst            = M (subst # ask)

withSubst          :: Subst -> M a -> M a
withSubst s (M m)   = M $ ask >>= \e -> local (e { subst = s }) m

addSubst           :: [(I.Name, (O.Atom, O.SimpleType))] -> M a -> M a
addSubst xs m       = do ys <- getSubst 
                         withSubst (Map.fromList xs `Map.union` ys) m

apSubst            :: I.Name -> M (O.Atom, O.SimpleType)
apSubst x           = do s <- getSubst 
                         return $
                           case Map.lookup x s of
                             Just a  -> a
                             Nothing -> bug "Spec2Sil.apSubst" 
                                            ("missing var: " ++ show x)

newTmp             :: M O.Name
newTmp              = O.Tmp # M (do s <- get; set (s+1); return s)

nameExpr' :: HasComm a -> Maybe O.Name -> (O.Expr, O.SimpleType) 
           -> (O.Atom -> M (a, O.SimpleType)) -> M (a, O.SimpleType) 
nameExpr' mk x (e,t) k = case e of
                           O.Atom x -> k x
                           _ -> do x <- case x of
                                          Nothing -> newTmp
                                          Just x -> return x
                                   let b = O.Bind x t 
                                       d = O.AVal b e
                                   (e',t') <- k (O.Var x)
                                   return (mk $ O.Let d e', t')

nameExpr mk p k = nameExpr' mk Nothing p k


type Ctxt           = Subst

getCtxt            :: M Ctxt
getCtxt             = getSubst 

inCtxt             :: Ctxt -> M a -> M a
inCtxt s m          = withSubst s m







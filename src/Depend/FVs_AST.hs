module Depend.FVs_AST where

import AST
import Depend.FVs

import qualified Data.Set as Set

binder x e = fvs x `Set.union` (fvs e `Set.difference` defs x)

instance FVs Match Name where
  fvs (MPat p m)      = binder p m 
  fvs (MAbsEv _ _ m)  = fvs m
  fvs (MAbsT _ m)     = fvs m
  fvs (MOr m1 m2)     = fvs [m1,m2]
  fvs (MIs e)         = fvs e
  fvs (MGrd q m)      = binder q m

instance FVs Pat Name where
  fvs (PVar _)          = Set.empty
  fvs PWild             = Set.empty
  fvs (PAbs p qs)       = binder p qs
  fvs (PApp _ _ _ ps)   = fvs ps
  fvs (PSig p _)        = fvs p

{-
  fvs (PCon _ _ ps)     = fvs ps
  fvs (PSplit p1 p2)    = fvs (p1,p2)
  fvs (p `PEv` _)       = fvs p 
  fvs (PInc _ _ e)      = fvs e
  fvs (PDec _ _ e)      = fvs e
-}

  fvs (PParens p)       = fvs p
  fvs (PInfix p1 _ p2)  = fvs (p1,p2)

instance Defs Pat Name where
  defs (PVar x)         = Set.singleton x
  defs PWild            = Set.empty
  defs (PAbs p q)       = defs (p,q) -- shadowing?
  defs (PApp _ _ _ ps)  = defs ps
  defs (PSig p _)       = defs p

{-
  defs (PCon _ _ ps)    = defs ps
  defs (PSplit p1 p2)   = defs (p1,p2)
  defs (p `PEv` _)      = defs p
  defs (PInc x _ _)     = Set.singleton x
  defs (PDec x _ _)     = Set.singleton x
-}

  defs (PParens p)      = defs p
  defs (PInfix p1 _ p2) = defs (p1,p2)

instance FVs FieldP Name where fvs (FieldP _ _ p)  = fvs p
instance Defs FieldP Name where defs (FieldP _ _ p)  = defs p

instance FVs Qual Name where
  fvs (QPat p e)      = fvs (p,e)
  fvs (QLet bs)       = fvs bs `Set.difference` defs bs
  fvs (QGrd e)        = fvs e
  fvs (QLocal q1 q2)  = binder q1 q2
  fvs (QThen q1 q2)   = binder q1 q2

instance Defs Qual Name where
  defs (QPat p _)     = defs p
  defs (QLet bs)      = defs bs
  defs (QGrd _)       = Set.empty
  defs (QLocal _ q)   = defs q
  defs (QThen q1 q2)  = defs (q2,q1)

instance FVs Expr Name where
  fvs e = case e of
            App e1 e2   -> fvs (e1,e2)
            AppEv e1 _  -> fvs e1
            AppT e _    -> fvs e
            Var x       -> Set.singleton x
            Lit _       -> Set.empty
            Sig e _     -> fvs e
            Match m     -> fvs m

            Con _ fs    -> fvs fs 
            Upd e fs    -> fvs (e,fs) 

            Do p e1 e2  -> fvs e1 `Set.union` binder p e2

            Parens e      -> fvs e
            Infix e1 x e2 -> Set.singleton x `Set.union` fvs (e1,e2)
  

instance FVs FieldV Name where fvs (FieldV _ _ e)   = fvs e

instance FVs BindBlock Name where
  fvs b = Set.unions (map fvs (expBinds b) ++ map fvs (impBinds b))

instance FVs ImpBind Name where fvs (ImpBind _ m) = fvs m
instance FVs ExpBind Name where fvs (ExpBind i _) = fvs i

instance Defs BindBlock Name where
  defs b  = Set.unions (map defs (prims b) ++ 
                        map defs (areas b) ++
                        map defs (expBinds b) ++
                        map defs (impBinds b))

instance Defs ExpBind Name  where defs (ExpBind b _)  = defs b
instance Defs ImpBind Name  where defs b  = Set.singleton (biName b)
instance Defs AreaDecl Name where defs a  = Set.singleton (arName a)
instance Defs PrimDecl Name where defs p  = Set.singleton (primName p)


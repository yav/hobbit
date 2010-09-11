{-# OPTIONS_GHC -fallow-undecidable-instances #-}
module Depend.FVs_SIL where

import Depend.FVs
import AST.SIL 
import qualified Data.Set as Set



instance FVs TopDecl Name where 
  fvs (FunD f)  = fvs f 
  fvs (ProcD p) = fvs p 
  fvs (ValD v)  = fvs v 
                      
instance Defs TopDecl Name where
  defs (FunD f)   = defs f
  defs (ProcD p)  = defs p
  defs (ValD v)   = defs v 


instance Defs Binder Name where
  defs b      = Set.singleton (varName b) 

instance FVs Name Name where
  fvs x       = Set.singleton x


instance FVs Atom Name where
  fvs (Var x) = fvs x
  fvs (Lit _) = Set.empty

instance FVs Expr Name where
  fvs (Atom a)    = fvs a
  fvs (Con _ as)  = fvs as
  fvs (Prim _ as) = fvs as
  fvs (App f as)  = fvs (f,as) 
  fvs (Do s)      = fvs s
  fvs (CommE e)   = fvs e

instance FVs a Name => FVs (Comm a) Name where
  fvs (Let d e)         = fvs d `Set.union` (fvs e `Set.difference` defs d)
  
  fvs (Switch x as)     = fvs (x,as) 
  fvs (BSwitch a as)    = fvs (a,as)
  fvs (Raise _)         = Set.empty
  fvs (Handle x y)      = fvs (x,y)

instance FVs Stmt Name where
  fvs (Call f xs)     = fvs (f,xs)
  fvs (LetM x s1 s2)  = fvs s1 `Set.union` (fvs s2 `Set.difference` defs x)
  fvs (PrimS _ xs)    = fvs xs
  fvs (CommS s)       = fvs s 

instance FVs a Name => FVs (Alt a) Name where
  fvs (Case _ e)  = fvs e
  
instance FVs a Name => FVs (BAlt a) Name where
  fvs (BCase _ e) = fvs e

instance FVs Decl Name where
  fvs (AVal _ e)    = fvs e
  fvs (Area {})     = Set.empty
  fvs (AFun f)      = fvs f
  fvs d@(Cyc xs)    = fvs [ as | (_,_,as) <- xs ] `Set.difference` defs d
  fvs d@(Rec fs)    = fvs fs `Set.difference` defs d

instance Defs Decl Name where
  defs (AVal x _)   = defs x
  defs (Cyc xs)     = defs [ x | (x,_,_) <- xs ]
  defs (Area x _ _ _) = defs x
  defs (AFun f)     = defs f
  defs (Rec fs)     = defs fs

instance FVs a Name => FVs (FunDecl a) Name where
  fvs f = fvs (funDef f) `Set.difference` defs (funArgs f)

instance Defs (FunDecl a) Name where
  defs f = Set.singleton (funName f)





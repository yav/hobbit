{-# OPTIONS_GHC -fallow-undecidable-instances #-}
-- The FVs (Poly t) instance seems to require this?

-- | Compute type constructors used by a type.
module Depend.FVs_Data where

import AST
import Depend.FVs 
import Error

import qualified Data.Set as Set

instance Defs DataDecl Name where
  defs (BitdataDecl d)  = defs d
  defs (DataDecl d)     = defs d
  defs (TypeDecl d)     = defs d
  defs (StructDecl d)   = defs d
  defs (KSigDecl d)     = defs d

instance FVs DataDecl Name where
  fvs (BitdataDecl d)   = fvs d
  fvs (DataDecl d)      = fvs d
  fvs (TypeDecl d)      = fvs d
  fvs (StructDecl d)    = fvs d
  fvs (KSigDecl d)      = fvs d

instance Defs BitData Name where defs d = Set.singleton (bdName d)
instance FVs BitData Name where fvs d   = fvs (bdCtrs d) 
instance FVs FlatCon Name where
  fvs c@(FlatCon{})   = fvs (fcFields c, fcAs c)
  fvs c@(FlatCon2{})  = fvs (fcFields2 c)

instance FVs Field Name where fvs f     = fvs (fieldType f)

instance FVs Layout2 Name where 
  fvs (BF_Named f)  = fvs f
  fvs (BF_Cat l r)  = fvs l `Set.union` fvs r
  fvs (BF_Sig l t)  = fvs l `Set.union` fvs t
  fvs (BF_Wild {})  = Set.empty
  fvs (BF_Tag {})   = Set.empty
  fvs (BF_Unit {})  = Set.empty

instance FVs Layout Name where fvs (LaySig ls t) = fvs (ls, t)
                               fvs _             = Set.empty

instance Defs (Struct t) Name where defs x = Set.singleton (stName x)
instance FVs (Struct t) Name where fvs x = fvs (stFields x) `Set.union`
                                           fvs (stSize x) 

instance FVs t Name => FVs (Poly t) Name where
  fvs (Forall _ ps t) = fvs (ps,t)

-- NOTE: Should we count `c`?
instance FVs Pred Name where
  fvs (CIn c ts)  = Set.singleton c `Set.union` fvs ts



instance FVs StructField Name where 
  fvs (StField _ t _) = fvs t
  fvs (StPad t)       = fvs t

instance Defs KSig Name where defs (KSig x _) = Set.singleton x
instance FVs KSig Name where fvs (KSig _ _)   = Set.empty

instance Defs AlgData Name where defs (AlgData c _ _) = Set.singleton c
instance FVs AlgData Name where fvs (AlgData _ _ cs)  = fvs cs
instance FVs DataCon Name where fvs (DataCon _ ts)    = fvs ts

instance Defs TypeSyn Name where defs (TypeSyn x _ _) = Set.singleton x
instance FVs TypeSyn Name where fvs (TypeSyn _ _ t) = fvs t

-- Assumes no pointers in types.
instance FVs Type Name where
  fvs (TApp t1 t2)      = fvs t1 `Set.union` fvs t2
  fvs (TCon (TSub t _)) = Set.singleton t
  fvs (TCon c)          = Set.singleton c
  fvs (TFree _)         = Set.empty
  fvs (TSyn {})         = "Depend.FVs" `unexpected` "TSyn"
  fvs (TInfix {})       = "Depend.FVs" `unexpected` "TInfix"
  fvs (TParens {})      = "Depend.FVs" `unexpected` "TParens"









module AST.Type
  ( ModName, QName(..), Name(..)
  , Type(..), Kind, TyVar(..), Pred(..), Poly(..), Schema, Rule(..), RuleEnv(..)
  , Goal(..), DGoal(..), FunDep'

  , sSort, sFun
  , kType, kArea, kNat, kLab, kPred, kFun
  , tcFun
  , tBool, tString, tChar, tSub, subName
  , tFun, tTup, tBit, tIx, tARef, tM
  , tNat, tLab
  , tLE, tBE, tArray
  , cAdd, cTimes, cExp2, cGCD
  , cDNat, cWidth, cIndex, cAlign
  , cBitRep, cBitData, cJoin
  , cLiteral, cEq, cOrd, cNum, cBitOps, cBounded
  , cField, cUpdField, cSizeOf, cAreaDecl, cValIn, cBytes
  , tDom, tCod

  , defName, ifCheckName, mainName, mainType, entryName
  , ruleHead

  , qPrim, qPrel

  , mono 
  , typeToPred, predToType, splitTApp
  ) where

import AST.Evidence

import Error
import PP

import Data.IORef
import Data.Word

type ModName        = String
newtype QName       = Q Name deriving (Eq,Ord)


data Name           = VarName String              -- ^ User variables
                    | ConName String              -- ^ User constructors
                    | Qual ModName Name           -- ^ Qualified name
                    | Select Name                 -- ^ Record selector
                    | Update Name                 -- ^ record updator
                    | IfCheck Name                -- ^ An 'if' clause
                    | DefaultVal Name Name        -- ^ A default (ctr,field)
                    | Tup Integer                 -- ^ Tuple constructors

                    -- Sort names
                    | SFun                        -- ^ Function scpace
                    | SSort                       -- ^ Sort


                    | TNat Word32                 -- ^ A natural number types
                    | TLab Name                   -- ^ A label type
                    | TSub Name Name              -- ^ Bitdata constructor types
                    | TSome                       -- ^ No empty kinds (Spec.hs)

                    -- Introduced during specialization.
                    | Inst Name [Name]            -- ^ Type application
                                                
                      deriving (Eq,Ord)

data Type           = TApp Type Type
                    | TCon Name
                    | TFree TyVar
                    | TSyn Name [Type] Type       -- ^ Last type is expansion

                    | TInfix Type Name Type       -- Parsing
                    | TParens Type
                      deriving (Eq)

type Kind           = Type

data TyVar          = TyVar 
                    { tyVarName :: Name               -- ^ Suggested name
                    , tyVarPtr  :: IORef (Maybe Type) -- ^ To get bound
                    , tyVarKind :: Kind               -- ^ The variable kind
                    } 
                    | TyUser
                    { tyVarName :: Name }

instance Eq TyVar where 
  TyVar { tyVarPtr = x } == TyVar { tyVarPtr = y }      = x == y
  TyUser { tyVarName = x } == TyUser { tyVarName = y }  = x == y
  _ == _                                                = False
  


data Pred           = CIn Name [Type]       
data Poly p         = Forall { polyVars :: [TyVar]
                             , polyPreds :: [Pred]
                             , poly :: p }
                      
type Schema         = Poly Type

type FunDep'        = ([Int],[Int])

-- | Note: the arguments in 'ruleProof' should match the 'rulePred'
data Rule           = Rule { ruleProof :: [Ev] -> Ev
                           , rulePred  :: Poly Pred }

data RuleEnv        = RuleEnv
                    { superRules :: [Rule]
                    , instRules  :: [Rule]
                    }

data Goal           = Ev { goalName :: EvName, goalPred :: Pred }
data DGoal          = DGoal [Ev] (Poly [Goal]) 




-- Sugar -----------------------------------------------------------------------

ruleHead           :: Rule -> Pred
ruleHead r          = poly (rulePred r)

tDom, tCod         :: Type -> Type
tDom (_ `TApp` x `TApp` _)  = x
tDom _                      = bug "tDom" "Not a function type."

tCod (_ `TApp` _ `TApp` x)  = x
tCod _                      = bug "tCod" "Not a function type."


infixr `tFun`
infixr `kFun`
infixr `sFun`

-- Sorts 
sSort               = TCon SSort
sFun s1 s2          = TCon SFun `TApp` s1 `TApp` s2

-- Kinds (built in)
kFun k1 k2          = TCon (ConName "->") `TApp` k1 `TApp` k2

kType               = TCon (ConName "Type")
kArea               = TCon (ConName "Area") 
kNat                = TCon (ConName "Nat")
kLab                = TCon (ConName "Label")
kPred               = TCon (ConName "Pred")
                                                      


qPrim x             = Qual "Prims" x  -- where prims are defined
qPrel x             = Qual "Prelude" x

-- Types 
tcFun               = TCon (qPrim (ConName "->"))
tFun t1 t2          = tcFun `TApp` t1 `TApp` t2
tM t                = TCon (qPrim (ConName "M")) `TApp` t

tTup xs             = foldl TApp (TCon (Tup (fromIntegral (length xs)))) xs
tSub t c            = TCon (subName t c) 

-- XXX: argh
subName             :: Name -> Name -> Name
subName b c          = qual $ TSub (unqual b) (unqual c)
  where unqual (Qual _ x) = x
        unqual x          = x
        qual x = case b of
                   Qual q _ -> Qual q x
                   _        -> x
 

tARef n t           = TCon (qPrim (ConName "ARef")) `TApp` n `TApp` t
tBit t              = TCon (qPrim (ConName "Bit")) `TApp` t
tIx t               = TCon (qPrim (ConName "Ix")) `TApp` t
tNat n              = TCon (TNat n)   -- built in
tLab l              = TCon (TLab l)   -- built in

tArray n a          = TCon (qPrim (ConName "Array")) `TApp` n `TApp` a
tLE a               = TCon (qPrim (ConName "LE")) `TApp` a
tBE a               = TCon (qPrim (ConName "BE")) `TApp` a

tChar               = TCon (qPrim (ConName "Char"))
tString             = TCon (qPrim (ConName "String")) 
tBool               = TCon (qPrel (ConName "Bool"))

-- predicates/classes
cLiteral            = qPrim (ConName "Literal")
cEq                 = qPrim (ConName "Eq")
cOrd                = qPrim (ConName "Ord")
cNum                = qPrim (ConName "Num")
cBitOps             = qPrim (ConName "BitOps")
cBounded            = qPrim (ConName "Bounded")

cAdd                = qPrim (ConName ":+")
cTimes              = qPrim (ConName ":*")
cExp2               = qPrim (ConName "Exp2")
cGCD                = qPrim (ConName "GCD")

cDNat               = qPrim (ConName "DNat")
cWidth              = qPrim (ConName "Width")
cIndex              = qPrim (ConName "Index")
cAlign              = qPrim (ConName "Align")

cJoin               = qPrim (ConName ":#")
cBitRep             = qPrim (ConName "BitRep")
cBitData            = qPrim (ConName "BitData")

cField              = qPrim (ConName "Field")
cUpdField           = qPrim (ConName "UpdField")
cSizeOf             = qPrim (ConName "SizeOf")
cValIn              = qPrim (ConName "ValIn")
cBytes              = qPrim (ConName "Bytes")
cAreaDecl           = qPrim (ConName "AreaDecl")
  

-- Schemas  
mono t              = Forall [] [] t


typeToPred       :: Type -> Maybe Pred
typeToPred t      = let (t',ts) = splitTApp t []
                    in case t' of
                         TCon c -> Just (CIn c ts)
                         TSyn _ _ t -> do CIn c ts1 <- typeToPred t
                                          return (CIn c (ts1 ++ ts))
                         _      -> Nothing

predToType       :: Pred -> Type
predToType (CIn c ts) = foldl TApp (TCon c) ts

splitTApp (TApp t1 t2) ts = splitTApp t1 (t2:ts)
splitTApp t ts            = (t,ts)

-- Names
defName c f     = DefaultVal c f
ifCheckName c   = IfCheck c

-- The original name of the entry point (see also AST/SIL)
mainName        = Qual "Main" (VarName "main")
mainType        = tM (tBit (tNat 0))
entryName       = qPrel (VarName "$entry")



-- Pretty printing -------------------------------------------------------------

instance Show QName where show x = prShow x
instance Pr QName where pr (Q x) = pr x

instance Show Name where show x = prShow x
instance Pr Name where
  pr (VarName x)      = text x
  pr (ConName x)      = text x
  -- pr (Qual _ x)       = {-text m <> char '.' <>-} pr x 
  pr (Qual m x)       = text m <> char '.' <> pr x 
  pr (Select l)       = parens (char '.' <> pr l)
  pr (Update l)       = parens (pr l <> char '=')
  pr (IfCheck c)      = text "$if_" <> pr c
  pr (DefaultVal c f) = text "$dfl_"<> pr c <> text "." <> pr f
  

  pr SFun             = text "(->)"
  pr SSort            = text "sort"

  pr (TSub x y)       = pr x <> char '\'' <> pr y
  pr TSome            = text "$SomeT"
  pr (TNat n)         = text (show n)
  pr (TLab l)         = pr l
  pr (Tup 0)          = text "()"
  pr (Tup 1)          = bug "prName" "1-tuple"
  pr (Tup n)          = parens (hsep (replicate (fromIntegral (n-1)) comma))

  pr (Inst x xs)      = pr x <> tris (commaSep (map pr xs))


prFun arr n a b         = wrap (prn 1 a <+> text arr <+> prn 0 b)
  where wrap
          | n < 1     = id
          | otherwise = parens



instance Show Type where show x = prShow x
instance Pr Type where
  prn n (TCon SFun `TApp` t1 `TApp` t2) = prFun "--->" n t1 t2
  prn n (TCon (ConName "->") `TApp` t1 `TApp` t2) = prFun "->" n t1 t2
  prn n (TApp t1 t2)        
    | n < 2         = prn 1 t1 <+> prn 2 t2
  prn _ (TSyn c [] _) = pr c
  prn n (TSyn c ts _)
    | n < 2         = pr c <+> hsep (map (prn 2) ts)
  prn _ (TCon c)    = pr c
  prn _ (TFree x)   = pr x
  
  prn _ (TParens t)     = parens (pr t)
  prn _ (TInfix s op t) = parens (pr s <+> pr op <+> pr t)

  prn _ t           = parens (pr t)

instance Show TyVar where show x = prShow x
instance Pr TyVar where
  pr x              = char '?' <> pr (tyVarName x)


instance Show Pred where show x = prShow x
instance Pr Pred where
  pr (CIn c ts)            = pr c <+> hsep (map (prn 2) ts)


instance Pr t => Show (Poly t) where show x = prShow x
instance Pr t => Pr (Poly t) where 
  pr (Forall xs ps t)  = prSchema xs ps (pr t)

prSchema xs [] d    = withQs xs d
prSchema xs ps d    = withQs xs (parens (hsep (punctuate comma (map pr ps)))
                              <+> text "=>" <+> d)


withQs [] t         = t
withQs qs t         = text "forall" <+> hsep (map prQ qs) <> char '.' <+> t
  where
  prQ v             = parens (pr v <+> text "::" <+> pr (tyVarKind v))


instance Show RuleEnv where show = prShow
instance Pr RuleEnv where 
  pr p = prSuper $$ prInsts 
    where
    prSuper = case superRules p of
                [] -> text "-- No super class rules"
                ps -> text "-- Super class rules --" $$ vcat (map pr ps)

    prInsts = case instRules p of
                [] -> text "-- No instance rules"
                ps -> text "-- Intsnace rules --" $$ vcat (map pr ps)
              

      

instance Show Rule where show = prShow
instance Pr Rule where pr p = pr (rulePred p)

instance Show Goal where show x = prShow x
instance Pr Goal where
  pr (Ev x p)       = pr x <+> text "::" <+> pr p

instance Show DGoal where show x = prShow x
instance Pr DGoal where
  pr (DGoal _ p)    = prSchema (polyVars p) (polyPreds p) 
                    $ case poly p of
                        [d] -> pr d
                        ds  -> parens (commaSep (map pr ds))

















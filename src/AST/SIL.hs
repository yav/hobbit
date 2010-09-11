module AST.SIL (module AST.SIL) where

import qualified AST as A
import qualified BDD
import PP
import Utils
import Error
import Opts

import Numeric(showHex)
import Data.Set hiding (map,empty)
import Data.Word


data Name           = Name String         
                    | UName A.Name        -- ^ Names from previous AST

                    -- From Spec2SIL
                    | Ren Name Word32     -- ^ Renamed name
                    | Tmp Word32          -- ^ Names for temporaries
                    | TmpRes              -- ^ Result in over-application
                    | Arg Name Word32     -- ^ A function argument (1)
                    | Fld Name Name Word32  -- ^ A value field (2)

                    -- From ClosureConv
                    | GlobFor Name        -- ^ The global version of a local
                    | FunFor Name         -- ^ Worker function
                    | ProcFor Name        -- ^ Worker procedure

                    | ConName ConName   -- ^ Closure constructor
                    | OpName  OpName    -- ^ Application/run  operator
                      deriving (Eq,Ord)

-- Notes:
--  (1) The n-th argument of a function called 'f' is named 'Arg f n'
--  (2) The n-th field of a value 'x', that was constructed with
--      constructor 'C' is named 'Fld x C n'


-- | Names for primitives
data PrimName       
  = UserPrim A.Name [A.Ev]
  | PGetFieldB Word32 A.BitField | PUpdFields Word32 [A.BitField]
  | PGetFieldA Name Word32
  | PGEQ | PLEQ | PIncBy | PDecBy



type SimpleType     = A.Name
type FunADT         = A.ADT' ConName

-- | Known functions
data KnownFun       = Info
                    { kWorker   :: Name
                      -- ^ The name of the worker.

                    , kWorkerM  :: Maybe Name
                      -- ^ The effectful worker for a function.

                    , kType     :: FunType
                      -- ^ The type of the worker

                    , kFreeArgs :: [Binder]
                      -- ^ The free variable arguments of the worker (lazy)

                    , kFreeVars :: Set Binder
                      -- ^ An approx. to 'kFreeArgs' used during closure conv.
                    }


-- | Names for the constructors of function closures.
data ConName        = ConOp
                    { conWorker :: KnownFun
                      -- ^ Worker for the constructor

                    , conType   :: FunType
                      -- ^ Type of the constructor

                    , conHave   :: Word32
                      -- ^ How many of the arguments of the function we have.

                    }

data OpName         = AppOp { opType :: SimpleType, opArgs :: Word32 }
                    | RunOp { opType :: SimpleType, opArgs :: Word32 }
                      deriving (Eq,Ord)




data Binder         = Bind { varName :: Name
                           , varType :: SimpleType }

data Literal        = Int Integer deriving Eq

data Atom           = Var Name | Lit Literal
                      deriving Eq


data Comm e         = Let Decl e                        -- ^ Local definition

                    -- Local control flow
                    | Switch Name [Alt e]               -- ^ ADT decision
                    | BSwitch Atom [BAlt e]             -- ^ Binary decision
                    | Raise SimpleType                  -- ^ Next alternative
                    | Handle e e                        -- ^ Alternatives


data Alt e          = Case Name e
data BAlt e         = BCase BDD.Pat e


data Expr           = Atom Atom                         -- ^ Simple value

                    | Con Name [Atom]                   -- ^ Constructed value
                    | Prim PrimName [Atom]              -- ^ Simple expression
                    | App Name [Atom]                   -- ^ Function call
                    
                    | Do Stmt                           -- ^ Statments
                    | CommE (Comm Expr)                 -- ^ Other exprs

                    
data Stmt           = Call Name [Atom]                  -- ^ Call an impure fun
                    | LetM Binder Stmt Stmt             -- ^ Name a result
                    | PrimS PrimName [Atom]       
                    | CommS (Comm Stmt)                 -- ^ Other stmts


data Decl           -- Values
                    = AVal Binder Expr                -- ^ Normal values
                    | Cyc [(Binder,Name,[Atom])]      -- ^ Cyclic ADT ctrs
                    | Area Binder (Maybe String) (Maybe Integer) A.Ev 
                                                      -- ^ Memroy area

                    -- Functions
                    | AFun (FunDecl Expr)             -- ^ Non-rec fun.
                    | Rec [FunDecl Expr]              -- ^ Recursive funs.


data TopDecl        = FunD (FunDecl Expr) 
                    | ProcD (FunDecl Stmt)
                    | ValD Decl


data FunDecl a      = Fun {
                        funName :: Name,
                        funArgs :: [Binder],
                        funResT :: SimpleType,
                        funDef  :: a
                      }

data FunType        = FunT { args :: [SimpleType], result :: SimpleType }

eInt               :: Integer -> Expr
eInt x              = Atom (Lit (Int x))

funArity           :: FunDecl a -> Word32
funArity f          = fromIntegral (length (funArgs f))

funTypeV           :: FunDecl a -> SimpleType
funTypeV f          = foldr tFunSimple (funResT f) (map varType (funArgs f))

funTypeF           :: FunDecl a -> FunType
funTypeF f          = FunT (map varType (funArgs f)) (funResT f)

funBinderV         :: FunDecl a -> Binder
funBinderV f        = Bind (funName f) (funTypeV f) 

opSig              :: OpName -> FunType
opSig a             = f [ t ] t (opArgs a)
  where
  t                 = opType a
  f as t 0          = case a of
                        AppOp {} -> FunT (reverse as) t
                        RunOp {} -> case isM t of
                                      Just t  -> FunT (reverse as) t
                                      Nothing -> bug "opSig" 
                                         ("'run' op that is not IO: "++ show t)
  f as t n          = f (tDomSimple t : as) (tCodSimple t) (n-1)

-- | Note that this does not include free variables.
kArity             :: KnownFun -> Word32
kArity f            = fromIntegral (length (args (kType f)))


-- XXX: Return Maybe?
tCodSimple                 :: SimpleType -> SimpleType
tCodSimple (A.Inst _ [_,t]) = t
tCodSimple t                = "tCodSimple" `unexpected` show t

tDomSimple                 :: SimpleType -> SimpleType
tDomSimple (A.Inst _ [t,_]) = t
tDomSimple t                = "tDomSimple" `unexpected` show t

isM                :: SimpleType -> Maybe SimpleType
isM (A.Inst (A.Qual "Prims" (A.ConName "M")) [x]) = Just x
isM _               = Nothing



tBitSimple         :: Word32 -> SimpleType
tBitSimple n        = A.Inst (A.qPrim (A.ConName "Bit")) [A.TNat n]

tIntSimple         :: SimpleType
tIntSimple          = tBitSimple maxWidth 

tFunSimple         :: SimpleType -> SimpleType -> SimpleType
tFunSimple a b      = A.Inst (A.qPrim (A.ConName "->")) [a,b] 

fun2funT           :: SimpleType -> FunType
fun2funT (A.Inst (A.Qual "Prims" (A.ConName "->")) [s,t])
                    = let FunT xs y = fun2funT t in FunT (s : xs) y
fun2funT t          = FunT [] t

-- primitives
primFromLitBit        :: Word32 -> Atom -> Expr
primFromLitBit w a  = Prim (UserPrim name [A.litBitEv (A.IntEv w)]) [a]
  where name        = A.Inst (A.qPrim (A.VarName "fromNat")) [A.TNat w]

primUpdFields      :: Word32 -> [A.BitField] -> [Atom] -> Expr
primUpdFields w bs as = Prim (PUpdFields w bs) as

primGetFieldA      :: Name -> Word32 -> Atom -> Expr
primGetFieldA c n a = Prim (PGetFieldA c n) [a]

primGetFieldB      :: Word32 -> A.BitField -> Atom -> Expr
primGetFieldB w b a = Prim (PGetFieldB w b) [a]


-- The entry point to the program
finalEntry         :: Name 
finalEntry          = ProcFor (UName A.entryName)



instance Eq Binder  where (==)          = (==) `on` varName
instance Ord Binder where compare       = compare `on` varName

instance Eq ConName where
  x == y            = kWorker (conWorker x) == kWorker (conWorker y)
                   && conHave x == conHave y

instance Ord ConName where
  compare x y       = compare (conHave x, kWorker (conWorker x))
                              (conHave y, kWorker (conWorker y))





-- Pretty printing -------------------------------------------------------------

instance Show ConName where show x = show (pr x)
instance Pr ConName where
  pr c  = pr (kWorker (conWorker c)) <> char '$' <> text (show (conHave c))

instance Show OpName where show x = show (pr x)
instance Pr OpName where
  pr (AppOp {})     = text "app"
  pr (RunOp {})     = text "run"


instance Show Name where show x = show (pr x)
instance Pr Name where
  pr (Name x)       = text x

  pr (UName x)      = pr x
  pr (Ren x n)      = pr x <> char '$' <> text (show n)
  pr (Tmp x)        = text "$t" <> text (show x)
  pr TmpRes         = text "$r"
  pr (Arg f n)      = text "$arg_" <> text (show n) <> text "_" <> pr f
  pr (Fld _ _ n)    = text "$f" <> text (show n) -- XXX
  pr (GlobFor x)    = text "$glob_" <> pr x
  pr (FunFor x)     = text "$fun_" <> pr x
  pr (ProcFor x)    = text "$proc_" <> pr x

  pr (OpName a)     = pr a
  pr (ConName c)    = pr c


instance Show Literal where show x = show (pr x)
instance Pr Literal where
  pr (Int x)        = text (show x)

instance Show Atom where show x = show (pr x)
instance Pr Atom where
  pr (Var x)        = pr x
  pr (Lit l)        = pr l

instance Show Expr where show x = show (pr x)
instance Pr Expr where
  pr (Con c xs)     = text "con" <+> pr c <> prTup (map pr xs)
  pr (Prim p xs)    = text "prim" <+> pr p <> prTup (map pr xs)
  pr (App f xs)     = pr f <> prTup (map pr xs)
  pr (Atom a)       = pr a
  pr (Do s)         = text "do" <+> pr s
  pr (CommE e)      = pr e

prTup xs            = parens (commaSep xs)

instance Pr a => Show (Comm a) where show = prShow
instance Pr a => Pr (Comm a) where
  pr (Let d m)         = text "let" <+> pr d <+> text "in" $$ pr m
  pr (Switch x as)    = text "case" <+> pr x <+> text "of" 
                     $$ nest 2 (block (map pr as))
                     
  pr (BSwitch x as)   = text "case" <+> pr x <+> text "of" 
                     $$ nest 2 (block (map pr as))
                    
  pr (Raise t)        = text "$Raise" <+> text "::" <+> pr t
  pr (Handle m1 m2)   = char ' ' <+> pr m1 $$ char '|' <+> pr m2


instance Show Stmt where show x = prShow x
instance Pr Stmt where
  pr (Call f xs)    = pr f <> prTup (map pr xs)
  pr (LetM x s1 s2) = pr x <+> text "<-" <+> pr s1 $$ pr s2
  pr (PrimS p xs)   = text "prim" <+> pr p <> prTup (map pr xs)
  pr (CommS s)      = pr s
 

instance Pr a => Show (Alt a) where show x = show (pr x)
instance Pr a => Pr (Alt a) where
  pr (Case c e)     = pr c <+> text "=" <+> pr e

instance Pr a => Show (BAlt a) where show x = show (pr x)
instance Pr a => Pr (BAlt a) where
  pr (BCase p e)    = vcat (map text (BDD.showPat p))
                     <+> text "=" <+> pr e

instance Show Binder where show x = show (pr x)
instance Pr Binder where
  pr (Bind x t)     = pr x <+> text "::" <+> pr t

prArgList xs        = hsep (map (parens . pr) xs)




instance Show Decl where show x = show (pr x)
instance Pr Decl where
  pr (AVal x e)     = pr x $$ pr (varName x) <+> char '=' <+> pr e
  pr (AFun f)       = pr f
  pr (Rec fs)       = text "rec" $$ nest 2 (vcat (map pr fs))
  pr (Area x r v e) = text "area" <+> pr x <+> val <+> reg <+> text ":" <+> pr e
    where reg = maybe empty (\r -> text "in" <+> text r) r
          val = maybe empty (\x -> text "=" <+> text (showHex x [])) v

  pr (Cyc es)       = text "cyc" $$ nest 2 (vcat (map p es))
    where p (x,c,as)  = pr (AVal x (Con c as))

instance Pr a => Show (FunDecl a) where show x = show (pr x)
instance Pr a => Pr (FunDecl a) where
  pr (Fun f xs t e) = pr f <+> text "::" <+> pr (FunT (map varType xs) t) 
                   $$ fsep [ pr f <+> parens (commaSep (map (pr . varName) xs))
                           , nest 2 ( text rhsSep <+> pr e )
                           ]
    where rhsSep = "="

instance Show TopDecl where show x = show (pr x)
instance Pr TopDecl where
  pr (FunD f)   = pr f
  pr (ProcD f)  = pr f
  pr (ValD d)   = pr d
                    

instance Show PrimName where show x = prShow x
instance Pr PrimName where 
  pr op = case op of
            UserPrim x e    -> foldl (\d e -> d <> cdot <> pr e) (pr x) e
            PGetFieldA c n  -> pr c <> text ".getField." <> int (fromIntegral n)
            PGetFieldB _ f  -> text "getBits" <> pr f
            PUpdFields _ f  -> text "updBits" <> parens (commaSep (map pr f))
            PGEQ            -> parens (text ">=")
            PLEQ            -> parens (text "<=")
            PIncBy          -> text "inc"
            PDecBy          -> text "dec"

instance Show FunType where show = prShow 
instance Pr FunType where
  pr f    = parens (commaSep (map pr (args f))) <+> text "->" <+> pr (result f)




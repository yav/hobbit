-- | This module defines abstract syntax for expressions and declarations.
module AST.Expr 
  ( Expr (..), FieldV(..), Literal(..),
    Match(..), Qual(..), Pat(..), BPat(..), IxOp(..), FieldP(..),
    BindBlock(..), emptyBindBlock,
    ExpBind(..), ImpBind(..), AreaDecl(..), PrimDecl(..),
    var, apps, tapps, eapps, eAnd, eOr, eEquals,
    isNull, isPtr
  ) where 

import AST.Type
import AST.Evidence        
import Numeric

import PP


data Expr           = App Expr Expr         -- ^ Application
                    | AppEv Expr Ev         -- ^ Evidence application
                    | AppT Expr Type        -- ^ Type application

                    | Match Match           -- ^ Local declaration/case

                    | Var Name              -- ^ Variable
                    | Lit Literal           -- ^ Literal
                    | Sig Expr Type         -- ^ Signature

                    | Con Name [FieldV]     -- ^ Flat value
                    | Upd Expr [FieldV]     -- ^ Record update

                    -- Note similarity with matches...
                    | Do Pat Expr Expr      -- ^ Do statement

                    -- For parsing purposes
                    | Parens Expr           -- ^ Parens (parser)
                    | Infix Expr Name Expr  -- ^ Infix expressions (parser)


data FieldV         = FieldV Name (Maybe Ev) Expr


data Literal        = Int Integer           -- ^ Numeric literal
                    | Str String            -- ^ String literal
                    | Chr Char              -- ^ Character literal

data PrimDecl       = PrimDecl {
                        primName  :: Name,
                        primEv    :: Maybe [Ev],
                        primType  :: Schema
                      }

data AreaDecl       = AreaDecl {
                        arName    :: Name,
                        arRegion  :: Maybe String,
                        arValue   :: Maybe Integer,
                        arEv      :: Maybe Ev,
                        arType    :: Type
                      }
                      
data ExpBind        = ExpBind { impBind :: ImpBind, biSchema :: Schema }
data ImpBind        = ImpBind { biName :: Name, biDef :: Match }

data BindBlock      = BindBlock {
                        prims     :: [PrimDecl],
                        areas     :: [AreaDecl],
                        expBinds  :: [ExpBind],
                        impBinds  :: [ImpBind]
                      }

emptyBindBlock      = BindBlock [] [] [] []

data Match          = MPat Pat Match            -- ^ A value argument
                    | MAbsT TyVar Match         -- ^ A type argument
                    | MAbsEv EvName Pred Match  -- ^ An evidence argument

                    | MOr Match Match           -- ^ Alternatives
                    | MGrd Qual Match           -- ^ Conditionals/definitions
                    | MIs Expr                  -- ^ The result


data Qual           = QPat Pat Expr         -- ^ Pattern guard
                    | QLet BindBlock        -- ^ Local definition
                    | QGrd Expr             -- ^ A guard, like (True <- e)
                    | QLocal Qual Qual      -- ^ Local qualifiers
                    | QThen Qual Qual       -- ^ Qualifier sequencing


data Pat  = PVar Name                   -- ^ Name a component
          | PWild                       -- ^ A wild card
          | PAbs Pat Qual               -- ^ Guarded pattern
          | PApp BPat [Type] [Ev] [Pat] -- ^ instantiation, sub-patterns
          | PSig Pat Type               -- ^ Specify type

          | PParens Pat                 -- ^ For parser
          | PInfix Pat Name Pat         -- ^ ditto

-- Note: Could add user-defined patterns here.
data BPat = BPSplit               -- ^ Split a bit-vector
          | BPCon Name            -- ^ ADT/BDT constructor (perhaps separate?)
          | BPUpd IxOp Expr Expr  -- ^ op, amount, bound

data IxOp = Inc | Dec deriving Show
                


data FieldP         = FieldP Name (Maybe Ev) Pat  -- ^ Fields of a constructor


-- Sugar -----------------------------------------------------------------------

var                :: String -> Expr
var x               = Var (VarName x)

apps               :: Expr -> [Expr] -> Expr
apps e es           = foldl App e es

tapps              :: Expr -> [Type] -> Expr
tapps e ts          = foldl AppT e ts

eapps              :: Expr -> [Ev] -> Expr
eapps e es          = foldl AppEv e es

eAnd, eOr          :: Expr -> Expr -> Expr
eAnd e1 e2          = Match (MGrd (QGrd e1) (MIs e2) `MOr` MIs eFalse)
eOr e1 e2           = Match (MGrd (QGrd e1) (MIs eTrue) `MOr` MIs e2)

eEquals             = Var (qPrel (VarName "=="))

eTrue, eFalse      :: Expr
eTrue               = Var (qPrel (ConName "True"))
eFalse              = Var (qPrel (ConName "False"))

isNull (Inst (Qual "Prelude" (ConName "Null")) _) = True
isNull _ = False

isPtr (Inst (Qual "Prelude" (ConName "Ptr")) _) = True
isPtr _ = False



-- Pretty printing -------------------------------------------------------------                    
instance Show BindBlock where show x = prShow x
instance Pr BindBlock where
  pr p  = vcat [ pp "Primitives" (prims p)
               , pp "Areas" (areas p)
               , pp "Explicitly typed bindings" (expBinds p)
               , pp "Implicitly typed bindings" (impBinds p)
               ]

    where pp _ [] = empty
          pp x y = text "--" <+> text x <+> text "------------------"
               $+$ vcat (map pr y)
               $+$ text "-------------------------------"

              
instance Show PrimDecl where show x = prShow x
instance Pr PrimDecl where 
  pr (PrimDecl x ev t)  = text "primitive" <+> pr x <+> d <+> text "::" <+> pr t
    where d = case ev of
                Nothing -> empty
                Just ev -> foldl (\d e -> d <> cdot <> pr e) (pr x) ev

instance Show AreaDecl where show x = prShow x
instance Pr AreaDecl where
  pr (AreaDecl x r v e t) = pr x <> ev <+> val <+> reg <+> text "::" <+> pr t
    where ev  = case e of
                  Nothing -> empty
                  Just e  -> cdot <> pr e
          reg = case r of
                  Nothing -> empty
                  Just x  -> text "in" <+> text x
          val = case v of
                  Nothing -> empty  
                  Just x -> text "=" <+> text (showHex x [])

instance Show ExpBind where show x = prShow x
instance Pr ExpBind where 
  pr p  = pr (biName (impBind p)) <+> text "::" <+> pr (biSchema p)
       $$ pr (impBind p)

instance Show ImpBind where show x = prShow x
instance Pr ImpBind where
  pr p  = pr (biName p) <+> text "=" <+> pr (biDef p)

instance Show Expr where show x = prShow x
instance Pr Expr where
  prn n (App f x)   | n < 3 = prn 2 f <+> prn 3 x
  prn n (AppT e1 t) | n < 3 = prAppT e1 [t]
  prn n (AppEv x y) | n < 3 = prn 2 x <> cdot <> prn 3 y

  prn n (Match m)   = prn n m 

  prn _ (Var x)     = pr x
  prn _ (Lit l)     = pr l
  prn n (Sig e t) | n < 1 = pr e <+> text "::" <+> pr t

  prn n (Con c fs) | n < 3 = pr c <+> braces (commaSep (map pr fs))
  prn _ (Upd e fs)  = braces (pr e <+> char '|' <+> commaSep (map pr fs))

  prn n e@(Do _ _ _) | n < 1  = text "do" <+> prStmts empty e

  prn n (Infix e1 op e2) | n < 2 = prn 2 e1 <+> pr op <+> prn 2 e2
  prn _ (Parens e)  = parens (pr e)

  prn _ e           = parens (pr e)

prAppT (AppT e t) ts = prAppT e (t:ts)
prAppT e []  = prn 2 e
prAppT e ts  = prn 2 e <> tris (commaSep (map pr ts))

prStmts d (Do p e1 e2)  = prStmts (d $$ pr p <+> text "<-" <+> pr e1) e2
prStmts d e             = d $$ pr e
                                                

instance Show FieldV where show x = prShow x
instance Pr FieldV where
  pr (FieldV l x e) = pr l <> ev <+> char '=' <+> pr e
    where ev = case x of
                 Nothing -> empty
                 Just e  -> cdot <> prn 3 e

 
instance Show FieldP where show x = prShow x
instance Pr FieldP where
  pr (FieldP l e p)  = pr l <> ev <+> char '=' <+> pr p
    where ev  = case e of
                  Nothing -> empty
                  Just ev -> cdot <> prn 3 ev


instance Show Literal where show x = prShow x
instance Pr Literal where
  pr (Int i)        = text (show i)
  pr (Str s)        = text (show s)
  pr (Chr c)        = text (show c)



-- XXX: Prettier print
instance Show Match where show x = prShow x
instance Pr Match where
  pr (MPat p m)     = prMPat "=" [p] m
  pr (MAbsEv x p m) = prMAbsEv [(x,p)] m
  pr (MAbsT x m)    = prMAbsT [x] m
  pr (MIs e)        = pr e
  pr (MGrd q m)     = pr q $$ pr m
  pr (MOr m1 m2)    = char '|' <+> pr m1 
                   $$ char '|' <+> pr m2


prMPat c ps (MPat p m)  = prMPat c (p:ps) m
prMPat c ps m           = text "\\" <> hsep (map (prn 2) (reverse ps))
                            <+> text c <+> pr m

-- Note: we assume that evidence comes after abstracting type variables.
prMAbsEv xs (MAbsEv x p m)  = prMAbsEv ((x,p):xs) m
prMAbsEv xs m               = fsep [ hsep (map p (reverse xs)) <+> text "=>" 
                                   , pr m ]
  where p (x,p)             = parens (pr x <+> text "::" <+> pr p)


prMAbsT xs (MAbsT x m)      = prMAbsT (x:xs) m
prMAbsT xs m                = text "/\\" <> hsep (map pr (reverse xs))
                           <> char '.' <+> pr m


instance Show Qual where show x = prShow x
instance Pr Qual where
  pr (QGrd e)       = text "if" <+> pr e
  pr (QPat p e)     = text "let" <+> pr p <+> text "=" <+> pr e 
                          -- prn 1 p <+> text "<-" <+> pr e
  pr (QLet bs)      = text "let" $$ nest 2 (pr bs)
  pr (QLocal q1 q2) = text "local" $$ nest 2 (pr q1) $$ text "in" <+> pr q2
  pr (QThen q1 q2)  = pr q1 $$ pr q2


instance Show BPat where show x = prShow x
instance Pr BPat where
  pr BPSplit          = text "(_ # _)"
  pr (BPCon x)        = pr x
  pr (BPUpd op x y)   = parens (text (show op) <+> text "|" <+> pr x
                                                  <+> text "|" <+> pr y)

instance Show Pat where show x = prShow x
instance Pr Pat where
  prn _ (PVar x)    = pr x
  prn _ PWild       = char '_'

  prn _ (PAbs p q)  = parens (pr p <+> text "|" <+> pr q)
  -- ugly
  prn _ (PApp bp ts es ps) = pr bp <> 
                             text "@" <> parens (commaSep (map pr ts)) <> 
                             cdot <> parens (commaSep (map pr es)) <> 
                             hsep (map (prn 3) ps)

  prn n (PSig p t)
    | n < 1         = prn 1 p <+> text "::" <+> pr t
    | otherwise     = parens (pr p)
                                                
  prn _ (PInfix e1 op e2) = parens (pr e1 <+> pr op <+> pr e2)
  prn _ (PParens p)       = parens (pr p)
  -- prn _ p                 = parens (pr p)

                             
                            

{-


  prn n (PCon c _ ps)     
    | n < 3         = pr c <+> hsep (map (prn 3) ps)
  prn n (PSplit p1 p2)  
    | n < 2         = prn 1 p1 <+> char '#' <+> prn 1 p2

  prn n (PEv p e)   
    | n < 1         = prn 3 p <> cdot <> pr e
  prn _ (PInc x k e)  = parens (pr x <+> text "-" <+> text (show k) 
                                <+> text "|" <+> pr x <+> text "<=" <+> pr e)
  prn _ (PDec x k e)  = parens (pr x <+> text "+" <+> text (show k) 
                                <+> text "|" <+> pr x <+> text ">=" <+> pr e)

-}

 



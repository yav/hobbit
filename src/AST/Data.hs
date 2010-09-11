module AST.Data
  ( DataDecl(..), dataName
  , TParam(..)
  , AlgData(..), DataCon(..)
  , KSig(..)
  , BitData(..), FlatCon(..), Field(..), Layout2(..), l2Fields
  , TypeSyn(..)
  , Struct(..), StructField(..)
  , ADT, ADT'(..), ADTCtr, ADTCtr'(..)
  , BDT(..), BDTCtr(..), TS(..)
  , BitField(..), FreeLayout(..), Layout(..)
  , stKind, stAsType
  , bdAsType, bdKind, fcLayout, bdcSchema
  , acSchema
  , bcWidth, bcSchema, bcSubType
  , adtAsType, adtKind
  , bdtAsType, bdtWidth, bdtKind
  , tsKind
  , findADTCtr, findBDTCtr
  ) where

import AST.Type
import AST.Expr
import qualified BDD(Pat,width,showPat) 

import PP
import Utils(showBin)

import Data.List(find,intersperse)
import Data.Maybe(catMaybes,listToMaybe)
import Data.Word


-- XXX: we can probably get eliminate this type
-- and simply keep the different declarations separate.
data DataDecl       = BitdataDecl BitData
                    | DataDecl    AlgData
                    | TypeDecl    TypeSyn
                    | KSigDecl    KSig
                    | StructDecl  (Struct TParam)

dataName (BitdataDecl x)                = bdName x
dataName (DataDecl (AlgData x _ _))     = x
dataName (TypeDecl (TypeSyn x _ _))     = x
dataName (StructDecl x)                 = stName x
dataName (KSigDecl (KSig x _))          = x

data KSig           = KSig Name Kind

data TParam         = TP Name (Maybe Kind)

data AlgData        = AlgData Name [TParam] [DataCon]
data DataCon        = DataCon Name [Type]

data BitData        = BitData { bdName :: Name, bdCtrs ::  [FlatCon] 
                              , bdDeriving :: [Name] }
data FlatCon        = FlatCon 
                    { fcName    :: Name
                    , fcFields  :: [Field]      
                    , fcAs      :: Maybe [Layout]
                    , fcIf      :: Maybe Expr
                    }
                    | FlatCon2 {
                        fcName    :: Name,
                        fcFields2 :: Layout2,
                        fcIf      :: Maybe Expr
                    }



data Field          = Field 
                        { fieldName     :: Name       
                        , fieldType     :: Type        
                        , fieldDefault  :: Maybe Expr
                        }

data Layout         = LayField Name 
                    | LayInt Integer (Maybe Word32)    -- Value, width
                    | LaySig [Layout] Type
                    | LayWild


data Layout2        = BF_Named Field
                    | BF_Wild 
                    | BF_Tag Word32 
                    | BF_Sig Layout2 Type
                    | BF_Cat Layout2 Layout2
                    | BF_Unit



data TypeSyn        = TypeSyn Name [TParam] Type


data Struct p       = Struct { stName   :: Name
                             , stParams :: [p]
                             , stFields :: Poly [StructField] 
                             , stSize   :: Maybe Type }

data StructField    = StField { sfName :: Name, sfType :: Type, sfPad :: Bool }
                    | StPad (Maybe Type)


-- Internal representation for data types --------------------------------------

-- Algebraic types
type ADT            = ADT' Name
data ADT' name      = ADT
                    { adtName   :: Name
                    , adtParams :: [TyVar]
                    , adtCtrs   :: [ Poly (ADTCtr' name) ]
                    }

type ADTCtr         = ADTCtr' Name
data ADTCtr' name   = ADTCtr
                    { acName    :: name
                    , acFields  :: [Type] }


-- Bitdata types
data BDT            = BDT
                    { bdtName   :: Name
                    , bdtCtrs   :: [ BDTCtr ]
                    , bdtCover  :: BDD.Pat }

data BDTCtr         = BDTCtr
                    { bcName    :: Name
                    , bcFields  :: [Field]
                    , bcLayout  :: [FreeLayout]
                    , bcIf      :: Maybe Expr
                    , bcCover   :: BDD.Pat }

data BitField       = BitField { bfOffset :: Word32 , bfWidth :: Word32 }
data FreeLayout     = (:@:) { flSpec :: Layout, flLoc :: BitField }

-- Type synonyms
data TS             = TS 
                    { tsName    :: Name
                    , tsParams  :: [TyVar]
                    , tsBody    :: Poly Type
                    , tsBodyK   :: Kind }


-- Sugar -----------------------------------------------------------------------

-- Structs ---------------------------------------------------------------------
stKind             :: Struct TyVar -> Kind
stKind s            = foldr kFun kArea (map tyVarKind (stParams s))

stAsType           :: Struct TyVar -> Type
stAsType s          = foldl TApp (TCon (stName s)) (map TFree (stParams s))



-- ADTs ------------------------------------------------------------------------
adtAsType          :: ADT' a -> Type
adtAsType a         = foldl TApp (TCon (adtName a)) (map TFree (adtParams a))

adtKind            :: ADT' a -> Kind
adtKind a           = foldr kFun kType (map tyVarKind (adtParams a))

acSchema           :: ADT' a -> Poly (ADTCtr' a) -> Schema
acSchema a c        = Forall (polyVars c ++ adtParams a) (polyPreds c) 
                             (foldr tFun (adtAsType a) (acFields (poly c)))

findADTCtr         :: Eq a => a -> [ADT' a] -> Maybe (ADT' a, Poly (ADTCtr' a))
findADTCtr x adts   = listToMaybe $ catMaybes $ map one adts
  where one a       = (,) a `fmap` find ((x == ) . acName . poly) (adtCtrs a)



-- Bit Data --------------------------------------------------------------------

-- parser form: BitData
bdAsType           :: BitData -> Type
bdAsType b          = TCon (bdName b) -- (Just (bdKind b))

bdKind             :: BitData -> Kind
bdKind _            = kType

bdcSchema          :: BitData -> FlatCon -> Schema
bdcSchema b c
  | noFields c       = mono (bdAsType b)
  | otherwise        = mono (tSub (bdName b) (fcName c) `tFun` bdAsType b)
  where
  noFields (FlatCon { fcFields = fs }) = null fs
  noFields (FlatCon2 { fcFields2 = fs }) = null (l2Fields fs)

l2Fields (BF_Cat l1 l2)  = l2Fields l1 ++ l2Fields l2
l2Fields (BF_Sig l _)    = l2Fields l
l2Fields (BF_Named f)    = [f]
l2Fields (BF_Tag {})     = []
l2Fields (BF_Wild {})    = []
l2Fields (BF_Unit {})    = []

fcLayout           :: FlatCon -> [Layout]
fcLayout c          = case fcAs c of
                        Just ls -> ls
                        Nothing -> map (LayField . fieldName) (fcFields c)


-- internal form: BDT
bdtKind            :: BDT -> Kind
bdtKind _           = kType

bdtAsType          :: BDT -> Type
bdtAsType b         = TCon (bdtName b) -- (Just (bdtKind b))

bdtWidth           :: BDT -> Word32
bdtWidth b          = BDD.width (bdtCover b)

bcWidth            :: BDTCtr -> Word32
bcWidth c           = BDD.width (bcCover c)

bcSubType          :: Name -> BDTCtr -> Type
bcSubType b c       = TCon (subName b (bcName c)) 

bcSchema           :: BDT -> BDTCtr -> Schema
bcSchema b c
  | null (bcFields c) = mono (bdtAsType b)
  | otherwise         = mono (bcSubType (bdtName b) c `tFun` bdtAsType b)

findBDTCtr         :: Name -> [BDT] -> Maybe (BDT,BDTCtr)
findBDTCtr x bdts   = listToMaybe $ catMaybes $ map one bdts
  where one a       = (,) a `fmap` find ((x == ) . bcName) (bdtCtrs a)


-- Type Synonyms ---------------------------------------------------------------

tsKind             :: TS -> Kind
tsKind t            = foldr kFun (tsBodyK t) (map tyVarKind (tsParams t))

 


-- Pretty printing -------------------------------------------------------------


instance Show DataDecl where show x = prShow x
instance Pr DataDecl where
  pr (BitdataDecl x)  = pr x
  pr (DataDecl x)     = pr x
  pr (TypeDecl x)     = pr x
  pr (StructDecl x)   = pr x
  pr (KSigDecl x)     = pr x

instance Show TParam where show x = prShow x
instance Pr TParam where pr (TP x _) = pr x

instance Pr t => Show (Struct t) where show x = prShow x
instance Pr t => Pr (Struct t) where
  pr x = text "struct" <+> preds (polyPreds (stFields x)) <+> pr (stName x) 
                       <+> hsep (map pr (stParams x))
                       <+> optSize
                       <+> text "=" <+> vcat (map pr $ poly $ stFields x)
    where optSize   = maybe empty (\x -> text "| size " <+> pr x) (stSize x)
          preds []  = empty
          preds [p] = pr p <+> text "=>"
          preds ps  = parens (commaSep (map pr ps)) <+> text "=>"

instance Show StructField where show x = prShow x
instance Pr StructField where
  pr (StField x t p)  = pad <+> pr x <+> text "::" <+> pr t
    where pad = if p then text ".." else empty
  pr (StPad Nothing)  = text ".."
  pr (StPad (Just t)) = pr t

instance Show TypeSyn where show x = prShow x
instance Pr TypeSyn where
  pr (TypeSyn c as t) = fsep [ text "type" <+> pr c <+> hsep (map pr as)
                             , text "=" <+> pr t ]

instance Show KSig where show x = prShow x
instance Pr KSig where
  pr (KSig x k) = text "primitive" <+> pr x <+> text "::" <+> pr k

instance Show BitData where show x = prShow x
instance Pr BitData where
  pr (BitData t cs ds) = text "bitdata" <+> pr t 
                   $$ nest 8 (lineUp (char '=') (char '|') empty (map pr cs))
                   $$ nest 2 (der ds)
    where der []  = empty
          der [d] = text "deriving" <+> pr d
          der ds  = parens (commaSep (map pr ds))


instance Show AlgData where show x = prShow x
instance Pr AlgData where
  pr (AlgData c as cs) 
                    = text "data" <+> pr c <+> hsep (map pr as)
                   <+> lineUp (char '=') (char '|') empty (map pr cs)


instance Show DataCon where show x = prShow x
instance Pr DataCon where
  pr (DataCon c ts) = pr c <+> hsep (map (prn 2) ts)


instance Show FlatCon where show x = prShow x
instance Pr FlatCon where
  pr (FlatCon x fs a i) = prFlatCon x fs a i
  pr (FlatCon2 x fs i)  = pr x <+> brackets (pr fs) <+> maybeIf
    where
    maybeIf = prOpt i (\e -> text "if" <+> pr e)


instance Show BitField where show x = prShow x
instance Pr BitField where
  pr x              = parens (text (show (bfOffset x)) <> colon 
                        <> text (show (bfWidth x)))


instance Show FreeLayout where show x = prShow x
instance Pr FreeLayout where
  pr (l :@: x)      = pr l <> char '@' <> pr x


prFlatCon x fs a i  = pr x <+> flds
                   $$ prOpt a (\x -> text "as" <+> prLayout 0 x)
                   $$ prOpt i (\x -> text "if" <+> pr x)
    where flds | null fs    = empty
               | otherwise  = lineUp (char '{') comma (char '}') (map pr fs)


prLayout _ [l]      = pr l
prLayout 0 xs       = hsep (intersperse (char '#') (map pr xs))
prLayout _ xs       = parens (prLayout 0 xs)


instance Show Field where show x = prShow x
instance Pr Field where
  pr (Field l t e)  = pr l <+> text "::" <+> pr t 
                  <+> prOpt e (\x -> char '=' <+> pr x)

instance Show Layout2 where show x = prShow x
instance Pr Layout2 where
  prn _ BF_Unit         = empty
  prn _ BF_Wild         = char '_'
  prn _ (BF_Tag n)      = text (show n)
  prn _ (BF_Named f)    = pr f
  prn n (BF_Sig l t)
    | n < 2             = prn 1 l <+> text "::" <+> pr t
  prn n (BF_Cat l r)    
    | n < 1             = pr l <+> char '|' <+> pr r
  prn _ l               = brackets (pr l)



instance Pr name => Show (ADT' name) where show x = prShow x
instance Pr name => Pr (ADT' name) where
  pr a              = fsep [ text "data" <+> pr (adtName a) 
                                <+> hsep (map pr (adtParams a))
                           , nest 2 $ lineUp (char '=') (char '|') empty 
                                          (map pr (adtCtrs a)) ]

instance Pr name => Show (ADTCtr' name) where show x = prShow x
instance Pr name => Pr (ADTCtr' name) where 
  pr a              = pr (acName a) <+> hsep (map (prn 2) (acFields a))


instance Show BDT where show x = prShow x
instance Pr BDT where
  pr b              = text "bitdata" <+> pr (bdtName b)
                  <+> lineUp (char '=') (char '|') empty (map pr (bdtCtrs b))
                  $$ vcat (map text (BDD.showPat (bdtCover b)))


instance Show BDTCtr where show x = prShow x
instance Pr BDTCtr where 
  pr b              = prFlatCon (bcName b) (bcFields b) (Just (bcLayout b)) 
                                                        (bcIf b)
                    

instance Show Layout where show x = prShow x
instance Pr Layout where 
  pr (LayField x)         = pr x
  pr (LayInt n Nothing)   = text (show n)
  pr (LayInt n (Just w))  = char 'B' <> text (showBin w n)
  pr (LaySig ls t)        = prLayout 1 ls <+> text "::" <+> pr t
  pr LayWild              = char '_'

instance Show TS where show x = prShow x
instance Pr TS where
  pr (TS t xs b _)  = fsep [ text "type" <+> pr t <+> hsep (map pr xs) 
                           , nest 2 (text "=" <+> pr b) ]


                    



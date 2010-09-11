-- | Here we rewrite fixities.

module Parsing.Fixity
  ( Fixity(..), Assoc(..), Rewrite
  , defaultFixity, fixTable, rewrite
  ) where

import AST
import qualified Pass
import Error
import Utils
import MonadLib



data Fixity         = Fixity { prec :: Int, assoc :: Assoc }

data Assoc          = LeftAssoc | RightAssoc | NonAssoc
                      deriving Eq

defaultFixity       = Fixity { prec = 9, assoc = LeftAssoc }

type FixTable       = [(Name,Fixity)]


fixTable           :: FixTable
fixTable            = map (left 7)  [VarName "*"] ++
                      map (left 6)  [VarName "+", VarName "-", 
                                     VarName "@", VarName "@@"] ++
                      map (right 5) [VarName "#"] ++
                      map (non 4)   [ VarName "==", VarName "/="
                                    , VarName "<", VarName "<="
                                    , VarName ">", VarName ">="] ++
                      map (right 3) [VarName "&", VarName "&&"] ++
                      map (right 2) [VarName "!", VarName "||", ConName "->"]
  where
  left n x          = (x,Fixity n LeftAssoc)
  right n x         = (x,Fixity n RightAssoc)
  non n x           = (x,Fixity n NonAssoc)
                   

--------------------------------------------------------------------------------
type DesugarM       = ReaderT FixTable (ExceptionT String Id)

run m               = runId
                    $ runExceptionT
                    $ runReaderT fixTable m

err                :: String -> DesugarM a
err x               = raise x
                
rewrite            :: Rewrite a => a -> Pass.Pass a
rewrite x           = case run (rew x) of
                        Left e  -> Pass.err [e]
                        Right a -> return a
--------------------------------------------------------------------------------



class Rewrite t where
  rew                      :: t -> DesugarM t

instance Rewrite t => Rewrite [t] where
  rew xs                    = forEach xs rew

instance Rewrite t => Rewrite (Maybe t) where
  rew Nothing               = return Nothing
  rew (Just x)              = Just # rew x


instance Rewrite Module where
  rew m                     = do bs <- rew (modBinds m) 
                                 ts <- rew (modTypes m) 
                                 return (m { modBinds = bs, modTypes = ts })

instance Rewrite DataDecl where
  rew (BitdataDecl d)       = BitdataDecl # rew d
  rew (DataDecl d)          = DataDecl # rew d
  rew (TypeDecl d)          = TypeDecl # rew d
  rew (StructDecl d)        = StructDecl # rew d
  rew (KSigDecl d)          = KSigDecl # rew d

instance Rewrite (Struct t) where
  rew (Struct x as fs s)    = Struct x as # rew fs <# rew s 

instance Rewrite StructField where
  rew (StField l t p)       = StField l # rew t <# return p
  rew (StPad p)             = StPad # rew p

instance Rewrite KSig where
  rew (KSig x t)            = KSig x # rew t

instance Rewrite AlgData where
  rew (AlgData x as cs)     = AlgData x as # rew cs

-- XXX: should the 'ts' be split before this rewriting?
instance Rewrite DataCon where
  rew (DataCon c ts)        = DataCon c # rew ts

instance Rewrite TypeSyn where
  rew (TypeSyn x as t)      = TypeSyn x as # rew t

instance Rewrite BitData where
  rew (BitData x cs ds)     = BitData x # rew cs <# return ds

instance Rewrite FlatCon where
  rew (FlatCon c fs a i)    = FlatCon c # rew fs <# return a <# rew i
  rew (FlatCon2 c fs i)     = FlatCon2 c # rew fs <# rew i

instance Rewrite Field where
  rew (Field x t e)         = Field x # rew t <# rew e

instance Rewrite Layout2 where
  rew (BF_Named f)          = BF_Named # rew f
  rew (BF_Cat l r)          = BF_Cat # rew l <# rew r
  rew (BF_Sig l t)          = BF_Sig # rew l <# rew t
  rew (BF_Wild)             = return BF_Wild  
  rew (BF_Tag n)            = return (BF_Tag n)
  rew (BF_Unit)             = return (BF_Unit)

instance Rewrite BindBlock where
  rew (BindBlock p a e i)   = BindBlock # rew p <# rew a <# rew e <# rew i

instance Rewrite PrimDecl where
  rew p                     = (\t -> p { primType = t } ) # rew (primType p)

instance Rewrite AreaDecl where
  rew a                     = (\t -> a { arType = t }) # rew (arType a)

instance Rewrite ExpBind where
  rew (ExpBind i s)         = ExpBind # rew i <# rew s

instance Rewrite ImpBind where
  rew (ImpBind x m)         = ImpBind x # rew m

instance Rewrite Match where
  rew (MOr m1 m2)           = MOr # rew m1 <# rew m2
  rew (MIs e)               = MIs # rew e
  rew (MPat p m)            = MPat # rew p <# rew m
  rew (MGrd q m)            = MGrd # rew q <# rew m
  rew (MAbsT _ _)           = bug "Fixity.rew[Match]" "MAbsT"
  rew (MAbsEv _ _ _)        = bug "Fixity.rew[Match]" "MAbsEv"


instance Rewrite Pat where
  rew (PVar x)              = return (PVar x)
  rew PWild                 = return PWild
  rew (PSig p t)            = PSig # rew p <# rew t
  rew (PAbs p q)            = PAbs # rew p <# rew q
  rew (PApp p ts es ps)     = PApp # rew p <# rew ts <# return es <# rew ps

{-
  rew (PCon c ts ps)        = PCon c # rew ts <# rew ps
  rew (PSplit p1 p2)        = PSplit # rew p1 <# rew p2
  rew (PInc x k e)          = PInc x k # rew e
  rew (PDec x k e)          = PDec x k # rew e
  rew (PEv _ _)             = bug "Fixity.rew[Pat]" "PEv"
-}

  rew (PParens p)           = rew p
  rew (PInfix p1 op p2)     = infixOp app isInfix p1 op p2
    where app p1 op p2      = PApp (BPCon op) [] [] [p1,p2] 
          isInfix (PInfix p1 op p2) = Just (p1,op,p2)
          isInfix _                 = Nothing


instance Rewrite BPat where
  rew BPSplit               = return BPSplit
  rew (BPCon x)             = return (BPCon x)
  rew (BPUpd d e1 e2)       = BPUpd d # rew e1 <# rew e2

instance Rewrite FieldP where
  rew (FieldP l x p)        = FieldP l x # rew p


 
instance Rewrite Qual where
  rew (QGrd e)              = QGrd # rew e
  rew (QPat p e)            = QPat # rew p <# rew e
  rew (QLet bs)             = QLet # rew bs
  rew (QLocal q1 q2)        = QLocal # rew q1 <# rew q2
  rew (QThen q1 q2)         = QThen # rew q1 <# rew q2


instance Rewrite Expr where
  rew e = case e of 
            App e1 e2       -> App # rew e1 <# rew e2
            Match m         -> Match # rew m
            Var x           -> return (Var x)
            Sig e t         -> Sig # rew e <# rew t
            Lit l           -> return (Lit l)

            Con x fs        -> Con x # rew fs
            Upd e fs        -> Upd # rew e <# rew fs 

            Do p e1 e2      -> Do # rew p <# rew e1 <# rew e2

            Parens e        -> rew e
            Infix e1 op e2  -> infixOp app isInfix e1 op e2
              where 
              app e1 (VarName "&&") e2  = eAnd e1 e2
              app e1 (VarName "||") e2  = eOr e1 e2
              app e1 op e2  = Var op `App` e1 `App` e2
              isInfix (Infix e1 op e2) =  Just (e1,op,e2)
              isInfix _ = Nothing

            AppT _ _        -> "Fixity.rew[Expr]" `unexpected` "AppT"
            AppEv _ _       -> "Fixity.rew[Expr]" `unexpected` "AppEv"

instance Rewrite FieldV where
  rew (FieldV l x e)        = FieldV l x # rew e

instance Rewrite Type where
  rew t = case t of
            TApp t1 t2      -> TApp # rew t1 <# rew t2
            TInfix t1 c t2  -> infixOp app isInfix t1 c t2
              where app t1 c t2  = TCon c `TApp` t1 `TApp` t2
                    isInfix (TInfix x c y) = Just (x,c,y)
                    isInfix _ = Nothing
            TParens t       -> rew t
            TCon _          -> return t
            TFree _         -> return t 
            TSyn _ _ _      -> "Fixity.rew[Type]" `unexpected` "TSyn"

instance Rewrite p => Rewrite (Poly p) where
  rew (Forall xs ps t)  = Forall xs # rew ps <# rew t

instance Rewrite Pred where
  rew (CIn c ts)        = CIn c # rew ts

instance Rewrite Rule where
  rew (Rule how p)      = Rule how # rew p


lkpFixity op        = do table <- ask
                         return (case lookup op table of
                                   Just f   -> f
                                   Nothing  -> defaultFixity)

infixOp app isInfix e1 opL e
  = case isInfix e of
      Just (e2,opR,e3) -> 

        lkpFixity opL >>= \fixL -> 
        lkpFixity opR >>= \fixR ->
      
        -- Left?
        if (prec fixL > prec fixR) || 
           (prec fixL == prec fixR && 
            assoc fixL == LeftAssoc && 
            assoc fixR == LeftAssoc) 
           then do eL  <- infixOp app isInfix e1 opL e2
                   e3' <- rew e3
                   return (app eL opR e3')
        else 
        -- Right?
        if (prec fixL < prec fixR) || 
           (prec fixL == prec fixR && 
            assoc fixL == RightAssoc && 
            assoc fixR == RightAssoc) 
           then do e1' <- rew e1
                   eR  <- infixOp app isInfix e2 opR e3
                   return (app e1' opL eR)
      
        -- Error
        else err ("Non-associative operators with the same precedence: " ++ 
                      show opL ++ " and " ++ show opR)
      
      Nothing -> app # rew e1 <# return opL <# rew e




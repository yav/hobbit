module Parsing.Utils where

import AST 
import Parsing.Lexer
import Parsing.Range
import Error

import Utils
import MonadLib
import List

type ParseM = ExceptionT String Id

run txt p = runId $ runExceptionT $ p $ layout [] $ lexer txt

parseError :: String -> ParseM a
parseError = raise

happyError :: [Lexeme] -> ParseM a
happyError ls = raise ("Parse error at " ++ show (
                        case ls of
                          []  -> end
                          l:_ -> from (lexPos l)))


-- Modules ---------------------------------------------------------------------

data ParseTop     = TopBind ParseBind
                  | TopType DataDecl

data ParseBind    = ParsePrim PrimDecl
                  | ParseArea AreaDecl
                  | ParseSig Name Schema
                  | ParseBind ImpBind

topDecls         :: [ParseTop] -> ParseM ([DataDecl], BindBlock)
topDecls ps       = do b <- bindBlock [ b | TopBind b <- ps ]
                       return ([ b | TopType b <- ps ], b) 

-- Note: Expects that the argument is reversed.
-- This matters when we join the equations that belong to a definition.
bindBlock        :: [ParseBind] -> ParseM BindBlock
bindBlock bs      = case dupSigs of
                      [] -> foldM addSig block1 sigs 
                      xs -> parseError $ unlines ( "Duplicate signatures"
                                                 : map show xs )
  where
  act (b,m) (ParsePrim p)   = (b { prims     = p : prims b }, m)
  act (b,m) (ParseArea p)   = (b { areas     = p : areas b }, m)
  act (b,m) (ParseBind i)   = (consBind i b, m)
  act (b,m) (ParseSig x s)  = (b, (x,s) : m)

  (block1, sigs) = foldl act (emptyBindBlock,[]) bs

  dupSigs = filter multiple
          $ groupBy ((==) `on` fst) 
          $ sortBy (compare `on` fst) sigs

  multiple [_]  = False
  multiple _    = True

  consBind i@(ImpBind x m) b =
    case impBinds b of
      ImpBind y m' : js | x == y -> b { impBinds = ImpBind x (MOr m m') : js }
      js -> b { impBinds = i : js }

  addSig b (x,s) = case remove ((x ==) . biName) (impBinds b) of
                     Just (i,is) -> return 
                        b { expBinds  = ExpBind i s : expBinds b,
                            impBinds  = is }
                     Nothing -> parseError ("Signature " ++ show x ++ 
                                                    " has no definition.")


qualName f (x,y)  = Qual x (f y)
notQual (Q n)     = case n of
                      Qual _ _  -> parseError ("Qualified name: " ++ show n)
                      n         -> return n

impSpec (Ent x s) = (`Ent` s) # notQual x 




-- Expressions -----------------------------------------------------------------

eCase e@(Var _) m = Match (m e)
eCase e m         = Match (MGrd (QLet b) (m (Var x)))
  where x         = VarName "$case"
        b         = emptyBindBlock { impBinds = [ImpBind x (MIs e)] }

eIf e1 e2 e3      = Match (MGrd (QGrd e1) (MIs e2) `MOr` MIs e3)

eRecord x fs  
  | isCon x   = Con x fs
  | otherwise = Upd (Var x) fs 

isCon (Qual _ x)  = isCon x
isCon (ConName _) = True
isCon _           = False


intLit n            = Lit (Int n)
binLit (BinTok n w) = intLit n `Sig` 
                        TApp (TCon (ConName "Bit")) (tNat (fromIntegral w))
binLit x            = "binLit" `unexpected` show x
charLit x           = binLit (BinTok (fromIntegral (fromEnum x)) 8)
strLit xs           = foldr eCons eNil (map charLit xs)
  where eNil        = Var (ConName "Nil")
        eCons x xs  = apps (Var (ConName "Cons")) [x,xs]


-- Patterns --------------------------------------------------------------------

pBin (BinTok n w) = pInt n `PSig` tBit (tNat $ fromIntegral w) 
pBin x            = "pBin" `unexpected` show x
pInt n            = PAbs (PVar it) $ QGrd (apps eEquals [Var it, intLit n])
  where it        = VarName "it"    -- is it safe to reuse the name?
                                    -- we could make it unique by using the pos.


pCon c ps         = PApp (BPCon c) [] [] ps
pSplit p1 p2      = PApp BPSplit [] [] [p1,p2]
pIxUpd op e1 e2 p = PApp (BPUpd op e1 e2) [] [] [p]



{-
pDec x k          = PApp (BPUpd Inc (Lit (Int k)) (Var (VarName "minVal"))) [] [] [PVar x]
pInc x k          = PApp (BPUpd Inc (Lit (Int k)) (Var (VarName "minVal"))) [] [] [PVar x]

pDecBd x k e      = case e of
                      Infix (Var x') (VarName ">=") e
                        | x == x' -> return (PDec x k e)
                      Infix e (VarName "=<") (Var x')
                        | x == x' -> return (PDec x k e)
                      _ -> parseError "Invalid decrement pattern"

pIncBd x k e      = case e of
                      Infix (Var x') (VarName "<=") e
                        | x == x' -> return (PInc x k e)
                      Infix e (VarName ">=") (Var x')
                        | x == x' -> return (PInc x k e)
                      _ -> parseError "Invalid increment pattern"
-}


pFields            :: Pat -> [FieldP] -> Pat
pFields p fs        = foldl pUpd p fs

pUpd p1 (FieldP l _ p2) = PAbs (PVar it) (QPat p1 (Var it) `QThen`
                                QPat p2 (apps (Var (Select l)) [Var it]))
  where it        = VarName "it"    -- is it safe to reuse the name?
                                    -- we could make it unique by using the pos.

pAs x p             = PAbs (PVar x) (QPat p (Var x))

pChar x       = pBin (BinTok (fromIntegral (fromEnum x)) 8)






-- Types -----------------------------------------------------------------------

prelType         :: String -> Type
prelType t        = TCon (qPrel (ConName t))

tExp2 (TCon (TNat 2)) t1 t2 = return (prelType "Exp2" `TApp` t1 `TApp` t2)
tExp2 _ _ _ = parseError "Invalid exponent predicate"

tyVar            :: Name -> Type
tyVar x           = TFree (TyUser { tyVarName = x }) 

typeToCon        :: Type -> ParseM DataCon
typeToCon (TInfix s c t) = return (DataCon c [s,t])
typeToCon t       = case splitTApp t [] of
                      (TCon c, ts)  -> return (DataCon c ts)
                      _ -> parseError ("Invalid constructr: " ++ show t)




typeToSchema     :: Type -> Type -> ParseM Schema
typeToSchema ps t = do ps <- preds
                       return (Forall [] ps t)
    where 
    preds         = case splitTApp ps [] of
                      (TCon (Tup _), ps)  -> forEach ps typeToPred'
                      _                   -> return # typeToPred' ps

schemaToRule       :: Schema -> ParseM (Poly Pred)
schemaToRule s      = do c <- typeToPred' (poly s)
                         return (s { poly = c })



typeToPred'      :: Type -> ParseM Pred
typeToPred' (TParens t) = typeToPred' t
typeToPred' t     = case splitTApp t [] of 
                      (TCon c, ts) -> pred c ts
                      (TInfix t1 c t2, ts) -> pred c (t1:t2:ts)
                      _ -> parseError ("Invalid predicate " ++ show t)
  where
  pred name args  = return (CIn name args)



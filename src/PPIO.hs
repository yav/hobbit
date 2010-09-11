module PPIO ( PrM, runPrM, PrintM(..), printM
            , wrap, withPrec, withQuants, getQuants
            , module PP) where

import PP
import AST
import Type.MonadIO 
import Error

import Utils
import MonadLib

-- Precedence:
--  (high)
--  * application (left)
--  * function (right)
--  (low)


type PrM            = ReaderT Env IO
data Env            = Env
                    { prec      :: !Int
                    , boundVars :: ![(TyVar,String)] 
                    , showTyAp  :: Bool }

class PrintM t where
  prM :: t -> PrM Doc

runPrM             :: PrM a -> IO a
runPrM m            = runReaderT (Env { prec = 0,
                                        boundVars = [],
                                        showTyAp = True }) 
                    $ m

printM             :: PrintM t => t -> IO Doc
printM t            = runPrM (prM t)

wrap x d            = do p <- prec # ask
                         return (if p < x then d else parens d)



instance PrintM Name where
  prM (VarName x)      = return $ text x
  prM (ConName x)      = return $ text x
  prM (Qual m x)       = do x <- prM x
                            return ({-text m <> char '.' <>-} x)

  prM (Select l)       = (parens . (char '.' <>)) # prM l
  prM (Update l)       = (parens . (<> char '=')) # prM l
  prM (IfCheck c)      = (text "$if_" <>) # prM c
  prM (DefaultVal c f) = do c <- prM c 
                            f <- prM f
                            return (text "$dfl_"<> c <> text "." <> f)

  prM SFun             = return $ text "(->)"
  prM SSort            = return $ text "sort"

  prM (TSub x y)       = do x <- prM x; y <- prM y
                            return (x <> char '\'' <> y)
  prM TSome            = return $ text "$SomeT"
  prM (TNat n)         = return $ text (show n)
  prM (TLab l)         = prM l
  prM (Tup 0)          = return $ text "()"
  prM (Tup 1)          = bug "prName" "1-tuple"
  prM (Tup n)          = return $ parens $ hsep $ replicate 
                                                  (fromIntegral (n-1)) comma

  prM (Inst x ts)      = do ts <- withPrec 0 
                                $ ifM (showTyAp # ask)
                                      ((tris . commaSep) # (forEach ts prM))
                                      (return empty)
                            x <- prM x
                            return (x<>ts)



instance PrintM x => PrintM (ADT' x) where
  prM a = withTyAp True
        $ do x <- prM $ adtName a
             (xs,cs) <- withQuants (adtParams a) $ \xs -> 
                        do cs <- forEach (adtCtrs a) prM
                           return (xs,alts cs)
             return (text "data" <+> x <+> hsep (map text xs) $$ nest 2 cs)
    where alts []     = empty
          alts (x:xs) = vcat (text "=" <+> x : [ text "|" <+> x | x <- xs ])
          
                 
instance PrintM x => PrintM (ADTCtr' x) where 
  prM c = do x  <- withTyAp True {-False-} $ prM (acName c)
             fs <- withPrec 1 $ forEach (acFields c) prM
             return (x <+> hsep fs)



instance PrintM Type where
  prM t             = p =<< inBase (pruneIO False t)
    where
    p (TApp t1 t2)  = prTApps t1 [t2]
    p (TSyn c ts _) = prTApps (TCon c) ts 
    p (TFree x)     = do as <- getQuants 
                         return $ case lookup x as of
                                    Just x  -> text x
                                    Nothing -> char '?' <> pr x
    p (TCon c)      = prM c
    p (TInfix {})   = "PPIO.prM[Type]" `unexpected` "TInfix"
    p (TParens {})  = "PPIO.prM[Type]" `unexpected` "TParens"

prTApps            :: Type -> [Type] -> PrM Doc
prTApps t ts        = (`p` ts) =<< inBase (pruneIO False t)
  where 
  p (TApp t1 t2) ts       = prTApps t1 (t2:ts)
  p (TCon SFun) [t1,t2]   = prFun "--->" t1 t2
  p (TCon t) [t1,t2] | t == name = prFun "->" t1 t2
    where TCon name = tcFun
  p t ts                  = do t  <- prM t
                               ts <- withPrec 2 (forEach ts prM)
                               wrap 2 (t <+> hsep ts)


prFun              :: String -> Type -> Type -> PrM Doc 
prFun arrow t1 t2   = do t1 <- withPrec 1 (prM t1)
                         t2 <- withPrec 0 (prM t2)
                         wrap 1 (t1 <+> text arrow <+> t2)


instance PrintM Pred where
  prM (CIn c ts) | c == cJoin
    = do [t1,t2,t3] <- withPrec 1 (forEach ts prM)
         return (t1 <+> text "#" <+> t2 <+> char '=' <+> t3)
  prM (CIn c [t1,t2]) 
    | c == cBitRep 
      = do t1 <- withPrec 0 (prM t1)
           t2 <- withPrec 1 (prM t2)
           return (char '|' <> t1 <> text "| =" <+> t2)
    | c == cExp2 
      = do t1 <- withPrec 0 (prM t1)
           t2 <- withPrec 1 (prM t2)
           return (text "2 ^" <+> t1 <+> text "=" <+> t2)
  prM (CIn c ts)    = do ts <- withPrec 2 (forEach ts prM)
                         c  <- prM c
                         wrap 2 (c <+> hsep ts)


instance PrintM [Pred] where
  prM [p]           = prM p
  prM ps            = (parens . commaSep) # withPrec 0 (forEach ps prM)

instance PrintM t => PrintM (Poly t) where
  prM (Forall xs ps t)  = withQuants xs $ \xs -> 
                            do ps <- prContext ps
                               t  <- withPrec 0 $ prM t
                               wrap 1 (prQuants xs <+> ps <+> t)

prQuants [] = empty
prQuants xs = text "forall" <+> hsep (map text xs) <> text "."

prContext [] = return empty
prContext ps = do ps <- withPrec 1 (prM ps)
                  return (ps <+> text "=>")

instance PrintM RuleEnv where
  prM p = do ss <- forEach (superRules p) prM 
             is <- forEach (instRules p) prM 
             return (text "-- Super class rules" $$ vcat ss $$
                     text "-- Instance rules" $$ vcat is)

instance PrintM Rule where
  prM (Rule _ p)    = prM p

withQuants         :: [TyVar] -> ([String] -> PrM a) -> PrM a
withQuants xs f     = loop [] xs 
  where
  loop qs []        = f (reverse qs)
  loop qs (x:xs)    = case tyVarName x of
                        VarName s -> 
                          do s <- pickName s
                             e <- ask
                             let e' = e { boundVars = (x,s) : boundVars e }
                             local e' $ loop (s:qs) xs
                        x -> "withQuants" `unexpected` show x

instance PrintM (Struct TyVar) where
  prM (Struct s xs (Forall ys ps fs) m) 
    = withQuants xs $ \xs -> 
      withQuants ys $ \ys -> 
         do s  <- prM s
            ps <- prContext ps
            fs <- vcat # forEach fs prM 
            m <- case m of
                   Nothing -> return empty
                   Just t -> do t <- withPrec 0 $ prM t
                                return (text "of size" <+> t)
            return (text "struct" <+> prQuants ys <+> ps 
                      <+> s <+> hsep (map text xs) 
                      <+> m <+> text "where" $$ nest 2 fs)


instance PrintM StructField where
  prM (StField { sfName = x, sfType = t })  = do x <- prM x
                                                 t <- withPrec 0 $ prM t
                                                 return (x <+> text "::" <+> t)
  prM (StPad Nothing)   = return (text "..")
  prM (StPad (Just t))  = withPrec 0 $ prM t



getQuants          :: PrM [(TyVar,String)]
getQuants           = boundVars # ask

withPrec           :: Int -> PrM a -> PrM a
withPrec p m        = ask >>= \e -> local (e { prec = p }) m

withTyAp b m        = ask >>= \e -> local (e { showTyAp = b }) m
                    
pickName           :: String -> PrM String
pickName x          = do ys <- map snd # getQuants
                         let loop (x:xs) | x `elem` ys  = loop xs
                                         | otherwise    = x
                             loop _ = "pickName(loop)" `bug` "Out of names"
                         return $ loop $
                           case x of
                             "" -> nameVariations [ c:[] | c <- ['a'..'z'] ]
                             _  -> nameVariations [ x ] 
  

nameVariations names = names ++ concatMap toNames modifiers 
  where modifiers   = map show [1..]
        toNames xs  = map (++xs) names



  

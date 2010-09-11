-- XXX: this needs to be fixed
-- perhaps moved earlier in the compiler pipeline.

module CheckDefs(checkDefs) where

import AST(ADT,ADT'(..),ADTCtr'(..),poly)
import AST.SIL
import qualified BDD
import qualified Pass
import Error
import PP

import Utils
import Data.List
import Data.Word
import MonadLib


type M        = ReaderT [ADT] (WriterT [Warning] Id)

checkDefs    :: [ADT] -> [Decl] -> Pass.Pass ()
checkDefs adts ds = Pass.warn ws >> return ()
  where ws = map show 
           $ snd
           $ runId $ runWriterT $ runReaderT adts
           $ mapM_ (`decl` true) ds

-- Data structures -------------------------------------------------------------


type Prop   = Or
newtype Or  = Or [And]
data And    = And [(Name,Name)]       -- variable matches constructor
                  [(Name,BDD.Pat)]    -- variable matches bin. pat.

false       = Or []
true        = Or [And [] []]

Or p \/ Or q  = Or (p ++ q)
Or p /\ Or q  = Or $ concatMap normAnd [ And (as ++ cs) (bs ++ ds) 
                                            | And as bs <- p, And cs ds <- q ] 

x `bis` p       = Or [And [] [(x,p)]]
x `is` c        = isOneOf x [c]
x `isOneOf` cs  = Or [ And [(x,c)] [] | c <- cs ]

Or p `andNot` (x,cs)        = Or (filter ok p)
  where ok (And as _)       = all notContr as
        notContr (y,c)      = (x /= y) || (c `notElem` cs)
  

normAnd (And as bs) 
  = case And # forEach (regroup as) reA <# forEach (regroup bs) reB of
      Nothing -> []
      Just a  -> [a]

  where
  reA (x,c:cs) | all (c ==) cs  = Just (x,c)
               | otherwise      = Nothing
  reA (_,[])  = "reA" `bug` "regroup returned []?"

  reB (x,ps)
    | BDD.willAlwaysFail p  = Nothing
    | otherwise             = Just (x,p)
      where p = foldr1 BDD.pAnd ps                         
        

isFalse (Or []) = True
isFalse _       = False

-- Analysis --------------------------------------------------------------------

expr (Atom _) _   = return false
expr (Con _ _) _  = return false
expr (Prim _ _) _ = return false
expr (App _ _) _  = return false   -- syntactic not semantic!
expr (Do s) f     = stmt s f
expr (CommE e) f  = comm expr e f

stmt (Call _ _) _   = return false
stmt (LetM b s1 s2) f = do ws <- getWarns (stmt s1 f)  -- Note: we commit 
                           report (varName b) ws
                           stmt s2 f
stmt (PrimS _ _) _  = return false    
stmt (CommS s) f    = comm stmt s f


comm :: (a -> Or -> M Or) -> Comm a -> Or -> M Or
comm how (Let d e) facts  = decl d facts >> how e facts

-- Note: we assume that the alternatives do not overlap
-- a switch can fail if:
--  * a value does not match any of the ctrs, OR
--  * a value matches one of the ctrs, and its body fails
comm how (Switch x as) facts  
  = do (cs,fs) <- unzip # forEach as (\a -> alt how x a facts)
       return (foldl (\/) (facts `andNot` (x,cs)) fs)

-- Note: we assume that the alternatives do not overlap
-- a swicth can fail if:
--  * the pattern does not match any of the cases (is in all complements), OR
--  * matches a branch, which itself fails 
comm how (BSwitch x as) facts  
  = do (ns,fs) <- unzip # forEach as (\a -> balt how x a facts)
       return (foldl (\/) (foldl (/\) facts ns) fs)

comm _ (Raise _) facts = return facts

comm how (Handle e1 e2) facts 
  = do canFail <- how e1 facts
       if isFalse canFail 
          then do warn "Unreachable" -- XXX: How to report? 
                  return false
          else how e2 (canFail /\ facts)

-- returns: (the name of the constructor, how to fail if ctr matches)
alt how x (Case c e) facts 
  = do let facts' = (x `is` c) /\ facts
       if isFalse facts' 
          then do warn "Trivial failure (1)" -- XXX: Report
                  return (c, facts')
          else do canFail <- how e facts'
                  return (c, canFail)

balt how (Lit (Int n)) (BCase p e) facts 
  | pN `BDD.willMatchIf` p  = do canFail <- how e facts
                                 return (false,canFail)
  | otherwise               = do warn "Trivial failure (2)"
                                 return (true, false)
    where 
    pN    = BDD.pInt (BDD.width p) (fromIntegral n)

-- returns: (the complement of the case, how to fail if pattern matches)
balt how (Var x) (BCase p e) facts 
  = do let itIs   = x `bis` p
           orNot  = x `bis` BDD.pNot p
           facts' = itIs /\ facts
       if isFalse facts' 
          then do warn "Trivial failure (3)" -- XXX: Report
                  return (orNot, facts')
          else do canFail <- how e facts'
                  return (orNot, canFail)

decl (AVal b e) facts  
                    = report (varName b) =<< getWarns (expr e facts)
decl (Cyc _) _      = "decl" `unexpected` "Cyc"
decl (Area {}) _    = return ()
decl (AFun f) facts = funDecl f facts 
decl (Rec fs) facts = forEach_ fs $ \f -> decl (AFun f) facts

funDecl f facts = do fs <- forEach (funArgs f) ctrs
                     ws <- getWarns $ expr (funDef f) (foldl (/\) facts fs)
                     report (funName f) ws
  where
  ctrs (Bind x t) = do cs <- getCtrsT t
                       return $ case cs of
                                  Just cs -> x `isOneOf` cs
                                  Nothing -> true
                       

       
-- Monad -----------------------------------------------------------------------

getCtrsT           :: SimpleType -> M (Maybe [Name])
getCtrsT t          = do as <- ask
                         return $ case find ((t ==) . adtName) as of
                                    Just a -> Just (map toCon (adtCtrs a))
                                    Nothing -> Nothing
  where toCon c     = UName (acName (poly c))
                

data Warning  = Msg String
              | Fail Prop
              | In Name [Warning]

warn       :: String -> M ()
warn msg     = put [Msg msg]

getWarns    :: M a -> M (a,[Warning])
getWarns m   = collect m

report x (canFail,ws) 
  | isFalse canFail   = when (not (null ws)) (put [In x ws])
  | otherwise         = put [In x (Fail canFail : ws)]


instance Show Warning where show = prShow
instance Pr Warning where
  pr (In x ws) = text "In the definition of" <+> pr x <> colon
                $$ nest 2 (vcat (map pr ws))
  pr (Msg s)   = text s
  pr (Fail p)  = text "Fails when:" $$ nest 2 (pr p)

instance Show Prop where show = prShow
instance Pr Or where
  pr (Or [])      = text "(never)"
  pr (Or [a])     = pr a
  pr (Or (a:as))  = fsep ( text (replicate (length pre) ' ') <+> pr a
                         : map ((text pre <+>) . pr) as )
    where pre = "or"

instance Pr And where
{-
  pr p@(And as bs)
    = case roots of
        []  -> text "(always)"
        as  -> fsep (punctuate (text ", and") (map prRoot as))

    where 
    prRoot r  = fsep [name r <+> text "is", nest 2 (ppAnd p r) ]
    roots     = filter isRoot (map fst as ++ map fst bs)
    isRoot (Fld _ _ _)  = False
    isRoot _            = True
-}


  pr (And as bs)  = vcat (punctuate (text ", and") ds)
    where 
    ds = [ name x <+> text "matches ctr." <+> pr c | (x,c) <- as ]
      ++ map prBin bs 

    prBin (x,p) = name x <+> descr
      where
      descr   
        | length pos <= length neg = fsep [ text "is of the form" 
                                                    , nest 2 (vcat pos) ]
        | otherwise = fsep [ text "is not of the form", nest 2 (vcat neg) ]
        where
        pos = showBin p
        neg = showBin (BDD.pNot p)
        showBin b = [ char 'B' <> text x | x <- BDD.showPat b ]
 
    


name (Arg f x)  = text "the" <+> text (say (x+1)) 
                <+> text "argument of" <+> name f
name (Fld x c n)  = text "the" <+> text (say (n+1))
                <+> text "field of" <+> name x
                <+> parens (text "if" <+> name x
                    <+> text "is of the form" <+> pr c)
name x          = quotes (pr x)

-- XXX: 11,12  
say   :: Word32 -> String
say x  = let xs = show x in xs ++ suff (last xs)
  where
  suff '1'  = "st"
  suff '2'  = "nd"
  suff '3'  = "rd"
  suff _    = "th"













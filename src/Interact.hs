module Main where -- (module Main,loadFiles,logo) where
-- import AST
import CmdArgs
import Compiler
import qualified Interp
-- import qualified C.Print
import ATT(att)
import Text.PrettyPrint.HughesPJ
-- import PPIO
-- import qualified BDD
-- import UI.Logo(logo)
-- import UI.ANSI hiding (cmd)

-- import Utils
-- import Control.Exception(catch)
-- import Prelude hiding (catch)

-- import Data.List(find)
-- import Data.Maybe

-- import Text.Show.Functions()


main = do (opts,ms) <- cmdOptions
          c <- loadFiles opts ms
          case [ x | OutFile x <- opts ] of
            []  -> runProg c
            [o] -> saveCode o c
            os  -> error ("Multiple outputs: " ++ show os)


runProg f           = print =<< Interp.run (ccFuns f) (ccProcs f) (ccDecls f)

saveCode n f        = do writeFile sFile (show (att (code f)) ++ "\n")
                         writeFile cFile (show (text "#include \"rts.h\"" $$
                                                codeC f $$ text "\n"))
  where sFile       = n ++ ".s"
        cFile       = n ++ ".c"

{-
cmd c _             = return (c ++ " file")
pCmd c x            = return (c ++ " " ++ show x ++ " file")


showRules f         = print =<< printM (dcRules $ frontEnd f)

showKind "" f       = showAs (kADTs f) >> showBs (tcBDT $ frontEnd  f) 
  where

  showAs []         = return ()
  showAs as         = putStrLn "Algebraic data types" >> forEach_ as showType
                      >> putStrLn ""
  showBs []         = return ()
  showBs bs         = putStrLn "Bitdata types" >> forEach_ bs showType

showKind x f        = (showType =<< getADT x f) `catch` \_ -> 
                      (showType =<< getBDT x f)       

showFuns f          = case ccADTs f of
                        [] -> print "(no function types)"
                        fs -> print $ vcat $ punctuate (char ' ') $ map pr fs

showClosure f       = do putStrLn "-- Functions"
                         print $ vpr $ map pr (ccFuns f)
                         putStrLn "\n\n-- Values"
                         print $ vpr $ map pr (ccDecls f)

showSIL f           = mapM print (sDecls f)

kADTs f             = kcADT $ frontEnd f

showSpecADTs f      = forEach (sADTs f) print
showSpecBinds f     = forEach (sBinds f) print

showCover          :: BDD.Pat -> IO ()
showCover s         = putStrLn (unlines (BDD.showPat s))

try                :: Maybe a -> IO a
try Nothing         = error $ bold $ red $ "Failed."
try (Just x)        = return x

getADT x f          = try $ find ((ConName x ==) . adtName) (kADTs f)
getBDT x f          = try $ find ((ConName x ==) . bdtName) (tcBDT $ frontEnd f)

findACon x f        = try $ findADTCtr (ConName x) $ kADTs f
findBCon x f        = try $ findBDTCtr (ConName x) $ tcBDT $ frontEnd f

showData x f        = (print =<< getADT x f) `catch` \_ -> 
                      (print =<< getBDT x f) 
  
getBind x f         = try $ find ((name ==) . bindName) (tcBinds $ frontEnd f)
  where name        = let (as,bs) = span (/='.') x
                      in case bs of 
                           [] -> VarName x
                           _:bs -> Qual as (VarName bs)

class ShowType t where
  showType         :: t -> IO ()

instance ShowType Bind where
  -- showType b        = (print . BSig (bindName b)) =<< deepPruneIO (bindSchema b)
  showType b        = prSig (bindName b) (bindSchema b)-- print (BSig (bindName b) (bindSchema b))

instance ShowType (ADT' a) where
  showType a        = print (pr (adtName a) <+> text "::" <+> pr (adtKind a))

instance ShowType BDT where
  showType b        = print (pr (bdtName b) <+> text "::" <+> pr (bdtKind b))

instance ShowType (ADT' a,Poly (ADTCtr' a)) where
  showType (a,b)    = print (acSchema a b)

instance ShowType (BDT,BDTCtr) where
  showType (a,b)    = print (bcSchema a b)

instance ShowType (String,CompFile) where
  showType ("",f)   = case tcBinds $ frontEnd f of
                        []  -> print "(no definitions)"
                        bs  -> forEach_ bs showType

  showType (x,f)    = (showType =<< getBind x f) `catch` \_ ->
                      (showType =<< findACon x f) `catch` \_ -> 
                      (showType =<< findBCon x f) 
-}


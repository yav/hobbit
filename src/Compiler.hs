module Compiler where

import Pass
import AST
import qualified AST.SIL as SIL

import CmdArgs
import Chase
import ModuleSystem
import Type.Instances
import Type.Kind as K
import Type.Bitdata
import Type.Struct
import Type.Infer as T
import qualified Type.Env
import Spec
import Spec2SIL
import CheckDefs
import ClosureConv
import CodeGen.Main(compile)
import PPIO
-- import Utils

import qualified HAsm

import qualified Data.Map as Map (empty)
-- import System.Exit


data FrontEnd       = FrontEnd  
                    { primTypes   :: Type.Env.Env
                    , primVals    :: Type.Env.Env
                    , modules     :: [Module]

                    -- Module System
                    , origBinds   :: BindBlock
                    , origData    :: [DataDecl]
                    , origRules   :: RuleEnv

                    -- Kind checking
                    , kindCheck   :: KMod

                    -- Extra checks for data
                    , dcBDT       :: [BDT]
                    , dcRules     :: RuleEnv

                    -- Type checking
                    , tcBinds     :: BindBlock
                    , tcBDT       :: [BDT]
                    }



data CompFile       = CompFile
                    { frontEnd    :: FrontEnd

                    -- Specialization
                    , sADTs       :: [ADT]
                    , sBinds      :: BindBlock

                    -- Sequentialization
                    , sDecls      :: [SIL.Decl]

                    -- Closure conversion
                    , ccADTs      :: [SIL.FunADT]
                    , ccFuns      :: [SIL.FunDecl SIL.Expr]
                    , ccProcs     :: [SIL.FunDecl SIL.Stmt]
                    , ccDecls     :: [SIL.Decl]

                    -- Code generation
                    , code        :: [HAsm.Instr] -- asm parts of the code
                    , codeC       :: Doc          -- C parts of the code
                    }

loadFiles :: [Option] -> [FilePath] -> IO CompFile
loadFiles opts fs        
  = do let paths = [ x | InPath x <- opts ]
       mods <- runPass "Parsing" (chaseModules paths fs)
       rEnv <- runPass "Parsing rules" parseRuleEnv
       modSys <- runPass "Module system" (ModuleSystem.resolve mods rEnv)

       (kMod, primTs, primVs, ps) <- runPass "Checking kinds" 
                                           $ K.checkModule modSys 

       let kRules = K.rules kMod

       (cBDTs, bRules, ctrBinds) <- runPass "Checking bitdata" 
            $ Type.Bitdata.checkBitdata primTs kRules (K.bdts kMod) 

       -- mapM print cBDTs
       -- mapM print ctrBinds
  
       let rules1 = kRules { instRules = bRules ++ instRules kRules }

       sRules <- runPass "Checking structs" 
               $ Type.Struct.structRules primTs (K.structs kMod) rules1

       let theRules = rules1 { instRules = sRules }

       case [ x | Dump Structs x <- opts ] of
         Nothing : _ -> print =<< printM theRules
         Just f : _  -> (writeFile f . show) =<< printM theRules
         _ -> return ()
          

       let db = DB { typingEnv  = primVs -- XXX: (these data constructors)
                   , kindingEnv = primTs
                   , recVars    = Map.empty
                   , evMap      = Map.empty
                   , T.rules    = theRules
                   , T.bdts     = cBDTs 
                   , curDefs    = [] }
        -- XXX: I think it is too late to solve the 'ps' here.

       let kBinds = K.binds kMod
           kBinds' = kBinds { expBinds = ctrBinds ++ expBinds kBinds }
       (tBDTs, tBinds) <- runPass "Checking types" 
                        $ T.inferModule db ps kBinds'

{-
       case [ x | JustTypes x <- opts ] of
         [] -> return ()
         xs -> do showSchemas [ toName x | Just x <- xs ] tBinds
                  exitWith ExitSuccess
-}

       let uses = [ Use entryName [] [] ]
       (sADTs, sBinds) <- runPass "Specializing" 
           $ io $ specialize (K.adts kMod,tBinds,uses)

      -- dump specialized data, if requested -----------------------
       let doc = do d1 <- vpr `fmap` mapM printM sADTs
                    -- let d2 = vpr (map pr sBinds)
                    return (text "-- Data --" $$ d1 $$ text " " 
                         $$ text "-- Values --" $$ pr sBinds)
       case [ x | Dump Spec x <- opts ] of
         Nothing : _ -> print =<< doc
         Just f : _  -> (writeFile f . show) =<< doc
         _ -> return ()
      -- end dump -------------------------------------------


       sDecls <- runPass "Sequentializing" 
                    $ return (seqProg sADTs tBDTs sBinds)
       let doc = vpr (map pr sDecls)
       case [ x | Dump SIL x <- opts ] of
         Nothing : _ -> print doc
         Just f : _  -> writeFile f (show doc)
         _           -> return ()


       () <- runPass "Checking definitions" (checkDefs sADTs sDecls)

       cc@(ccADTs,ccFuns,ccProcs, ccDecls) <- runPass "Firstification" 
                                            $ return (closureConv sDecls)
       case [ x | Dump CC x <- opts ] of
         Nothing : _ -> print (showCC cc)
         Just f  : _ -> writeFile f (show (showCC cc))
         _ -> return ()
                                       
       (code,codeC) <- runPass "Generating code"
         $ compile opts [] sADTs ccADTs ccFuns ccProcs ccDecls

       return $ CompFile
              { frontEnd  = FrontEnd
                          { primTypes   = primTs
                          , primVals    = primVs
                          , modules     = mods
      
                          -- Module System
                          , origData    = let (x,_,_) = modSys in x
                          , origBinds   = let (_,x,_) = modSys in x
                          , origRules   = let (_,_,x) = modSys in x
      
                          -- Kind checking
                          , kindCheck   = kMod
      
                          -- Extra checks for data
                          , dcBDT       = cBDTs
                          , dcRules     = theRules
      
                          -- Type checking
                          , tcBinds     = tBinds
                          , tcBDT       = tBDTs
                          }
              , sADTs   = sADTs
              , sBinds  = sBinds 
              , sDecls  = sDecls
   
              , ccADTs  = ccADTs
              , ccFuns  = ccFuns
              , ccProcs = ccProcs
              , ccDecls = ccDecls 
    
              , code    = code
              , codeC   = codeC
              }
        
{- 
toName x  = case break ('.' ==) x of
              (a,_:b) -> Qual a (VarName b)
              _ -> VarName x

showSchemas xs (b:bs)
  = case remove (bindName b ==) xs of
      Nothing     -> showSchemas xs bs
      Just (x,xs) -> prSig x (bindSchema b) >> showSchemas xs bs
showSchemas _ _ = return ()

prSig x t = do t <- printM t
               print (pr x <+> text "::" <+> t)
-}
     

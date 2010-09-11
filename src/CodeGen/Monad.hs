module CodeGen.Monad where

import qualified AST as A
import AST.SIL
import CodeGen.Mach
import HAsm hiding (M)
import Error
import Pass

import Utils
import MonadLib hiding (Label,runM)
import Data.List(findIndex,find)
import qualified Data.Map as Map

type Label          = String

type L              = StateT Int Pass
type M              = ReaderT Env (WriterT [Shape] L)

data Handler        = Handler { hPop  :: Integer
                              , hGoto :: Label }

defaultHandler      = Handler { hPop  = 0
                              , hGoto = "CRASH" }

data Env            = Env { handler :: Handler
                          , funs    :: Map.Map Name (Label,Bool) -- is glob?
                          , globals :: Map.Map Name GlobVar
                          , locals  :: [LocVar]
                          , adtCtrs :: Map.Map A.Name ConInfo
                          , funCtrs :: Map.Map ConName ConInfo }

defaultEnv          = Env { handler = defaultHandler
                          , funs    = Map.empty
                          , globals = Map.empty
                          , locals  = []
                          , adtCtrs = Map.empty
                          , funCtrs = Map.empty }


data GlobVar        = GlobVar { globLoc :: Label
                              , globPtr :: Bool } deriving Show

data LocVar         = LocVar { locName  :: Name
                             , locPtr   :: Bool } deriving Show

-- cSize the size of the value in words, cPtrs: offsets of ptrs (in words)
data ConInfo        = ConI { cTag   :: Integer
                           , cShape :: Shape
                           } deriving Show

data Shape = Shape
  { obj_size :: Integer    -- ^ in words
  , obj_ptrs :: [Integer]  -- ^ word offsets of references to the heap
  } deriving (Eq,Show)

runM               :: Env -> M a -> L (a, [Shape])
runM e m            = runWriterT $ runReaderT e m

runL               :: L a -> Pass a
runL m              = fmap fst $ runStateT 0 m

newLabelL          :: L Label
newLabelL           = do n <- get
                         set (n+1)
                         return ("L" ++ show n)

newLabel           :: M Label
newLabel            = lift $ lift newLabelL

getVarLoc x         = getVarLoc' 0 x

getVarLoc' off x    = do xs <- locals # ask

                         case findIndex ((x == ) . locName) xs of
                           Just s -> let moff = (fromIntegral s + off) * word_size
                                     in return (mem (moff :: Integer,reg_stack))
                           Nothing -> tryGlobal
  where
  tryGlobal         = do xs <- globals # ask
                         case Map.lookup x xs of
                           Just l -> return (mem (globLoc l))
                           Nothing -> bug "getVarLoc"
                                          ("Missing variable: " ++ show x)

varIsPtr x          = do xs <- locals # ask
                         case find ((x ==) . locName) xs of
                           Just s -> return (locPtr s)
                           Nothing -> do xs <- globals # ask
                                         case Map.lookup x xs of
                                           Just s -> return (globPtr s)
                                           Nothing -> bug "varIsPtr"
                                              ("Missing variable: " ++ show x)

getFunInfo         :: Name -> M (Label,Bool)
getFunInfo f        = do fs <- funs # ask
                         case Map.lookup f fs of
                           Just i   -> return i
                           Nothing  -> bug "getFunInfo"
                                            ("Missing function: " ++ show f)

getFunLabel        :: Name -> M Label
getFunLabel f       = fst # getFunInfo f


getGlob            :: Name -> M Label
getGlob x           = do xs <- globals # ask
                         case Map.lookup x xs of
                           Just (GlobVar l _) -> return l
                           Nothing -> bug "getGlob"
                                            ("Missing global: " ++ show x)

getGlobPtrs        :: M [Label]
getGlobPtrs         = (thePtrs . globals) # ask
  where thePtrs gs  = [ l | (_, GlobVar l True) <- Map.toList gs ]

withLocals         :: [Binder] -> M a -> M a
withLocals xs m =
  do e <- ask
     let h  = handler e
         vs = [ LocVar x (isPtr t) | Bind x t <- xs ]
         h' = h { hPop = fromIntegral (length xs) + hPop h }
         e' = e { handler = h', locals = vs ++ locals e }
     local e' m

withHandler        :: Label -> M a -> M a
withHandler l m     = do e <- ask
                         local (e { handler = Handler 0 l }) m

getHandler         :: M Handler
getHandler          = handler # ask

-- XXX: Use something more robust
isPtr              :: SimpleType -> Bool
isPtr (A.Inst (A.Qual "Prims" (A.ConName "Bit")) _)     = False
isPtr (A.Inst (A.Qual "Prims" (A.ConName "Ix")) _)      = False
isPtr (A.Inst (A.Qual "Prims" (A.ConName "ARef")) _)    = False
isPtr (A.Inst (A.Qual "Prelude" (A.ConName "APtr")) _)  = False
isPtr _             = True

-- The size of the frame does not include the location of the return addr.
-- see module CodeGen.GC
frameDescr :: M Shape
frameDescr = do xs <- locals # ask
                return Shape
                  { obj_size = fromIntegral (length xs)
                  , obj_ptrs =[ n | (n, LocVar _ True) <- zip [0..] xs]
                  }

getConInfo         :: Name -> M ConInfo
getConInfo (ConName x)  = do xs <- funCtrs # ask
                             case Map.lookup x xs of
                               Just i -> return i
                               Nothing -> bug "getConInfo"
                                            ("Missing fun ctr: " ++ show x)
getConInfo (UName x)    = do xs <- adtCtrs # ask
                             case Map.lookup x xs of
                               Just i -> return i
                               Nothing -> bug "getConInfo"
                                            ("Missing adt ctr: " ++ show x)
getConInfo x            = "getConInfo" `unexpected` show x

addScav            :: Shape -> M ()
addScav s           = put [s]





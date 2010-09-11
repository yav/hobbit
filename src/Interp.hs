module Interp(run) where

import qualified AST as A 
import AST.SIL
import AST.Evidence
import qualified AreaLayout as L
import qualified Depend.SCC as Dep
import Depend.FVs_SIL()
import BDD (willMatch)
import Error
import Utils

import Data.List(sortBy)
import Data.Bits
import Data.Array.IO
import Data.Word

import MonadLib

import Debug.Trace
import Numeric


data V    = IntV Word32
          | ConV Name [V] 
            deriving Show

type Fun  = [V] -> V   
type Proc = [V] -> IO V

type Mem  = IOUArray Word32 Word32 
data Env  = Env { vEnv :: [(Name,V)]
                , fEnv :: [(Name, Fun)] 
                , pEnv :: [(Name, Proc)]
                , mem  :: Mem }

lkpVal    :: Name -> Env -> V
lkpVal x e = case lookup x (vEnv e) of
               Just v -> v
               _      -> bug "lkpVal" ("Undefined variable: " ++ show x)

lkpFun    :: Name -> Env -> Fun
lkpFun x e = case lookup x (fEnv e) of
               Just v -> v
               _      -> bug "lkpFun" ("Undefined function: " ++ show x)

lkpProc   :: Name -> Env -> Proc
lkpProc x e = case lookup x (pEnv e) of
                Just v -> v
                _      -> bug "lkpProc" ("Undefined procedure: " ++ show x)




run       :: [FunDecl Expr] -> [FunDecl Stmt] -> [Decl] -> IO V
run fs ps ds  = do (env,arr) <- areas ds
                   let tds = map FunD fs ++ map ProcD ps ++ map ValD ds
                   loop (Dep.sccs tds) (Env env [] [] arr)
  where
  loop [] env   = lkpProc finalEntry env []

  loop (Dep.NonRec (FunD f) : ds) env  = loop ds 
                                          env { fEnv = fun f env : fEnv env }
  loop (Dep.NonRec (ProcD p) : ds) env  = loop ds
                                          env { pEnv = proc p env : pEnv env }
  loop (Dep.NonRec (ValD d) : ds) env  = loop ds (decl d env)
  loop (Dep.Rec fs : ds) env    = loop ds env'
    where 
    env'    = env { fEnv = map (`fun` env') funs ++ fEnv env 
                  , pEnv = map (`proc` env') procs ++ pEnv env }
    funs    = [ f | FunD f <- fs ]
    procs   = [ f | ProcD f <- fs ]
 
 
areas :: [Decl] -> IO ([(Name,V)], IOUArray Word32 Word32)
areas ds 
  = case L.order (4,max) as of
      Nothing -> error "Not enough space for areas"
      Just xs -> do putStrLn ("Memory size: " ++ show size)
                    arr <- newArray (0, fromIntegral size) 0
                    let ptrs = map cvt xs
                    return (ptrs, arr)
        where
        size = case xs of
                 [] -> 0
                 _  -> let a = last (sortBy (compare `on` L.addr) xs)
                           Just x = L.addr a
                       in ((x + L.size a + 3) `div` 4)
            
  where max = 40 * mB 
        kB  = 2^10
        mB  = 2^10 * kB

        -- Note: we ignore regions and area values...
        as =  [ L.Area x (cvtAli a) (fromIntegral s) v 
                | Area (Bind x _) _ v (OpEv AreaEv [IntEv s, IntEv a]) <- ds ]

        cvt a = (L.name a, IntV (fromIntegral x))
          where Just x = L.addr a

        cvtAli a = case lg2 (fromIntegral a) of
                     Just x -> 32 - x
                     Nothing -> bug "cvtAli" "Invalid area"


now []        = []
now ys@(x:xs) = seq x (seq (now xs)) ys

atom                       :: Atom -> Env -> V
atom (Var x) e              = lkpVal x e
atom (Lit (Int x)) _        = IntV (fromInteger x)

atoms as env                = now (map (`atom` env) as)

expr                       :: Expr -> Env -> Maybe V
expr (Atom a) env           = Just $! atom a env
expr (Con (UName c) []) _ | A.isNull c    = Just $! IntV 0
expr (Con (UName c) [a]) env | A.isPtr c  = Just $! atom a env
  

expr (Con c as) env         = Just $! ConV c $! atoms as env 
expr (Prim p as) env        = Just $! prim p $! atoms as env
expr (App f as) env         = Just $! lkpFun f env $! atoms as env 
expr (CommE e) env          = runId (comm monad expr' e env)
expr (Do _) _               = "expr" `unexpected` "Do"

expr'                      :: Expr -> Env -> Id (Maybe V)
expr' e env                 = return (expr e env)



data Monad' m = MonadD { ret  :: forall a. a -> m a 
                       , bind :: forall a b. m a -> (a -> m b) -> m b }


monad :: Monad m => Monad' m
monad = MonadD return (>>=) 

            
comm :: Monad' m -> (a -> Env -> m (Maybe b)) -> Comm a -> Env -> m (Maybe b)
comm _ how (Let d e) env        = how e (decl d env)
comm m how (Switch x as) env  
  = case lkpVal x env of
      ConV c _ -> case [ e | Case c' e <- as, c' == c ] of
                    e : _ -> how e env
                    _ -> ret m Nothing
      IntV 0 -> case [ e | Case (UName c) e <- as, A.isNull c ] of
                  e : _ -> how e env
                  _ -> ret m Nothing
      IntV _ -> case [ e | Case (UName c) e <- as, A.isPtr c ] of
                  e : _ -> how e env
                  _ -> ret m Nothing

comm m _ (Raise _) _            = ret m Nothing
comm m how (Handle e1 e2) env   
  = bind m (how e1 env) $ \x ->
    case x of 
      Nothing -> how e2 env 
      Just v -> seq v $ ret m (Just v)
comm m how (BSwitch a as) env 
  = let IntV n = atom a env in 
    case [ e | BCase p e <- as, p `willMatch` n] of
      e : _ -> how e env
      _ -> ret m Nothing

stmt :: Stmt -> Env -> IO (Maybe V)
stmt (Call f as) env      
  = do v <- lkpProc f env $! atoms as env
       return (Just v)

stmt (LetM b s1 s2) env   
  = do v1 <- stmt s1 env
       case v1 of
         Just v1 -> seq v1 $ stmt s2 $ env { vEnv = (varName b,v1) : vEnv env }
         Nothing -> error "Pattern match failure (in do)."

stmt (PrimS p as) env
  = do v <- primS p (mem env) $! atoms as env
       return (Just v)

stmt (CommS s) env = comm monad stmt s env


decl :: Decl -> Env -> Env
decl (AVal b e) env 
  = case expr e env of
      Just v  -> seq v (env { vEnv = (varName b,v) : vEnv env })
      Nothing -> error "Pattern match failure (in let)."

decl (Cyc bs) env = env'
  where 
  env' = env { vEnv = map (`con` env') bs ++ vEnv env }
  con (x, c, as) env = (varName x, ConV c (atoms as env)) -- lazy

decl (Area {}) env = env

decl (Rec {}) _   = error "Recursive declarations"
decl (AFun {}) _  = error "A function"




fun :: FunDecl Expr -> Env -> (Name, Fun)
fun f env = (funName f, code)
  where
  code vs = case expr (funDef f) env1 of
              Just v  -> v
              Nothing -> error "Pattern match failure"
    where
    arg x v   = (varName x,v)
    env1      = env { vEnv = zipWith arg (funArgs f) vs ++ vEnv env }

proc :: FunDecl Stmt -> Env -> (Name,Proc)
proc f env = (funName f, code)
  where
  code vs = do let arg x v = (varName x,v)
                   env1 = env { vEnv = zipWith arg (funArgs f) vs ++ vEnv env }
               x <- stmt (funDef f) env1
               case x of
                 Just v  -> return v
                 Nothing -> error "Pattern match failure"

                                  


--Primitives -------------------------------------------------------------------
norm n x    = (2^n-1) .&. x

bool True   = IntV 1
bool False  = IntV 0

bytes x     = x * 8

(<<<), (>>>) :: Word32 -> Word32 -> Word32
x <<< y       = x `shiftL` fromIntegral y
x >>> y       = x `shiftR` fromIntegral y

readMem :: IOUArray Word32 Word32 -> Word32 -> IO Word32
readMem arr x
  | b == 0    = readArray arr a
  | otherwise = do w1 <- readArray arr a     
                   w2 <- readArray arr (a+1)  
                   return ((w1 >>> bytes b) .|. 
                           (w2 <<< bytes (4-b)))
  where 
  (a,b) = x `divMod` 4
  

writeMem :: IOUArray Word32 Word32 -> Word32 -> Word32 -> IO ()
writeMem arr adr x 
  | n == 0    = writeArray arr adr' x
  | otherwise = do w1 <- readArray arr adr'
                   w2 <- readArray arr (adr'+1)
                   let a = bytes (4 - n)
                       b = bytes n
                   writeArray arr adr' ((x <<< b) .|. ((w1 <<< a) >>> a))
                   writeArray arr (adr'+1) ((x >>> a) .|. ((w2 >>> b) <<< b))
  where
  (adr',n) = adr `divMod` 4

writeMemB :: IOUArray Word32 Word32 -> Word32 -> Word32 -> IO ()
writeMemB arr adr x = do v <- readMem arr adr
                         let mask1 = 0xFF
                             mask2 = complement mask1
                         writeMem arr adr ((v .&. mask2) .|. (x .&. mask1))

readMemB arr adr    = do v <- readMem arr adr
                         return (v .&. 0xFF)

byte n x      = (x `shiftR` (fromIntegral n*8)) .&. 0xFF
x `nextTo` y  = (x `shiftL` 8) .|. y 

swapBytes :: Ev -> Word32 -> Word32
swapBytes (OpEv LeEv _) x = x
swapBytes (OpEv BeEv [IntEv n]) x
  = case n of
      0 -> x
      1 -> x
      2 -> byte 0 x `nextTo` byte 1 x
      3 -> byte 0 x `nextTo` byte 1 x `nextTo` byte 2 x
      4 -> byte 0 x `nextTo` byte 1 x `nextTo` byte 2 x `nextTo` byte 3 x
      _ -> "swapBytes" `unexpected` show n
swapBytes e _ = "swapBytes" `unexpected` show e

primS :: PrimName -> Mem -> [V] -> IO V
primS (UserPrim p es) mem as = strip p es as
  where
  strip (A.Inst f _) es as   = strip f es as      -- ignore type apps
  strip (A.Qual _ x) es as   = strip x es as      -- ignore qualifiers (XXX?)
  strip (A.VarName x) es as  = pick x es as
  strip x _ _ = "primS.strip" `unexpected` show x
 

  pick "return" [] [v] = return v

  pick "readRef" [_,e] [IntV x]
    = do x <- readMem mem x
         return (IntV (swapBytes e x))

  pick "writeRef" [_,e] [IntV x, IntV y]
    = do writeMem mem x (swapBytes e y) 
         return (IntV 0)

  pick "memZero" [_, IntEv n] [IntV r] 
    = do forEach_ [0..n-1] $ \o -> writeMemB mem (r+o) 0
         return (IntV 0)

  -- We assume that the regions are either separate or the same.
  -- This is OK because the source and target operations are of the same
  -- type and we do not have recursive area descriptions
  -- (i.e., a sucomponent cannot be the same as the whole thing).
  pick "memCopy" [_, IntEv n] [IntV from, IntV to] 
    = do forEach_ [0..n-1] $ \o -> do v <- readMemB mem (from + o)
                                      writeMemB mem (to + o) v
         return (IntV 0)

  pick "putChar" [] [IntV x] = do putChar (toEnum (fromIntegral x))
                                  return (IntV 0)                           
  
  pick p _ _ = "primS.pick" `unexpected` show p

primS p _ _ = "primS" `unexpected` show p




prim :: PrimName -> [V] -> V
prim p as = pick p as
  where 
  -- Note: we ignore instantiations
  pick (UserPrim (A.Inst x _) es) vs = pick (UserPrim x es) vs

  pick (UserPrim (A.Qual _ (A.VarName x)) es) vs = op x es vs
    where
    op "trace" [IntEv n] [IntV x, IntV y] = IntV $! trace ("trace: " ++ txt) y
      where base  = norm 4 x
            val   = norm n y
            txt | base == 10  = show val
                | base == 8   = showOct val []
                | otherwise   = showHex val []

    -- instances of Literal for Bit
    op "fromNat" [OpEv (LitEv ForBit) [_]] [x]      = x 

    -- instances of Literal for Ix
    op "fromNat" [OpEv (LitEv ForIx) [IntEv n]] [IntV x]  = IntV (x `mod` n)

    -- instance of Eq for Bit 
    op "==" [OpEv (EqEv ForBit) [IntEv n]] [IntV x,IntV y] 
      = bool (norm n x == norm n y) 
    op "/=" [OpEv (EqEv ForBit) [IntEv n]] [IntV x,IntV y] 
      = bool (norm n x /= norm n y)

    -- instance of Eq for Ix
    op "==" [OpEv (EqEv ForIx) []] [IntV x,IntV y]  = bool (x == y)
    op "/=" [OpEv (EqEv ForIx) []] [IntV x,IntV y]  = bool (x /= y)

    -- instance of Eq for ARef and APtr
    op "==" [OpEv (EqEv ForPtr) []] [IntV x,IntV y]  
      = bool (x == y)
    op "/=" [OpEv (EqEv ForPtr) []] [IntV x,IntV y] 
      = bool (x /= y)

    -- instance of Ord for Bit
    op "<"  [OpEv (OrdEv ForBit) [IntEv n]] [IntV x,IntV y] 
      = bool (norm n x < norm n y)
    op "<=" [OpEv (OrdEv ForBit) [IntEv n]] [IntV x,IntV y] 
      = bool (norm n x <= norm n y)
    op ">"  [OpEv (OrdEv ForBit) [IntEv n]] [IntV x,IntV y] 
      = bool (norm n x > norm n y)
    op ">=" [OpEv (OrdEv ForBit) [IntEv n]] [IntV x,IntV y] 
      = bool (norm n x >= norm n y)

    -- instance of Ord for Ix
    op "<"  [OpEv (OrdEv ForIx) []] [IntV x,IntV y] = bool (x < y)
    op "<=" [OpEv (OrdEv ForIx) []] [IntV x,IntV y] = bool (x <= y)
    op ">"  [OpEv (OrdEv ForIx) []] [IntV x,IntV y] = bool (x > y)
    op ">=" [OpEv (OrdEv ForIx) []] [IntV x,IntV y] = bool (x >= y)

    -- instance of Num for Bit
    op "+" [OpEv (NumEv ForBit) [_]] [IntV x,IntV y]  = IntV (x + y)
    op "-" [OpEv (NumEv ForBit) [_]] [IntV x,IntV y]  = IntV (x - y) 
    op "neg" [OpEv (NumEv ForBit) [_]] [IntV x]       = IntV (-x)
    op "*" [OpEv (NumEv ForBit) [_]] [IntV x,IntV y]  = IntV (x * y)
    op "/" [OpEv (NumEv ForBit) [IntEv n]] [IntV x,IntV y]  
                                                      = IntV (x `div` norm n y)
    -- instance of BitOps for Bit 
    op "<<" [OpEv (BitOpsEv ForBit) [_]] [IntV x,IntV y] = IntV (x <<< norm 5 y)
    op ">>" [OpEv (BitOpsEv ForBit) [_]] [IntV x,IntV y] = IntV (x >>> norm 5 y)
  
    op "&" [OpEv (BitOpsEv ForBit) [_]] [IntV x,IntV y]  = IntV (x .&. y) 
    op "!" [OpEv (BitOpsEv ForBit) [_]] [IntV x,IntV y]  = IntV (x .|. y)
    op "^" [OpEv (BitOpsEv ForBit) [_]] [IntV x,IntV y]  = IntV (x `xor` y)
    op "~" [OpEv (BitOpsEv ForBit) [_]] [IntV x]         = IntV (complement x)

    -- instance of bounded for Bit
    op "maxVal" [OpEv (BoundedEv ForBit) [IntEv m]] []  = IntV (2^m-1)
    op "minVal" [OpEv (BoundedEv ForBit) [IntEv _]] []  = IntV 0

    -- instance of bounded for Ix 
    op "maxVal" [OpEv (BoundedEv ForIx) [IntEv m]] []  = IntV (m-1)
    op "minVal" [OpEv (BoundedEv ForIx) [IntEv _]] []  = IntV 0

    op "fromBits" _ [x] = x
    op "toBits" _ [x]   = x

    op "sizeOf" [IntEv x] _ = IntV x

    -- XXX: 
    -- op "#" [OpEv JoinEv [IntEv _,IntEv n]] [IntV x, IntV y]
    op "#" [IntEv _,IntEv n,_,_] [IntV x, IntV y]
      = IntV ((x <<< n) .|. norm n y)

    op "@" [_,_,IntEv s,_] [IntV p, IntV x]
      = IntV (p + x * s)

    op "bitIx" [IntEv w,_,_] [IntV x] = IntV (norm w x)

    op "fromBytes" _ [x]  = x
    op "toBytes" _ [x]    = x

    op x es as = bug "prim.op"
      $ unlines ["Missing primitive", x, show es, show (length as)]

  pick PGEQ [IntV x, IntV y]    = let x' = fromIntegral x :: Int
                                      y' = fromIntegral y
                                  in bool (y' <= x')  -- signed
  pick PLEQ [IntV x, IntV y]    = bool (x <= y) -- unsigned
  pick PIncBy [IntV x, IntV y]  = IntV (x+y)
  pick PDecBy [IntV x, IntV y]  = IntV (y-x)

  pick (UserPrim (A.Select _) [OpEv BitFieldEv [IntEv z, IntEv x, IntEv y]]) vs
    = pick (PGetFieldB z (A.BitField x y)) vs   

  pick (UserPrim (A.Select _) [OpEv FieldEv [IntEv o,_,_]]) [IntV x] 
    = IntV (x + o)

  pick (UserPrim (A.Update _) [OpEv BitFieldEv [IntEv z, IntEv x, IntEv y]]) vs
    = pick (PUpdFields z [A.BitField x y]) vs

  pick (PGetFieldA (UName c) 0) [x] 
    | A.isPtr c = x
  pick (PGetFieldA _ n) [ConV _ vs] = vs !! fromIntegral n
  pick (PGetFieldB _ b) [IntV x]    = IntV (x >>> A.bfOffset b)

  pick (PUpdFields _ bs) (IntV a:as) 
    = IntV (foldr (.|.) base (zipWith moveTo bs as))
    where
    base              = a .&. foldr (.&.) (-1) (map bfMask bs)
    bfMask b          = complement ((2^(A.bfWidth b) - 1) <<< A.bfOffset b)
    moveTo b (IntV a) = norm (A.bfWidth b) a <<< A.bfOffset b
    moveTo _ v        = "prim.moveTo" `unexpected` show v

  pick op _ = "pick" `unexpected` show op






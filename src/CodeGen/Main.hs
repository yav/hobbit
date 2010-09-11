module CodeGen.Main (compile) where

import AST.SIL hiding (Stmt(..)) 
import qualified AST.SIL as S (Stmt(..))
import AST.Evidence hiding (E)
import qualified AST as A hiding (IntEv) 
import qualified BDD
import HAsm hiding (M)
import qualified HAsm
import CodeGen.Mach
import CodeGen.Labels
import CodeGen.Monad
import CodeGen.GC_Dyn
import CodeGen.FFI
import CmdArgs
import qualified Depend.DFS as D
import Error
import Pass
import Utils

import Data.Array(array)
import Data.Bits
import qualified Data.Map as Map
import Data.List(nub)
import Text.PrettyPrint.HughesPJ

import MonadLib hiding (Label,runM)

import Debug.Trace


{-------------------------------------------------------------------------------

A call frame:

big                                     small
 ----+-----+--------------+----------+-----
  ...| ret |  args L to R | locals   | ...
 ----+-----+--------------+--------|-+-----
                                  esp

The caller pushes 'ret', and the args.
The callee pushes any locals that it needs.
The callee deallocates the entire frame.

Side Note: There is no way to represent 'backwards' arrays in hobbit...

-------------------------------------------------------------------------------}

fun_call :: Name -> [Atom] -> M [Instr]
fun_call f as
  = do funL   <- getFunLabel f
       is     <- forEach2 [1..] as (atomIn' reg_A)
       f      <- frameDescr
       addScav f
       return
         ( Push addr (lab "1f")
         : do { i <- is; i ++ [ Push the_size (Reg reg_A)] } ++
         [ Jmp (lab funL)
         , Init addr [Lab (l_scav f)]
         , Label "1"
         ])




-- Difficulty: Overwriting something that we need (arg or local)
-- Solution:
--   * put variables in dependency ordedr
--   * use a temporary register to break cycles

-- NOTE: here we assume that the values all take a word
-- we need to adjust the code if this changes at some point.

-- ---+---------------+---------------+-------------------
--    |    safe       |  argRange     |  prev frames ...
-- ---+---------------+---------------+-------------------

tail_call :: Integer -> Name -> [Atom] -> M [Instr]
tail_call size f as
  = do let argRange  = (safe, size - 1)
       deps <- forEach2 [fst argRange .. snd argRange] (reverse as) uses
       upd  <- forEach (reverse $ D.scc $ array argRange deps) $ \c ->
          case c of
            D.NonRec n -> atom Nothing n
            D.Rec (n:ns) -> do is <- forEach (n:ns) (atom (Just n))
                               return (Mov the_size (loc n) (Reg reg_C)
                                                                 : concat is)
            D.Rec [] -> bug "tail_call.arg" "Empty Rec SCC"

       let adjStack
             | safe == 0  = []
             | otherwise  = [ Add the_size (num (safe * word_size))
                                           (Reg reg_stack) ]

       funL <- getFunLabel f
       return (concat upd ++ adjStack ++ [ Jmp (lab funL) ])
  where
  -- the safe range is where we are not going to overwrite anything
  -- may be negative if current frame is small
  safe = size - fromIntegral (length as)

  -- dependecies within the unsafe range
  uses n (Lit _) = return (n, [])
  uses n (Var x) = do l <- getVarLoc x
                      case stVar l of
                        Just m | m >= safe && m /= n  -> return (n,[m])
                        _                             -> return (n,[])

  loc n = arr n reg_stack

  stVar :: Arg t s -> Maybe Integer
  stVar (Mem (Offset (Num m) (Just reg) Nothing))
    | is_reg_stack reg = Just (m `div` word_size)
  stVar _              = Nothing

  -- update an argumnet (c is the cycle breaker)
  atom :: Maybe Integer -> Integer -> M [Instr]
  atom c n
    = case as !! fromIntegral (size - n - 1) of
        Lit (Int x) -> return [ Mov the_size (num x) (loc n) ]
        Var x ->
         do l <- getVarLoc x
            return $
              case (stVar l, c) of
                (Just m, Just c) | m == c  ->
                                [ Mov the_size (Reg reg_C) (loc n) ]
                (Just m, _)      | m == n  -> []
                _ -> [ Mov the_size l (Reg reg_A)
                     , Mov the_size (Reg reg_A) (loc n)
                     ]



-- | Crash with a message.
crash msg = let (pre,as,post) = call_C l_crash $ \_ -> [ arg (lab msg)
                                                       , arg (Reg reg_C)
                                                       ]
            in pre ++ concat as ++ post
  where arg _ (InReg r) | is_reg_C r = error $ "in def of 'crash':" ++
                              "the C calling convention will clobber the tag"
        arg x (InReg r)   = [ Mov the_size x (Reg r) ]
        arg x (OnStack m) = [ Mov the_size x m ]

fun :: (a -> M [Instr]) -> FunDecl a -> M [Instr]
fun how f
  = do let msgCrash = "2"
           crashL   = "3"
           name = show (funName f)

       body <- withLocals (reverse (funArgs f))
             $ withHandler (crashL ++ "f")
             $ how (funDef f)

       let msg = "Pattern match failure in " ++ name ++ "\n"
           crashCode
             = [ Label msgCrash
               , String msg
               , Label crashL
               ] ++ crash (msgCrash ++ "b")

       (l,glob) <- getFunInfo (funName f)
       let globD i = if glob then Global l : i else i
       return ( Comment ("Function: " ++ name)
              : globD (Label l : body ++ crashCode)
              )

-- Atoms -----------------------------------------------------------------------

-- Move a value to a register
atomIn             :: Reg R WordSize -> Atom -> M [Instr]
atomIn r a          = atomIn' r 0 a

-- Move a value to a register, adjusting for a stack change
atomIn'            :: Reg R WordSize -> Integer -> Atom -> M [Instr]
atomIn' r o (Var x)       = do l <- getVarLoc' o x
                               return [Mov the_size l (Reg r)]
atomIn' r _ (Lit (Int x)) = return [Mov the_size (num x) (Reg r)]


-- Clear junk from bitdata atoms
-- XXX: It appears that there is a problem when the mask becomes very big
-- so for now we just shift left & rught.
norm n x        = [ Shl the_size (Just bits) (Reg x)
                  , Shr the_size (Just bits) (Reg x)
                  ]
  where bits = num (word_size_bits - fromIntegral n)
--------------------------------------------------------------------------------


-- Statements ------------------------------------------------------------------

tail_stmt                  :: S.Stmt -> M [Instr]
tail_stmt (S.Call f as)     = do s <- frameDescr
                                 tail_call (obj_size s) f as
tail_stmt (S.LetM x s1 s2)  = do is1 <- stmt s1
                                 is2 <- withLocals [x] (tail_stmt s2)
                                 return (is1 ++ [Push the_size (Reg reg_C)]
                                                                        ++ is2)
tail_stmt (S.PrimS p as)    = toTail =<< primS p as
tail_stmt (S.CommS s)       = tail_comm tail_stmt s


stmt                       :: S.Stmt -> M [Instr]
stmt (S.Call f as)    = fun_call f as
stmt (S.LetM x s1 s2) =
  do is1 <- stmt s1
     is2 <- withLocals [x] (stmt s2)
     return ( is1 ++ [ Push the_size (Reg reg_C) ]
           ++ is2 ++ [ Add the_size (num word_size) (Reg reg_stack) ])
stmt (S.PrimS p as)         = primS p as
stmt (S.CommS s)            = comm stmt s




-- Expressions -----------------------------------------------------------------

tail_expr          :: Expr -> M [Instr]
tail_expr (Atom a)    = toTail =<< atomIn reg_A a
tail_expr (Con c as)  = toTail =<< con c as
tail_expr (Prim p as) = toTail =<< prim p as
tail_expr (App f as)  = do s <- frameDescr
                           tail_call (obj_size s) f as
tail_expr (CommE e)   = tail_comm tail_expr e
tail_expr (Do _)      = "tail_expr" `unexpected` "Do"



-- | Compile an expression.
-- We return (required heap, instructions)
expr               :: Expr -> M [Instr]
expr (Atom a)       = atomIn reg_A a
expr (Con c as)     = con c as
expr (Prim p as)    = prim p as
expr (App f as)     = fun_call f as
expr (CommE e)      = comm expr e
expr (Do _)         = "expr" `unexpected` "Do"



-- Common between statemnts and expressions ------------------------------------

tail_comm                      :: (a -> M [Instr]) -> Comm a -> M [Instr]
tail_comm how (Let d e)         = decl d (how e)
                                  -- XXX: the pops after the 'e' are dead code
tail_comm how (Handle e1 e2)    = do hL <- newLabel
                                     i1 <- withHandler hL (how e1)
                                     i2 <- how e2
                                     return (i1 ++ [Label hL] ++ i2)
tail_comm _ (Raise _)           = tryNext
tail_comm how (Switch x as)     = tail_switch # aTag x
                                      <## (unzip # forEach as (alt how))
tail_comm how (BSwitch x as)    = tail_switch # bTag x
                                      <##(unzip # forEach as (balt how))



comm                   :: (a -> M [Instr]) -> Comm a -> M [Instr]
comm how (Let d e)      = decl d (how e)
comm how (Handle e1 e2) = do hL <- newLabel
                             contL <- newLabel
                             i1 <- withHandler hL (how e1)
                             i2 <- how e2
                             return ( i1 ++ [ Jmp (lab contL) ]
                                 ++ ( Label hL : i2 )
                                 ++ [ Label contL ]
                                    )


comm how (Switch x as)    = switch # aTag x
                             <## (unzip # (forEach as (alt how)))
comm how (BSwitch x as)   = switch # bTag x
                             <## (unzip # (forEach as (balt how)))
comm _ (Raise _)          = tryNext


toTail code = do s <- frameDescr
                 return (code ++ [ Add the_size (num (obj_size s * word_size))
                                                (Reg reg_stack)
                                 , Ret Nothing])



-- Decisions -------------------------------------------------------------------

-- for APtr value is in reg_A
alt how (Case (UName c) e)
  | A.isNull c || A.isPtr c =
  do yes <- newLabel
     code <- how e
     let op   = if A.isNull c then E else NE
         test = [ Cmp the_size (num 0) (Reg reg_A)
                , J op (lab yes)
                ]
     return (test, Label yes : code)

-- tag in reg_C
alt how (Case c e)  = do inf <- getConInfo c
                         yes <- newLabel
                         code <- how e
                         let tag = fromIntegral (cTag inf) .&. lower_half_mask
                             test = [ Cmp the_size (num tag) (Reg reg_C)
                                    , J E (lab yes)
                                    ]
                         return (test, Label yes : code)

-- value in reg_C
balt how (BCase p e)= do yes <- newLabel
                         code <- how e
                         return (foldr (try yes) [] (BDD.patTests p)
                                , Label yes : code)
  where
  try y (v,m) next  = Mov the_size (Reg reg_C) (Reg reg_A)
                    : And the_size (num m) (Reg reg_A)
                    : Cmp the_size (num v) (Reg reg_A)
                    : J E (lab y)
                    : next

aTag   :: Name -> M [Instr]
aTag x  = do getX <- atomIn reg_A (Var x)
             p <- varIsPtr x
             return (if p then getX
                          ++ [ Mov the_size (mem reg_A) (Reg reg_C) ]
                          ++ just_tag
                          else getX)
  -- XXX:
  where just_tag = let half = Just (num (word_size_bits `div` 2))
                   in [ Shl the_size half (Reg reg_C)
                      , Shr the_size half (Reg reg_C)
                      ]


bTag   :: Atom -> M [Instr]
bTag x  = atomIn reg_C x


switch :: [Instr] -> ([[Instr]],[[Instr]]) -> M [Instr]
switch getTag (tests, code)
  = do onSucc <- newLabel
       let code' = do c <- code; c ++ [Jmp (lab onSucc)]
       onFail <- tryNext
       return (getTag ++ concat tests ++ onFail ++ code' ++ [Label onSucc])

tail_switch :: [Instr] -> ([[Instr]],[[Instr]]) -> M [Instr]
tail_switch getTag (tests, code)
  = do onFail <- tryNext
       return (getTag ++ concat tests ++ onFail ++ concat code)


tryNext             = do h <- getHandler
                         return [ Add the_size (num (hPop h * word_size))
                                               (Reg reg_stack)
                                , Jmp (lab (hGoto h)) ]



--- Declarations ---------------------------------------------------------------

decl (AVal x e) k
  = do i1 <- expr e
       i2 <- withLocals [x] k
       return (i1 ++ [ Push the_size (Reg reg_A) ]
            ++ i2 ++ [ Add the_size (num word_size) (Reg reg_stack) ])

decl (Cyc xs) k = cycDecl addLocs save post xs
  where addLocs xs  = withLocals [ x | (x,_,_) <- reverse xs ]
        save _      = return (Push the_size (Reg reg_C))
        post        = do code <- k
                         let size = word_size * fromIntegral (length xs)
                         return (code ++ [ Add the_size (num size)
                                                        (Reg reg_stack) ])

decl d _            = "decl" `unexpected` show d



topDecl (AVal x e)  = do i <- expr e
                         l <- getGlob (varName x)
                         return (i ++ [ Mov the_size (Reg reg_A) (mem l) ])
topDecl (Area {})   = return []

topDecl (Cyc xs)    = cycDecl addLocs save post xs
  where addLocs _ m   = m
        save (x,_,_)  = (Mov the_size (Reg reg_C) . mem) #
                                                      getGlob (varName x)
        post          = return []

topDecl (AFun {})   = "topDecl" `unexpected` "AFun"
topDecl (Rec {})    = "topDecl" `unexpected` "Rec"

-- xs: The cyclic declarations.
cycDecl addLocs save post xs
  = do infos <- forEach xs (\(_,c,_) -> getConInfo c)
       let sizes = map (obj_size . cShape) infos
       doAlloc <- alloc (sum sizes)
       addLocs xs
         $ do saves   <- forEach xs save
              ass     <- forEach xs (\(_,_,as) -> forEach as (atomIn reg_C))
              code    <- post
              return ( doAlloc
                    ++ initObjs saves sizes
                    ++ initFields 0 sizes (map cTag infos) ass
                    ++ code )
  where
  -- | reg_A: pointer to 1st object
  initObjs :: [Instr] -> [Integer] -> [Instr]
  initObjs (save:saves) sizes
    = Mov the_size (Reg reg_A) (Reg reg_C)
    : save
    : do (save,s) <- zip saves (init sizes)
         [ Add the_size (num (word_size*s)) (Reg reg_C) , save ]

  initObjs _ _ = []

  -- the tag is usually a large immediate, which cannot be moved
  -- directly to memoy, so we move it via a reg.
  set_tag off t = [ Mov the_size (num (fromIntegral t)) (Reg reg_C)
                  , Mov the_size (Reg reg_C) (arr off reg_A)
                  ]

  -- | reg_A: pointer to 1st object
  initFields off (s:ss) (t:ts) (as:ass) =
      set_tag off t
   ++ concat [ a ++ [ Mov the_size (Reg reg_C) (arr o reg_A) ]
                                     | a <- as | o <- [off + 1 ..] ]
    ++ initFields (off + s) ss ts ass
  initFields _ _ _ _ = []




-- Constructors and primitives -------------------------------------------------

con (UName c) [] | A.isNull c = return [ Mov the_size (num 0) (Reg reg_A) ]
con (UName c) [a] | A.isPtr c = atomIn reg_A a
con c as = do inf <- getConInfo c
              is  <- forEach2 [1 :: Integer ..] as $ \n a ->
                     do getField <- atomIn reg_C a
                        return ( getField
                            ++ [ Mov the_size (Reg reg_C) (arr n reg_A) ]
                               )
              doAlloc <- alloc (obj_size $ cShape inf)
              return ( doAlloc
                    ++ [ Mov the_size (num (cTag inf)) (Reg reg_C)
                       , Mov the_size (Reg reg_C) (mem reg_A)
                       ]
                    ++ concat is )


-- call_C 

-- XXX
swapBytes (OpEv LeEv _) = []
swapBytes (OpEv BeEv [IntEv n])
  = case n of
      0 -> []
      1 -> []
      2 -> [ Xchg B1 (Reg AL) (Reg AH) ]
      3 -> [ Shl the_size (Just (num 8)) (Reg reg_A), Bswap the_size (Reg reg_A) ]
      4 -> [ Bswap the_size (Reg reg_A) ]
      5 -> [ Shl B8 (Just (num 24)) (Reg RAX), Bswap the_size (Reg RAX) ]
      6 -> [ Shl B8 (Just (num 16)) (Reg RAX), Bswap the_size (Reg RAX) ]
      7 -> [ Shl B8 (Just (num 8))  (Reg RAX), Bswap the_size (Reg RAX) ]
      8 -> [ Bswap the_size (Reg RAX) ]
      _ -> "swapBytes" `unexpected` show n
swapBytes e = "swapBytes" `unexpected` show e


-- | Effecful primitives
primS (UserPrim p es) as = strip p es as
  where
  strip (A.Inst f _) es as   = strip f es as      -- ignore type apps
  strip (A.Qual _ x) es as   = strip x es as      -- ignore qualifiers (XXX?)
  strip (A.VarName x) es as  = op x es as
  strip x _ _ = "primS.strip" `unexpected` show x

  op "return" [] [x] = atomIn reg_A x

  op "readRef" [_,e] [x]
    = do getX <- atomIn reg_A x
         return ( getX ++ [ Mov the_size (mem reg_A) (Reg reg_A) ]
                                                            ++ swapBytes e )

  op "writeRef" [_,e] [x,y]
    = do getX <- atomIn reg_C x
         getY <- atomIn reg_A y
         return (getX ++ getY ++ swapBytes e ++
                  [ Mov the_size (Reg reg_A) (mem reg_C) ])


  -- XXX: Perhaps call the external functions directly?

  op "memZero" [_,IntEv n] [x]
    = do getX <- atomIn reg_dst x
         return (getX ++ [ Mov the_size (num 0) (Reg AL)
                         , Mov the_size (num (fromIntegral n)) (Reg reg_C)
                         , Cld
                         , RepStos B1 ])

  op "memCopy" [_,IntEv n] [x,y]
    = do getX <- atomIn reg_src x
         getY <- atomIn reg_dst y
         return (getX ++ getY ++
                [ Mov the_size (Imm (Num (fromIntegral n))) (Reg reg_C)
                , Cld
                , RepMovs B1 ])

  -- XXX: 8 bytes/char is too much?
  -- XXX: should we clean the upper bits of the char?
  op "putChar" [] [x] = do_call_C l_putchar [ (x,Nothing) ]

{-
-- IA32 hardware primitives ----------------------------------------------------
  op "inB" [] [x] 
    = do getX <- atomIn EDX x
         return (getX ++ [In B1 Nothing])

  op "outB" [] [x,y] 
    = do getX <- atomIn EDX x
         getY <- atomIn reg_A y
         return (getX ++ getY ++ [Out B1 Nothing])
  -- Alignment is 8
  op "setGDT" [_,IntEv n] [x]
    = do getX <- atomIn reg_A x
         return (getX ++ [ Push the_size (Reg reg_A)
                         , Push B2 (Imm (Num (fromIntegral n - 1)))
                         , Lgdt (mem ESP)
                         , Add the_size (Imm (Num 6)) (Reg ESP) ])

  -- Alignemnt is 8
  op "setIDT" [_,IntEv n] [x]
    = do getX <- atomIn reg_A x
         return (getX ++ [ Push the_size (Reg reg_A)
                         , Push B2 (Imm (Num (fromIntegral n - 1)))
                         , Lidt (mem ESP)
                         , Add the_size (Imm (Num 6)) (Reg ESP) ])
 
  op "lidt" [] [x]
    = do getX <- atomIn reg_A x
         return (getX ++ [Lidt (mem reg_A)])

  op "ltr" [] [x]
    = do getX <- atomIn reg_A x
         return (getX ++ [Ltr (Reg AX)])

  op "setCS" [] [x] = do getX <- atomIn reg_A x
                         return (getX ++ [ Push B2 (Reg AX) 
                                         , Push the_size (Imm (Lab "1f"))
                                         , JmpFar (FarMem (mem ESP)) 
                                         , Label "1"
                                         , Add the_size (Imm (Num 6)) (Reg ESP) ])

  op "setDS" [] [x] = setSeg DS x
  op "setSS" [] [x] = setSeg SS x
  op "setES" [] [x] = setSeg ES x
  op "setFS" [] [x] = setSeg FS x
  op "setGS" [] [x] = setSeg GS x

  op "halt" [] [] = return [ Label "1"
                           , Halt
                           , Jmp (mem "1b") ]
                          
  op "cli" [] [] = return [ Cli ]
  op "sti" [] [] = return [ Sti ]

  op "asmCallUser" [_] [x] = do getX <- atomIn reg_A x
                                return (getX ++ [Jmp (Imm (Lab "asmCallUser"))])


  -- NOTE: here we assume that page tables have 1-1 phys/virt mapping

  op "getPDir" [] []
    = return [ Mov the_size (Reg CR3) (Reg reg_A) ]

  op "setPDir" [] [x]
    = do getX <- atomIn reg_A x
         return (getX ++ [Mov the_size (Reg reg_A) (Reg CR3)])

  op "tlbFlushAt" [] [x]
    = do getX <- atomIn reg_A x
         return (getX ++ [Invlpg (mem reg_A)])
-}

  op x e as = bug "primS.op" $ unlines ["(op) Missing (effecful) primitive:"
                                       , show x, show e, show as ]

primS p as = bug "primS" $ unlines ["(primS) Missing (effecful) primitive:"
                                       , show p, show as ]

{-
setSeg reg (Var x)  = do x <- getVarLoc x
                         return [Mov B2 x (Reg reg)]

setSeg reg (Lit (Int n)) = return [ Mov B2 (Imm (Num n)) (Reg AX)
                                  , Mov B2 (Reg AX) (Reg reg) ]
-}


c_arg n a c (InReg r)   = do is <- atomIn' r n a
                             return (is ++ clean)
  where clean = maybe [] (\x -> norm x r) c
c_arg n a c (OnStack m) = do is <- atomIn' reg_A n a
                             return (is ++ clean ++
                                            [ Mov the_size (Reg reg_A) m ])
  where clean = maybe [] (\x -> norm x reg_A) c

do_call_C f as =
  do let (pre,args,post) = call_C f $ \s -> map (uncurry (c_arg s)) as
     iss <- sequence args
     return (pre ++ concat iss ++ post)


-- | Pure primitives
prim (UserPrim (A.Inst x _) es) vs = prim (UserPrim x es) vs
prim (UserPrim (A.Qual _ (A.VarName x)) es) as = op x es as
  where

  -- ... just for debugging ...
  op "trace" [IntEv n] [x,y] = do_call_C l_trace [(x,Nothing),(y,Just n)]

  -- instances of Literal for Bit
  op "fromNat" [OpEv (LitEv ForBit) [_]] [x]  = atomIn reg_A x

  -- instances of Literal for Ix
  op "fromNat" [OpEv (LitEv ForIx) [IntEv n]] [x]
    = do getX <- atomIn reg_A x
         return ( getX ++
                [ Mov the_size (imm 0) (Reg reg_D)
                , Mov the_size (imm n) (Reg reg_C)
                , Div the_size (Reg reg_C)
                , Mov the_size (Reg reg_D) (Reg reg_A) ])

  -- Eq instance for Bit
  op "==" [OpEv (EqEv ForBit) [IntEv n]] [x,y] = boolI (J E) n x y
  op "/=" [OpEv (EqEv ForBit) [IntEv n]] [x,y] = boolI (J NE) n x y

  -- Eq instance for Ix
  op "==" [OpEv (EqEv ForIx) []] [x,y] = boolI' unchanged (J E) x y
  op "/=" [OpEv (EqEv ForIx) []] [x,y] = boolI' unchanged (J NE) x y

  -- Eq instance for APtr and ARef
  op "==" [OpEv (EqEv ForPtr) []] [x,y] = boolI' unchanged (J E) x y
  op "/=" [OpEv (EqEv ForPtr) []] [x,y] = boolI' unchanged (J NE) x y

  -- Ord instance for Bit
  op "<"  [OpEv (OrdEv ForBit) [IntEv n]] [x,y] = boolI (J B)   n x y
  op "<=" [OpEv (OrdEv ForBit) [IntEv n]] [x,y] = boolI (J BE)  n x y
  op ">"  [OpEv (OrdEv ForBit) [IntEv n]] [x,y] = boolI (J A)   n x y
  op ">=" [OpEv (OrdEv ForBit) [IntEv n]] [x,y] = boolI (J AE)  n x y


  -- Ord instance for Ix  (or signed?)
  op "<"  [OpEv (OrdEv ForIx) []] [x,y] = boolI' unchanged (J B)  x y
  op "<=" [OpEv (OrdEv ForIx) []] [x,y] = boolI' unchanged (J BE) x y
  op ">"  [OpEv (OrdEv ForIx) []] [x,y] = boolI' unchanged (J A)  x y
  op ">=" [OpEv (OrdEv ForIx) []] [x,y] = boolI' unchanged (J AE) x y

  -- Num instance for Bit
  op "+" [OpEv (NumEv ForBit) [_]] [x,y]  = simpleI Add x y
  op "-" [OpEv (NumEv ForBit) [_]] [x,y]  = simpleI Sub x y
  op "neg" [OpEv (NumEv ForBit) [_]] [x]  = simpleI1 Neg x

  op "*" [OpEv (NumEv ForBit) [_]] [x,y]  = simpleI (\o a _ -> Mul o a) x y

  op "/" [OpEv (NumEv ForBit) [IntEv n]] [x,y]
    = do getX <- atomIn reg_A x
         getY <- atomIn reg_C y
         return (getX ++ getY ++   norm n reg_C ++
                                 [ Mov the_size (num 0) (Reg reg_D)
                                 , Div the_size (Reg reg_C) ])

  -- BitOps instnace for Bit
  op "<<" [OpEv (BitOpsEv ForBit) [_]] [x,y]
      = do getX <- atomIn reg_A x
           getY <- atomIn reg_C y
           return (getX ++ getY ++ [ Shl the_size Nothing (Reg reg_A) ])

  op ">>" [OpEv (BitOpsEv ForBit) [_]] [x,y]
      = do getX <- atomIn reg_A x
           getY <- atomIn reg_C y
           return (getX ++ getY ++ [ Shr the_size Nothing (Reg reg_A) ])

  op "&" [OpEv (BitOpsEv ForBit) [_]] [x,y]  = simpleI And x y
  op "!" [OpEv (BitOpsEv ForBit) [_]] [x,y]  = simpleI Or x y
  op "^" [OpEv (BitOpsEv ForBit) [_]] [x,y]  = simpleI Xor x y
  op "~" [OpEv (BitOpsEv ForBit) [_]] [x]    = simpleI1 Not x


  -- Bounded instance Bit
  op "maxVal" [OpEv (BoundedEv ForBit) [IntEv m]] []
    = return [Mov the_size (num (2^m-1)) (Reg reg_A)]
  op "minVal" [OpEv (BoundedEv ForBit) [_]]  []
    = return [Mov the_size (num 0) (Reg reg_A)]

  -- Bounded instance Ix
  op "maxVal" [OpEv (BoundedEv ForIx) [IntEv m]] []
    = return [Mov the_size (imm (m-1)) (Reg reg_A)]
  op "minVal" [OpEv (BoundedEv ForIx) [_]]  [] 
    = return [Mov the_size (num 0) (Reg reg_A)]

  op "fromBits" _ [x] = atomIn reg_A x
  op "toBits" _ [x]   = atomIn reg_A x

  op "sizeOf" [IntEv x] _ = return [ Mov the_size (imm x) (Reg reg_A) ]

  -- XXX:
  -- op "#" [OpEv JoinEv [IntEv _,IntEv n]] [x,y]
  op "#" [IntEv _,IntEv n,_,_] [x,y]
    = do getX <- atomIn reg_A x
         getY <- atomIn reg_C y
         return ( getX ++ getY ++
                  norm n reg_C ++
                [ Shl the_size (Just (imm n)) (Reg reg_A)
                , Or the_size (Reg reg_C) (Reg reg_A) ])


  op "@" [_, _, IntEv s, _] [x,y]
    = do getX <- atomIn reg_C x
         getY <- atomIn reg_A y
         return (get getX getY s)

      where get x y 1 = x ++ y ++ [ Lea (mem (reg_C,reg_A,B1)) (Reg reg_A) ]
            get x y 2 = x ++ y ++ [ Lea (mem (reg_C,reg_A,B2)) (Reg reg_A) ]
            get x y 4 = x ++ y ++ [ Lea (mem (reg_C,reg_A,B4)) (Reg reg_A) ]
            get x y 8 = x ++ y ++ [ Lea (mem (reg_C,reg_A,B8)) (Reg reg_A) ]
            get x y s = y ++ [ Mov the_size (imm s) (Reg reg_C)
                             , Mul the_size (Reg reg_C)
                             ] ++ x ++ [ Lea (mem (reg_C,reg_A)) (Reg reg_A) ]

  op "bitIx" [IntEv w,_,_] [x]
    = do getX <- atomIn reg_A x
         return (getX ++ norm w reg_A)

  op "fromBytes" _ [x]  = atomIn reg_A x
  op "toBytes" _ [x]    = atomIn reg_A x

  op x [] []  = trace ("WARNING: " ++ x ++
                  " initialized to an external address.")
                return [ Mov the_size (lab x) (Reg reg_A) ]

  op x es as = bug "prim.op"
          $ unlines ["Missing primitive", x, show es, show (length as)]


-- signed
prim PGEQ [x,y]   = do getX <- atomIn reg_A x
                       getY <- atomIn reg_C y
                       code <- decide (J GE) reg_C reg_A
                       return (getX ++ getY ++ code)

-- unsigned
prim PLEQ [x,y]   = do getX <- atomIn reg_A x
                       getY <- atomIn reg_C y
                       code <- decide (J BE) reg_C reg_A
                       return (getX ++ getY ++ code)

prim PIncBy [x,y] = do getX <- atomIn reg_C x
                       getY <- atomIn reg_A y
                       return (getX ++ getY ++
                             [ Add the_size (Reg reg_C) (Reg reg_A) ])

prim PDecBy [x,y] = do getX <- atomIn reg_C x
                       getY <- atomIn reg_A y
                       return (getX ++ getY ++
                             [ Sub the_size (Reg reg_C) (Reg reg_A) ])

prim (UserPrim (A.Select _) [OpEv BitFieldEv [IntEv z, IntEv x, IntEv y]]) as
    = prim (PGetFieldB z (A.BitField x y)) as

prim (UserPrim (A.Select _) [OpEv FieldEv [IntEv o,_,_]]) [x]
    = do getX <- atomIn reg_A x
         return (getX ++ [ Add the_size (imm o) (Reg reg_A) ])

prim (UserPrim (A.Select l) e) _
  = bug ("select " ++ show l) ("bad evidence: " ++ show e)

prim (UserPrim (A.Update _) [OpEv BitFieldEv [IntEv z, IntEv x, IntEv y]]) as
    = prim (PUpdFields z [A.BitField x y]) as

prim (UserPrim (A.Update l) e) _
  = bug ("update " ++ show l) ("bad evidence: " ++ show e)

prim (PGetFieldA (UName c) 0) [x]
  | A.isPtr c = atomIn reg_A x

prim (PGetFieldA _ n) [x]
  = do getX <- atomIn reg_A x
       let off = word_size * (fromIntegral n + 1) :: Integer
       return (getX ++ [ Mov the_size (mem (off,reg_A)) (Reg reg_A) ])

prim (PGetFieldB _ b) [x]
  = do getX <- atomIn reg_A x
       return (getX ++ [ Shr the_size (Just (imm (A.bfOffset b))) (Reg reg_A) ])


prim (PUpdFields _ bs) (a:as)
  = do getA <- atomIn reg_A a
       let mask = foldr (.&.) (-1) (map bfMask bs)
       loop (getA ++ [ And the_size (num mask) (Reg reg_A) ]) as bs
  where
  loop code (a:as) (b:bs)
    = do getA <- atomIn reg_C a
         let code' = code ++ getA ++
                     norm (A.bfWidth b) reg_C ++
                   [ Shl the_size (Just (imm (A.bfOffset b))) (Reg reg_C)
                   , Or the_size (Reg reg_C) (Reg reg_A)
                   ]
         loop code' as bs
  loop code [] []         = return code
  loop _ _ _ = bug "prim.PUpdFields" "mismatched args"

  -- a maks that clears the content of a bit field.
  bfMask :: A.BitField -> Integer
  bfMask b = complement
           ((2^(A.bfWidth b) - 1) `shiftL` fromIntegral (A.bfOffset b))


prim p as = "prim" `unexpected` show (p,as)


imm :: (Integral a) => a -> Arg I t
imm x = num (fromIntegral x)
 

boolI op n x y = boolI' (\x -> norm n x) op x y

boolI' norm op x y  
  = do getX <- atomIn reg_A x
       getY <- atomIn reg_C y
       code <- decide op reg_C reg_A
       return (getX ++ getY ++ norm reg_A ++ norm reg_C ++ code)

decide op a b  
  = do false <- getGlob (UName (A.Qual "Prelude" (A.ConName "False")))
       true <- getGlob (UName (A.Qual "Prelude" (A.ConName "True")))
       doneL <- newLabel
       yesL <- newLabel
       return [ Cmp the_size (Reg a) (Reg b)
              , op (lab yesL)
              , Mov the_size (mem false) (Reg reg_A)
              , Jmp (lab doneL)
              , Label yesL
              , Mov the_size (mem true) (Reg reg_A)
              , Label doneL
              ]

-- XXX: we can use a memory operation for the one operand
simpleI op x y  = do getX <- atomIn reg_A x
                     getY <- atomIn reg_C y
                     return (getX ++ getY ++ [ op the_size (Reg reg_C) (Reg reg_A) ])

simpleI1 op x   = do getX <- atomIn reg_A x
                     return (getX ++ [ op the_size (Reg reg_A) ])

unchanged _     = []





-- Put it all together ---------------------------------------------------------

type ExpOpts  = [ (A.Name, Label) ]


nameFunDs    :: (A.Name -> Name) 
             -> [FunDecl a] -> StateT ExpOpts L (Map.Map Name (Label,Bool))
nameFunDs how fs = Map.fromList # forEach fs pickLabel
  where 
  pickLabel f = do opts <- get
                   let name = funName f
                   l <- case remove (\(x,_) -> how x == name) opts of
                          Nothing -> do l <- lift newLabelL
                                        return (l,False)
                          Just ((_,l),xs) -> set xs >> return (l,True)
                   return (name, l)


nameFuns :: ExpOpts 
         -> [FunDecl S.Stmt] -> [FunDecl Expr] -> L (Map.Map Name (Label,Bool))
nameFuns exps ps fs  
  = do (m,s) <- runStateT exps
              $ do e1 <- nameFunDs (ProcFor . UName) ps
                   e2 <- nameFunDs (FunFor . UName) fs
                   return (e1 `Map.union` e2)
       case s of
         [] -> return m  
         xs -> inBase (err [msg])
            where msg = unlines ("Unknown exports:" : map sh xs)
                  sh (a,l) = show a ++ " -> " ++ l
                                          
                            
  
              
               
compile :: [Option] -> ExpOpts -> [A.ADT] -> [FunADT] 
        -> [FunDecl Expr] -> [FunDecl S.Stmt] -> [Decl]
        -> Pass ([Instr],Doc)
compile opts exps adts fdts fs ps ds
  = runL 
  $ do funEnv <- nameFuns exps ps fs
       (globDs, scavGlobsC, globEnv) <- gcGlobs opts ds
       let (tables, fdtEnv, adtEnv, scav1) = gcData fdts adts
           env = defaultEnv 
                   { globals  = globEnv
                   , funs     = funEnv
                   , adtCtrs  = adtEnv
                   , funCtrs  = fdtEnv
                   }

       (code,scav2) <- runM env 
             $ do is1 <- forEach ds topDecl
                  is2 <- forEach fs (fun tail_expr)
                  is3 <- forEach ps (fun tail_stmt)
                  is4 <- fun_call finalEntry []
                  return (
                    [ CommentBlock [ "Initialize global variables" ]
                    , Section ".text"
                    , Global l_main
                    , Label l_main ]
                   ++ concat is1  -- init other globals
                   ++ is4 ++
                    [ Ret Nothing
                    , Label "CRASH" ]
                   ++ crash "CRASH_msg" ++

                    [ Section ".data"
                    , Label "CRASH_msg"
                    , String "Pattern match failure at top level"

                    , Section ".text"
                    , CommentBlock [ "The functions" ] ]
                   ++ concat is2 ++
                    [ CommentBlock [ "The procedures" ] ]
                   ++ concat is3 )

       let scavs = scavGlobsC $$ scavFunsC (nub (scav1 ++ scav2))

       return (globDs ++ code
              , scavs $$ tables
              )



